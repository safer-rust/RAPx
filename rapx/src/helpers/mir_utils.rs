#[cfg(not(rapx_ge_100))]
use rustc_hir::LangItem;
#[cfg(rapx_ge_100)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::{
    ItemKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::interpret::{AllocId, GlobalAlloc},
    mir::{
        BasicBlock, Body, ConstValue, Local, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    },
    ty::{
        ConstKind, FieldDef, GenericArgKind, GenericArgsRef, PseudoCanonicalInput, Ty, TyCtxt,
        TyKind, TypingEnv,
    },
};
use rustc_span::{DUMMY_SP, Symbol};

use std::collections::{HashMap, HashSet};

#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;

use crate::{
    analysis::alias::{LocalOriginMap, collect_local_origins},
    compat::FxHashMap,
    helpers::mir_scan::Checkpoint,
};

use super::def_use::PlaceKey;

pub(crate) fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

pub(crate) fn dep_callee_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = c.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

/// Whether `func` is a call to `PartialEq::eq` (the equality comparison),
/// determined from its `DefId` rather than by string-matching the callee path.
pub(crate) fn is_eq_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(def_id) = dep_callee_def_id(func) else {
        return false;
    };
    let Some(assoc) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    if assoc.name().as_str() != "eq" {
        return false;
    }
    // Must be a trait method (`PartialEq::eq`), not an inherent `eq`.
    let Some(trait_id) = assoc.trait_container(tcx) else {
        return false;
    };
    tcx.def_path_str(trait_id).ends_with("PartialEq")
}

/// Whether `def_id` is `core::ptr::drop_in_place`.
pub(crate) fn is_drop_in_place(def_id: DefId) -> bool {
    crate::def_id::drop_in_place() == Some(def_id)
}

/// Whether `def_id` is a diverging call target: a `panic*` lang item or the
/// `unreachable`/`abort` intrinsics.
pub(crate) fn is_diverging_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.is_lang_item(def_id, LangItem::Panic)
        || tcx.is_lang_item(def_id, LangItem::PanicNounwind)
        || tcx.is_lang_item(def_id, LangItem::PanicFmt)
        || tcx.is_lang_item(def_id, LangItem::PanicDisplay)
        || tcx.is_lang_item(def_id, LangItem::ConstPanicFmt)
        || tcx.is_lang_item(def_id, LangItem::PanicBoundsCheck)
        || tcx.is_lang_item(def_id, LangItem::PanicMisalignedPointerDereference)
        || tcx.intrinsic(def_id).is_some_and(|i| {
            i.name == rustc_span::sym::unreachable || i.name == rustc_span::sym::abort
        })
}

/// The concrete `core::ops::Range*` struct a `DefId` denotes.
pub(crate) enum RangeKind {
    RangeTo,
    RangeFrom,
    Range,
    RangeInclusive,
    Other,
}

/// Classify a `DefId` as one of the `core::ops::Range*` structs.
pub(crate) fn range_kind(tcx: TyCtxt<'_>, def_id: DefId) -> RangeKind {
    if tcx.is_lang_item(def_id, LangItem::RangeTo) {
        RangeKind::RangeTo
    } else if tcx.is_lang_item(def_id, LangItem::RangeFrom) {
        RangeKind::RangeFrom
    } else if tcx.is_lang_item(def_id, LangItem::RangeInclusiveStruct) {
        RangeKind::RangeInclusive
    } else if tcx.is_lang_item(def_id, LangItem::Range) {
        RangeKind::Range
    } else {
        RangeKind::Other
    }
}

/// Whether `def_id` is any `core::ops::Range*` struct.
pub(crate) fn is_range_type(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    !matches!(range_kind(tcx, def_id), RangeKind::Other)
        || tcx.is_lang_item(def_id, LangItem::RangeToInclusive)
        || tcx.is_lang_item(def_id, LangItem::RangeFull)
}

/// Whether `def_id` is the `Index::index` / `IndexMut::index_mut` trait method.
pub(crate) fn is_index_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    let name = assoc.name();
    if name.as_str() != "index" && name.as_str() != "index_mut" {
        return false;
    }
    let Some(trait_id) = assoc.trait_container(tcx) else {
        return false;
    };
    (tcx.is_lang_item(trait_id, LangItem::Index) && name.as_str() == "index")
        || (tcx.is_lang_item(trait_id, LangItem::IndexMut) && name.as_str() == "index_mut")
}

/// Whether `def_id` is `slice::Iter`/`IterMut`'s private `post_inc_start`
/// helper (a pointer-advancing side effect that cannot be inlined because of
/// its ZST `SwitchInt` branch).
pub(crate) fn is_post_inc_start(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let name = tcx.item_name(def_id);
    name.as_str() == "post_inc_start"
}

/// Whether `def_id` is one of `post_inc_start` / `pre_dec_end`.
pub(crate) fn is_iter_ptr_adj(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let name = tcx.item_name(def_id);
    let n = name.as_str();
    n == "post_inc_start" || n == "pre_dec_end"
}

/// Resolve a (possibly trait-method) callee to the concrete impl method that
/// will actually be dispatched, given the caller context and the callee's
/// generic arguments. Returns `None` when the callee cannot be resolved to a
/// distinct concrete item (e.g. still generic/virtual), or is not a trait
/// method at all (callers should then keep the original DefId).
pub(crate) fn resolve_callee_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    callee_def_id: DefId,
    callee_args: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    let assoc = tcx.opt_associated_item(callee_def_id)?;
    if assoc.trait_container(tcx).is_none() {
        return None;
    }
    let typing_env = TypingEnv::post_analysis(tcx, caller_def_id);
    let instance =
        rustc_middle::ty::Instance::try_resolve(tcx, typing_env, callee_def_id, callee_args)
            .ok()
            .flatten()?;
    let resolved = match instance.def {
        rustc_middle::ty::InstanceKind::Item(def_id) => def_id,
        _ => return None,
    };
    if resolved == callee_def_id {
        None
    } else {
        Some(resolved)
    }
}

/// Like [`dep_callee_def_id`], but resolves trait-method callees to their
/// concrete impl so cross-crate `Deref`/`DerefMut` bodies — whose trait-method
/// DefId has no available MIR — can still be inlined.
pub(crate) fn dep_callee_resolved_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<DefId> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, callee_args) = c.const_.ty().kind() else {
        return None;
    };
    let callee_def_id = *def_id;
    #[cfg(rapx_ge_99)]
    let callee_args = callee_args.skip_binder();
    resolve_callee_impl(tcx, caller, callee_def_id, callee_args).or(Some(callee_def_id))
}

/// Collect all return basic block indices for a function body.
pub fn collect_return_block_indices(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<BasicBlock> {
    let mut blocks = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return blocks;
    }
    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if matches!(data.terminator().kind, TerminatorKind::Return) {
            blocks.push(bb);
        }
    }
    blocks
}

/// Return the callee argument index represented by a MIR local.
///
/// Contract annotations written with parameter names are parsed in the callee's
/// local namespace.  MIR local `_0` is the return place and argument locals are
/// `_1..=_arg_count`, so callee local `_1` denotes checkpoint argument `0`.
pub fn callee_param_index_for_local(tcx: TyCtxt<'_>, callee: DefId, local: usize) -> Option<usize> {
    let arg_count = if tcx.is_mir_available(callee) {
        tcx.optimized_mir(callee).arg_count
    } else {
        tcx.fn_sig(callee)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len()
    };
    arg_of_local(Local::from_usize(local), arg_count)
}

pub fn is_std_crate_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.crate_name(def_id.krate).as_str(),
        "core" | "std" | "alloc"
    )
}

pub fn is_trait_unsafe(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    let Some(local_id) = trait_def_id.as_local() else {
        return false;
    };
    let item = tcx.hir_expect_item(local_id);

    #[cfg(not(rapx_ge_99))]
    if let ItemKind::Trait(_, _, unsafety, _, _, _, _) = &item.kind {
        return matches!(unsafety, rustc_hir::Safety::Unsafe);
    }
    #[cfg(rapx_ge_99)]
    if let ItemKind::Trait { safety, .. } = &item.kind {
        return matches!(safety, rustc_hir::Safety::Unsafe);
    }

    false
}

pub fn resolve_impl_self_ty_def_id(item: &rustc_hir::Item<'_>) -> Option<DefId> {
    let ItemKind::Impl(rustc_hir::Impl { self_ty, .. }) = &item.kind else {
        return None;
    };
    match &self_ty.kind {
        rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Def(
                rustc_hir::def::DefKind::Struct
                | rustc_hir::def::DefKind::Enum
                | rustc_hir::def::DefKind::Union,
                def_id,
            ) => Some(def_id),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a local item carries a `#[rapx::<name>(...)]` attribute.
pub(crate) fn has_rapx_attr(tcx: TyCtxt<'_>, def_id: LocalDefId, name: Symbol) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);

    let rapx = Symbol::intern("rapx");
    let attrs = tcx.hir_attrs(hir_id);

    attrs.iter().any(|attr| {
        if attr.is_doc_comment().is_some() {
            return false;
        }

        let path = attr.path();

        path.len() == 2 && path[0] == rapx && path[1] == name
    })
}

pub fn has_rapx_verify_attr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    has_rapx_attr(tcx, def_id, Symbol::intern("verify"))
}

/// True when a type transitively contains a const-generic parameter or
/// an associated type alias (which may be layout-ambiguous).
fn ty_has_param_const(ty: Ty<'_>) -> bool {
    for arg in ty.walk() {
        match arg.kind() {
            GenericArgKind::Const(c) if matches!(c.kind(), ConstKind::Param(_)) => return true,
            GenericArgKind::Type(inner_ty) if matches!(inner_ty.kind(), TyKind::Alias(..)) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Run `f` inside `catch_unwind`, returning either the result or the
/// downcasted panic message.
pub(crate) fn catch_panic<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_err(|e| {
        e.downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "<rustc ICE>".to_string())
    })
}

/// Return a stable, human-readable name for a MIR call operand.
pub fn call_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> String {
    dep_callee_def_id(func)
        .map(|def_id| tcx.def_path_str(def_id))
        .unwrap_or_else(|| format!("{func:?}"))
}

/// Return the zero-based argument index of `local`, if it is a MIR argument.
///
/// MIR local `_0` is the return place; argument locals start at `_1`.
pub fn arg_of_local(local: Local, arg_count: usize) -> Option<usize> {
    let i = local.as_usize();
    if i >= 1 && i <= arg_count {
        Some(i - 1)
    } else {
        None
    }
}

pub fn has_crate(tcx: TyCtxt<'_>, name: &str) -> bool {
    for num in tcx.crates(()) {
        if tcx.crate_name(*num) == Symbol::intern(name) {
            return true;
        }
    }
    false
}

/// Extracts the source `Place` from an rvalue for simple forwarding operations
/// (copy, move, cast, reference, raw-pointer, copy-for-deref).
pub fn rvalue_source_place<'a, 'tcx>(
    rvalue: &'a Rvalue<'tcx>,
) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    use rustc_middle::mir::{Operand, Rvalue};
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}

// ── PlaceKey / operand utilities ─────────────────────────────────

/// Extract a PlaceKey from a MIR operand.
pub fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    operand_mir_place(operand).map(PlaceKey::from_mir_place)
}

/// Extract the MIR Place from an operand.
pub fn operand_mir_place<'a, 'tcx>(operand: &'a Operand<'tcx>) -> Option<&'a Place<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

/// Return the destination local for a checkpoint's call or deref.
pub fn call_destination<'tcx>(tcx: TyCtxt<'tcx>, checkpoint: &Checkpoint<'tcx>) -> Option<Local> {
    if checkpoint.kind == crate::helpers::mir_scan::CheckpointKind::RawPtrDeref {
        return checkpoint.destination;
    }
    let body = tcx.optimized_mir(checkpoint.caller);
    let terminator = body.basic_blocks[checkpoint.block].terminator();
    let TerminatorKind::Call { destination, .. } = &terminator.kind else {
        return None;
    };
    Some(destination.local)
}

// ── Place resolution utilities ───────────────────────────────────

/// Follow local-origin associations transitively to resolve to the
/// ultimate source (parameter or root local) and accumulated field path.
pub fn deep_resolve_place(mut local: usize, origins: &LocalOriginMap) -> (usize, Vec<usize>) {
    let mut seen = HashSet::new();
    let mut all_fields: Vec<usize> = Vec::new();
    loop {
        if !seen.insert(local) {
            return (local, all_fields);
        }
        match origins.get(&local) {
            Some((l, fields)) => {
                let mut combined = fields.clone();
                combined.extend(all_fields.iter());
                all_fields = combined;
                if *l == 1 {
                    return (1, all_fields);
                }
                local = *l;
            }
            None => {
                return (local, all_fields);
            }
        }
    }
}

// ── Block reachability ───────────────────────────────────────────

/// Collect all basic blocks reachable after (and including) a call block.
pub fn blocks_reachable_after_call(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
) -> HashSet<BasicBlock> {
    let body = tcx.optimized_mir(caller);
    let mut starts = Vec::new();
    if let TerminatorKind::Call { target, .. } = &body.basic_blocks[call_block].terminator().kind
        && let Some(target) = target
    {
        starts.push(*target);
    }

    let mut seen = HashSet::new();
    let mut stack = starts;
    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let terminator = body.basic_blocks[block].terminator();
        for successor in terminator.successors() {
            stack.push(successor);
        }
    }
    seen
}

// ── MIR place alias mapping ──────────────────────────────────────

/// Build a mapping from MIR locals to their resolved PlaceKey origins.
pub fn collect_place_aliases(tcx: TyCtxt<'_>, def_id: DefId) -> HashMap<Local, PlaceKey> {
    collect_local_origins(tcx, def_id)
        .into_iter()
        .map(|(local, (origin_local, fields))| {
            (
                Local::from_usize(local),
                PlaceKey::from_origin(origin_local, fields),
            )
        })
        .collect()
}

/// Resolve a MIR place through alias mapping to get a canonical PlaceKey.
pub fn resolve_mir_place<'tcx>(
    place: &Place<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> PlaceKey {
    let key = PlaceKey::from_mir_place(place);
    if !key.fields.is_empty() {
        return key;
    }
    aliases.get(&place.local).cloned().unwrap_or(key)
}

// ── Rvalue place scanning ────────────────────────────────────────

/// Check whether any MIR place used in an rvalue matches a predicate.
pub fn rvalue_any_place_matching<'tcx>(
    rvalue: &Rvalue<'tcx>,
    pred: &mut impl FnMut(&Place<'tcx>) -> bool,
) -> bool {
    match rvalue {
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => pred(place),
            Operand::Constant(_) => false,
            #[cfg(rapx_ge_99)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => rvalue_source_place(rvalue).map_or(false, |place| pred(place)),
    }
}

// ── Pointer arithmetic origin tracing ────────────────────────────

/// Trace a place back to its root local via local origin map.
pub fn trace_place_root(origins: &LocalOriginMap, place: &PlaceKey) -> Option<(usize, Vec<usize>)> {
    let Some(local) = place.local() else {
        return None;
    };
    let (root_local, root_fields) = deep_resolve_place(local.as_usize(), origins);
    Some((root_local, root_fields))
}

/// Extract raw bytes from a `ConstValue`, following reference indirection.
fn const_value_bytes<'tcx>(tcx: TyCtxt<'tcx>, value: ConstValue, depth: usize) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    match value {
        ConstValue::Slice { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        ConstValue::Scalar(scalar) => {
            #[cfg(rapx_scalar_to_pointer_interp_result)]
            let ptr = scalar.to_pointer(&tcx).discard_err()?;
            #[cfg(not(rapx_scalar_to_pointer_interp_result))]
            let ptr = scalar.to_pointer(&tcx);
            let alloc_id = ptr.provenance?.alloc_id();
            alloc_id_bytes(tcx, alloc_id, depth)
        }
        ConstValue::Indirect { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        _ => None,
    }
}

/// Read bytes from a global allocation.
fn alloc_id_bytes<'tcx>(tcx: TyCtxt<'tcx>, alloc_id: AllocId, depth: usize) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    let alloc = match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(alloc) => alloc,
        GlobalAlloc::Static(def_id) => tcx.eval_static_initializer(def_id).ok()?,
        _ => return None,
    };
    let alloc = alloc.inner();
    let provenance = alloc.provenance().ptrs();
    if let Some((_, prov)) = provenance.iter().next() {
        return alloc_id_bytes(tcx, prov.alloc_id(), depth + 1);
    }
    Some(
        alloc
            .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
            .to_vec(),
    )
}

// ── Type layout helpers ───────────────────────────────────────────

/// If `constant` is a promoted `offset_of!(Container, field)` constant (an
/// unevaluated `Const` whose body is a call to the `offset_of` intrinsic),
/// return the container type.
///
/// Used by the verifier to recognise `byte_add(offset_of!(Container, ..))` and
/// prove the resulting pointer stays within the container allocation.
pub(crate) fn offset_of_container<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
) -> Option<Ty<'tcx>> {
    let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant else {
        return None;
    };
    // `mir_for_ctfe` only accepts const-like defs; unevaluated consts may also
    // reference plain functions, so gate on the def kind first.
    if !is_const_def_kind(tcx, uneval.def) {
        return None;
    }
    // `mir_for_ctfe` panics for cross-crate constants (e.g. `char::MAX` from
    // `core`), since it only serves local, CTFE-able definitions. `offset_of!`
    // always expands to a local `AnonConst`, so rejecting external defs loses
    // nothing but avoids the ICE.
    if !uneval.def.is_local() {
        return None;
    }
    let body = tcx.mir_for_ctfe(uneval.def);
    for bb in body.basic_blocks.iter() {
        if let Some(term) = &bb.terminator
            && let TerminatorKind::Call { func, .. } = &term.kind
            && let Some(ty) = offset_of_ty_from_func(tcx, func)
        {
            return Some(ty);
        }
    }
    None
}

/// Whether a `DefId` is a const-like item that `mir_for_ctfe` accepts.
fn is_const_def_kind(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    #[cfg(rapx_ge_99)]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const { .. }
            | DefKind::Static { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
    );
    #[cfg(not(rapx_ge_99))]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const | DefKind::Static { .. } | DefKind::AssocConst | DefKind::AnonConst
    );
    #[cfg(rapx_ge_99)]
    {
        base
    }
    #[cfg(not(rapx_ge_99))]
    {
        base || matches!(tcx.def_kind(def_id), DefKind::InlineConst)
    }
}

/// Extract the first `Type` generic argument of an `FnDef` call operand.
///
/// Many monomorphized std APIs have the interesting type (the receiver or
/// container element) as their first generic argument.
pub(crate) fn fn_def_first_type_arg<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else {
        return None;
    };
    args.iter().find_map(|a| {
        #[cfg(rapx_ge_99)]
        let a = a.skip_binder();
        match a.kind() {
            GenericArgKind::Type(t) => Some(t),
            _ => None,
        }
    })
}

fn offset_of_ty_from_func<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = c.const_.ty().kind() else {
        return None;
    };
    if !tcx.is_lang_item(*def_id, LangItem::OffsetOf) {
        return None;
    }
    fn_def_first_type_arg(func)
}

pub fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) {
        return None;
    }
    match layout_of_ty(tcx, caller, ty) {
        Some(l) => Some((l.align.abi.bytes(), l.size.bytes())),
        None if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        None => None,
    }
}

/// Compute the full type layout, catching rustc panics and layout errors.
/// Shared by `type_layout` and the symbolic VM's size/align/field-offset
/// queries so the `layout_of` call and its panic-guard live in one place.
pub fn layout_of_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
) -> Option<rustc_abi::TyAndLayout<'tcx, Ty<'tcx>>> {
    let env = TypingEnv::post_analysis(tcx, caller);
    catch_panic(|| {
        tcx.layout_of(PseudoCanonicalInput {
            typing_env: env,
            value: ty,
        })
    })
    .ok()
    .and_then(|r| r.ok())
}

/// Byte offset of a struct field within its container type (0 on failure).
pub fn field_offset_in_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
    field_idx: usize,
) -> u64 {
    let Some(layout) = layout_of_ty(tcx, caller, ty) else {
        return 0;
    };
    match layout.fields {
        rustc_abi::FieldsShape::Arbitrary { ref offsets, .. } => {
            let idx = rustc_abi::FieldIdx::from_usize(field_idx);
            if idx.as_usize() < offsets.len() {
                return offsets[idx].bytes();
            }
        }
        _ => {}
    }
    0
}

pub fn destination_stride<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<u64> {
    let d = dest?;
    let pointee = pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty)?;
    type_layout(tcx, caller, pointee).map(|(_, s)| s)
}

pub fn pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<(u64, String)> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let pointee = pointee_ty(ty).or(Some(ty))?;
    if let Some((a, _)) = type_layout(tcx, caller, pointee) {
        return Some((a, format!("{pointee:?}")));
    }
    if let TyKind::Array(e, _) = pointee.kind()
        && let Some((a, _)) = type_layout(tcx, caller, *e)
    {
        return Some((a, format!("{pointee:?}")));
    }
    Some((0, format!("{pointee:?}")))
}

// ── Constant scalar / byte-string extraction ───────────────────

/// Parse an integer from a MIR constant's `Debug` text. Handles decimal,
/// `0x` hex, and `Value(...)` forms.
pub fn const_int_from_debug(text: &str) -> Option<u64> {
    if let Ok(v) = text.parse::<u64>() {
        return Some(v);
    }
    if let Some(start) = text.find("0x") {
        let hex_part = &text[start..];
        let end = hex_part
            .find(|c: char| !c.is_ascii_hexdigit() && c != 'x')
            .unwrap_or(hex_part.len());
        u64::from_str_radix(&hex_part[2..end], 16).ok()
    } else if let Some(start) = text.find("Value(") {
        let inner = &text[start + 6..];
        if let Some(end) = inner.find(')') {
            inner[..end].parse::<u64>().ok()
        } else {
            None
        }
    } else {
        None
    }
}

/// Resolve a MIR constant to a concrete integer, falling back from the cheap
/// debug-text parse to full const evaluation.
///
/// Layout constants (`offset_of!(Container, field)`) and the `T::{BITS,MAX,MIN}`
/// associated constants of *small* integer types (`u8`..`u32`, `i8`..`i32`) are
/// evaluated here.  Arbitrary unevaluated consts — and the wide bounds
/// `usize::MAX` / `u64::MAX` / `u128::MAX` — are deliberately left symbolic:
/// forcing them to a concrete `u64` would overflow downstream size arithmetic.
pub fn eval_const_scalar_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
    text: &str,
) -> Option<i128> {
    if let Some(v) = const_int_from_debug(text) {
        return Some(v as i128);
    }
    // Resolve `T::{BITS,MAX,MIN}` associated constants of small integer types,
    // used in numeric bounds (`u32::MAX`) and shift-width masks (`u32::BITS`).
    let is_num_bound = text.contains("::BITS") || text.contains("::MAX") || text.contains("::MIN");
    if !is_num_bound && offset_of_container(tcx, constant).is_none() {
        return None;
    }
    let typing_env = TypingEnv::fully_monomorphized();
    let val = constant.eval(tcx, typing_env, rustc_span::DUMMY_SP).ok()?;
    let scalar = val.try_to_scalar_int()?;
    let bits = scalar.size().bits() as u32;
    let raw = scalar.to_bits(scalar.size()) as i128;
    // Keep wide bounds (`u64::MAX`, `usize::MAX`, `u128::MAX`) symbolic so
    // they don't overflow downstream size arithmetic.
    if raw > u32::MAX as i128 {
        return None;
    }
    // Sign-extend signed integer constants (e.g. `i32::MIN` == -2147483648).
    let ty = constant.ty();
    if let TyKind::Int(_) = ty.kind() {
        let sign = 1i128 << (bits - 1);
        if raw >= sign {
            Some(raw - (1i128 << bits))
        } else {
            Some(raw)
        }
    } else {
        Some(raw)
    }
}

/// Try to extract raw bytes from a MIR constant operand that is a reference
/// to a byte array/slice (e.g. `b"hello\0"`). Returns the byte values.
/// Used by the VM to populate byte-level tracking for constant C strings.
pub fn const_operand_bytes<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>) -> Option<Vec<u8>> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    let ty = constant.const_.ty();
    let inner_ty = match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => return None,
    };
    // Peel through nested references (e.g. &&[u8])
    let inner_ty = if let TyKind::Ref(_, innermost, _) = inner_ty.kind() {
        *innermost
    } else {
        inner_ty
    };
    if !matches!(inner_ty.kind(), TyKind::Array(..) | TyKind::Slice(..)) {
        return None;
    }

    // Evaluate the MIR constant to get a ConstValue
    let typing_env = TypingEnv::fully_monomorphized();
    let value = constant
        .const_
        .eval(tcx, typing_env, rustc_span::DUMMY_SP)
        .ok()?;

    const_value_bytes(tcx, value, 0)
}

/// Extract the bare local from a Copy/Move operand with no projection.
pub fn extract_local(operand: &Operand<'_>) -> Option<Local> {
    operand_mir_place(operand)
        .filter(|place| place.projection.is_empty())
        .map(|place| place.local)
}

/// Extract a constant u64 value from an operand, if it's a known constant.
pub fn operand_const_u64(operand: &Operand<'_>) -> Option<u64> {
    operand_scalar_int(operand).map(|v| v as u64)
}

/// Whether a type is a `u8` array (`[u8; N]`) or `u8` slice (`[u8]`).
pub fn is_u8_array_or_slice(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Array(elem_ty, _) => {
            matches!(elem_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8))
        }
        TyKind::Slice(elem_ty) => {
            matches!(elem_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8))
        }
        _ => false,
    }
}

/// Whether a type transitively contains a reference.
///
/// This is a shallow check: it recurses only through `Adt` generic arguments,
/// not through tuple elements or `Adt` fields. See [`type_contains_ref_or_ptr`]
/// for a deeper check that also matches raw pointers.
pub fn type_contains_reference(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(..) => true,
        TyKind::Adt(_, substs) => substs.types().any(type_contains_reference),
        _ => false,
    }
}

/// Whether a type transitively contains a reference or raw pointer,
/// recursing through tuple elements and `Adt` fields. Unlike
/// [`type_contains_reference`], this also matches raw pointers.
pub fn type_contains_ref_or_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => true,
        TyKind::Tuple(elems) => elems.iter().any(|t| type_contains_ref_or_ptr(tcx, t)),
        TyKind::Adt(def, args) => {
            if args.iter().any(|arg| {
                if let Some(t) = arg.as_type() {
                    type_contains_ref_or_ptr(tcx, t)
                } else {
                    false
                }
            }) {
                return true;
            }
            let adt = tcx.adt_def(def.did());
            adt.all_fields()
                .any(|field| type_contains_ref_or_ptr(tcx, field_ty(tcx, field, args)))
        }
        _ => false,
    }
}

/// Resolve a struct field's type, normalizing where the rustc version requires it.
///
/// On newer rustc `field.ty(tcx, args)` returns an `Unnormalized<Ty>` that must
/// be `.skip_norm_wip()`-ed; on older toolchains the `SkipNormWip` shim makes
/// the same call a no-op, so this is version-independent.
pub fn field_ty<'tcx>(tcx: TyCtxt<'tcx>, field: &FieldDef, args: GenericArgsRef<'tcx>) -> Ty<'tcx> {
    field.ty(tcx, args).skip_norm_wip()
}

/// Whether `def_id` is a single-field struct wrapping a raw pointer (i.e.
/// `NonNull`-shaped).  Used by alias/ownership reasoning to recognize pointer
/// wrappers — including local re-implementations — by their structure rather
/// than by a std `DefId`.
pub fn is_raw_ptr_wrapper<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let adt = tcx.adt_def(def_id);
    let variant = adt.non_enum_variant();
    if variant.fields.len() != 1 {
        return false;
    }
    let args = rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id);
    let field = variant.fields.iter().next().unwrap();
    let field_ty = field_ty(tcx, field, args);
    matches!(field_ty.kind(), TyKind::RawPtr(..))
}

/// Collect the layouts of every concrete implementor of a generic type
/// parameter's trait bounds (empty for non-param types).
fn generic_param_impl_layouts<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
) -> Vec<rustc_abi::TyAndLayout<'tcx, Ty<'tcx>>> {
    if !matches!(ty.kind(), TyKind::Param(_)) {
        return Vec::new();
    }
    let param_env = tcx.param_env(caller);
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    for clause in param_env.caller_bounds() {
        let Some(trait_clause) = clause.as_trait_clause() else {
            continue;
        };
        let self_ty = trait_clause.self_ty().skip_binder();
        if self_ty != ty {
            continue;
        }
        let mut layouts = Vec::new();
        for impl_def_id in tcx.all_impls(trait_clause.def_id()) {
            let impl_ty = tcx.type_of(impl_def_id).skip_binder();
            if ty_has_param_const(impl_ty) {
                continue;
            }
            let Ok(Ok(layout)) = catch_panic(|| {
                tcx.layout_of(PseudoCanonicalInput {
                    typing_env,
                    value: impl_ty,
                })
            }) else {
                continue;
            };
            layouts.push(layout);
        }
        return layouts;
    }
    Vec::new()
}

/// Max `size_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn size_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    generic_param_impl_layouts(tcx, caller, ty)
        .into_iter()
        .map(|l| l.size.bytes())
        .max()
        .unwrap_or(0)
}

/// Min `align_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn min_align_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    generic_param_impl_layouts(tcx, caller, ty)
        .into_iter()
        .map(|l| l.align.abi.bytes())
        .min()
        .unwrap_or(0)
}

/// Follow a `parents` map (built by `verify::property_checker::cstr`'s
/// `body_parents`) from `start` to its root local, guarding against cycles.
pub fn follow_parents(parents: &FxHashMap<Local, Local>, start: Local) -> Local {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let Some(next) = parents.get(&current) else {
            break;
        };
        current = *next;
    }
    current
}

/// Resolve a local through `Cast` assignments back to its non-cast source.
pub fn resolve_through_casts<'tcx>(body: &Body<'tcx>, local: Local) -> Local {
    let mut current = local;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let found = body.basic_blocks.iter().any(|data| {
            data.statements.iter().any(|stmt| {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    return false;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != current || !target.projection.is_empty() {
                    return false;
                }
                if let Rvalue::Cast(_, operand, _) = rvalue {
                    #[allow(unreachable_patterns)]
                    match operand {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            current = p.local;
                            return true;
                        }
                        _ => {}
                    }
                }
                false
            })
        });
        if !found {
            break;
        }
    }
    current
}

// ── Constant byte recovery from MIR ─────────────────────────────

fn operand_scalar_int(operand: &Operand<'_>) -> Option<u128> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    constant
        .const_
        .try_to_scalar_int()
        .map(|s| s.to_uint(s.size()))
        .or_else(|| const_int_from_debug(&format!("{:?}", constant.const_)).map(|v| v as u128))
}

fn is_as_ptr_or_as_method(name: &str) -> bool {
    name.contains("as_ptr") || name.contains("::as_")
}

fn rvalue_const_bytes<'tcx>(tcx: TyCtxt<'tcx>, rvalue: &Rvalue<'tcx>) -> Option<Vec<u8>> {
    let constant = match rvalue {
        Rvalue::Use(Operand::Constant(constant), ..)
        | Rvalue::Cast(_, Operand::Constant(constant), _) => constant,
        _ => return None,
    };
    let value = constant
        .const_
        .eval(tcx, TypingEnv::fully_monomorphized(), DUMMY_SP)
        .ok()?;
    const_value_bytes(tcx, value, 0)
}

pub fn collect_all_const_bytes_worklist<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Vec<Vec<u8>> {
    let mut results: Vec<Vec<u8>> = Vec::new();
    let mut worklist: Vec<Local> = vec![root];
    let mut visited: std::collections::HashSet<Local> = std::collections::HashSet::new();

    while let Some(local) = worklist.pop() {
        if !visited.insert(local) {
            continue;
        }

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != local || !target.projection.is_empty() {
                    continue;
                }

                if let Rvalue::Ref(_, _, place) = rvalue {
                    if let Some(bytes) = const_bytes_for_local(tcx, body, place.local) {
                        results.push(bytes);
                    }
                    continue;
                }

                if let Rvalue::Use(operand, ..) = rvalue {
                    #[allow(unreachable_patterns)]
                    match operand {
                        Operand::Copy(p) | Operand::Move(p) => {
                            worklist.push(p.local);
                            if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                                results.push(bytes);
                            }
                            continue;
                        }
                        Operand::Constant(_) => {}
                        _ => continue,
                    }
                }

                if let Some(bytes) = rvalue_const_bytes(tcx, rvalue) {
                    results.push(bytes);
                }
            }
        }

        for data in body.basic_blocks.iter() {
            if let Some(terminator) = &data.terminator {
                if let TerminatorKind::Call {
                    destination,
                    func,
                    args,
                    ..
                } = &terminator.kind
                {
                    let dlocal = destination.local;
                    if dlocal != local {
                        continue;
                    }
                    if !destination.projection.is_empty() {
                        continue;
                    }
                    let name = call_name(tcx, func);
                    if is_as_ptr_or_as_method(&name) {
                        for arg in args {
                            if let Some(bytes) =
                                trace_const_bytes_from_operand(tcx, body, &arg.node)
                            {
                                results.push(bytes);
                            }
                        }
                    }
                    if name.contains("::add") {
                        if let Some(offset) = args.get(1).and_then(|a| operand_scalar_int(&a.node))
                        {
                            if let Some(base) = args.first() {
                                if let Some(bytes) =
                                    trace_const_bytes_from_operand(tcx, body, &base.node)
                                {
                                    let start = offset as usize;
                                    if start < bytes.len() {
                                        results.push(bytes[start..].to_vec());
                                    }
                                }
                            }
                        }
                    }
                    if name.contains("box_assume_init_into_vec_unsafe") {
                        if let Some(box_op) = args.first() {
                            if let Operand::Copy(p) | Operand::Move(p) = &box_op.node {
                                if p.projection.is_empty() {
                                    worklist.push(p.local);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    collect_aggregate_const_bytes(tcx, body, &mut results);
    collect_as_ptr_const_bytes(tcx, body, &mut results);

    results
}

fn collect_aggregate_const_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    results: &mut Vec<Vec<u8>>,
) {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (_, rvalue) = assign.as_ref();
            let Rvalue::Aggregate(_, operands) = rvalue else {
                continue;
            };
            if operands.len() < 2 {
                continue;
            }
            let last_op = operands.iter().last().unwrap();
            if !is_constant_zero(last_op) {
                continue;
            }
            let mut all_nonzero = true;
            for op in operands.iter().take(operands.len() - 1) {
                if !aggregate_op_is_nonzero(tcx, body, op) {
                    all_nonzero = false;
                    break;
                }
            }
            if all_nonzero {
                let len = operands.len();
                let mut bytes = Vec::with_capacity(len);
                for _ in 0..len - 1 {
                    bytes.push(b'x');
                }
                bytes.push(0);
                results.push(bytes);
            }
        }
    }
}

fn collect_as_ptr_const_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    results: &mut Vec<Vec<u8>>,
) {
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let name = call_name(tcx, func);
                if is_as_ptr_or_as_method(&name) {
                    for arg in args {
                        if let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &arg.node) {
                            results.push(bytes);
                        }
                    }
                }
            }
        }
    }
}

fn trace_const_bytes_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Vec<u8>> {
    if let Some(bytes) = const_operand_bytes(tcx, operand) {
        return Some(bytes);
    }
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                return Some(bytes);
            }
            const_bytes_from_call_dest(tcx, body, p.local)
        }
        _ => None,
    }
}

fn const_bytes_from_call_dest<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call {
                destination,
                func,
                args,
                ..
            } = &terminator.kind
            {
                if destination.local != local || !destination.projection.is_empty() {
                    continue;
                }
                let name = call_name(tcx, func);
                if is_as_ptr_or_as_method(&name) {
                    for arg in args {
                        if let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &arg.node) {
                            return Some(bytes);
                        }
                    }
                }
            }
        }
    }
    None
}

pub fn const_bytes_for_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != root || !target.projection.is_empty() {
                continue;
            }
            if let Rvalue::Ref(_, _, place) = rvalue {
                let deref_local = place.local;
                if let Some(bytes) = const_bytes_for_local(tcx, body, deref_local) {
                    return Some(bytes);
                }
                continue;
            }
            if let Rvalue::Use(operand, ..) = rvalue {
                #[allow(unreachable_patterns)]
                match operand {
                    Operand::Copy(p) | Operand::Move(p) => {
                        if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                            return Some(bytes);
                        }
                        if let Some(bytes) = const_bytes_from_call_dest(tcx, body, p.local) {
                            return Some(bytes);
                        }
                        continue;
                    }
                    Operand::Constant(_) => {}
                    _ => continue,
                }
            }
            if let Rvalue::Cast(_, operand, _) = rvalue {
                if let Operand::Copy(p) | Operand::Move(p) = operand {
                    if p.projection.is_empty() {
                        if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                            return Some(bytes);
                        }
                    }
                }
                continue;
            }
            return rvalue_const_bytes(tcx, rvalue);
        }
    }
    None
}

fn aggregate_op_is_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    if is_constant_zero(operand) {
        return false;
    }
    if const_operand_bytes(tcx, operand).is_some() {
        return true;
    }
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            for data in body.basic_blocks.iter() {
                if let Some(terminator) = &data.terminator {
                    if let TerminatorKind::Call {
                        destination, func, ..
                    } = &terminator.kind
                    {
                        if destination.local == p.local && destination.projection.is_empty() {
                            return fn_always_returns_nonzero(tcx, func);
                        }
                    }
                }
            }
            false
        }
        Operand::Constant(_) => operand_scalar_int(operand).is_some_and(|v| v != 0),
        _ => false,
    }
}

fn is_constant_zero(operand: &Operand<'_>) -> bool {
    operand_scalar_int(operand) == Some(0)
}

fn fn_always_returns_nonzero<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Some(fn_def_id) = dep_callee_def_id(func) else {
        return false;
    };
    let callee_body = tcx.optimized_mir(fn_def_id);

    let mut has_return = false;
    for bb_data in callee_body.basic_blocks.iter() {
        if let Some(terminator) = &bb_data.terminator {
            if matches!(terminator.kind, TerminatorKind::Return) {
                has_return = true;
            }
        }
        for stmt in &bb_data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != Local::from_usize(0) || !target.projection.is_empty() {
                continue;
            }
            if !rvalue_is_nonzero(rvalue) {
                return false;
            }
        }
    }

    has_return
}

fn rvalue_is_nonzero(rvalue: &Rvalue<'_>) -> bool {
    match rvalue {
        #[allow(unreachable_patterns)]
        Rvalue::Use(operand, ..) => match operand {
            Operand::Constant(_) => operand_scalar_int(operand).is_some_and(|v| v != 0),
            Operand::Copy(_) | Operand::Move(_) => true,
            _ => false,
        },
        _ => false,
    }
}
