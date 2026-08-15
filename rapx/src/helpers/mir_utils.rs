use rustc_hir::{
    ItemKind,
    def_id::{DefId, LocalDefId},
};
#[cfg(not(rapx_rustc_ge_199))]
use rustc_hir::LangItem;
#[cfg(rapx_rustc_ge_199)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_middle::{
    mir::{BasicBlock, ConstValue, Local, Operand, Place, Rvalue, StatementKind, TerminatorKind},
    mir::interpret::{AllocId, GlobalAlloc},
    ty::{ConstKind, GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::Symbol;

use std::collections::{HashMap, HashSet};

use crate::{
    analysis::alias::{collect_local_origins, LocalOriginMap},
    helpers::mir_scan::Checkpoint,
    verify::def_use::PlaceKey,
};

pub(crate) fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

pub(crate) fn dep_callee_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(func_constant) = func else { return None };
    let TyKind::FnDef(def_id, _) = func_constant.const_.ty().kind() else { return None };
    Some(*def_id)
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

/// Return true when `def_id`'s MIR body is "linear" enough for lightweight
/// inlining: no `SwitchInt` terminators, at most one return, and at most
/// `max_blocks` basic blocks.
pub fn callee_is_linear(tcx: TyCtxt<'_>, def_id: DefId, max_blocks: usize) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.len() <= max_blocks
        && !body
            .basic_blocks
            .iter()
            .any(|bb| matches!(bb.terminator().kind, TerminatorKind::SwitchInt { .. }))
        && body
            .basic_blocks
            .iter()
            .filter(|bb| matches!(bb.terminator().kind, TerminatorKind::Return))
            .count()
            <= 1
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

    #[cfg(not(rapx_rustc_ge_198))]
    if let ItemKind::Trait(_, _, unsafety, _, _, _, _) = &item.kind {
        return matches!(unsafety, rustc_hir::Safety::Unsafe);
    }
    #[cfg(rapx_rustc_ge_198)]
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

pub fn has_rapx_verify_attr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);

    let rapx = Symbol::intern("rapx");
    let verify = Symbol::intern("verify");

    let attrs = tcx.hir_attrs(hir_id);

    attrs.iter().any(|attr| {
        #[cfg(rapx_rustc_ge_193)]
        if attr.is_doc_comment().is_some() {
            return false;
        }
        #[cfg(not(rapx_rustc_ge_193))]
        if attr.is_doc_comment() {
            return false;
        }

        let path = attr.path();

        path.len() == 2 && path[0] == rapx && path[1] == verify
    })
}

pub fn get_owner_struct_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    let self_ty = tcx.type_of(impl_id).skip_binder();

    match self_ty.kind() {
        TyKind::Adt(adt_def, _) => Some(adt_def.did()),
        _ => None,
    }
}

/// True when a type transitively contains a const-generic parameter or
/// an associated type alias (which may be layout-ambiguous).
pub(crate) fn ty_has_param_const(ty: Ty<'_>) -> bool {
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
pub fn rvalue_source_place<'a, 'tcx>(rvalue: &'a Rvalue<'tcx>) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    use rustc_middle::mir::{Operand, Rvalue};
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        |         Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}

// ── PlaceKey / operand utilities ─────────────────────────────────

/// Extract a PlaceKey from a MIR operand.
pub fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract the MIR Place from an operand.
pub fn operand_mir_place<'a, 'tcx>(operand: &'a Operand<'tcx>) -> Option<&'a Place<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

/// Return the destination local for a checkpoint's call or deref.
pub fn call_destination<'tcx>(
    tcx: TyCtxt<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<Local> {
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
pub fn deep_resolve_place(
    mut local: usize,
    origins: &LocalOriginMap,
) -> (usize, Vec<usize>) {
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

/// Trace a raw pointer local back through call terminators to find the
/// originating place (e.g. slice from `get_unchecked`).
pub fn trace_raw_ptr_through_call(
    tcx: TyCtxt<'_>,
    caller: DefId,
    checkpoint_block: BasicBlock,
    raw_ptr: Local,
) -> Option<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut block = checkpoint_block;
    let mut visited = HashSet::new();
    loop {
        if !visited.insert(block) {
            break;
        }
        for statement in body.basic_blocks[block].statements.iter().rev() {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _rvalue) = assign.as_ref();
            if target.local != raw_ptr {
                continue;
            }
            break;
        }
        let predecessors = &body.basic_blocks.predecessors()[block];
        if predecessors.len() != 1 {
            break;
        }
        let prev = predecessors[0];
        let terminator = body.basic_blocks[prev].terminator();
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            if destination.local == raw_ptr {
                let callee_name = call_name(tcx, func);
                if callee_name.contains("::get_unchecked") {
                    if let Some(slice) = args.get(1) {
                        return operand_place(&slice.node);
                    }
                }
                break;
            }
        }
        block = prev;
    }
    None
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
pub fn collect_place_aliases(
    tcx: TyCtxt<'_>,
    def_id: DefId,
) -> HashMap<Local, PlaceKey> {
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
    _tcx: TyCtxt<'tcx>,
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
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => rvalue_source_place(rvalue)
            .map_or(false, |place| pred(place)),
    }
}

// ── Pointer arithmetic origin tracing ────────────────────────────

/// Trace a place back to its root local via local origin map.
pub fn trace_place_root(
    origins: &LocalOriginMap,
    place: &PlaceKey,
) -> Option<(usize, Vec<usize>)> {
    let Some(local) = place.local() else {
        return None;
    };
    let (root_local, root_fields) = deep_resolve_place(local.as_usize(), origins);
    Some((root_local, root_fields))
}

/// Extract raw bytes from a `ConstValue`, following reference indirection.
pub fn const_value_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    value: ConstValue,
    depth: usize,
) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    match value {
        ConstValue::Slice { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        ConstValue::Scalar(scalar) => {
            let ptr = scalar.to_pointer(&tcx).discard_err()?;
            let alloc_id = ptr.provenance?.alloc_id();
            alloc_id_bytes(tcx, alloc_id, depth)
        }
        ConstValue::Indirect { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        _ => None,
    }
}

/// Read bytes from a global allocation.
pub fn alloc_id_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: AllocId,
    depth: usize,
) -> Option<Vec<u8>> {
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
    #[cfg(rapx_rustc_ge_196)]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const { .. }
            | DefKind::Static { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
    );
    #[cfg(not(rapx_rustc_ge_196))]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const | DefKind::Static { .. } | DefKind::AssocConst | DefKind::AnonConst
    );
    #[cfg(rapx_rustc_ge_199)]
    {
        base
    }
    #[cfg(not(rapx_rustc_ge_199))]
    {
        base || matches!(tcx.def_kind(def_id), DefKind::InlineConst)
    }
}

fn offset_of_ty_from_func<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else { return None };
    let TyKind::FnDef(def_id, args) = c.const_.ty().kind() else { return None };
    if !tcx.is_lang_item(*def_id, LangItem::OffsetOf) {
        return None;
    }
    args.iter().find_map(|a| {
        #[cfg(rapx_rustc_ge_199)]
        let a = a.skip_binder();
        match a.kind() {
            GenericArgKind::Type(t) => Some(t),
            _ => None,
        }
    })
}

pub fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) { return None }
    let env = TypingEnv::post_analysis(tcx, caller);
    let result = catch_panic(|| {
        tcx.layout_of(PseudoCanonicalInput { typing_env: env, value: ty })
    });
    match result {
        Ok(Ok(l)) => Some((l.align.abi.bytes(), l.size.bytes())),
        Ok(Err(_)) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        _ => None,
    }
}

pub fn destination_stride<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, dest: Option<Local>,
) -> Option<u64> {
    let d = dest?;
    let pointee = pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty)?;
    type_layout(tcx, caller, pointee).map(|(_, s)| s)
}

pub fn pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, dest: Option<Local>,
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

pub fn nonnull_inner_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let TyKind::Adt(def, args) = ty.kind() else { return None };
    if !tcx.def_path_str(def.did()).contains("ptr::non_null::NonNull") { return None }
    args.iter().find_map(|a| match a.kind() { GenericArgKind::Type(t) => Some(t), _ => None })
}

pub fn slice_element_size(
    tcx: TyCtxt<'_>, caller: DefId, _func: &Operand<'_>, dest: Option<Local>,
) -> u64 {
    let d = match dest {
        Some(d) => d,
        None => return 1,
    };
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let elem = match ty.kind() {
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Slice(e) => *e,
            _ => return 1,
        },
        TyKind::RawPtr(inner, _) => match inner.kind() {
            TyKind::Slice(e) => *e,
            _ => return 1,
        },
        _ => return 1,
    };
    type_layout(tcx, caller, elem)
        .map(|(_, s)| s)
        .unwrap_or(1)
}

pub fn vec_element_size(tcx: TyCtxt<'_>, caller: DefId, dest: Option<Local>) -> u64 {
    let d = match dest {
        Some(d) => d,
        None => return 1,
    };
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let elem = match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            let name = tcx.def_path_str(adt_def.did());
            if name.ends_with("::Vec") || name == "Vec" {
                substs.first().map(|s| s.as_type()).flatten()
            } else {
                None
            }
        }
        _ => None,
    };
    match elem {
        Some(elem_ty) => type_layout(tcx, caller, elem_ty).map(|(_, s)| s).unwrap_or(1),
        None => 1,
    }
}
