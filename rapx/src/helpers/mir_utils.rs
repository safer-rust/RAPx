use rustc_hir::{
    ItemKind,
    def_id::{DefId, LocalDefId},
};
#[cfg(not(rapx_ge_100))]
use rustc_hir::LangItem;
#[cfg(rapx_ge_100)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_middle::{
    mir::{BasicBlock, ConstValue, Local, Operand, Place, Rvalue, TerminatorKind},
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

pub fn has_rapx_verify_attr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);

    let rapx = Symbol::intern("rapx");
    let verify = Symbol::intern("verify");

    let attrs = tcx.hir_attrs(hir_id);

    attrs.iter().any(|attr| {
        if attr.is_doc_comment().is_some() {
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
        #[cfg(rapx_ge_99)]
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
            #[cfg(rapx_ge_99)]
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
        #[cfg(rapx_ge_99)]
        let a = a.skip_binder();
        match a.kind() {
            GenericArgKind::Type(t) => Some(t),
            _ => None,
        }
    })
}

pub fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) { return None }
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
    catch_panic(|| tcx.layout_of(PseudoCanonicalInput { typing_env: env, value: ty }))
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
    let Some(layout) = layout_of_ty(tcx, caller, ty) else { return 0 };
    match layout.fields {
        rustc_abi::FieldsShape::Arbitrary { ref offsets, .. } => {
            let idx = rustc_abi::FieldIdx::from_usize(field_idx);
            if idx.as_usize() < offsets.len() { return offsets[idx].bytes(); }
        }
        _ => {}
    }
    0
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

pub fn slice_element_size(
    tcx: TyCtxt<'_>, caller: DefId, dest: Option<Local>,
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
    vec_elem_ty(tcx, ty)
        .and_then(|elem_ty| type_layout(tcx, caller, elem_ty).map(|(_, s)| s))
        .unwrap_or(1)
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
pub fn const_scalar_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
    text: &str,
) -> Option<i128> {
    if let Some(v) = const_int_from_debug(text) {
        return Some(v as i128);
    }
    // Resolve `T::{BITS,MAX,MIN}` associated constants of small integer types,
    // used in numeric bounds (`u32::MAX`) and shift-width masks (`u32::BITS`).
    let is_num_bound =
        text.contains("::BITS") || text.contains("::MAX") || text.contains("::MIN");
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
pub fn extract_const_bytes_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Vec<u8>> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    let ty = constant.const_.ty();
    let (inner_ty, _is_ref) = match ty.kind() {
        TyKind::Ref(_, inner, _) => (*inner, true),
        _ => return None,
    };
    // Peel through nested references (e.g. &&[u8])
    let inner_ty = if let TyKind::Ref(_, innermost, _) = inner_ty.kind() {
        *innermost
    } else {
        inner_ty
    };
    let _elem_ty = match inner_ty.kind() {
        TyKind::Array(elem, _) | TyKind::Slice(elem) => *elem,
        _ => return None,
    };

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
    match operand {
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() => Some(place.local),
        _ => None,
    }
}

/// Extract a constant u64 value from an operand, if it's a known constant.
pub fn extract_operand_const(operand: &Operand<'_>) -> Option<u64> {
    match operand {
        Operand::Constant(constant) => {
            let text = format!("{:?}", constant.const_);
            const_int_from_debug(&text)
        }
        _ => None,
    }
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
pub fn type_contains_reference(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(..) => true,
        TyKind::Adt(_, substs) => substs.types().any(type_contains_reference),
        _ => false,
    }
}

/// Element type of a `Vec<T>`, if `ty` is a `Vec`.
pub fn vec_elem_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, substs) = ty.kind() {
        let name = tcx.def_path_str(adt_def.did());
        if crate::helpers::api_classify::is_std_vec(&name) {
            return substs.first().and_then(|s| s.as_type());
        }
    }
    None
}

/// Max `size_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn size_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    match ty.kind() {
        TyKind::Param(_) => {}
        _ => return 0,
    };
    let param_env = tcx.param_env(caller);
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    for clause in param_env.caller_bounds() {
        let Some(trait_clause) = clause.as_trait_clause() else { continue };
        let self_ty = trait_clause.self_ty().skip_binder();
        if self_ty != ty {
            continue;
        }
        let trait_def_id = trait_clause.def_id();
        let mut max_size: u64 = 0;
        for impl_def_id in tcx.all_impls(trait_def_id) {
            let impl_ty = tcx.type_of(impl_def_id).skip_binder();
            if ty_has_param_const(impl_ty) {
                continue;
            }
            let layout = match catch_panic(|| {
                tcx.layout_of(PseudoCanonicalInput { typing_env, value: impl_ty })
            }) {
                Ok(Ok(l)) => l,
                _ => continue,
            };
            max_size = max_size.max(layout.size.bytes());
        }
        return max_size;
    }
    0
}

/// Min `align_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn min_align_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    match ty.kind() {
        TyKind::Param(_) => {}
        _ => return 0,
    };
    let param_env = tcx.param_env(caller);
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    for clause in param_env.caller_bounds() {
        let Some(trait_clause) = clause.as_trait_clause() else { continue };
        let self_ty = trait_clause.self_ty().skip_binder();
        if self_ty != ty {
            continue;
        }
        let trait_def_id = trait_clause.def_id();
        let mut min_align: u64 = u64::MAX;
        for impl_def_id in tcx.all_impls(trait_def_id) {
            let impl_ty = tcx.type_of(impl_def_id).skip_binder();
            if ty_has_param_const(impl_ty) {
                continue;
            }
            let layout = match catch_panic(|| {
                tcx.layout_of(PseudoCanonicalInput { typing_env, value: impl_ty })
            }) {
                Ok(Ok(l)) => l,
                _ => continue,
            };
            min_align = min_align.min(layout.align.abi.bytes());
        }
        return if min_align == u64::MAX { 0 } else { min_align };
    }
    0
}
