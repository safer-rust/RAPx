//! Hand-written effect models for standard-library APIs: a matcher + effect
//! builder per API, looked up by [`lookup_effect`].

use crate::def_ids::lang_api::{self, LangItem};
use crate::helpers::mir_utils;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{BoundedArithmeticOp, CallEffect, CallEffectSummary, OverflowOp};
use crate::def_ids::other_api;
use crate::def_ids::{intrinsic_api, nomir_api, nomir_ffi};
use crate::helpers::mir_utils::{pointee_alignment, type_layout};
use crate::verify::api_classify;

// ── Context for effect builders ────────────────────────────────────────

pub(crate) struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub func: &'a Operand<'tcx>,
    pub dest: Option<rustc_middle::mir::Local>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(Option<DefId>) -> bool,
    effects: fn(&EffCtx<'_, '_>) -> Vec<CallEffect>,
}

fn is_cstr_runtime_strlen(callee: Option<DefId>) -> bool {
    callee.is_some() && callee == nomir_ffi::cstr_runtime_strlen()
}

/// `DefId`-based matcher row (`fn(Option<DefId>) -> bool`).
macro_rules! ED {
    ($m:expr, $e:ident) => {
        Entry {
            matches: $m,
            effects: $e,
        }
    };
}

static REGISTRY: &[Entry] = &[
    // ── Hand-specialized VM shapes ──────────────────────────────────
    // Listed first so they win over the generic def-path matchers below.
    ED!(api_classify::is_branch, eff_branch),
    ED!(api_classify::is_index_method, eff_slice_range_index),
    ED!(api_classify::is_iter_len, eff_iter_len),
    ED!(api_classify::is_iter_is_empty, eff_iter_is_empty),
    ED!(api_classify::is_nonnull_checked_new, eff_nonnull_new),
    ED!(api_classify::is_iter_next, eff_iter_next),
    ED!(api_classify::is_range_next, eff_range_next),
    // ── Layout and intrinsic effects ───────────────────────────────
    ED!(api_classify::is_layout_constant, eff_layout_const),
    ED!(intrinsic_api::is_select_unpredictable, eff_select_unpredictable),
    ED!(api_classify::is_intrinsic_branch_hint, eff_alias_arg0),
    ED!(intrinsic_api::is_cold_path, eff_no_effect),
    ED!(api_classify::is_intrinsic_ptr_offset_from, eff_ptr_offset_from),
    ED!(intrinsic_api::is_arith_offset, eff_arith_offset),
    ED!(intrinsic_api::is_black_box, eff_return_arg_value),
    ED!(api_classify::is_intrinsic_with_overflow, eff_with_overflow),
    ED!(intrinsic_api::is_integer_min, eff_cmp_min),
    ED!(intrinsic_api::is_integer_max, eff_return_max),
    ED!(intrinsic_api::is_saturating_add, eff_saturating_add),
    ED!(intrinsic_api::is_saturating_sub, eff_saturating_sub),
    ED!(intrinsic_api::is_unchecked_add, eff_return_add),
    ED!(intrinsic_api::is_unchecked_mul, eff_return_mul),
    ED!(intrinsic_api::is_wrapping_sub, eff_wrapping_sub),
    ED!(api_classify::is_intrinsic_copy, eff_copy_memory),
    ED!(intrinsic_api::is_typed_swap_nonoverlapping, eff_swap_memory),
    ED!(intrinsic_api::is_write_bytes, eff_fill_bytes),
    ED!(api_classify::is_intrinsic_nonzero_preserving, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_raw_eq, eff_raw_eq),
    ED!(intrinsic_api::is_exact_div, eff_exact_div),
    ED!(intrinsic_api::is_size_of_val, eff_size_of_val),
    ED!(api_classify::is_intrinsic_pure_opaque, eff_opaque_return),
    // ── Allocation and capacity effects ─────────────────────────────
    ED!(nomir_api::is_global_alloc_shim, eff_nullable_allocation),
    ED!(nomir_api::is_global_alloc_zeroed_shim, eff_nullable_zeroed_allocation),
    ED!(nomir_api::is_alloc_shim_marker, eff_no_effect),
    ED!(is_cstr_runtime_strlen, eff_opaque_return),
    ED!(api_classify::is_vec_from_box, eff_vec_from_box),
    ED!(nomir_api::is_slice_to_vec, eff_vec_from_box),
    ED!(api_classify::is_vec_push_or_reserve, eff_write_mem),
    // ── MIR available — precise symbolic summary ────────────────────
    ED!(api_classify::is_checked_next_pow2, eff_return_option_some_nonzero),
    ED!(api_classify::is_manually_drop_drop, eff_drop_memory),
    ED!(api_classify::is_std_drop, eff_drop_memory),
    ED!(api_classify::is_drop_in_place, eff_drop_memory),
    ED!(api_classify::is_from_raw_parts, eff_from_raw_parts),
    ED!(api_classify::is_with_metadata_of, eff_return_pointer_arg),
    ED!(api_classify::is_align_offset, eff_align_offset),
    ED!(api_classify::is_slice_range, eff_slice_range),
    ED!(api_classify::is_mem_replace, eff_mem_replace),
    ED!(api_classify::is_layout_align, eff_layout_align),
    ED!(api_classify::is_iter_position, eff_option_scan_index),
    // ── MIR available — summarized instead of inlined ───────────────
    ED!(api_classify::is_maybe_uninit_uninit, eff_uninit_wrapper),
    ED!(api_classify::is_maybe_uninit_assume_init, eff_return_arg_value),
    ED!(api_classify::is_maybe_uninit_write, eff_write_mem),
];

/// A registry entry keeps the call opaque in the path graph, including entries
/// with an intentionally empty effect. Operand-dependent fallbacks are checked
/// later by the VM and cannot be identified by `DefId` alone.
pub(crate) fn has_registry_entry(callee: Option<DefId>) -> bool {
    REGISTRY.iter().any(|e| (e.matches)(callee))
}

pub(crate) fn is_unmodeled_intrinsic(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| intrinsic_api::is_intrinsic(tcx, id))
        && !has_registry_entry(callee)
}

pub(crate) fn lookup_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    func: &Operand<'tcx>,
    destination: rustc_middle::mir::Local,
) -> Option<CallEffectSummary> {
    let dest = Some(destination);
    for e in REGISTRY {
        if (e.matches)(callee) {
            let ctx = EffCtx {
                tcx,
                caller,
                func,
                dest,
            };
            return Some((e.effects)(&ctx));
        }
    }
    if callee.is_some_and(|id| api_classify::is_ptr_copy(Some(id)) && !tcx.is_mir_available(id)) {
        return Some(eff_copy_memory(&EffCtx {
            tcx,
            caller,
            func,
            dest,
        }));
    }
    None
}

// ── Effect builders — one small function per API semantic ──────────────

fn eff_uninit_wrapper(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnUninitWrapper]
}

fn eff_return_arg_value(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnArgValue { arg: 0 }]
}

fn eff_opaque_return(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOpaque]
}

fn eff_size_of_val(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSizeOfVal { arg: 0 }]
}

fn eff_raw_eq(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnRawEq {
        left_arg: 0,
        right_arg: 1,
    }]
}

fn eff_exact_div(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnExactDiv {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_select_unpredictable(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SelectUnpredictable]
}

fn eff_alias_arg0(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAliasArg { arg: 0 }]
}

fn eff_return_pointer_arg(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPointerFromArg { arg: 0 }]
}

fn eff_ptr_offset_from(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPtrOffsetFrom {
        ptr_arg: 0,
        base_arg: 1,
    }]
}

fn eff_arith_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnWrappingPointerOffset {
        base_arg: 0,
        offset_arg: 1,
    }]
}

fn eff_write_mem(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::WriteMemory { pointer_arg: 0 }]
}

fn eff_copy_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::CopyMemory {
        source_arg: 0,
        destination_arg: 1,
        count_arg: 2,
    }]
}

fn eff_swap_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SwapMemory {
        left_arg: 0,
        right_arg: 1,
    }]
}

fn eff_fill_bytes(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::FillBytes {
        pointer_arg: 0,
        byte_arg: 1,
        count_arg: 2,
    }]
}

fn eff_cmp_min(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMin {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_nonzero_iff(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNonZeroIff { arg: 0 }]
}

fn eff_return_option_some_nonzero(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeNonZero]
}

fn eff_return_max(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMax {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAdd {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMul {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_saturating_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoundedArithmetic {
        lhs_arg: 0,
        rhs_arg: 1,
        op: BoundedArithmeticOp::SaturatingAdd,
    }]
}

fn eff_saturating_sub(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoundedArithmetic {
        lhs_arg: 0,
        rhs_arg: 1,
        op: BoundedArithmeticOp::SaturatingSub,
    }]
}

fn eff_wrapping_sub(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoundedArithmetic {
        lhs_arg: 0,
        rhs_arg: 1,
        op: BoundedArithmeticOp::WrappingSub,
    }]
}

fn eff_with_overflow(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let callee = mir_utils::dep_callee_def_id(ctx.func);
    let op = if intrinsic_api::is_add_with_overflow(callee) {
        OverflowOp::Add
    } else if intrinsic_api::is_sub_with_overflow(callee) {
        OverflowOp::Sub
    } else {
        OverflowOp::Mul
    };
    vec![CallEffect::ReturnWithOverflow {
        lhs_arg: 0,
        rhs_arg: 1,
        op,
    }]
}

fn eff_drop_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::DropMemory { pointer_arg: 0 }]
}

fn eff_option_scan_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeScanIndex { self_arg: 0 }]
}

fn eff_align_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOffset {
        ptr_arg: 0,
        align_arg: 1,
    }]
}

fn eff_slice_range(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnRange { bounds_arg: 1 }]
}

fn eff_mem_replace(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnDerefArg { arg: 0 }]
}

fn eff_from_raw_parts(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    // The DST *pointer* constructor (`ptr::from_raw_parts`, used by
    // `with_metadata_of` in `byte_add`/`byte_offset`) is a no-op cast for a
    // *sized* pointee: preserve the pointer's provenance and non-nullness
    // instead of materializing a fresh allocation.
    if let Some(d) = ctx.dest {
        let ty = ctx.tcx.optimized_mir(ctx.caller).local_decls[d].ty;
        if let Some(pointee) = mir_utils::pointee_ty(ty)
            && pointee.is_sized(
                ctx.tcx,
                rustc_middle::ty::TypingEnv::post_analysis(ctx.tcx, ctx.caller),
            )
        {
            return vec![CallEffect::ReturnPointerFromArg { arg: 0 }];
        }
    }
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    let mut eff = vec![
        CallEffect::ReturnFreshAllocation {
            pointer_arg: 0,
            size_arg: 1,
            elem_size: elem,
        },
        CallEffect::ReturnNonZero,
    ];
    if pointee_alignment(ctx.tcx, ctx.caller, ctx.dest).is_some() {
        eff.push(CallEffect::ReturnAligned);
    }
    eff
}

fn eff_nullable_allocation(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNullableAllocation {
        size_arg: 0,
        align_arg: 1,
        zeroed: false,
    }]
}

fn eff_nullable_zeroed_allocation(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNullableAllocation {
        size_arg: 0,
        align_arg: 1,
        zeroed: true,
    }]
}

fn eff_no_effect(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    Vec::new()
}

fn eff_vec_from_box(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNewAllocationFromBox]
}

fn eff_layout_align(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPowerOfTwo]
}

fn eff_layout_const(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    layout_constant_effect(ctx.tcx, ctx.caller, ctx.func).map_or_else(Vec::new, |e| vec![e])
}

fn eff_branch(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBranchPayload { arg: 0 }]
}

fn eff_slice_range_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSliceRangeIndex]
}

fn eff_iter_len(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterLen { is_len: true }]
}

fn eff_iter_is_empty(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterLen { is_len: false }]
}

fn eff_nonnull_new(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNonNullNew]
}

fn eff_iter_next(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIterNext]
}

fn eff_range_next(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnRangeNext]
}

// ── Layout helpers (used by effect builders) ─────────────────────────

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    mir_utils::fn_def_first_type_arg(func)
}

fn layout_constant_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<CallEffect> {
    let ty = layout_call_ty(func)?;
    let callee = mir_utils::dep_callee_def_id(func)?;
    let is_align =
        other_api::mem_align_of() == Some(callee) || intrinsic_api::is_align_of(Some(callee));
    let is_size =
        other_api::mem_size_of() == Some(callee) || intrinsic_api::is_size_of(Some(callee));
    if !is_size && !is_align {
        return None;
    }
    let (align, size) = type_layout(tcx, caller, ty)?;
    // `type_layout` reports `(0, 0)` for a generic `T` (layout unknown): bind
    // the shared symbolic `sizeof_T` / `align_T` at apply time (the
    // `align_of::<T>() >= 1` bound keeps a cast like `align as *const T` in
    // `NonNull::dangling` non-null).
    if align == 0 && size == 0 {
        return Some(CallEffect::ReturnLayoutSymbolic { is_size });
    }
    Some(CallEffect::ReturnConst {
        value: if is_align { align } else { size },
    })
}

// ── Non-registry effect fallback ────────────────────────────────────

/// Transparent-wrapper deref (`ManuallyDrop`/`MaybeDangling`) when the registry
/// has no match: the return aliases the receiver's inner value.
pub(crate) fn effect_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> Option<CallEffectSummary> {
    if let Some(peel) = transparent_deref_peel(tcx, func) {
        return Some(vec![CallEffect::ReturnTransparentDeref { arg: 0, peel }]);
    }
    None
}

fn transparent_deref_peel<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<usize> {
    let self_ty = mir_utils::fn_def_first_type_arg(func)?;
    let TyKind::Adt(adt_def, _) = self_ty.kind() else {
        return None;
    };
    let did = adt_def.did();
    if lang_api::matches(tcx, did, LangItem::ManuallyDrop) {
        return Some(2);
    }
    if lang_api::matches(tcx, did, LangItem::MaybeDangling) {
        return Some(1);
    }
    None
}

// ── Collection element-size helpers ─────────────────────────────────

/// Element type of a `Vec<T>`, if `ty` is a `Vec`.
pub(crate) fn vec_elem_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    if let TyKind::Adt(adt_def, substs) = ty.kind()
        && api_classify::is_std_vec(adt_def.did())
    {
        return substs.first().and_then(|s| s.as_type());
    }
    None
}

/// Element type of a `from_raw_parts` result: `&[T]`/`*[T]`/`Vec<T>` yield `T`;
/// other types (including `String`) return `None`.
pub(crate) fn from_raw_parts_elem_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<Ty<'tcx>> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    match ty.kind() {
        TyKind::Ref(_, inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::RawPtr(inner, _) => match inner.kind() {
            TyKind::Slice(e) => Some(*e),
            _ => None,
        },
        TyKind::Adt(..) => vec_elem_ty(ty),
        _ => None,
    }
}

/// Element size of a `from_raw_parts` result; `String`/unknown layouts fall
/// back to 1 (`String`'s element is `u8`).
pub(crate) fn from_raw_parts_elem_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> u64 {
    from_raw_parts_elem_ty(tcx, caller, dest)
        .and_then(|e| mir_utils::type_layout(tcx, caller, e).map(|(_, s)| s))
        .unwrap_or(1)
}
