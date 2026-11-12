//! Call effect builders for intrinsics, FFI APIs, and other calls.

use std::{collections::HashMap, sync::OnceLock};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Operand,
    ty::{Ty, TyCtxt, TyKind},
};
use serde::Deserialize;

use super::{
    BoundedArithmeticOp, CallEffect, CallEffectSummary, OverflowOp, SimdArithOp, SimdCmpOp,
};
use crate::{
    def_ids::{
        intrinsic_api,
        lang_api::{self, LangItem},
        nomir_api,
        other_api,
    },
    helpers::{
        mir_utils::{self, type_layout},
        name::public_def_path,
    },
    verify::api_classify,
};

// ── Context for effect builders ────────────────────────────────────────

pub(crate) struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub func: &'a Operand<'tcx>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(Option<DefId>) -> bool,
    effects: EffectBuilder,
}

type EffectBuilder = for<'a, 'tcx> fn(&EffCtx<'a, 'tcx>) -> Vec<CallEffect>;

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
    // ── APIs without MIR ────────────────────────────────────────────
    ED!(nomir_api::is_global_alloc_shim, eff_nullable_allocation),
    ED!(nomir_api::is_global_alloc_zeroed_shim, eff_nullable_zeroed_allocation),
    ED!(nomir_api::is_alloc_shim_marker, eff_no_effect),
    ED!(nomir_api::is_slice_to_vec, eff_vec_from_slice),
    // ── Other APIs ──────────────────────────────────────────────────
    ED!(api_classify::is_align_offset, eff_align_offset),
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct EffectModel {
    effect: String,
}

fn load_effect_models(source: &'static str) -> HashMap<String, EffectModel> {
    serde_json::from_str(source).expect("failed to parse call effect models")
}

fn intrinsic_effects() -> &'static HashMap<String, EffectModel> {
    static MODELS: OnceLock<HashMap<String, EffectModel>> = OnceLock::new();
    MODELS.get_or_init(|| load_effect_models(include_str!("assets/intrinsic-effects.json")))
}

fn ffi_effects() -> &'static HashMap<String, EffectModel> {
    static MODELS: OnceLock<HashMap<String, EffectModel>> = OnceLock::new();
    MODELS.get_or_init(|| load_effect_models(include_str!("assets/ffi-effects.json")))
}

fn effect_builder(name: &str) -> Option<EffectBuilder> {
    match name {
        "eff_alias_arg0" => Some(eff_alias_arg0),
        "eff_align_of_val" => Some(eff_align_of_val),
        "eff_arith_offset" => Some(eff_arith_offset),
        "eff_atomic_rmw" => Some(eff_atomic_rmw),
        "eff_cmp_min" => Some(eff_cmp_min),
        "eff_compare_bytes" => Some(eff_compare_bytes),
        "eff_copy_memory" => Some(eff_copy_memory),
        "eff_exact_div" => Some(eff_exact_div),
        "eff_fill_bytes" => Some(eff_fill_bytes),
        "eff_layout_const" => Some(eff_layout_const),
        "eff_leading_zeros" => Some(eff_leading_zeros),
        "eff_load_memory" => Some(eff_load_memory),
        "eff_no_effect" => Some(eff_no_effect),
        "eff_opaque_return" => Some(eff_opaque_return),
        "eff_ptr_mask" => Some(eff_ptr_mask),
        "eff_ptr_offset_from" => Some(eff_ptr_offset_from),
        "eff_raw_eq" => Some(eff_raw_eq),
        "eff_return_add" => Some(eff_return_add),
        "eff_return_arg_value" => Some(eff_return_arg_value),
        "eff_return_max" => Some(eff_return_max),
        "eff_return_mul" => Some(eff_return_mul),
        "eff_return_nonzero_iff" => Some(eff_return_nonzero_iff),
        "eff_saturating_add" => Some(eff_saturating_add),
        "eff_saturating_sub" => Some(eff_saturating_sub),
        "eff_select_unpredictable" => Some(eff_select_unpredictable),
        "eff_simd_add" => Some(eff_simd_add),
        "eff_simd_bitmask" => Some(eff_simd_bitmask),
        "eff_simd_eq" => Some(eff_simd_eq),
        "eff_simd_extract" => Some(eff_simd_extract),
        "eff_simd_gather" => Some(eff_simd_gather),
        "eff_simd_ge" => Some(eff_simd_ge),
        "eff_simd_gt" => Some(eff_simd_gt),
        "eff_simd_insert" => Some(eff_simd_insert),
        "eff_simd_le" => Some(eff_simd_le),
        "eff_simd_lt" => Some(eff_simd_lt),
        "eff_simd_masked_load" => Some(eff_simd_masked_load),
        "eff_simd_masked_store" => Some(eff_simd_masked_store),
        "eff_simd_mul" => Some(eff_simd_mul),
        "eff_simd_ne" => Some(eff_simd_ne),
        "eff_simd_opaque" => Some(eff_simd_opaque),
        "eff_simd_saturating_add" => Some(eff_simd_saturating_add),
        "eff_simd_saturating_sub" => Some(eff_simd_saturating_sub),
        "eff_simd_scatter" => Some(eff_simd_scatter),
        "eff_simd_splat" => Some(eff_simd_splat),
        "eff_simd_sub" => Some(eff_simd_sub),
        "eff_size_of_val" => Some(eff_size_of_val),
        "eff_store_memory" => Some(eff_store_memory),
        "eff_swap_memory" => Some(eff_swap_memory),
        "eff_trailing_zeros" => Some(eff_trailing_zeros),
        "eff_volatile_copy_memory" => Some(eff_volatile_copy_memory),
        "eff_with_overflow" => Some(eff_with_overflow),
        "eff_wrapping_add" => Some(eff_wrapping_add),
        "eff_wrapping_sub" => Some(eff_wrapping_sub),
        _ => None,
    }
}

fn model_builder(model: &EffectModel) -> EffectBuilder {
    let name = model.effect.as_str();
    effect_builder(name).unwrap_or_else(|| panic!("unknown call effect builder: {name}"))
}

fn validate_model_effects() {
    static VALIDATED: OnceLock<()> = OnceLock::new();
    VALIDATED.get_or_init(|| {
        for model in intrinsic_effects()
            .values()
            .chain(ffi_effects().values())
        {
            model_builder(model);
        }
    });
}

fn lookup_builder(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<EffectBuilder> {
    let id = callee?;
    if let Some(intrinsic) = tcx.intrinsic(id) {
        validate_model_effects();
        return intrinsic_effects()
            .get(intrinsic.name.as_str())
            .map(model_builder);
    }
    if tcx.is_foreign_item(id) {
        validate_model_effects();
        if let Some(builder) = ffi_effects()
            .get(&public_def_path(tcx, id))
            .map(model_builder)
        {
            return Some(builder);
        }
    }
    REGISTRY
        .iter()
        .find(|entry| (entry.matches)(callee))
        .map(|entry| entry.effects)
}

pub(crate) fn has_registered_effect(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    lookup_builder(tcx, callee).is_some()
}

pub(crate) fn is_unmodeled_intrinsic(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| intrinsic_api::is_intrinsic(tcx, id))
        && !has_registered_effect(tcx, callee)
}

pub(crate) fn lookup_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    func: &Operand<'tcx>,
) -> Option<CallEffectSummary> {
    if let Some((owner, delta)) =
        callee.and_then(|did| crate::def_ids::other_api::ref_count_adjust(tcx, did))
    {
        return Some(vec![CallEffect::AdjustRefCount { arg: 0, owner, delta }]);
    }
    if let Some(builder) = lookup_builder(tcx, callee) {
        let ctx = EffCtx {
            tcx,
            caller,
            func,
        };
        return Some(builder(&ctx));
    }
    if callee.is_some_and(|id| api_classify::is_ptr_copy(Some(id)) && !tcx.is_mir_available(id)) {
        return Some(eff_copy_memory(&EffCtx {
            tcx,
            caller,
            func,
        }));
    }
    None
}
// ── Effect builders — one small function per API semantic ──────────────

fn eff_return_arg_value(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnArgValue { arg: 0 }]
}

fn eff_opaque_return(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOpaque]
}

fn eff_size_of_val(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSizeOfVal { arg: 0 }]
}

fn eff_align_of_val(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOfVal { arg: 0 }]
}

fn eff_trailing_zeros(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnTrailingZeros { arg: 0 }]
}

fn eff_load_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::LoadMemory { pointer_arg: 0 }]
}

fn eff_store_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::StoreMemory {
        pointer_arg: 0,
        value_arg: 1,
    }]
}

fn eff_volatile_copy_memory(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::CopyMemory {
        source_arg: 1,
        destination_arg: 0,
        count_arg: 2,
    }]
}

fn eff_compare_bytes(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnCompareBytes {
        left_arg: 0,
        right_arg: 1,
        count_arg: 2,
    }]
}

fn eff_atomic_rmw(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::AtomicRmw { pointer_arg: 0 }]
}

fn eff_ptr_mask(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMaskedPointer {
        pointer_arg: 0,
        mask_arg: 1,
    }]
}

fn eff_simd_lt(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Lt }]
}

fn eff_simd_eq(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Eq }]
}

fn eff_simd_gt(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Gt }]
}

fn eff_simd_ne(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Ne }]
}

fn eff_simd_le(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Le }]
}

fn eff_simd_ge(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdCompare { lhs_arg: 0, rhs_arg: 1, op: SimdCmpOp::Ge }]
}

fn eff_simd_bitmask(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdBitmask { arg: 0 }]
}

fn eff_simd_opaque(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdOpaque]
}

fn eff_simd_splat(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdSplat { arg: 0 }]
}

fn eff_simd_extract(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdExtract { vector_arg: 0, index_arg: 1 }]
}

fn eff_simd_insert(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdInsert { vector_arg: 0, index_arg: 1, value_arg: 2 }]
}

fn eff_simd_scatter(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdHavocMemory { pointer_arg: 1, mask_arg: 2 }]
}

fn eff_simd_masked_store(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdHavocMemory { pointer_arg: 1, mask_arg: 0 }]
}

fn eff_simd_gather(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdMaskedFallback { mask_arg: 2, fallback_arg: 0 }]
}

fn eff_simd_masked_load(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdMaskedFallback { mask_arg: 0, fallback_arg: 2 }]
}

fn eff_simd_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdArithmetic { lhs_arg: 0, rhs_arg: 1, op: SimdArithOp::Add }]
}

fn eff_simd_sub(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdArithmetic { lhs_arg: 0, rhs_arg: 1, op: SimdArithOp::Sub }]
}

fn eff_simd_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdArithmetic { lhs_arg: 0, rhs_arg: 1, op: SimdArithOp::Mul }]
}

fn eff_simd_saturating_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdArithmetic { lhs_arg: 0, rhs_arg: 1, op: SimdArithOp::SaturatingAdd }]
}

fn eff_simd_saturating_sub(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::SimdArithmetic { lhs_arg: 0, rhs_arg: 1, op: SimdArithOp::SaturatingSub }]
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

fn eff_leading_zeros(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnLeadingZeros { arg: 0 }]
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

fn eff_wrapping_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoundedArithmetic {
        lhs_arg: 0,
        rhs_arg: 1,
        op: BoundedArithmeticOp::WrappingAdd,
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
    let intrinsic = intrinsic_api::name(callee);
    let op = match intrinsic.as_ref().map(|name| name.as_str()) {
        Some("add_with_overflow") => OverflowOp::Add,
        Some("sub_with_overflow") => OverflowOp::Sub,
        _ => OverflowOp::Mul,
    };
    vec![CallEffect::ReturnWithOverflow {
        lhs_arg: 0,
        rhs_arg: 1,
        op,
    }]
}

fn eff_align_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOffset {
        ptr_arg: 0,
        align_arg: 1,
    }]
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

fn eff_vec_from_slice(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnVecFromSlice]
}

fn eff_layout_const(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    layout_constant_effect(ctx.tcx, ctx.caller, ctx.func).map_or_else(Vec::new, |e| vec![e])
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
    let intrinsic = intrinsic_api::name(Some(callee));
    let intrinsic = intrinsic.as_ref().map(|name| name.as_str());
    let is_align = other_api::mem_align_of() == Some(callee) || intrinsic == Some("align_of");
    let is_size = other_api::mem_size_of() == Some(callee) || intrinsic == Some("size_of");
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
