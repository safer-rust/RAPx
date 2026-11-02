//! Hand-written effect models for standard-library APIs: a matcher + effect
//! builder per API, looked up by [`lookup_effect`].

use crate::def_ids::lang_api::{self, LangItem};
use crate::helpers::mir_utils;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::{BoundedArithmeticOp, CallEffect, CallEffectSummary, OverflowOp, SimdArithOp, SimdCmpOp};
use crate::def_ids::other_api;
use crate::def_ids::{intrinsic_api, nomir_api, nomir_ffi};
use crate::helpers::mir_utils::type_layout;
use crate::verify::api_classify;

// ── Context for effect builders ────────────────────────────────────────

pub(crate) struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub func: &'a Operand<'tcx>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(Option<DefId>) -> bool,
    effects: fn(&EffCtx<'_, '_>) -> Vec<CallEffect>,
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
    // ── Intrinsics ──────────────────────────────────────────────────
    ED!(intrinsic_api::is_ceil, eff_opaque_return),
    ED!(intrinsic_api::is_copysignf32, eff_opaque_return),
    ED!(intrinsic_api::is_cos, eff_opaque_return),
    ED!(intrinsic_api::is_exp, eff_opaque_return),
    ED!(intrinsic_api::is_exp2, eff_opaque_return),
    ED!(intrinsic_api::is_fabs, eff_opaque_return),
    ED!(intrinsic_api::is_fadd_algebraic, eff_opaque_return),
    ED!(intrinsic_api::is_fadd_fast, eff_opaque_return),
    ED!(intrinsic_api::is_fdiv_algebraic, eff_opaque_return),
    ED!(intrinsic_api::is_fdiv_fast, eff_opaque_return),
    ED!(intrinsic_api::is_floor, eff_opaque_return),
    ED!(intrinsic_api::is_fma, eff_opaque_return),
    ED!(intrinsic_api::is_fmul_algebraic, eff_opaque_return),
    ED!(intrinsic_api::is_fmul_fast, eff_opaque_return),
    ED!(intrinsic_api::is_fmuladd, eff_opaque_return),
    ED!(intrinsic_api::is_frem_algebraic, eff_opaque_return),
    ED!(intrinsic_api::is_frem_fast, eff_opaque_return),
    ED!(intrinsic_api::is_fsub_algebraic, eff_opaque_return),
    ED!(intrinsic_api::is_fsub_fast, eff_opaque_return),
    ED!(intrinsic_api::is_log, eff_opaque_return),
    ED!(intrinsic_api::is_log10, eff_opaque_return),
    ED!(intrinsic_api::is_log2, eff_opaque_return),
    ED!(intrinsic_api::is_maximum_number_nsz_f32, eff_opaque_return),
    ED!(intrinsic_api::is_maximumf32, eff_opaque_return),
    ED!(intrinsic_api::is_minimum_number_nsz_f32, eff_opaque_return),
    ED!(intrinsic_api::is_minimumf32, eff_opaque_return),
    ED!(intrinsic_api::is_powf, eff_opaque_return),
    ED!(intrinsic_api::is_powi, eff_opaque_return),
    ED!(intrinsic_api::is_round, eff_opaque_return),
    ED!(intrinsic_api::is_round_ties_even, eff_opaque_return),
    ED!(intrinsic_api::is_sin, eff_opaque_return),
    ED!(intrinsic_api::is_sqrt, eff_opaque_return),
    ED!(intrinsic_api::is_trunc, eff_opaque_return),
    ED!(intrinsic_api::is_size_of, eff_layout_const),
    ED!(intrinsic_api::is_align_of, eff_layout_const),
    ED!(intrinsic_api::is_select_unpredictable, eff_select_unpredictable),
    ED!(intrinsic_api::is_unlikely, eff_alias_arg0),
    ED!(intrinsic_api::is_likely, eff_alias_arg0),
    ED!(intrinsic_api::is_cold_path, eff_no_effect),
    ED!(intrinsic_api::is_assert_inhabited, eff_no_effect),
    ED!(intrinsic_api::is_ptr_offset_from, eff_ptr_offset_from),
    ED!(intrinsic_api::is_ptr_offset_from_unsigned, eff_ptr_offset_from),
    ED!(intrinsic_api::is_arith_offset, eff_arith_offset),
    ED!(intrinsic_api::is_black_box, eff_return_arg_value),
    ED!(intrinsic_api::is_add_with_overflow, eff_with_overflow),
    ED!(intrinsic_api::is_sub_with_overflow, eff_with_overflow),
    ED!(intrinsic_api::is_mul_with_overflow, eff_with_overflow),
    ED!(intrinsic_api::is_integer_min, eff_cmp_min),
    ED!(intrinsic_api::is_integer_max, eff_return_max),
    ED!(intrinsic_api::is_saturating_add, eff_saturating_add),
    ED!(intrinsic_api::is_saturating_sub, eff_saturating_sub),
    ED!(intrinsic_api::is_unchecked_add, eff_return_add),
    ED!(intrinsic_api::is_unchecked_mul, eff_return_mul),
    ED!(intrinsic_api::is_wrapping_sub, eff_wrapping_sub),
    ED!(intrinsic_api::is_copy, eff_copy_memory),
    ED!(intrinsic_api::is_copy_nonoverlapping, eff_copy_memory),
    ED!(intrinsic_api::is_typed_swap_nonoverlapping, eff_swap_memory),
    ED!(intrinsic_api::is_write_bytes, eff_fill_bytes),
    ED!(intrinsic_api::is_volatile_load, eff_load_memory),
    ED!(intrinsic_api::is_volatile_store, eff_store_memory),
    ED!(intrinsic_api::is_unaligned_volatile_load, eff_load_memory),
    ED!(intrinsic_api::is_unaligned_volatile_store, eff_store_memory),
    ED!(intrinsic_api::is_nontemporal_store, eff_store_memory),
    ED!(intrinsic_api::is_volatile_copy_memory, eff_volatile_copy_memory),
    ED!(intrinsic_api::is_volatile_copy_nonoverlapping_memory, eff_volatile_copy_memory),
    ED!(intrinsic_api::is_volatile_set_memory, eff_fill_bytes),
    ED!(intrinsic_api::is_compare_bytes, eff_compare_bytes),
    ED!(intrinsic_api::is_ptr_mask, eff_ptr_mask),
    ED!(intrinsic_api::is_atomic_load, eff_load_memory),
    ED!(intrinsic_api::is_atomic_store, eff_store_memory),
    ED!(intrinsic_api::is_atomic_xchg, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_xadd, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_xsub, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_and, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_or, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_xor, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_max, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_min, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_cxchg, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_cxchgweak, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_nand, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_umin, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_umax, eff_atomic_rmw),
    ED!(intrinsic_api::is_atomic_fence, eff_no_effect),
    ED!(intrinsic_api::is_atomic_singlethreadfence, eff_no_effect),
    ED!(intrinsic_api::is_simd_lt, eff_simd_lt),
    ED!(intrinsic_api::is_simd_eq, eff_simd_eq),
    ED!(intrinsic_api::is_simd_gt, eff_simd_gt),
    ED!(intrinsic_api::is_simd_ne, eff_simd_ne),
    ED!(intrinsic_api::is_simd_le, eff_simd_le),
    ED!(intrinsic_api::is_simd_ge, eff_simd_ge),
    ED!(intrinsic_api::is_simd_add, eff_simd_add),
    ED!(intrinsic_api::is_simd_sub, eff_simd_sub),
    ED!(intrinsic_api::is_simd_mul, eff_simd_mul),
    ED!(intrinsic_api::is_simd_saturating_add, eff_simd_saturating_add),
    ED!(intrinsic_api::is_simd_saturating_sub, eff_simd_saturating_sub),
    ED!(intrinsic_api::is_simd_splat, eff_simd_splat),
    ED!(intrinsic_api::is_simd_extract, eff_simd_extract),
    ED!(intrinsic_api::is_simd_extract_dyn, eff_simd_extract),
    ED!(intrinsic_api::is_simd_insert, eff_simd_insert),
    ED!(intrinsic_api::is_simd_insert_dyn, eff_simd_insert),
    ED!(intrinsic_api::is_simd_and, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_or, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_xor, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_neg, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_as, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_bswap, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_bitreverse, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_ctlz, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_ctpop, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_cttz, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fabs, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_minimum_number_nsz, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_maximum_number_nsz, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_ceil, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_floor, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_round, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_round_ties_even, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_trunc, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fsqrt, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fma, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_relaxed_fma, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fsin, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fcos, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fexp, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_fexp2, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_flog10, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_flog2, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_flog, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_reduce_add_ordered, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_add_unordered, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_mul_ordered, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_mul_unordered, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_max, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_min, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_and, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_or, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_xor, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_all, eff_opaque_return),
    ED!(intrinsic_api::is_simd_reduce_any, eff_opaque_return),
    ED!(intrinsic_api::is_simd_arith_offset, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_carryless_mul, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_cast, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_cast_ptr, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_div, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_expose_provenance, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_funnel_shl, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_funnel_shr, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_gather, eff_simd_gather),
    ED!(intrinsic_api::is_simd_masked_load, eff_simd_masked_load),
    ED!(intrinsic_api::is_simd_masked_store, eff_simd_masked_store),
    ED!(intrinsic_api::is_simd_rem, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_scatter, eff_simd_scatter),
    ED!(intrinsic_api::is_simd_select, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_select_bitmask, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_shl, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_shr, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_shuffle, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_with_exposed_provenance, eff_simd_opaque),
    ED!(intrinsic_api::is_simd_bitmask, eff_simd_bitmask),
    ED!(intrinsic_api::is_bswap, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_ctpop, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_bitreverse, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_rotate_left, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_rotate_right, eff_return_nonzero_iff),
    ED!(intrinsic_api::is_ctlz, eff_leading_zeros),
    ED!(intrinsic_api::is_ctlz_nonzero, eff_leading_zeros),
    ED!(intrinsic_api::is_cttz, eff_trailing_zeros),
    ED!(intrinsic_api::is_cttz_nonzero, eff_trailing_zeros),
    ED!(intrinsic_api::is_raw_eq, eff_raw_eq),
    ED!(intrinsic_api::is_exact_div, eff_exact_div),
    ED!(intrinsic_api::is_size_of_val, eff_size_of_val),
    ED!(intrinsic_api::is_align_of_val, eff_align_of_val),
    ED!(intrinsic_api::is_float_to_int_unchecked, eff_opaque_return),
    ED!(intrinsic_api::is_vtable_size, eff_opaque_return),
    ED!(intrinsic_api::is_vtable_align, eff_opaque_return),
    // ── APIs without MIR ────────────────────────────────────────────
    ED!(nomir_api::is_global_alloc_shim, eff_nullable_allocation),
    ED!(nomir_api::is_global_alloc_zeroed_shim, eff_nullable_zeroed_allocation),
    ED!(nomir_api::is_alloc_shim_marker, eff_no_effect),
    ED!(nomir_ffi::is_cstr_runtime_strlen, eff_opaque_return),
    ED!(nomir_api::is_slice_to_vec, eff_vec_from_slice),
    // ── Other APIs ──────────────────────────────────────────────────
    ED!(api_classify::is_vec_push_or_reserve, eff_write_mem),
    ED!(api_classify::is_align_offset, eff_align_offset),
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
) -> Option<CallEffectSummary> {
    for e in REGISTRY {
        if (e.matches)(callee) {
            let ctx = EffCtx {
                tcx,
                caller,
                func,
            };
            return Some((e.effects)(&ctx));
        }
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
