//! Identity of compiler intrinsics by `DefId`.

use std::collections::HashMap;
use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::Symbol;

static IDS: OnceLock<HashMap<DefId, Symbol>> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut ids = HashMap::new();
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|krate| matches!(krate.name.as_str(), "core" | "std" | "alloc"))
        {
            for function in krate.fn_defs() {
                let id = rustc_internal::internal(tcx, function.def_id());
                if let Some(intrinsic) = tcx.intrinsic(id) {
                    ids.insert(id, intrinsic.name);
                }
            }
        }
        ids
    });
}

fn matches_name(callee: Option<DefId>, name: &str) -> bool {
    callee
        .and_then(|id| {
            IDS.get()
                .expect("Intrinsic IDs have not been initialized")
                .get(&id)
        })
        .is_some_and(|intrinsic| intrinsic.as_str() == name)
}

fn get(name: &str) -> Option<DefId> {
    IDS.get()
        .expect("Intrinsic IDs have not been initialized")
        .iter()
        .find_map(|(&id, intrinsic)| (intrinsic.as_str() == name).then_some(id))
}

pub fn copy_nonoverlapping_id() -> Option<DefId> {
    get("copy_nonoverlapping")
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}

macro_rules! intrinsic_apis {
    ($($matcher:ident => $name:literal,)+) => {
        $(
            pub fn $matcher(callee: Option<DefId>) -> bool {
                matches_name(callee, $name)
            }
        )+
    };
}

intrinsic_apis! {
    is_ceil => "ceil",
    is_copysignf32 => "copysignf32",
    is_cos => "cos",
    is_exp => "exp",
    is_exp2 => "exp2",
    is_fabs => "fabs",
    is_fadd_algebraic => "fadd_algebraic",
    is_fadd_fast => "fadd_fast",
    is_fdiv_algebraic => "fdiv_algebraic",
    is_fdiv_fast => "fdiv_fast",
    is_floor => "floor",
    is_fma => "fma",
    is_fmul_algebraic => "fmul_algebraic",
    is_fmul_fast => "fmul_fast",
    is_fmuladd => "fmuladd",
    is_frem_algebraic => "frem_algebraic",
    is_frem_fast => "frem_fast",
    is_fsub_algebraic => "fsub_algebraic",
    is_fsub_fast => "fsub_fast",
    is_log => "log",
    is_log10 => "log10",
    is_log2 => "log2",
    is_maximum_number_nsz_f32 => "maximum_number_nsz_f32",
    is_maximumf32 => "maximumf32",
    is_minimum_number_nsz_f32 => "minimum_number_nsz_f32",
    is_minimumf32 => "minimumf32",
    is_powf => "powf",
    is_powi => "powi",
    is_round => "round",
    is_round_ties_even => "round_ties_even",
    is_sin => "sin",
    is_sqrt => "sqrt",
    is_trunc => "trunc",
    is_copy => "copy",
    is_copy_nonoverlapping => "copy_nonoverlapping",
    is_typed_swap_nonoverlapping => "typed_swap_nonoverlapping",
    is_write_bytes => "write_bytes",
    is_volatile_load => "volatile_load",
    is_volatile_store => "volatile_store",
    is_unaligned_volatile_load => "unaligned_volatile_load",
    is_unaligned_volatile_store => "unaligned_volatile_store",
    is_nontemporal_store => "nontemporal_store",
    is_volatile_copy_memory => "volatile_copy_memory",
    is_volatile_copy_nonoverlapping_memory => "volatile_copy_nonoverlapping_memory",
    is_volatile_set_memory => "volatile_set_memory",
    is_compare_bytes => "compare_bytes",
    is_ptr_mask => "ptr_mask",
    is_atomic_load => "atomic_load",
    is_atomic_store => "atomic_store",
    is_atomic_xchg => "atomic_xchg",
    is_atomic_xadd => "atomic_xadd",
    is_atomic_xsub => "atomic_xsub",
    is_atomic_and => "atomic_and",
    is_atomic_or => "atomic_or",
    is_atomic_xor => "atomic_xor",
    is_atomic_max => "atomic_max",
    is_atomic_min => "atomic_min",
    is_atomic_cxchg => "atomic_cxchg",
    is_atomic_cxchgweak => "atomic_cxchgweak",
    is_atomic_nand => "atomic_nand",
    is_atomic_umin => "atomic_umin",
    is_atomic_umax => "atomic_umax",
    is_atomic_fence => "atomic_fence",
    is_atomic_singlethreadfence => "atomic_singlethreadfence",
    is_simd_lt => "simd_lt",
    is_simd_eq => "simd_eq",
    is_simd_gt => "simd_gt",
    is_simd_ne => "simd_ne",
    is_simd_le => "simd_le",
    is_simd_ge => "simd_ge",
    is_simd_add => "simd_add",
    is_simd_sub => "simd_sub",
    is_simd_mul => "simd_mul",
    is_simd_saturating_add => "simd_saturating_add",
    is_simd_saturating_sub => "simd_saturating_sub",
    is_simd_splat => "simd_splat",
    is_simd_extract => "simd_extract",
    is_simd_extract_dyn => "simd_extract_dyn",
    is_simd_insert => "simd_insert",
    is_simd_insert_dyn => "simd_insert_dyn",
    is_simd_and => "simd_and",
    is_simd_or => "simd_or",
    is_simd_xor => "simd_xor",
    is_simd_neg => "simd_neg",
    is_simd_as => "simd_as",
    is_simd_bswap => "simd_bswap",
    is_simd_bitreverse => "simd_bitreverse",
    is_simd_ctlz => "simd_ctlz",
    is_simd_ctpop => "simd_ctpop",
    is_simd_cttz => "simd_cttz",
    is_simd_fabs => "simd_fabs",
    is_simd_minimum_number_nsz => "simd_minimum_number_nsz",
    is_simd_maximum_number_nsz => "simd_maximum_number_nsz",
    is_simd_ceil => "simd_ceil",
    is_simd_floor => "simd_floor",
    is_simd_round => "simd_round",
    is_simd_round_ties_even => "simd_round_ties_even",
    is_simd_trunc => "simd_trunc",
    is_simd_fsqrt => "simd_fsqrt",
    is_simd_fma => "simd_fma",
    is_simd_relaxed_fma => "simd_relaxed_fma",
    is_simd_fsin => "simd_fsin",
    is_simd_fcos => "simd_fcos",
    is_simd_fexp => "simd_fexp",
    is_simd_fexp2 => "simd_fexp2",
    is_simd_flog10 => "simd_flog10",
    is_simd_flog2 => "simd_flog2",
    is_simd_flog => "simd_flog",
    is_simd_reduce_add_ordered => "simd_reduce_add_ordered",
    is_simd_reduce_add_unordered => "simd_reduce_add_unordered",
    is_simd_reduce_mul_ordered => "simd_reduce_mul_ordered",
    is_simd_reduce_mul_unordered => "simd_reduce_mul_unordered",
    is_simd_reduce_max => "simd_reduce_max",
    is_simd_reduce_min => "simd_reduce_min",
    is_simd_reduce_and => "simd_reduce_and",
    is_simd_reduce_or => "simd_reduce_or",
    is_simd_reduce_xor => "simd_reduce_xor",
    is_simd_reduce_all => "simd_reduce_all",
    is_simd_reduce_any => "simd_reduce_any",
    is_simd_arith_offset => "simd_arith_offset",
    is_simd_carryless_mul => "simd_carryless_mul",
    is_simd_cast => "simd_cast",
    is_simd_cast_ptr => "simd_cast_ptr",
    is_simd_div => "simd_div",
    is_simd_expose_provenance => "simd_expose_provenance",
    is_simd_funnel_shl => "simd_funnel_shl",
    is_simd_funnel_shr => "simd_funnel_shr",
    is_simd_gather => "simd_gather",
    is_simd_masked_load => "simd_masked_load",
    is_simd_masked_store => "simd_masked_store",
    is_simd_rem => "simd_rem",
    is_simd_scatter => "simd_scatter",
    is_simd_select => "simd_select",
    is_simd_select_bitmask => "simd_select_bitmask",
    is_simd_shl => "simd_shl",
    is_simd_shr => "simd_shr",
    is_simd_shuffle => "simd_shuffle",
    is_simd_with_exposed_provenance => "simd_with_exposed_provenance",
    is_simd_bitmask => "simd_bitmask",
    is_black_box => "black_box",
    is_float_to_int_unchecked => "float_to_int_unchecked",
    is_exact_div => "exact_div",
    is_raw_eq => "raw_eq",
    is_vtable_size => "vtable_size",
    is_vtable_align => "vtable_align",
    is_size_of_val => "size_of_val",
    is_align_of_val => "align_of_val",
    is_size_of => "size_of",
    is_align_of => "align_of",
    is_select_unpredictable => "select_unpredictable",
    is_unlikely => "unlikely",
    is_likely => "likely",
    is_cold_path => "cold_path",
    is_assert_inhabited => "assert_inhabited",
    is_add_with_overflow => "add_with_overflow",
    is_sub_with_overflow => "sub_with_overflow",
    is_mul_with_overflow => "mul_with_overflow",
    is_saturating_add => "saturating_add",
    is_unchecked_add => "unchecked_add",
    is_unchecked_mul => "unchecked_mul",
    is_wrapping_sub => "wrapping_sub",
    is_saturating_sub => "saturating_sub",
    is_integer_min => "integer_min",
    is_integer_max => "integer_max",
    is_bswap => "bswap",
    is_ctpop => "ctpop",
    is_ctlz => "ctlz",
    is_ctlz_nonzero => "ctlz_nonzero",
    is_cttz => "cttz",
    is_cttz_nonzero => "cttz_nonzero",
    is_bitreverse => "bitreverse",
    is_rotate_left => "rotate_left",
    is_rotate_right => "rotate_right",
    is_ptr_offset_from => "ptr_offset_from",
    is_ptr_offset_from_unsigned => "ptr_offset_from_unsigned",
    is_arith_offset => "arith_offset",
}
