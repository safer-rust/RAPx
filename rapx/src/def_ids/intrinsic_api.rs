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
    is_copy => "copy",
    is_copy_nonoverlapping => "copy_nonoverlapping",
    is_typed_swap_nonoverlapping => "typed_swap_nonoverlapping",
    is_write_bytes => "write_bytes",
    is_black_box => "black_box",
    is_float_to_int_unchecked => "float_to_int_unchecked",
    is_exact_div => "exact_div",
    is_raw_eq => "raw_eq",
    is_vtable_size => "vtable_size",
    is_vtable_align => "vtable_align",
    is_size_of_val => "size_of_val",
    is_size_of => "size_of",
    is_align_of => "align_of",
    is_select_unpredictable => "select_unpredictable",
    is_unlikely => "unlikely",
    is_likely => "likely",
    is_cold_path => "cold_path",
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
    is_bitreverse => "bitreverse",
    is_rotate_left => "rotate_left",
    is_rotate_right => "rotate_right",
    is_ptr_offset_from => "ptr_offset_from",
    is_ptr_offset_from_unsigned => "ptr_offset_from_unsigned",
    is_arith_offset => "arith_offset",
}
