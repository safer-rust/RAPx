//! Known `core`/`std`/`alloc` API identities, regardless of MIR availability.

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{TyCtxt, TyKind, UintTy};
use rustc_public::{CrateDef, rustc_internal};

use super::{diagnostic_api, type_ids};

pub fn is_ub_check(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !matches!(
        tcx.crate_name(callee.krate).as_str(),
        "core" | "alloc" | "std"
    ) {
        return false;
    }
    let path = tcx.def_path_str(callee);
    path.contains("ub_checks::check_language_ub")
        || path.contains("::precondition_check")
        || path.contains("::runtime_add_nowrap")
        || path.contains("ub_checks::maybe_is_aligned")
        || path.contains("ub_checks::is_valid_allocation_size")
        || path.contains("ub_checks::maybe_is_nonoverlapping")
}

fn is_std_api(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(tcx.crate_name(did.krate).as_str(), "core" | "alloc" | "std")
}

/// Whether `did` names `Box::new` or `Box::new_in` on the standard Box type.
pub fn is_box_new(tcx: TyCtxt<'_>, did: DefId) -> bool {
    if !matches!(tcx.item_name(did).as_str(), "new" | "new_in") {
        return false;
    }
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity().skip_norm_wip();
    matches!(self_ty.kind(), TyKind::Adt(adt, _) if type_ids::is_std_box(adt.did()))
}

/// Whether `did` names the standard `NonNull::dangling` constructor.
pub fn is_nonnull_dangling(tcx: TyCtxt<'_>, did: DefId) -> bool {
    if tcx.item_name(did).as_str() != "dangling" {
        return false;
    }
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity().skip_norm_wip();
    matches!(self_ty.kind(), TyKind::Adt(adt, _)
        if type_ids::is_std_nonnull(adt.did()))
        && tcx.fn_sig(did).skip_binder().inputs().skip_binder().is_empty()
}

pub fn is_manually_drop(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity();
    let self_ty = self_ty.skip_norm_wip();
    matches!(self_ty.kind(), TyKind::Adt(adt, _)
        if tcx.is_lang_item(adt.did(), crate::def_ids::lang_api::LangItem::ManuallyDrop))
        && tcx.item_name(did).as_str() == "drop"
}

pub fn is_align_offset(tcx: TyCtxt<'_>, did: DefId) -> bool {
    if !is_std_api(tcx, did) || tcx.item_name(did).as_str() != "align_offset" {
        return false;
    }
    let sig = tcx.fn_sig(did).skip_binder();
    let inputs = sig.inputs().skip_binder();
    inputs.len() == 2
        && matches!(inputs[0].kind(), TyKind::RawPtr(..))
        && matches!(inputs[1].kind(), TyKind::Uint(UintTy::Usize))
        && matches!(sig.output().skip_binder().kind(), TyKind::Uint(UintTy::Usize))
}

/// Whether a standard `ptr::copy` function copies between raw pointers.
pub fn is_std_ptr_copy_function(tcx: TyCtxt<'_>, did: DefId) -> bool {
    diagnostic_api::is_ptr_copy(tcx, did)
        || (matches!(tcx.def_kind(did), DefKind::Fn)
            && matches!(
                tcx.def_path_str(did).as_str(),
                "std::ptr::copy" | "std::ptr::copy_nonoverlapping"
            ))
}

pub fn is_gcd(tcx: TyCtxt<'_>, did: DefId) -> bool {
    is_std_api(tcx, did) && tcx.def_path_str(did).ends_with("::gcd")
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}

/// Find a call that explicitly drops a value.
pub fn is_drop_fn(tcx: TyCtxt<'_>, target: DefId) -> bool {
    diagnostic_api::is_drop(tcx, target)
        || diagnostic_api::is_drop_in_place(tcx, target)
        || is_manually_drop(tcx, target)
}
