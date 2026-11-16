//! Identify `core`, `alloc`, and `std` APIs without depending on MIR availability.
//! Callers use these identities to select verification and analysis behavior.
//!
//! # Agent Policy
//!
//! Keep this module limited to API identity checks based on compiler metadata,
//! types, signatures, or standard-library paths. Do not depend on RAPx modules
//! outside `def_ids` or implement call semantics here.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{TyCtxt, TyKind, UintTy};

use crate::def_ids::lang_api;

use super::{diagnostic_api, is_std_api, type_ids};

/// Identify standard-library UB and precondition checks so verification can
/// handle their calls without expanding the check implementation.
pub fn is_ub_check(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if !is_std_api(tcx, callee) {
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

/// Identify standard `Box::new` and `Box::new_in` for constructor and pointer
/// dependency handling.
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

/// Identify `NonNull::dangling` so constructor modeling can record its aligned,
/// allocation-free pointer result.
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

/// Identify `ManuallyDrop::drop` for explicit-drop verification and lifetime
/// tracking.
pub fn is_manually_drop(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity();
    let self_ty = self_ty.skip_norm_wip();
    matches!(self_ty.kind(), TyKind::Adt(adt, _)
        if tcx.is_lang_item(adt.did(), lang_api::LangItem::ManuallyDrop))
        && tcx.item_name(did).as_str() == "drop"
}

/// Identify the standard raw-pointer `align_offset` method for its registered
/// call effect.
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

/// Identify a standard-library `gcd` call used when folding layout constants.
pub fn is_gcd(tcx: TyCtxt<'_>, did: DefId) -> bool {
    is_std_api(tcx, did) && tcx.def_path_str(did).ends_with("::gcd")
}

/// Identify `drop`, `drop_in_place`, and `ManuallyDrop::drop` so slicing keeps
/// calls that can end a value's lifetime.
pub fn is_drop_fn(tcx: TyCtxt<'_>, target: DefId) -> bool {
    diagnostic_api::is_drop(tcx, target)
        || diagnostic_api::is_drop_in_place(tcx, target)
        || is_manually_drop(tcx, target)
}
