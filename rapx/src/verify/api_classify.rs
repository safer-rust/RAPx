//! Identities of standard-library APIs and types used by verification.
//!
//! Call classifiers recognize specific intrinsics, diagnostic items, or
//! inherent methods. Type classifiers compare ADT `DefId`s with the standard
//! type sets resolved in [`crate::def_ids::type_ids`].
//!
//! # Agent Policy
//!
//! Keep this module a thin wrapper around API and type identities from
//! [`crate::def_ids`]. Do not depend on other RAPx modules or interpret MIR
//! semantics here.

use crate::def_ids::{diagnostic_api, intrinsic_api, other_api, type_ids};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// Whether `callee` is an intrinsic with one of the given names.
fn is_intrinsic(tcx: TyCtxt<'_>, callee: Option<DefId>, names: &[&str]) -> bool {
    intrinsic_api::intrinsic_name(tcx, callee).is_some_and(|name| names.contains(&name.as_str()))
}

/// Whether `callee` explicitly drops the value stored in `ManuallyDrop<T>`.
pub fn is_manually_drop_drop(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::is_manually_drop(tcx, c))
}

/// Whether `callee` is the `ptr_offset_from` or `ptr_offset_from_unsigned` intrinsic.
pub fn is_intrinsic_ptr_offset_from(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic(
        tcx,
        callee,
        &["ptr_offset_from", "ptr_offset_from_unsigned"],
    )
}

/// Whether `callee` is a diagnostic-item pointer write API whose destination
/// is its first argument (`write`, `write_bytes`, `write_unaligned`, or `write_volatile`).
pub fn is_ptr_write(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| diagnostic_api::is_ptr_write(tcx, did))
}

// Standard-library ADT identities used throughout verification.

pub fn is_std_vec(def_id: DefId) -> bool {
    type_ids::vec_types().contains(&def_id)
}

pub fn is_std_string(def_id: DefId) -> bool {
    type_ids::string_types().contains(&def_id)
}

pub fn is_std_box(def_id: DefId) -> bool {
    type_ids::box_types().contains(&def_id)
}

pub fn is_std_cstring(def_id: DefId) -> bool {
    type_ids::cstring_types().contains(&def_id)
}

pub fn is_std_nonnull(def_id: DefId) -> bool {
    type_ids::nonnull_types().contains(&def_id)
}

pub fn is_maybe_uninit_type(def_id: DefId) -> bool {
    type_ids::maybe_uninit_types().contains(&def_id)
}

/// Whether the type inside any references, raw pointers, slices, or arrays is
/// the standard `MaybeUninit<T>`.
pub fn is_maybe_uninit_ty(ty: Ty<'_>) -> bool {
    let mut t = ty;
    loop {
        match t.kind() {
            TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
            TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
            TyKind::Adt(adt, _) => return is_maybe_uninit_type(adt.did()),
            _ => return false,
        }
    }
}

/// Whether `def_id` is the slice iterator type `Iter` or `IterMut`.
pub fn is_std_iter_or_itermut(def_id: DefId) -> bool {
    type_ids::iter_types().contains(&def_id)
}

/// Whether `def_id` is `core::cmp::Ordering`.
pub fn is_std_ordering(def_id: DefId) -> bool {
    type_ids::ordering_types().contains(&def_id)
}

/// Whether `def_id` is the standard `IndexRange` type.
pub fn is_index_range(def_id: DefId) -> bool {
    type_ids::index_range_types().contains(&def_id)
}
