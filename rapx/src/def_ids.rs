//! Known API and type identities.
//!
//! # Agent Rules
//!
//! Keep this module limited to identity submodules and shared identity helpers.
//! Do not depend on other RAPx modules.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

pub(crate) mod diagnostic_api;
pub(crate) mod intrinsic_api;
pub(crate) mod lang_api;
pub(crate) mod nomir_api;
pub(crate) mod other_api;
pub(crate) mod type_ids;

fn is_std_api(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(tcx.crate_name(did.krate).as_str(), "core" | "alloc" | "std")
}

/// Whether `callee` explicitly drops the value stored in `ManuallyDrop<T>`.
pub(crate) fn is_manually_drop_drop(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| other_api::is_manually_drop(tcx, did))
}

/// Whether `callee` is the `ptr_offset_from` or `ptr_offset_from_unsigned` intrinsic.
pub(crate) fn is_intrinsic_ptr_offset_from(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    intrinsic_api::intrinsic_name(tcx, callee).is_some_and(|name| {
        matches!(name.as_str(), "ptr_offset_from" | "ptr_offset_from_unsigned")
    })
}

/// Whether `callee` is a diagnostic-item pointer write API.
pub(crate) fn is_ptr_write(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| diagnostic_api::is_ptr_write(tcx, did))
}

/// Whether stripping references, raw pointers, slices, and arrays from `ty`
/// reaches the standard `MaybeUninit<T>` type.
pub(crate) fn strips_to_maybe_uninit(ty: Ty<'_>) -> bool {
    let mut ty = ty;
    loop {
        match ty.kind() {
            TyKind::Slice(element) | TyKind::Array(element, _) => ty = *element,
            TyKind::RawPtr(element, _) | TyKind::Ref(_, element, _) => ty = *element,
            TyKind::Adt(adt, _) => return type_ids::is_maybe_uninit_type(adt.did()),
            _ => return false,
        }
    }
}
