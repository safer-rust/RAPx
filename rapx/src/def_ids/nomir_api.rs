//! Known standard-library APIs without MIR.
//!
//! # Agent Rules
//!
//! Keep this module limited to identifying standard-library APIs when their
//! MIR is unavailable. Do not depend on other RAPx modules.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::canonical_std_def_path;

fn matches_path(tcx: TyCtxt<'_>, did: DefId, paths: &[&str]) -> bool {
    let Some(name) = canonical_std_def_path(tcx, did) else {
        return false;
    };
    paths.iter().any(|path| {
        name == *path
            || path
                .split_once("::")
                .is_some_and(|(_, suffix)| name == suffix)
    })
}

fn has_no_mir(tcx: TyCtxt<'_>, did: DefId) -> bool {
    !tcx.is_mir_available(did)
}

pub fn is_convert_vec_to_vec(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        has_no_mir(tcx, did)
            && matches_path(
                tcx,
                did,
                &[
                    "std::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec",
                    "alloc::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec",
                ],
            )
    })
}

pub fn is_global_alloc_shim(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        has_no_mir(tcx, did)
            && matches_path(
                tcx,
                did,
                &["alloc::alloc::__rust_alloc", "std::alloc::__rust_alloc"],
            )
    })
}

/// Identify the allocator reallocation shim, whose MIR is unavailable.
pub fn is_global_realloc_shim(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        has_no_mir(tcx, did)
            && matches_path(tcx, did, &["alloc::alloc::__rust_realloc", "std::alloc::__rust_realloc"])
    })
}

pub fn is_alloc_shim_marker(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        has_no_mir(tcx, did)
            && matches_path(
                tcx,
                did,
                &[
                    "alloc::alloc::__rust_no_alloc_shim_is_unstable_v2",
                    "std::alloc::__rust_no_alloc_shim_is_unstable_v2",
                ],
            )
    })
}

pub fn is_global_alloc_zeroed_shim(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        has_no_mir(tcx, did)
            && matches_path(
                tcx,
                did,
                &[
                    "alloc::alloc::__rust_alloc_zeroed",
                    "std::alloc::__rust_alloc_zeroed",
                ],
            )
    })
}
