//! Known APIs without MIR and trait calls handled by name.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::intrinsic_api;

fn is_std_api(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches!(tcx.crate_name(did.krate).as_str(), "core" | "alloc" | "std")
}

fn matches_path(tcx: TyCtxt<'_>, did: DefId, paths: &[&str]) -> bool {
    if !is_std_api(tcx, did) {
        return false;
    }
    let name = tcx.def_path_str(did);
    paths.iter().any(|path| {
        name == *path
            || path
                .split_once("::")
                .is_some_and(|(_, suffix)| name == suffix)
    })
}

fn is_no_mir(tcx: TyCtxt<'_>, did: DefId) -> bool {
    !tcx.is_mir_available(did) && !intrinsic_api::is_intrinsic(tcx, did)
}

pub fn is_call_mut(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches_path(
        tcx,
        did,
        &[
            "std::ops::FnMut::call_mut",
            "core::ops::FnMut::call_mut",
            "std::ops::function::FnMut::call_mut",
            "core::ops::function::FnMut::call_mut",
        ],
    )
}

pub fn is_clone(tcx: TyCtxt<'_>, did: DefId) -> bool {
    matches_path(
        tcx,
        did,
        &["std::clone::Clone::clone", "core::clone::Clone::clone"],
    )
}

pub fn is_slice_to_vec(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        is_no_mir(tcx, did)
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
        is_no_mir(tcx, did)
            && matches_path(
                tcx,
                did,
                &["alloc::alloc::__rust_alloc", "std::alloc::__rust_alloc"],
            )
    })
}

pub fn is_alloc_shim_marker(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        is_no_mir(tcx, did)
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
        is_no_mir(tcx, did)
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
