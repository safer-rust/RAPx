//! APIs that can lack MIR and the unavailable `DefId`s in this compilation.

use std::collections::HashSet;
use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};

use super::intrinsic_api;

const PATHS: [&[&str]; 6] = [
    &[
        "std::ops::FnMut::call_mut",
        "core::ops::FnMut::call_mut",
        "std::ops::function::FnMut::call_mut",
        "core::ops::function::FnMut::call_mut",
    ],
    &["std::clone::Clone::clone", "core::clone::Clone::clone"],
    &[
        "std::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec",
        "alloc::slice::<impl [T]>::to_vec_in::ConvertVec::to_vec",
    ],
    &["alloc::alloc::__rust_alloc", "std::alloc::__rust_alloc"],
    &[
        "alloc::alloc::__rust_no_alloc_shim_is_unstable_v2",
        "std::alloc::__rust_no_alloc_shim_is_unstable_v2",
    ],
    &["alloc::alloc::__rust_alloc_zeroed", "std::alloc::__rust_alloc_zeroed"],
];

struct NoMirIds {
    known: [Option<DefId>; 6],
    unavailable: HashSet<DefId>,
}

static IDS: OnceLock<NoMirIds> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut known = [None; 6];
        let mut unavailable = HashSet::new();
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|krate| {
                krate.is_local || matches!(krate.name.as_str(), "core" | "std" | "alloc")
            })
        {
            for function in krate.fn_defs() {
                let id = rustc_internal::internal(tcx, function.def_id());
                if !tcx.is_mir_available(id) && !intrinsic_api::is_intrinsic(tcx, id) {
                    unavailable.insert(id);
                }
                if matches!(krate.name.as_str(), "core" | "std" | "alloc") {
                    let name = function.name();
                    for (index, paths) in PATHS.iter().enumerate() {
                        if paths.iter().any(|path| {
                            name == *path
                                || path
                                    .split_once("::")
                                    .is_some_and(|(_, suffix)| name == suffix)
                        }) {
                            known[index].get_or_insert(id);
                        }
                    }
                }
            }
        }
        NoMirIds { known, unavailable }
    });
}

fn known(index: usize) -> Option<DefId> {
    IDS.get()
        .expect("No-MIR API IDs have not been initialized")
        .known[index]
}

pub fn is_no_mir(callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| {
        IDS.get()
            .expect("No-MIR API IDs have not been initialized")
            .unavailable
            .contains(&id)
    })
}

pub fn call_mut() -> Option<DefId> {
    known(0)
}

pub fn clone() -> Option<DefId> {
    known(1)
}

pub fn slice_to_vec() -> Option<DefId> {
    known(2)
}

pub fn is_slice_to_vec(callee: Option<DefId>) -> bool {
    is_no_mir(callee) && callee == slice_to_vec()
}

pub fn is_global_alloc_shim(callee: Option<DefId>) -> bool {
    is_no_mir(callee) && callee == known(3)
}

pub fn is_alloc_shim_marker(callee: Option<DefId>) -> bool {
    is_no_mir(callee) && callee == known(4)
}

pub fn is_global_alloc_zeroed_shim(callee: Option<DefId>) -> bool {
    is_no_mir(callee) && callee == known(5)
}
