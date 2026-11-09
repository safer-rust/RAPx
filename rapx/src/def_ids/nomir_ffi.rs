//! FFI-facing standard-library APIs whose MIR may be unavailable.

use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{rustc_internal, CrateDef};

const PATHS: [&[&str]; 1] = [
    &[
        "std::ffi::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::CString::from_vec_with_nul_unchecked",
        "std::ffi::c_str::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::c_str::CString::from_vec_with_nul_unchecked",
    ],
];

static IDS: OnceLock<[Option<DefId>; 1]> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut known = [None; 1];
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|krate| matches!(krate.name.as_str(), "std" | "alloc" | "core"))
        {
            for function in krate.fn_defs() {
                let name = function.name();
                for (index, paths) in PATHS.iter().enumerate() {
                    if paths.iter().any(|path| {
                        name == *path
                            || path
                                .split_once("::")
                                .is_some_and(|(_, suffix)| name == suffix)
                    }) {
                        known[index].get_or_insert_with(|| {
                            rustc_internal::internal(tcx, function.def_id())
                        });
                    }
                }
            }
        }
        known
    });
}

pub fn cstring_from_vec_with_nul_unchecked() -> Option<DefId> {
    IDS.get()
        .expect("No-MIR FFI API IDs have not been initialized")[0]
}
