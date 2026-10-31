//! FFI-facing standard-library APIs whose MIR may be unavailable.

use std::sync::OnceLock;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{rustc_internal, CrateDef};

const PATHS: [&[&str]; 3] = [
    &[
        "std::ffi::CString::from_raw",
        "alloc::ffi::CString::from_raw",
        "std::ffi::c_str::CString::from_raw",
        "alloc::ffi::c_str::CString::from_raw",
    ],
    &[
        "std::ffi::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::CString::from_vec_with_nul_unchecked",
        "std::ffi::c_str::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::c_str::CString::from_vec_with_nul_unchecked",
    ],
    &["core::ffi::c_str::strlen::runtime::strlen"],
];

static IDS: OnceLock<[Option<DefId>; 3]> = OnceLock::new();

pub fn init(tcx: TyCtxt<'_>) {
    IDS.get_or_init(|| {
        let mut known = [None; 3];
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

pub fn cstring_from_raw() -> Option<DefId> {
    IDS.get()
        .expect("No-MIR FFI API IDs have not been initialized")[0]
}

pub fn cstring_from_vec_with_nul_unchecked() -> Option<DefId> {
    IDS.get()
        .expect("No-MIR FFI API IDs have not been initialized")[1]
}

pub fn cstr_runtime_strlen() -> Option<DefId> {
    IDS.get()
        .expect("No-MIR FFI API IDs have not been initialized")[2]
}
