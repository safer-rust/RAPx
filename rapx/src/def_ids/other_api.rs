//! Known `core`/`std`/`alloc` API identities, regardless of MIR availability.
//!
//! [`init`] scans standard-library functions once for the fixed paths declared
//! by [`std_api_def_ids!`]. Other methods are recognized directly from their `DefId`.
//! Missing items in `#![no_std]` builds are reported as warnings.

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use std::sync::OnceLock;

pub fn ref_count_adjust(tcx: TyCtxt<'_>, did: DefId) -> Option<(DefId, i8)> {
    if !is_std_api(tcx, did) {
        return None;
    }
    let path = tcx.def_path_str(did);
    let delta = if path.ends_with("::increment_strong_count")
        || path.ends_with("::increment_strong_count_in")
    {
        1
    } else if path.ends_with("::decrement_strong_count")
        || path.ends_with("::decrement_strong_count_in")
    {
        -1
    } else {
        return None;
    };
    let owner = crate::helpers::name::get_struct_self_ty(tcx, did)?;
    let rustc_middle::ty::TyKind::Adt(adt, _) = owner.kind() else {
        return None;
    };
    if !crate::verify::contract::json::query_json_contracts(tcx, did)
        .iter()
        .any(|property| {
            property.kind() == Some(crate::verify::contract::PropertyKind::RefCountShare)
        })
    {
        return None;
    }
    Some((adt.did(), delta))
}

static INIT: OnceLock<IndexMap<Box<str>, DefId>> = OnceLock::new();

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
}

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

pub fn is_gcd(tcx: TyCtxt<'_>, did: DefId) -> bool {
    is_std_api(tcx, did) && tcx.def_path_str(did).ends_with("::gcd")
}

fn init_inner(tcx: TyCtxt) -> IndexMap<Box<str>, DefId> {
    const CRATES: &[&str] = &["core", "std", "alloc"];

    // Map every registered path — both with and without its
    // `std::`/`core::`/`alloc::` prefix — to its entry index.
    // `rustc_public::CrateDef::name()` emits the crate prefix only on newer
    // toolchains, so both forms must resolve to the same entry.
    let path_to_idx: std::collections::HashMap<&str, usize> = KNOWN_ITEM_PATHS
        .iter()
        .enumerate()
        .flat_map(|(idx, paths)| {
            paths.iter().flat_map(move |&p| {
                std::iter::once(p)
                    .chain(
                        ["std::", "core::", "alloc::"]
                            .into_iter()
                            .filter_map(move |pfx| p.strip_prefix(pfx)),
                    )
                    .map(move |q| (q, idx))
            })
        })
        .collect();

    let mut indices: IndexMap<_, _> = (0..KNOWN_ITEM_PATHS.len())
        .map(|idx| (idx, false))
        .collect();
    let mut map = IndexMap::<Box<str>, DefId>::with_capacity(KNOWN_ITEM_PATHS.len());

    let mut try_insert = |name: &str, def_id: rustc_public::DefId| {
        let Some(&idx) = path_to_idx.get(name) else {
            return;
        };
        assert_eq!(
            indices.insert(idx, true),
            Some(false),
            "DefId for {name} has been found: {:?}",
            map.get(KNOWN_ITEM_PATHS[idx][0])
        );
        // Store under the canonical (first) registered path so the `{id}()`
        // accessors — which probe the registered paths — find it regardless of
        // whether `name` carried a crate prefix.
        map.insert(
            Box::from(KNOWN_ITEM_PATHS[idx][0]),
            rustc_internal::internal(tcx, def_id),
        );
    };

    let mut loaded_crates = std::collections::HashSet::new();
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|krate| CRATES.iter().any(|name| *name == krate.name))
    {
        loaded_crates.insert(krate.name.clone());
        for fn_def in krate.fn_defs() {
            try_insert(&fn_def.name(), fn_def.def_id());
        }
    }

    #[cfg(debug_assertions)]
    map.sort_unstable_by(|a, _, b, _| a.cmp(b));

    if KNOWN_ITEM_PATHS.len() != map.len() {
        // Missing APIs are expected when a no_std crate does not load alloc.
        // cc https://github.com/Artisan-Lab/RAPx/issues/190#issuecomment-3303049000
        let not_found = indices
            .iter()
            .filter_map(|(&idx, &found)| {
                if found {
                    return None;
                }
                // Only report entries whose crate was actually loaded for this
                // compilation. Entries pointing solely at unloaded crates (e.g.
                // `alloc` when verifying `core`) are expected to be absent.
                let in_loaded_crate = KNOWN_ITEM_PATHS[idx].iter().any(|p| {
                    p.split("::")
                        .next()
                        .is_some_and(|pfx| loaded_crates.contains(pfx))
                });
                in_loaded_crate.then_some(KNOWN_ITEM_PATHS[idx])
            })
            .collect::<Vec<_>>();
        if !not_found.is_empty() {
            rap_warn!(
                "Known standard-library functions are incompletely resolved.\n\
                 {} fn ids are not found: {not_found:#?}",
                not_found.len()
            );
        }
    }

    map
}

macro_rules! std_api_def_ids {
    ($( $(#[$attr:meta])* $id:ident : $paths:expr ,)+) => {
        const KNOWN_ITEM_PATHS: &[&[&str]] = &[$( $(#[$attr])* $paths ,)+];
        $(
            $(#[$attr])*
            pub fn $id() -> Option<DefId> {
                let map = INIT.get().expect("Known item DefIds haven't been initialized.");
                for path in $paths {
                    match map.get(*path) {
                        Some(id) => return Some(*id),
                        None => ()
                    }
                }
                None
            }
        )+
    };
}

// For no_std crates, function paths start from core instead of std.
// cc https://github.com/Artisan-Lab/RAPx/issues/190
std_api_def_ids! {
    dealloc: &[
        "std::alloc::dealloc",
        "alloc::alloc::dealloc"
    ],
    drop: &[
        "std::mem::drop",
        "core::mem::drop",
    ],
    drop_in_place: &[
        "std::ptr::drop_in_place",
        "core::ptr::drop_in_place",
    ],
    manually_drop: &[
        "std::mem::ManuallyDrop::<T>::drop",
        "core::mem::ManuallyDrop::<T>::drop",
        "std::mem::manually_drop::ManuallyDrop::<T>::drop",
        "core::mem::manually_drop::ManuallyDrop::<T>::drop"
    ],
    replace: &[
        "std::mem::replace",
        "core::mem::replace"
    ],
    take: &[
        "std::mem::take",
        "core::mem::take"
    ],
    ptr_read: &[
        "std::ptr::read",
        "core::ptr::read"
    ],
    ptr_read_unaligned: &[
        "std::ptr::read_unaligned",
        "core::ptr::read_unaligned"
    ],
    ptr_read_volatile: &[
        "std::ptr::read_volatile",
        "core::ptr::read_volatile"
    ],
    ptr_write: &[
        "std::ptr::write",
        "core::ptr::write"
    ],
    ptr_write_unaligned: &[
        "std::ptr::write_unaligned",
        "core::ptr::write_unaligned"
    ],
    ptr_write_volatile: &[
        "std::ptr::write_volatile",
        "core::ptr::write_volatile"
    ],
    ptr_write_bytes: &[
        "std::ptr::write_bytes",
        "core::ptr::write_bytes"
    ],
    ptr_copy: &[
        "std::ptr::copy",
        "core::ptr::copy"
    ],
    ptr_copy_nonoverlapping: &[
        "std::ptr::copy_nonoverlapping",
        "core::ptr::copy_nonoverlapping"
    ],
    assume_init_read: &[
        "std::mem::MaybeUninit::<T>::assume_init_read",
        "core::mem::MaybeUninit::<T>::assume_init_read",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read"
    ],
    mem_size_of: &[
        "std::mem::size_of",
        "core::mem::size_of"
    ],
    mem_align_of: &[
        "std::mem::align_of",
        "core::mem::align_of"
    ],
    ptr_align_offset: &[
        "std::ptr::align_offset",
        "core::ptr::align_offset"
    ],
    const_ptr_align_offset: &[
        "std::ptr::const_ptr::<impl *const T>::align_offset",
        "core::ptr::const_ptr::<impl *const T>::align_offset"
    ],
    mut_ptr_align_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::align_offset",
        "core::ptr::mut_ptr::<impl *mut T>::align_offset"
    ],
    cstr_from_bytes_with_nul_unchecked: &[
        "std::ffi::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::CStr::from_bytes_with_nul_unchecked",
        "std::ffi::c_str::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::c_str::CStr::from_bytes_with_nul_unchecked"
    ],
    #[cfg(rapx_ge_99)]
    box_assume_init_into_vec_unsafe: &[
        "std::boxed::box_assume_init_into_vec_unsafe",
        "alloc::boxed::box_assume_init_into_vec_unsafe"
    ],
    const_ptr_is_null: &[
        "std::ptr::const_ptr::<impl *const T>::is_null",
        "core::ptr::const_ptr::<impl *const T>::is_null"
    ],
    const_ptr_addr: &[
        "std::ptr::const_ptr::<impl *const T>::addr",
        "core::ptr::const_ptr::<impl *const T>::addr"
    ],
    const_ptr_cast: &[
        "std::ptr::const_ptr::<impl *const T>::cast",
        "core::ptr::const_ptr::<impl *const T>::cast"
    ],
    const_ptr_cast_mut: &[
        "std::ptr::const_ptr::<impl *const T>::cast_mut",
        "core::ptr::const_ptr::<impl *const T>::cast_mut"
    ],
    const_ptr_cast_array: &[
        "std::ptr::const_ptr::<impl *const T>::cast_array",
        "core::ptr::const_ptr::<impl *const T>::cast_array"
    ],
    const_ptr_slice_is_empty: &[
        "std::ptr::const_ptr::<impl *const [T]>::is_empty",
        "core::ptr::const_ptr::<impl *const [T]>::is_empty"
    ],
    const_ptr_slice_len: &[
        "std::ptr::const_ptr::<impl *const [T]>::len",
        "core::ptr::const_ptr::<impl *const [T]>::len"
    ],
    const_ptr_slice_as_ptr: &[
        "std::ptr::const_ptr::<impl *const [T]>::as_ptr",
        "core::ptr::const_ptr::<impl *const [T]>::as_ptr"
    ],
    mut_ptr_is_null: &[
        "std::ptr::mut_ptr::<impl *mut T>::is_null",
        "core::ptr::mut_ptr::<impl *mut T>::is_null"
    ],
    mut_ptr_addr: &[
        "std::ptr::mut_ptr::<impl *mut T>::addr",
        "core::ptr::mut_ptr::<impl *mut T>::addr"
    ],
    mut_ptr_cast: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast",
        "core::ptr::mut_ptr::<impl *mut T>::cast"
    ],
    mut_ptr_cast_const: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast_const",
        "core::ptr::mut_ptr::<impl *mut T>::cast_const"
    ],
    mut_ptr_cast_array: &[
        "std::ptr::mut_ptr::<impl *mut T>::cast_array",
        "core::ptr::mut_ptr::<impl *mut T>::cast_array"
    ],
    mut_ptr_slice_is_empty: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::is_empty",
        "core::ptr::mut_ptr::<impl *mut [T]>::is_empty"
    ],
    mut_ptr_slice_len: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::len",
        "core::ptr::mut_ptr::<impl *mut [T]>::len"
    ],
    mut_ptr_slice_as_mut_ptr: &[
        "std::ptr::mut_ptr::<impl *mut [T]>::as_mut_ptr",
        "core::ptr::mut_ptr::<impl *mut [T]>::as_mut_ptr"
    ],
    nonnull_addr: &[
        "std::ptr::NonNull::<T>::addr",
        "core::ptr::NonNull::<T>::addr",
        "std::ptr::non_null::NonNull::<T>::addr",
        "core::ptr::non_null::NonNull::<T>::addr"
    ],
    nonnull_cast: &[
        "std::ptr::NonNull::<T>::cast",
        "core::ptr::NonNull::<T>::cast",
        "std::ptr::non_null::NonNull::<T>::cast",
        "core::ptr::non_null::NonNull::<T>::cast"
    ],
    nonnull_slice_is_empty: &[
        "std::ptr::NonNull::<[T]>::is_empty",
        "core::ptr::NonNull::<[T]>::is_empty",
        "std::ptr::non_null::NonNull::<[T]>::is_empty",
        "core::ptr::non_null::NonNull::<[T]>::is_empty"
    ],
    nonnull_slice_len: &[
        "std::ptr::NonNull::<[T]>::len",
        "core::ptr::NonNull::<[T]>::len",
        "std::ptr::non_null::NonNull::<[T]>::len",
        "core::ptr::non_null::NonNull::<[T]>::len"
    ],
    slice_len: &[
        "std::slice::<impl [T]>::len",
        "core::slice::<impl [T]>::len"
    ],
    str_len: &[
        "std::str::<impl str>::len",
        "core::str::<impl str>::len"
    ],
    str_is_empty: &[
        "std::str::<impl str>::is_empty",
        "core::str::<impl str>::is_empty"
    ],
    vec_len: &[
        "std::vec::Vec::<T, A>::len",
        "alloc::vec::Vec::<T, A>::len"
    ],
    string_len: &[
        "std::string::String::len",
        "alloc::string::String::len"
    ],
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}

/// Find any drop fn. Any of these drop fns can be missing, e.g. for crates like no_std without
/// using alloc, dealloc doesn't exist.
pub fn is_drop_fn(target: DefId) -> bool {
    let drop_fn = [drop(), drop_in_place(), manually_drop(), dealloc()];
    matches_any(Some(target), &drop_fn)
}

pub(crate) fn matches_any(target: Option<DefId>, candidates: &[Option<DefId>]) -> bool {
    target.is_some_and(|id| candidates.contains(&Some(id)))
}
