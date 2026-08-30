//! Resolution of well-known `core`/`std`/`alloc` function paths to their
//! internal [`DefId`]s.
//!
//! This module is the single home for "which standard-library item is this
//! `DefId`?", used by [`crate::helpers::api_classify`] and the alias checker to
//! match APIs exactly instead of substring-matching a `def_path_str`.  It is
//! deliberately placed at the crate root (next to [`crate::compat`]) rather
//! than under `helpers/`, because it owns global state and a one-time
//! `init(tcx)` hook in the compiler callback.
//!
//! # How a lookup works
//!
//! 1. The [`intrinsics!`] macro declares a *path table*: each identifier maps
//!    to one or more candidate `fn_def.name()` strings (typically the `std::`
//!    re-export plus the `core::`/`alloc::` canonical form, for `#![no_std]`
//!    crates) and generates a `{id}() -> Option<DefId>` accessor.
//! 2. [`init`] runs once from [`crate::RapCallback::after_analysis`], iterates
//!    every `fn_def` of the `core`/`std`/`alloc` crates via `rustc_public`,
//!    and caches the `path -> DefId` map in a `OnceLock`.
//! 3. [`contains`] tests whether a call-site `DefId` is in a set of resolved
//!    ids; [`is_drop_fn`] is a convenience wrapper over the drop family.
//!
//! # Path format
//!
//! `rustc_public::CrateDef::name()` is `def_path_str` with crate-name
//! resolution and untrimmed paths, so a re-exported item appears under its
//! `std::` name and generics are kept: `std::mem::MaybeUninit::<T>::write`,
//! `std::result::Result::<T, E>::unwrap`, `std::vec::Vec::<T, A>::push`,
//! `std::ptr::mut_ptr::<impl *mut T>::copy_from`.
//!
//! # Limitations
//!
//! - Not every std item is emitted by `rustc_public::Crate::fn_defs()` (e.g.
//!   `Vec::from_raw_parts`), so some APIs cannot be resolved here and must
//!   keep a name matcher — see `api_classify::is_from_raw_parts`.
//! - In `#![no_std]` builds some intrinsics are absent; [`init`] only warns
//!   (`rap_warn!`) instead of panicking, so an entry with no matching path
//!   simply yields `None`.

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use std::sync::OnceLock;

static INIT: OnceLock<Intrinsics> = OnceLock::new();

struct Intrinsics {
    // The key is fn path, starting from `core::` or `std::`. The value is internal def id.
    map: IndexMap<Box<str>, DefId>,
}

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
}

fn init_inner(tcx: TyCtxt) -> Intrinsics {
    const CRATES: &[&str] = &["core", "std", "alloc"];

    // Map every registered path — both with and without its
    // `std::`/`core::`/`alloc::` prefix — to its entry index.
    // `rustc_public::CrateDef::name()` emits the crate prefix only on newer
    // toolchains, so both forms must resolve to the same entry.
    let path_to_idx: std::collections::HashMap<&str, usize> = INTRINSICS
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

    let mut indices: IndexMap<_, _> = (0..INTRINSICS.len()).map(|idx| (idx, false)).collect();
    let mut map = IndexMap::<Box<str>, DefId>::with_capacity(INTRINSICS.len());

    let mut try_insert = |name: &str, def_id: rustc_public::DefId| {
        let Some(&idx) = path_to_idx.get(name) else { return };
        assert_eq!(
            indices.insert(idx, true),
            Some(false),
            "DefId for {name} has been found: {:?}",
            map.get(INTRINSICS[idx][0])
        );
        // Store under the canonical (first) registered path so the `{id}()`
        // accessors — which probe the registered paths — find it regardless of
        // whether `name` carried a crate prefix.
        map.insert(Box::from(INTRINSICS[idx][0]), rustc_internal::internal(tcx, def_id));
    };

    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates().into_iter())
        .filter(|krate| CRATES.iter().any(|name| *name == krate.name))
    {
        for fn_def in krate.fn_defs() {
            try_insert(&fn_def.name(), fn_def.def_id());
        }
    }

    #[cfg(debug_assertions)]
    map.sort_unstable_by(|a, _, b, _| a.cmp(b));

    if INTRINSICS.len() != map.len() {
        // The reason to not make this an assertion is allowing compilation on
        // missing instrinsics, e.g. no_std crates without using alloc will never
        // have the dealloc intrinsic.
        // cc https://github.com/Artisan-Lab/RAPx/issues/190#issuecomment-3303049000
        let not_found = indices
            .iter()
            .filter_map(|(&idx, &found)| (!found).then_some(INTRINSICS[idx]))
            .collect::<Vec<_>>();
        rap_warn!(
            "Intrinsic functions is incompletely retrieved.\n\
             {} fn ids are not found: {not_found:#?}",
            not_found.len()
        );
    }

    Intrinsics { map }
}

macro_rules! intrinsics {
    ($( $id:ident : $paths:expr ,)+) => {
        const INTRINSICS: &[&[&str]] = &[$( $paths ,)+];
        $(
            pub fn $id() -> Option<DefId> {
                let map = &INIT.get().expect("Intrinsics DefIds haven't been initialized.").map;
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

// for #![no_std] crates, intrinsics fn paths start from core instead of core.
// cc https://github.com/Artisan-Lab/RAPx/issues/190
intrinsics! {
    call_mut: &[
        "std::ops::FnMut::call_mut",
        "core::ops::FnMut::call_mut",
        "std::ops::function::FnMut::call_mut",
        "core::ops::function::FnMut::call_mut"
    ],
    clone: &[
        "std::clone::Clone::clone",
        "core::clone::Clone::clone"
    ],
    copy_from: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from"
    ],
    copy_from_nonoverlapping: &[
        "std::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping",
        "core::ptr::mut_ptr::<impl *mut T>::copy_from_nonoverlapping"
    ],
    copy_to: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to",
        "core::ptr::const_ptr::<impl *const T>::copy_to",
    ],
    copy_to_nonoverlapping: &[
        "std::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping",
        "core::ptr::const_ptr::<impl *const T>::copy_to_nonoverlapping"
    ],
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
    select_unpredictable: &[
        "std::intrinsics::select_unpredictable",
        "core::intrinsics::select_unpredictable"
    ],
    hint_select_unpredictable: &[
        "std::hint::select_unpredictable",
        "core::hint::select_unpredictable"
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
    intrinsics_copy: &[
        "std::intrinsics::copy",
        "core::intrinsics::copy"
    ],
    intrinsics_copy_nonoverlapping: &[
        "std::intrinsics::copy_nonoverlapping",
        "core::intrinsics::copy_nonoverlapping"
    ],
    assume_init_read: &[
        "std::mem::MaybeUninit::<T>::assume_init_read",
        "core::mem::MaybeUninit::<T>::assume_init_read",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_read"
    ],
    maybe_uninit_uninit: &[
        "std::mem::MaybeUninit::<T>::uninit",
        "core::mem::MaybeUninit::<T>::uninit",
        "std::mem::maybe_uninit::MaybeUninit::<T>::uninit",
        "core::mem::maybe_uninit::MaybeUninit::<T>::uninit"
    ],
    maybe_uninit_write: &[
        "std::mem::MaybeUninit::<T>::write",
        "core::mem::MaybeUninit::<T>::write",
        "std::mem::maybe_uninit::MaybeUninit::<T>::write",
        "core::mem::maybe_uninit::MaybeUninit::<T>::write"
    ],
    maybe_uninit_as_ptr: &[
        "std::mem::MaybeUninit::<T>::as_ptr",
        "core::mem::MaybeUninit::<T>::as_ptr",
        "std::mem::maybe_uninit::MaybeUninit::<T>::as_ptr",
        "core::mem::maybe_uninit::MaybeUninit::<T>::as_ptr"
    ],
    maybe_uninit_as_mut_ptr: &[
        "std::mem::MaybeUninit::<T>::as_mut_ptr",
        "core::mem::MaybeUninit::<T>::as_mut_ptr",
        "std::mem::maybe_uninit::MaybeUninit::<T>::as_mut_ptr",
        "core::mem::maybe_uninit::MaybeUninit::<T>::as_mut_ptr"
    ],
    maybe_uninit_assume_init: &[
        "std::mem::MaybeUninit::<T>::assume_init",
        "core::mem::MaybeUninit::<T>::assume_init",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init"
    ],
    maybe_uninit_assume_init_ref: &[
        "std::mem::MaybeUninit::<T>::assume_init_ref",
        "core::mem::MaybeUninit::<T>::assume_init_ref",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_ref",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_ref"
    ],
    maybe_uninit_assume_init_mut: &[
        "std::mem::MaybeUninit::<T>::assume_init_mut",
        "core::mem::MaybeUninit::<T>::assume_init_mut",
        "std::mem::maybe_uninit::MaybeUninit::<T>::assume_init_mut",
        "core::mem::maybe_uninit::MaybeUninit::<T>::assume_init_mut"
    ],
    mem_size_of: &[
        "std::mem::size_of",
        "core::mem::size_of"
    ],
    mem_align_of: &[
        "std::mem::align_of",
        "core::mem::align_of"
    ],
    intrinsics_size_of: &[
        "std::intrinsics::size_of",
        "core::intrinsics::size_of"
    ],
    intrinsics_align_of: &[
        "std::intrinsics::align_of",
        "core::intrinsics::align_of"
    ],
    ptr_align_offset: &[
        "std::ptr::align_offset",
        "core::ptr::align_offset"
    ],
    nonnull_align_offset: &[
        "std::ptr::NonNull::<T>::align_offset",
        "core::ptr::NonNull::<T>::align_offset"
    ],
    nonnull_new: &[
        "std::ptr::NonNull::<T>::new",
        "core::ptr::NonNull::<T>::new"
    ],
    const_ptr_align_offset: &[
        "std::ptr::const_ptr::<impl *const T>::align_offset",
        "core::ptr::const_ptr::<impl *const T>::align_offset"
    ],
    mut_ptr_align_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::align_offset",
        "core::ptr::mut_ptr::<impl *mut T>::align_offset"
    ],
    const_ptr_add: &[
        "std::ptr::const_ptr::<impl *const T>::add",
        "core::ptr::const_ptr::<impl *const T>::add"
    ],
    const_ptr_wrapping_add: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_add",
        "core::ptr::const_ptr::<impl *const T>::wrapping_add"
    ],
    const_ptr_sub: &[
        "std::ptr::const_ptr::<impl *const T>::sub",
        "core::ptr::const_ptr::<impl *const T>::sub"
    ],
    const_ptr_wrapping_sub: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_sub",
        "core::ptr::const_ptr::<impl *const T>::wrapping_sub"
    ],
    const_ptr_offset: &[
        "std::ptr::const_ptr::<impl *const T>::offset",
        "core::ptr::const_ptr::<impl *const T>::offset"
    ],
    const_ptr_wrapping_offset: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_offset",
        "core::ptr::const_ptr::<impl *const T>::wrapping_offset"
    ],
    const_ptr_byte_add: &[
        "std::ptr::const_ptr::<impl *const T>::byte_add",
        "core::ptr::const_ptr::<impl *const T>::byte_add"
    ],
    const_ptr_wrapping_byte_add: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_add",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_add"
    ],
    const_ptr_byte_sub: &[
        "std::ptr::const_ptr::<impl *const T>::byte_sub",
        "core::ptr::const_ptr::<impl *const T>::byte_sub"
    ],
    const_ptr_wrapping_byte_sub: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_sub",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_sub"
    ],
    const_ptr_byte_offset: &[
        "std::ptr::const_ptr::<impl *const T>::byte_offset",
        "core::ptr::const_ptr::<impl *const T>::byte_offset"
    ],
    const_ptr_wrapping_byte_offset: &[
        "std::ptr::const_ptr::<impl *const T>::wrapping_byte_offset",
        "core::ptr::const_ptr::<impl *const T>::wrapping_byte_offset"
    ],
    mut_ptr_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::add",
        "core::ptr::mut_ptr::<impl *mut T>::add"
    ],
    mut_ptr_wrapping_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_add",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_add"
    ],
    mut_ptr_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::sub",
        "core::ptr::mut_ptr::<impl *mut T>::sub"
    ],
    mut_ptr_wrapping_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_sub",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_sub"
    ],
    mut_ptr_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::offset",
        "core::ptr::mut_ptr::<impl *mut T>::offset"
    ],
    mut_ptr_wrapping_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_offset",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_offset"
    ],
    mut_ptr_byte_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_add",
        "core::ptr::mut_ptr::<impl *mut T>::byte_add"
    ],
    mut_ptr_wrapping_byte_add: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_add",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_add"
    ],
    mut_ptr_byte_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_sub",
        "core::ptr::mut_ptr::<impl *mut T>::byte_sub"
    ],
    mut_ptr_wrapping_byte_sub: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_sub",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_sub"
    ],
    mut_ptr_byte_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::byte_offset",
        "core::ptr::mut_ptr::<impl *mut T>::byte_offset"
    ],
    mut_ptr_wrapping_byte_offset: &[
        "std::ptr::mut_ptr::<impl *mut T>::wrapping_byte_offset",
        "core::ptr::mut_ptr::<impl *mut T>::wrapping_byte_offset"
    ],
    nonnull_add: &[
        "std::ptr::NonNull::<T>::add",
        "core::ptr::NonNull::<T>::add"
    ],
    nonnull_sub: &[
        "std::ptr::NonNull::<T>::sub",
        "core::ptr::NonNull::<T>::sub"
    ],
    nonnull_byte_add: &[
        "std::ptr::NonNull::<T>::byte_add",
        "core::ptr::NonNull::<T>::byte_add"
    ],
    nonnull_byte_sub: &[
        "std::ptr::NonNull::<T>::byte_sub",
        "core::ptr::NonNull::<T>::byte_sub"
    ],
    nonnull_offset: &[
        "std::ptr::NonNull::<T>::offset",
        "core::ptr::NonNull::<T>::offset"
    ],
    nonnull_byte_offset: &[
        "std::ptr::NonNull::<T>::byte_offset",
        "core::ptr::NonNull::<T>::byte_offset"
    ],
    option_unwrap: &[
        "std::option::Option::<T>::unwrap",
        "core::option::Option::<T>::unwrap"
    ],
    option_expect: &[
        "std::option::Option::<T>::expect",
        "core::option::Option::<T>::expect"
    ],
    option_unwrap_unchecked: &[
        "std::option::Option::<T>::unwrap_unchecked",
        "core::option::Option::<T>::unwrap_unchecked"
    ],
    result_unwrap: &[
        "std::result::Result::<T, E>::unwrap",
        "core::result::Result::<T, E>::unwrap"
    ],
    result_unwrap_err: &[
        "std::result::Result::<T, E>::unwrap_err",
        "core::result::Result::<T, E>::unwrap_err"
    ],
    result_expect: &[
        "std::result::Result::<T, E>::expect",
        "core::result::Result::<T, E>::expect"
    ],
    result_expect_err: &[
        "std::result::Result::<T, E>::expect_err",
        "core::result::Result::<T, E>::expect_err"
    ],
    result_unwrap_unchecked: &[
        "std::result::Result::<T, E>::unwrap_unchecked",
        "core::result::Result::<T, E>::unwrap_unchecked"
    ],
    cstr_from_ptr: &[
        "std::ffi::CStr::from_ptr",
        "core::ffi::CStr::from_ptr"
    ],
    cstr_from_bytes_with_nul_unchecked: &[
        "std::ffi::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::CStr::from_bytes_with_nul_unchecked"
    ],
    cstring_from_vec_with_nul_unchecked: &[
        "std::ffi::CString::from_vec_with_nul_unchecked",
        "alloc::ffi::CString::from_vec_with_nul_unchecked"
    ],
    vec_push: &[
        "std::vec::Vec::<T, A>::push",
        "alloc::vec::Vec::<T, A>::push"
    ],
    vec_reserve: &[
        "std::vec::Vec::<T, A>::reserve",
        "alloc::vec::Vec::<T, A>::reserve"
    ],
    vec_reserve_exact: &[
        "std::vec::Vec::<T, A>::reserve_exact",
        "alloc::vec::Vec::<T, A>::reserve_exact"
    ],
    vec_shrink_to_fit: &[
        "std::vec::Vec::<T, A>::shrink_to_fit",
        "alloc::vec::Vec::<T, A>::shrink_to_fit"
    ],
    vec_shrink_to: &[
        "std::vec::Vec::<T, A>::shrink_to",
        "alloc::vec::Vec::<T, A>::shrink_to"
    ],
    vec_insert: &[
        "std::vec::Vec::<T, A>::insert",
        "alloc::vec::Vec::<T, A>::insert"
    ],
    vec_remove: &[
        "std::vec::Vec::<T, A>::remove",
        "alloc::vec::Vec::<T, A>::remove"
    ],
    vec_clear: &[
        "std::vec::Vec::<T, A>::clear",
        "alloc::vec::Vec::<T, A>::clear"
    ],
    vec_truncate: &[
        "std::vec::Vec::<T, A>::truncate",
        "alloc::vec::Vec::<T, A>::truncate"
    ],
    vec_set_len: &[
        "std::vec::Vec::<T, A>::set_len",
        "alloc::vec::Vec::<T, A>::set_len"
    ],
    box_from_raw: &[
        "std::boxed::Box::<T>::from_raw",
        "alloc::boxed::Box::<T>::from_raw"
    ],
    cstring_from_raw: &[
        "std::ffi::CString::from_raw",
        "alloc::ffi::CString::from_raw"
    ],
    arc_from_raw: &[
        "std::sync::Arc::<T>::from_raw",
        "alloc::sync::Arc::<T>::from_raw"
    ],
    rc_from_raw: &[
        "std::rc::Rc::<T>::from_raw",
        "alloc::rc::Rc::<T>::from_raw"
    ],
    box_from_raw_in: &[
        "std::boxed::Box::<T, A>::from_raw_in",
        "alloc::boxed::Box::<T, A>::from_raw_in"
    ],
    arc_from_raw_in: &[
        "std::sync::Arc::<T, A>::from_raw_in",
        "alloc::sync::Arc::<T, A>::from_raw_in"
    ],
    rc_from_raw_in: &[
        "std::rc::Rc::<T, A>::from_raw_in",
        "alloc::rc::Rc::<T, A>::from_raw_in"
    ],
    box_into_raw: &[
        "std::boxed::Box::<T>::into_raw",
        "alloc::boxed::Box::<T>::into_raw"
    ],
    box_as_ptr: &[
        "std::boxed::Box::<T, A>::as_ptr",
        "alloc::boxed::Box::<T, A>::as_ptr"
    ],
    box_as_mut_ptr: &[
        "std::boxed::Box::<T, A>::as_mut_ptr",
        "alloc::boxed::Box::<T, A>::as_mut_ptr"
    ],
    cstring_into_raw: &[
        "std::ffi::CString::into_raw",
        "alloc::ffi::CString::into_raw"
    ],
    arc_into_raw: &[
        "std::sync::Arc::<T>::into_raw",
        "alloc::sync::Arc::<T>::into_raw"
    ],
    arc_as_ptr: &[
        "std::sync::Arc::<T>::as_ptr",
        "alloc::sync::Arc::<T>::as_ptr"
    ],
    rc_into_raw: &[
        "std::rc::Rc::<T>::into_raw",
        "alloc::rc::Rc::<T>::into_raw"
    ],
    rc_as_ptr: &[
        "std::rc::Rc::<T>::as_ptr",
        "alloc::rc::Rc::<T>::as_ptr"
    ],
    vec_from_elem: &[
        "std::vec::from_elem",
        "alloc::vec::from_elem"
    ],
    vec_into_boxed_slice: &[
        "std::vec::Vec::<T, A>::into_boxed_slice",
        "alloc::vec::Vec::<T, A>::into_boxed_slice"
    ],
    slice_into_vec: &[
        "std::slice::<impl [T]>::into_vec",
        "core::slice::<impl [T]>::into_vec"
    ],
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
        "core::ptr::NonNull::<T>::addr"
    ],
    nonnull_cast: &[
        "std::ptr::NonNull::<T>::cast",
        "core::ptr::NonNull::<T>::cast"
    ],
    nonnull_as_ptr: &[
        "std::ptr::NonNull::<T>::as_ptr",
        "core::ptr::NonNull::<T>::as_ptr"
    ],
    nonnull_slice_is_empty: &[
        "std::ptr::NonNull::<[T]>::is_empty",
        "core::ptr::NonNull::<[T]>::is_empty"
    ],
    nonnull_slice_len: &[
        "std::ptr::NonNull::<[T]>::len",
        "core::ptr::NonNull::<[T]>::len"
    ],
    nonnull_slice_as_mut_ptr: &[
        "std::ptr::NonNull::<[T]>::as_mut_ptr",
        "core::ptr::NonNull::<[T]>::as_mut_ptr"
    ],
    slice_len: &[
        "std::slice::<impl [T]>::len",
        "core::slice::<impl [T]>::len"
    ],
    slice_is_empty: &[
        "std::slice::<impl [T]>::is_empty",
        "core::slice::<impl [T]>::is_empty"
    ],
    slice_as_ptr: &[
        "std::slice::<impl [T]>::as_ptr",
        "core::slice::<impl [T]>::as_ptr"
    ],
    slice_as_mut_ptr: &[
        "std::slice::<impl [T]>::as_mut_ptr",
        "core::slice::<impl [T]>::as_mut_ptr"
    ],
    str_len: &[
        "std::str::<impl str>::len",
        "core::str::<impl str>::len"
    ],
    str_is_empty: &[
        "std::str::<impl str>::is_empty",
        "core::str::<impl str>::is_empty"
    ],
    str_as_ptr: &[
        "std::str::<impl str>::as_ptr",
        "core::str::<impl str>::as_ptr"
    ],
    str_as_mut_ptr: &[
        "std::str::<impl str>::as_mut_ptr",
        "core::str::<impl str>::as_mut_ptr"
    ],
    vec_len: &[
        "std::vec::Vec::<T, A>::len",
        "alloc::vec::Vec::<T, A>::len"
    ],
    vec_is_empty: &[
        "std::vec::Vec::<T, A>::is_empty",
        "alloc::vec::Vec::<T, A>::is_empty"
    ],
    vec_as_ptr: &[
        "std::vec::Vec::<T, A>::as_ptr",
        "alloc::vec::Vec::<T, A>::as_ptr"
    ],
    vec_as_mut_ptr: &[
        "std::vec::Vec::<T, A>::as_mut_ptr",
        "alloc::vec::Vec::<T, A>::as_mut_ptr"
    ],
    string_len: &[
        "std::string::String::len",
        "alloc::string::String::len"
    ],
    string_is_empty: &[
        "std::string::String::is_empty",
        "alloc::string::String::is_empty"
    ],
    cstr_as_ptr: &[
        "std::ffi::CStr::as_ptr",
        "core::ffi::CStr::as_ptr"
    ],
    cstr_is_empty: &[
        "std::ffi::CStr::is_empty",
        "core::ffi::CStr::is_empty"
    ],
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}

/// Find any drop fn. Any of these drop fns can be missing, e.g. for crates like no_std without
/// using alloc, dealloc doesn't exist.
pub fn is_drop_fn(target: DefId) -> bool {
    let drop_fn = [
        drop(),
        drop_in_place(),
        manually_drop(),
        dealloc(),
    ];
    contains(&drop_fn, target)
}

/// Is the targe DefId in the given array.
pub fn contains(v: &[Option<DefId>], target: DefId) -> bool {
    v.contains(&Some(target))
}
