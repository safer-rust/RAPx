//! Known `core`/`std`/`alloc` API identities, regardless of MIR availability.
//!
//! The path table resolves well-known items to [`DefId`]s. Classifiers in
//! [`crate::verify::api_classify`] combine those identities into operations.
//! The table owns global state initialized by the compiler callback.
//!
//! # How a lookup works
//!
//! 1. The [`known_items!`] macro declares a *path table*: each identifier maps
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
//! - In `#![no_std]` builds some standard-library items are absent; [`init`] only warns
//!   (`rap_warn!`) instead of panicking, so an entry with no matching path
//!   simply yields `None`.

use super::lang_api::{self, LangItem};
use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use std::sync::OnceLock;

use super::type_ids;

static INIT: OnceLock<KnownItems> = OnceLock::new();

struct KnownItems {
    // The key is fn path, starting from `core::` or `std::`. The value is internal def id.
    map: IndexMap<Box<str>, DefId>,
}

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
    METHODS.get_or_init(|| init_methods(tcx));
}

pub fn is_len(callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| len_fns().contains(&id))
}

pub fn is_slice_get(callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| slice_get_fns().contains(&id))
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

/// Resolved `DefId`s of std *methods* that are matched by *generic name* rather
/// than a fixed `known_items!` path (e.g. `len`, `capacity`, `::abs`,
/// `::checked_add`, `::split_at`, `Iterator::position`, …). Each group collects
/// matching `fn_def`s from `core`, `std`, and `alloc`. Callers match a call-site
/// `DefId` against these sets via [`contains`].
static METHODS: OnceLock<Methods> = OnceLock::new();

struct Methods {
    len_fns: Vec<DefId>,
    from_raw_parts_fns: Vec<DefId>,
    from_raw_parts_mut_fns: Vec<DefId>,
    with_metadata_of_fns: Vec<DefId>,
    integer_wrapping_sub_fns: Vec<DefId>,
    vec_ownership_transfer_fns: Vec<DefId>,
    checked_next_pow2: Vec<DefId>,
    layout_align: Vec<DefId>,
    split_at: Vec<DefId>,
    iter_position: Vec<DefId>,
    slice_get_unchecked: Vec<DefId>,
    slice_get: Vec<DefId>,
    slice_range_fns: Vec<DefId>,
    range_next: Vec<DefId>,
    iter_next: Vec<DefId>,
    iterator_next_trait: Vec<DefId>,
    iter_len: Vec<DefId>,
    iter_is_empty: Vec<DefId>,
    as_ptr_like: Vec<DefId>,
    ptr_add: Vec<DefId>,
    branch: Vec<DefId>,
    gcd: Vec<DefId>,
    known_nonnull: Vec<DefId>,
    null_ptr: Vec<DefId>,
    index_fns: Vec<DefId>,
    exchange_malloc: Option<DefId>,
}

pub fn exchange_malloc() -> Option<DefId> {
    METHODS
        .get()
        .expect("Method IDs have not been initialized")
        .exchange_malloc
}

fn init_methods(tcx: TyCtxt) -> Methods {
    let mut methods = Methods {
        len_fns: Vec::new(),
        from_raw_parts_fns: Vec::new(),
        from_raw_parts_mut_fns: Vec::new(),
        with_metadata_of_fns: Vec::new(),
        integer_wrapping_sub_fns: Vec::new(),
        vec_ownership_transfer_fns: Vec::new(),
        checked_next_pow2: Vec::new(),
        layout_align: Vec::new(),
        split_at: Vec::new(),
        iter_position: Vec::new(),
        slice_get_unchecked: Vec::new(),
        slice_get: Vec::new(),
        slice_range_fns: Vec::new(),
        range_next: Vec::new(),
        iter_next: Vec::new(),
        iterator_next_trait: Vec::new(),
        iter_len: Vec::new(),
        iter_is_empty: Vec::new(),
        as_ptr_like: Vec::new(),
        ptr_add: Vec::new(),
        branch: Vec::new(),
        gcd: Vec::new(),
        known_nonnull: Vec::new(),
        null_ptr: Vec::new(),
        index_fns: Vec::new(),
        exchange_malloc: None,
    };

    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for fn_def in krate.fn_defs() {
            let name = fn_def.name();
            let did = rustc_internal::internal(tcx, fn_def.def_id());
            if tcx.opt_associated_item(did).is_some_and(|item| {
                item.name() == rustc_span::sym::next
                    && item.trait_container(tcx).is_some_and(|trait_id| {
                        tcx.is_diagnostic_item(rustc_span::Symbol::intern("Iterator"), trait_id)
                    })
            }) {
                methods.iterator_next_trait.push(did);
            }
            if name.contains("exchange_malloc") {
                methods.exchange_malloc.get_or_insert(did);
            }

            // `Index::index` / `IndexMut::index_mut` (the `a[b]` indexing
            // sugar): matched by lang-item trait container, not by def_path.
            if let Some(assoc) = tcx.opt_associated_item(did)
                && let Some(trait_id) = assoc.trait_container(tcx)
                && (lang_api::matches(tcx, trait_id, LangItem::Index)
                    && assoc.name().as_str() == "index"
                    || lang_api::matches(tcx, trait_id, LangItem::IndexMut)
                        && assoc.name().as_str() == "index_mut")
            {
                methods.index_fns.push(did);
            }

            if name.ends_with("::len") {
                methods.len_fns.push(did);
            }
            if name.ends_with("::from_raw_parts") || name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_fns.push(did);
            }
            if name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_mut_fns.push(did);
            }
            if name.ends_with("::with_metadata_of") {
                methods.with_metadata_of_fns.push(did);
            }
            if name.ends_with("::wrapping_sub") && name.contains("::num::<impl ") {
                methods.integer_wrapping_sub_fns.push(did);
            }
            if (name.ends_with("::from_raw_parts") || name.ends_with("::from_parts"))
                && (name.contains("Vec") || name.contains("vec::"))
            {
                methods.vec_ownership_transfer_fns.push(did);
            }

            if name.ends_with("::checked_next_power_of_two") {
                methods.checked_next_pow2.push(did);
            }
            if name.ends_with("Layout::align") {
                methods.layout_align.push(did);
            }
            if name.contains("::split_at") {
                methods.split_at.push(did);
            }
            if name.contains("Iterator::position")
                || name.contains("Iterator::find")
                || name.contains("Iterator::rposition")
            {
                methods.iter_position.push(did);
            }
            if (name.contains("::get_unchecked") || name.contains("::get_unchecked_mut"))
                && (name.contains("::<impl [T]>::get_unchecked")
                    || name.contains("::<impl *mut [T]>::get_unchecked")
                    || name.contains("::<impl *const [T]>::get_unchecked")
                    || name.contains("::mut_ptr::get_unchecked")
                    || name.contains("::const_ptr::get_unchecked"))
            {
                methods.slice_get_unchecked.push(did);
            }
            if (name.ends_with("::get") || name.ends_with("::get_mut"))
                && (name.contains("::<impl [T]>::get")
                    || name.contains("::<impl *mut [T]>::get")
                    || name.contains("::<impl *const [T]>::get"))
            {
                methods.slice_get.push(did);
            }
            if name.ends_with("slice::index::range") || name.ends_with("::slice::range") {
                methods.slice_range_fns.push(did);
            }
            // `Range::next` / `RangeInclusive::next` and their `spec_next` impls:
            // the loop variable of `for i in 0..N` is produced by these, so the
            // VM models them to carry the `0 <= i < N` bound.
            if (name.ends_with("::next") || name.ends_with("::spec_next"))
                && (name.contains("RangeIteratorImpl")
                    || name.contains("RangeInclusiveIteratorImpl")
                    || (name.contains("Iterator for") && name.contains("Range<"))
                    || (name.contains("Iterator for") && name.contains("RangeInclusive<")))
            {
                methods.range_next.push(did);
            }
            if is_slice_iter_method(tcx, did)
                && let Some(item) = tcx.opt_associated_item(did)
            {
                match item.name().as_str() {
                    "next" => methods.iter_next.push(did),
                    "len" => methods.iter_len.push(did),
                    "is_empty" => methods.iter_is_empty.push(did),
                    _ => {}
                }
            }
            // `<Option<T> as Try>::branch` (the `?` operator on `Option`).
            // `branch` has no lang/diagnostic item; `Option` disambiguates it
            // from `<Result<T, E> as Try>::branch`.
            if name.ends_with("::branch") && name.contains("Option") {
                methods.branch.push(did);
            }
            // `gcd` const fn (const-eval integer GCD).
            if name.ends_with("::gcd") {
                methods.gcd.push(did);
            }
            if matches!(
                name.as_str(),
                "std::ptr::null"
                    | "std::ptr::null_mut"
                    | "core::ptr::null"
                    | "core::ptr::null_mut"
                    | "ptr::null"
                    | "ptr::null_mut"
            ) {
                methods.null_ptr.push(did);
            }
        }
    }

    methods.as_ptr_like = [
        slice_as_ptr(),
        slice_as_mut_ptr(),
        str_as_ptr(),
        str_as_mut_ptr(),
        vec_as_ptr(),
        vec_as_mut_ptr(),
        cstr_as_ptr(),
        nonnull_as_ptr(),
        nonnull_slice_as_mut_ptr(),
        box_as_ptr(),
        box_as_mut_ptr(),
        maybe_uninit_as_ptr(),
        maybe_uninit_as_mut_ptr(),
        arc_as_ptr(),
        rc_as_ptr(),
        const_ptr_slice_as_ptr(),
        mut_ptr_slice_as_mut_ptr(),
    ]
    .into_iter()
    .flatten()
    .collect();
    methods.ptr_add = [const_ptr_byte_add(), mut_ptr_byte_add(), nonnull_byte_add()]
        .into_iter()
        .flatten()
        .collect();
    methods.known_nonnull = [
        slice_as_ptr(),
        slice_as_mut_ptr(),
        str_as_ptr(),
        str_as_mut_ptr(),
        vec_as_ptr(),
        vec_as_mut_ptr(),
        cstr_as_ptr(),
        nonnull_as_ptr(),
        nonnull_slice_as_mut_ptr(),
        box_as_ptr(),
        box_as_mut_ptr(),
        maybe_uninit_as_ptr(),
        maybe_uninit_as_mut_ptr(),
        arc_as_ptr(),
        rc_as_ptr(),
        box_into_raw(),
        cstring_into_raw(),
        arc_into_raw(),
        rc_into_raw(),
    ]
    .into_iter()
    .flatten()
    .collect();

    methods
}

fn is_slice_iter_method(tcx: TyCtxt<'_>, did: DefId) -> bool {
    crate::helpers::name::get_struct_self_ty(tcx, did)
        .and_then(|ty| match ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt, _) => Some(adt.did()),
            _ => None,
        })
        .is_some_and(|adt| type_ids::iter_types().contains(&adt))
}

macro_rules! method_fns {
    ($( $(#[$attr:meta])* $name:ident => $field:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name() -> &'static [DefId] {
                &METHODS
                    .get()
                    .expect("Method DefIds haven't been initialized.")
                    .$field
            }
        )+
    };
}

method_fns! {
    /// `len` query methods (`slice::len`, `str::len`, `Vec::len`, `String::len`,
    /// and pointer-slice `len`).
    len_fns => len_fns,
    /// `from_raw_parts` constructors (`slice`/`str`/`ptr`/`NonNull`/`Vec`/`String`).
    from_raw_parts_fns => from_raw_parts_fns,
    /// `from_raw_parts_mut` constructors (`slice`/`ptr`/`NonNull`).
    from_raw_parts_mut_fns => from_raw_parts_mut_fns,
    /// `*const T::with_metadata_of` / `*mut T::with_metadata_of` (used by
    /// `byte_add`/`byte_offset`).
    with_metadata_of_fns => with_metadata_of_fns,
    integer_wrapping_sub_fns => integer_wrapping_sub_fns,
    /// `Vec::from_raw_parts` / `Vec::from_parts` (ownership transfer into a `Vec`).
    vec_ownership_transfer_fns => vec_ownership_transfer_fns,
}

method_fns! {
    checked_next_pow2_fns => checked_next_pow2,
    layout_align_fns => layout_align,
    split_at_fns => split_at,
    iter_position_fns => iter_position,
    slice_get_unchecked_fns => slice_get_unchecked,
    slice_get_fns => slice_get,
    slice_range_fns => slice_range_fns,
    range_next_fns => range_next,
    /// Slice `Iter::next` / `IterMut::next`.
    iter_next_fns => iter_next,
    iterator_next_trait_fns => iterator_next_trait,
    /// `Iter::len` / `IterMut::len`.
    iter_len_fns => iter_len,
    /// `Iter::is_empty` / `IterMut::is_empty`.
    iter_is_empty_fns => iter_is_empty,
    /// Pointer accessors that retain the source bytes.
    as_ptr_like_fns => as_ptr_like,
    /// Byte-strided pointer `add` methods.
    ptr_add_fns => ptr_add,
    /// `<Option<T> as Try>::branch`.
    branch_fns => branch,
    /// `gcd` const functions.
    gcd_fns => gcd,
    /// Known non-null-returning pointer methods (`into_raw` / `Box::new` /
    /// `as_ptr` / `as_mut_ptr`).
    known_nonnull_fns => known_nonnull,
    /// Null-returning pointer methods (`null` / `null_mut`).
    null_ptr_fns => null_ptr,
    /// `Index::index` / `IndexMut::index_mut` (the `a[b]` indexing sugar).
    index_fns => index_fns,
}

fn init_inner(tcx: TyCtxt) -> KnownItems {
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

    KnownItems { map }
}

macro_rules! known_items {
    ($( $(#[$attr:meta])* $id:ident : $paths:expr ,)+) => {
        const KNOWN_ITEM_PATHS: &[&[&str]] = &[$( $(#[$attr])* $paths ,)+];
        $(
            $(#[$attr])*
            pub fn $id() -> Option<DefId> {
                let map = &INIT.get().expect("Known item DefIds haven't been initialized.").map;
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
known_items! {
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
    ptr_align_offset: &[
        "std::ptr::align_offset",
        "core::ptr::align_offset"
    ],
    nonnull_align_offset: &[
        "std::ptr::NonNull::<T>::align_offset",
        "core::ptr::NonNull::<T>::align_offset",
        "std::ptr::non_null::NonNull::<T>::align_offset",
        "core::ptr::non_null::NonNull::<T>::align_offset"
    ],
    nonnull_as_ref: &[
        "std::ptr::NonNull::<T>::as_ref",
        "core::ptr::NonNull::<T>::as_ref",
        "std::ptr::non_null::NonNull::<T>::as_ref",
        "core::ptr::non_null::NonNull::<T>::as_ref"
    ],
    nonnull_as_mut: &[
        "std::ptr::NonNull::<T>::as_mut",
        "core::ptr::NonNull::<T>::as_mut",
        "std::ptr::non_null::NonNull::<T>::as_mut",
        "core::ptr::non_null::NonNull::<T>::as_mut"
    ],
    nonnull_new: &[
        "std::ptr::NonNull::<T>::new",
        "core::ptr::NonNull::<T>::new",
        "std::ptr::non_null::NonNull::<T>::new",
        "core::ptr::non_null::NonNull::<T>::new"
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
        "core::ptr::NonNull::<T>::add",
        "std::ptr::non_null::NonNull::<T>::add",
        "core::ptr::non_null::NonNull::<T>::add"
    ],
    nonnull_sub: &[
        "std::ptr::NonNull::<T>::sub",
        "core::ptr::NonNull::<T>::sub",
        "std::ptr::non_null::NonNull::<T>::sub",
        "core::ptr::non_null::NonNull::<T>::sub"
    ],
    nonnull_byte_add: &[
        "std::ptr::NonNull::<T>::byte_add",
        "core::ptr::NonNull::<T>::byte_add",
        "std::ptr::non_null::NonNull::<T>::byte_add",
        "core::ptr::non_null::NonNull::<T>::byte_add"
    ],
    nonnull_byte_sub: &[
        "std::ptr::NonNull::<T>::byte_sub",
        "core::ptr::NonNull::<T>::byte_sub",
        "std::ptr::non_null::NonNull::<T>::byte_sub",
        "core::ptr::non_null::NonNull::<T>::byte_sub"
    ],
    nonnull_offset: &[
        "std::ptr::NonNull::<T>::offset",
        "core::ptr::NonNull::<T>::offset",
        "std::ptr::non_null::NonNull::<T>::offset",
        "core::ptr::non_null::NonNull::<T>::offset"
    ],
    nonnull_byte_offset: &[
        "std::ptr::NonNull::<T>::byte_offset",
        "core::ptr::NonNull::<T>::byte_offset",
        "std::ptr::non_null::NonNull::<T>::byte_offset",
        "core::ptr::non_null::NonNull::<T>::byte_offset"
    ],
    cstr_from_ptr: &[
        "std::ffi::CStr::from_ptr",
        "core::ffi::CStr::from_ptr",
        "std::ffi::c_str::CStr::from_ptr",
        "core::ffi::c_str::CStr::from_ptr"
    ],
    cstr_from_bytes_with_nul_unchecked: &[
        "std::ffi::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::CStr::from_bytes_with_nul_unchecked",
        "std::ffi::c_str::CStr::from_bytes_with_nul_unchecked",
        "core::ffi::c_str::CStr::from_bytes_with_nul_unchecked"
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
        "alloc::ffi::CString::into_raw",
        "std::ffi::c_str::CString::into_raw",
        "alloc::ffi::c_str::CString::into_raw"
    ],
    arc_into_raw: &[
        "std::sync::Arc::<T>::into_raw",
        "alloc::sync::Arc::<T>::into_raw"
    ],
    arc_as_ptr: &[
        "std::sync::Arc::<T>::as_ptr",
        "alloc::sync::Arc::<T>::as_ptr",
        "std::sync::Arc::<T, A>::as_ptr",
        "alloc::sync::Arc::<T, A>::as_ptr"
    ],
    rc_into_raw: &[
        "std::rc::Rc::<T>::into_raw",
        "alloc::rc::Rc::<T>::into_raw"
    ],
    rc_as_ptr: &[
        "std::rc::Rc::<T>::as_ptr",
        "alloc::rc::Rc::<T>::as_ptr",
        "std::rc::Rc::<T, A>::as_ptr",
        "alloc::rc::Rc::<T, A>::as_ptr"
    ],
    vec_into_boxed_slice: &[
        "std::vec::Vec::<T, A>::into_boxed_slice",
        "alloc::vec::Vec::<T, A>::into_boxed_slice"
    ],
    slice_into_vec: &[
        "std::slice::<impl [T]>::into_vec",
        "alloc::slice::<impl [T]>::into_vec"
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
    nonnull_as_ptr: &[
        "std::ptr::NonNull::<T>::as_ptr",
        "core::ptr::NonNull::<T>::as_ptr",
        "std::ptr::non_null::NonNull::<T>::as_ptr",
        "core::ptr::non_null::NonNull::<T>::as_ptr"
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
    nonnull_slice_as_mut_ptr: &[
        "std::ptr::NonNull::<[T]>::as_mut_ptr",
        "core::ptr::NonNull::<[T]>::as_mut_ptr",
        "std::ptr::non_null::NonNull::<[T]>::as_mut_ptr",
        "core::ptr::non_null::NonNull::<[T]>::as_mut_ptr"
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
        "core::ffi::CStr::as_ptr",
        "std::ffi::c_str::CStr::as_ptr",
        "core::ffi::c_str::CStr::as_ptr"
    ],
    cstr_is_empty: &[
        "std::ffi::CStr::is_empty",
        "core::ffi::CStr::is_empty",
        "std::ffi::c_str::CStr::is_empty",
        "core::ffi::c_str::CStr::is_empty"
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
    contains(&drop_fn, target)
}

/// Whether the target `DefId` is in the given array.
pub fn contains(v: &[Option<DefId>], target: DefId) -> bool {
    v.contains(&Some(target))
}

pub(crate) fn matches_any(target: Option<DefId>, candidates: &[Option<DefId>]) -> bool {
    target.is_some_and(|id| contains(candidates, id))
}
