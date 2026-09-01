//! Resolution of well-known `core`/`std`/`alloc` function paths to their
//! internal [`DefId`]s.
//!
//! This module is the single home for "which standard-library item is this
//! `DefId`?", used by [`crate::verify::api_classify`] and the alias checker to
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
//! - In `#![no_std]` builds some intrinsics are absent; [`init`] only warns
//!   (`rap_warn!`) instead of panicking, so an entry with no matching path
//!   simply yields `None`.

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::sync::OnceLock;

static INIT: OnceLock<Intrinsics> = OnceLock::new();

struct Intrinsics {
    // The key is fn path, starting from `core::` or `std::`. The value is internal def id.
    map: IndexMap<Box<str>, DefId>,
}

static TYPES: OnceLock<Types> = OnceLock::new();

/// Resolved `DefId`s of well-known std *types* (ADTs), used by the ADT
/// type-name classifiers ([`crate::verify::api_classify::is_std_box`],
/// [`crate::verify::api_classify::is_std_vec`], …).  Each entry collects the
/// std type's `DefId` (via lang/diagnostic item, or — for `NonNull`, which has
/// neither — by name-scanning the std crates' `adts()`) *and* any same-named
/// re-implementations in the local crate (the std-challenge suites re-implement
/// `Vec`/`NonNull` under the same names).
struct Types {
    box_types: Vec<DefId>,
    cstring_types: Vec<DefId>,
    vec_types: Vec<DefId>,
    nonnull_types: Vec<DefId>,
    maybe_uninit_types: Vec<DefId>,
    ordering_types: Vec<DefId>,
    iter_types: Vec<DefId>,
}

pub fn init(tcx: TyCtxt) {
    INIT.get_or_init(|| init_inner(tcx));
    TYPES.get_or_init(|| init_types(tcx));
    METHODS.get_or_init(|| init_methods(tcx));
}

fn init_types(tcx: TyCtxt) -> Types {
    let mut types = Types {
        box_types: Vec::new(),
        cstring_types: Vec::new(),
        vec_types: Vec::new(),
        nonnull_types: Vec::new(),
        maybe_uninit_types: Vec::new(),
        ordering_types: Vec::new(),
        iter_types: Vec::new(),
    };

    // Real std types via diagnostic/lang items (`NonNull` only before rustc
    // 1.100, when it was still a diagnostic item).
    types.box_types.extend(tcx.lang_items().owned_box());
    types
        .cstring_types
        .extend(tcx.get_diagnostic_item(sym::cstring_type));
    types.vec_types.extend(tcx.get_diagnostic_item(sym::Vec));
    // `core::cmp::Ordering` is `#[lang = "Ordering"]`.
    types
        .ordering_types
        .extend(tcx.lang_items().ordering_enum());
    // `core::mem::MaybeUninit` is `#[lang = "maybe_uninit"]`.
    types
        .maybe_uninit_types
        .extend(tcx.lang_items().maybe_uninit());

    // `core::slice::Iter` is `#[rustc_diagnostic_item = "SliceIter"]` on older
    // toolchains (the item was dropped once `adts()` became available, so only
    // referenced when `adts()` is absent). `slice::IterMut` has no diagnostic
    // item, so resolve it from the self type of its `fn_defs()`-emitted methods.
    #[cfg(not(rapx_has_public_adts))]
    {
        types
            .iter_types
            .extend(tcx.get_diagnostic_item(sym::SliceIter));
        types
            .nonnull_types
            .extend(tcx.get_diagnostic_item(sym::NonNull));

        for krate in rustc_public::external_crates()
            .into_iter()
            .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
        {
            for fn_def in krate.fn_defs() {
                let name = fn_def.name();
                if !name.contains("::IterMut::") {
                    continue;
                }
                let did = rustc_internal::internal(tcx, fn_def.def_id());
                if let Some(adt_did) = assoc_self_adt_did(tcx, did) {
                    types.iter_types.push(adt_did);
                }
            }
        }
    }

    // Same-named re-implementations in the local crate (the std-challenge
    // suites re-implement `NonNull`/`Iter`/`IterMut`). Scan local ADTs by name
    // via `iter_local_def_id`, which works on every toolchain.
    for local_did in tcx.iter_local_def_id() {
        let did = local_did.to_def_id();
        if !matches!(
            tcx.def_kind(did),
            rustc_hir::def::DefKind::Struct
                | rustc_hir::def::DefKind::Enum
                | rustc_hir::def::DefKind::Union
        ) {
            continue;
        }
        let name = tcx.def_path_str(did);
        if name.ends_with("::Iter")
            || name == "Iter"
            || name.ends_with("::IterMut")
            || name == "IterMut"
        {
            types.iter_types.push(did);
        }
        if name.ends_with("::NonNull") || name == "NonNull" {
            types.nonnull_types.push(did);
        }
        if name.ends_with("::MaybeUninit") || name == "MaybeUninit" {
            types.maybe_uninit_types.push(did);
        }
    }

    // External std ADTs with neither a lang nor a diagnostic item: `NonNull`
    // on newer toolchains (it became `#[lang = "non_null"]`, which has no
    // `LangItem` variant) and `slice::Iter`/`IterMut` (no diagnostic item).
    // Resolve by name-scanning the std crates' `adts()`.
    #[cfg(rapx_has_public_adts)]
    {
        for krate in rustc_public::external_crates()
            .into_iter()
            .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
        {
            for adt in krate.adts() {
                let name = adt.name();
                if name.ends_with("::NonNull") {
                    types
                        .nonnull_types
                        .push(rustc_internal::internal(tcx, adt.def_id()));
                }
                if name.ends_with("::MaybeUninit") {
                    types
                        .maybe_uninit_types
                        .push(rustc_internal::internal(tcx, adt.def_id()));
                }
                if name.ends_with("::Iter") || name.ends_with("::IterMut") {
                    types
                        .iter_types
                        .push(rustc_internal::internal(tcx, adt.def_id()));
                }
            }
        }
    }

    types
}

/// `alloc::boxed::Box` (and any local `Box` re-implementation).
pub fn box_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .box_types
}

/// `alloc::ffi::CString` (and any local `CString` re-implementation).
pub fn cstring_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .cstring_types
}

/// `alloc::vec::Vec` (and any local `Vec` re-implementation).
pub fn vec_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .vec_types
}

/// `core::ptr::NonNull` (and any local `NonNull` re-implementation).
pub fn nonnull_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .nonnull_types
}

/// `core::mem::MaybeUninit` (and any local re-implementation).
pub fn maybe_uninit_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .maybe_uninit_types
}

/// `core::cmp::Ordering`.
pub fn ordering_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .ordering_types
}

/// `core::slice::Iter` / `core::slice::IterMut` (the two-field `ptr`/`end`
/// slice iterators, plus any local re-implementation).
pub fn iter_types() -> &'static [DefId] {
    &TYPES
        .get()
        .expect("Type DefIds haven't been initialized.")
        .iter_types
}

/// Resolved `DefId`s of std *methods* that are matched by *generic name* rather
/// than a fixed `intrinsics!` path (e.g. `len`, `capacity`, `::abs`,
/// `::checked_add`, `::split_at`, `Iterator::position`, …). Each group collects
/// every `fn_def` — from the std crates *and* the local crate (the
/// std-challenge suites re-implement `Vec`/slice-like types and their methods) —
/// whose name matches the group's pattern. Callers match a call-site `DefId`
/// against these sets via [`contains`].
static METHODS: OnceLock<Methods> = OnceLock::new();

struct Methods {
    len_fns: Vec<DefId>,
    capacity_fns: Vec<DefId>,
    from_raw_parts_fns: Vec<DefId>,
    from_raw_parts_mut_fns: Vec<DefId>,
    with_capacity_fns: Vec<DefId>,
    vec_ownership_transfer_fns: Vec<DefId>,
    min_like: Vec<DefId>,
    max: Vec<DefId>,
    clamp: Vec<DefId>,
    abs: Vec<DefId>,
    neg: Vec<DefId>,
    sat_unchecked_add: Vec<DefId>,
    sat_unchecked_mul: Vec<DefId>,
    checked_add: Vec<DefId>,
    checked_mul: Vec<DefId>,
    overflowing_nz: Vec<DefId>,
    bit_preserving_nz: Vec<DefId>,
    checked_nonzero_iff: Vec<DefId>,
    checked_next_pow2: Vec<DefId>,
    layout_align: Vec<DefId>,
    split_at: Vec<DefId>,
    align_to_local: Vec<DefId>,
    iter_position: Vec<DefId>,
    strlen: Vec<DefId>,
    slice_get_unchecked: Vec<DefId>,
    sliceindex_get_unchecked: Vec<DefId>,
}

fn init_methods(tcx: TyCtxt) -> Methods {
    let mut methods = Methods {
        len_fns: Vec::new(),
        capacity_fns: Vec::new(),
        from_raw_parts_fns: Vec::new(),
        from_raw_parts_mut_fns: Vec::new(),
        with_capacity_fns: Vec::new(),
        vec_ownership_transfer_fns: Vec::new(),
        min_like: Vec::new(),
        max: Vec::new(),
        clamp: Vec::new(),
        abs: Vec::new(),
        neg: Vec::new(),
        sat_unchecked_add: Vec::new(),
        sat_unchecked_mul: Vec::new(),
        checked_add: Vec::new(),
        checked_mul: Vec::new(),
        overflowing_nz: Vec::new(),
        bit_preserving_nz: Vec::new(),
        checked_nonzero_iff: Vec::new(),
        checked_next_pow2: Vec::new(),
        layout_align: Vec::new(),
        split_at: Vec::new(),
        align_to_local: Vec::new(),
        iter_position: Vec::new(),
        strlen: Vec::new(),
        slice_get_unchecked: Vec::new(),
        sliceindex_get_unchecked: Vec::new(),
    };

    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| k.is_local || ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for fn_def in krate.fn_defs() {
            let name = fn_def.name();
            let did = rustc_internal::internal(tcx, fn_def.def_id());

            if name.ends_with("::len") {
                methods.len_fns.push(did);
            }
            if name.ends_with("::capacity") {
                methods.capacity_fns.push(did);
            }
            if name.ends_with("::from_raw_parts") || name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_fns.push(did);
            }
            if name.ends_with("::from_raw_parts_mut") {
                methods.from_raw_parts_mut_fns.push(did);
            }
            if name.ends_with("::with_capacity") && name.contains("::Vec::") {
                methods.with_capacity_fns.push(did);
            }
            if (name.ends_with("::from_raw_parts") || name.ends_with("::from_parts"))
                && (name.contains("Vec") || name.contains("vec::"))
            {
                methods.vec_ownership_transfer_fns.push(did);
            }

            if ((name.contains("::cmp::min") || name.contains("::Ord::min"))
                && !name.contains("min_by"))
                || name.ends_with("::midpoint")
                // Recent nightly lowered `Ord::min`/`Ord::max` for integers to the
                // `integer_min`/`integer_max` intrinsics (instead of an inline
                // `if self <= other` branch), so match those here to keep the
                // `ReturnMin`/`ReturnMax` (ite) modelling working.
                || name.ends_with("::integer_min")
            {
                methods.min_like.push(did);
            }
            if (name.contains("::cmp::max") || name.contains("::Ord::max"))
                && !name.contains("max_by")
                || name.ends_with("::integer_max")
            {
                methods.max.push(did);
            }
            if name.ends_with("::clamp") {
                methods.clamp.push(did);
            }
            if name.ends_with("::abs")
                || name.ends_with("::saturating_abs")
                || name.ends_with("::wrapping_abs")
                || name.ends_with("::unsigned_abs")
            {
                methods.abs.push(did);
            }
            if name.ends_with("::neg")
                || name.ends_with("::wrapping_neg")
                || name.ends_with("::saturating_neg")
            {
                methods.neg.push(did);
            }
            if name.ends_with("::saturating_add") || name.ends_with("::unchecked_add") {
                methods.sat_unchecked_add.push(did);
            }
            if name.ends_with("::saturating_mul") || name.ends_with("::unchecked_mul") {
                methods.sat_unchecked_mul.push(did);
            }
            if name.ends_with("::checked_add") {
                methods.checked_add.push(did);
            }
            if name.ends_with("::checked_mul") {
                methods.checked_mul.push(did);
            }
            if name.ends_with("::overflowing_abs") || name.ends_with("::overflowing_neg") {
                methods.overflowing_nz.push(did);
            }
            if name.contains("::rotate_left")
                || name.contains("::rotate_right")
                || name.contains("::swap_bytes")
                || name.contains("::reverse_bits")
                || name.contains("::from_be")
                || name.contains("::from_le")
                || name.contains("::to_be")
                || name.contains("::to_le")
                || name.contains("::count_ones")
                || name.contains("::isqrt")
                || name.contains("::saturating_pow")
            {
                methods.bit_preserving_nz.push(did);
            }
            if name.ends_with("::checked_pow")
                || name.ends_with("::checked_abs")
                || name.ends_with("::checked_neg")
            {
                methods.checked_nonzero_iff.push(did);
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
            if name.ends_with("align_to_ext") || name.ends_with("align_to_mut_ext") {
                methods.align_to_local.push(did);
            }
            if name.contains("Iterator::position")
                || name.contains("Iterator::find")
                || name.contains("Iterator::rposition")
            {
                methods.iter_position.push(did);
            }
            if name == "strlen" || name.ends_with("::strlen") {
                methods.strlen.push(did);
            }
            if (name.contains("::get_unchecked") || name.contains("::get_unchecked_mut"))
                && (name.contains("::<impl [T]>::get_unchecked")
                    || name.contains("::mut_ptr::get_unchecked")
                    || name.contains("::const_ptr::get_unchecked"))
            {
                methods.slice_get_unchecked.push(did);
            }
            if (name.contains("::get_unchecked") || name.contains("::get_unchecked_mut"))
                && name.contains("::SliceIndex")
            {
                methods.sliceindex_get_unchecked.push(did);
            }
        }
    }

    methods
}

/// `len` query methods (`slice::len`, `str::len`, `Vec::len`, `String::len`,
/// pointer-slice `len`, and any local re-implementation).
pub fn len_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .len_fns
}

/// `capacity` query methods (`Vec::capacity` and local re-implementations).
pub fn capacity_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .capacity_fns
}

/// `from_raw_parts` constructors (`slice`/`str`/`ptr`/`NonNull`/`Vec`/`String`
/// and local re-implementations).
pub fn from_raw_parts_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .from_raw_parts_fns
}

/// `from_raw_parts_mut` constructors (`slice`/`ptr`/`NonNull` and local
/// re-implementations).
pub fn from_raw_parts_mut_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .from_raw_parts_mut_fns
}

/// `Vec::with_capacity` (and local re-implementations).
pub fn with_capacity_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .with_capacity_fns
}

/// `Vec::from_raw_parts` / `Vec::from_parts` (ownership transfer into a `Vec`).
pub fn vec_ownership_transfer_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .vec_ownership_transfer_fns
}

/// The ADT `DefId` that `def_id`'s associated function belongs to (the impl's
/// `self` type), used to resolve an ADT that has no lang/diagnostic item from
/// one of its emitted methods (e.g. `slice::IterMut`).
#[cfg(not(rapx_has_public_adts))]
fn assoc_self_adt_did(tcx: TyCtxt, def_id: DefId) -> Option<DefId> {
    let ty = crate::helpers::name::get_struct_self_ty(tcx, def_id)?;
    match ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt, _) => Some(adt.did()),
        _ => None,
    }
}

pub fn min_like_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .min_like
}
pub fn max_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .max
}
pub fn clamp_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .clamp
}
pub fn abs_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .abs
}
pub fn neg_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .neg
}
pub fn sat_unchecked_add_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .sat_unchecked_add
}
pub fn sat_unchecked_mul_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .sat_unchecked_mul
}
pub fn checked_add_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .checked_add
}
pub fn checked_mul_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .checked_mul
}
pub fn overflowing_nz_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .overflowing_nz
}
pub fn bit_preserving_nz_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .bit_preserving_nz
}
pub fn checked_nonzero_iff_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .checked_nonzero_iff
}
pub fn checked_next_pow2_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .checked_next_pow2
}
pub fn layout_align_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .layout_align
}
pub fn split_at_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .split_at
}
pub fn align_to_local_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .align_to_local
}
pub fn iter_position_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .iter_position
}
pub fn strlen_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .strlen
}
pub fn slice_get_unchecked_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .slice_get_unchecked
}
pub fn sliceindex_get_unchecked_fns() -> &'static [DefId] {
    &METHODS
        .get()
        .expect("Method DefIds haven't been initialized.")
        .sliceindex_get_unchecked
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
        let Some(&idx) = path_to_idx.get(name) else {
            return;
        };
        assert_eq!(
            indices.insert(idx, true),
            Some(false),
            "DefId for {name} has been found: {:?}",
            map.get(INTRINSICS[idx][0])
        );
        // Store under the canonical (first) registered path so the `{id}()`
        // accessors — which probe the registered paths — find it regardless of
        // whether `name` carried a crate prefix.
        map.insert(
            Box::from(INTRINSICS[idx][0]),
            rustc_internal::internal(tcx, def_id),
        );
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
    // ── Core intrinsics ──
    intrinsics_copy: &[
        "std::intrinsics::copy",
        "core::intrinsics::copy"
    ],
    intrinsics_copy_nonoverlapping: &[
        "std::intrinsics::copy_nonoverlapping",
        "core::intrinsics::copy_nonoverlapping"
    ],
    intrinsics_size_of: &[
        "std::intrinsics::size_of",
        "core::intrinsics::size_of"
    ],
    intrinsics_align_of: &[
        "std::intrinsics::align_of",
        "core::intrinsics::align_of"
    ],
    select_unpredictable: &[
        "std::intrinsics::select_unpredictable",
        "core::intrinsics::select_unpredictable"
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
        "core::ptr::NonNull::<T>::align_offset"
    ],
    nonnull_as_ref: &[
        "std::ptr::NonNull::<T>::as_ref",
        "core::ptr::NonNull::<T>::as_ref"
    ],
    nonnull_as_mut: &[
        "std::ptr::NonNull::<T>::as_mut",
        "core::ptr::NonNull::<T>::as_mut"
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
    let drop_fn = [drop(), drop_in_place(), manually_drop(), dealloc()];
    contains(&drop_fn, target)
}

/// Is the targe DefId in the given array.
pub fn contains(v: &[Option<DefId>], target: DefId) -> bool {
    v.contains(&Some(target))
}
