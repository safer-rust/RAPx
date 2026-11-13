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

pub fn is_ptr_read(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did).is_some_and(|name| {
        matches!(name.as_str(), "ptr_read" | "ptr_read_unaligned" | "ptr_read_volatile")
    })
}

pub fn is_ptr_write(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did).is_some_and(|name| {
        matches!(name.as_str(), "ptr_write" | "ptr_write_unaligned" | "ptr_write_volatile" | "ptr_write_bytes")
    })
}

pub fn is_ptr_write_to_uninit(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did)
        .is_some_and(|name| matches!(name.as_str(), "ptr_write" | "ptr_write_bytes"))
}

pub fn is_ptr_copy(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.get_diagnostic_name(did)
        .is_some_and(|name| matches!(name.as_str(), "ptr_copy" | "ptr_copy_nonoverlapping"))
}

pub fn is_drop(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.is_diagnostic_item(rustc_span::Symbol::intern("mem_drop"), did)
}

pub fn is_drop_in_place(tcx: TyCtxt<'_>, did: DefId) -> bool {
    tcx.is_diagnostic_item(rustc_span::Symbol::intern("ptr_drop_in_place"), did)
}

pub fn is_manually_drop(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity();
    #[cfg(rapx_ge_99)]
    let self_ty = self_ty.skip_norm_wip();
    matches!(self_ty.kind(), rustc_middle::ty::TyKind::Adt(adt, _)
        if tcx.is_lang_item(adt.did(), crate::def_ids::lang_api::LangItem::ManuallyDrop))
        && tcx.item_name(did).as_str() == "drop"
}

pub fn is_assume_init_read(tcx: TyCtxt<'_>, did: DefId) -> bool {
    let Some(impl_id) = tcx.inherent_impl_of_assoc(did) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).instantiate_identity();
    #[cfg(rapx_ge_99)]
    let self_ty = self_ty.skip_norm_wip();
    matches!(self_ty.kind(), rustc_middle::ty::TyKind::Adt(adt, _)
        if tcx.is_lang_item(adt.did(), crate::def_ids::lang_api::LangItem::MaybeUninit))
        && tcx.item_name(did).as_str() == "assume_init_read"
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
}

/// rustc_public DefId to internal DefId
pub fn to_internal<T: CrateDef>(val: &T, tcx: TyCtxt) -> DefId {
    rustc_internal::internal(tcx, val.def_id())
}

/// Find a call that explicitly drops a value.
pub fn is_drop_fn(tcx: TyCtxt<'_>, target: DefId) -> bool {
    is_drop(tcx, target)
        || is_drop_in_place(tcx, target)
        || is_manually_drop(tcx, target)
}

pub(crate) fn matches_any(target: Option<DefId>, candidates: &[Option<DefId>]) -> bool {
    target.is_some_and(|id| candidates.contains(&Some(id)))
}
