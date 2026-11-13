//! DefIds of standard-library types used by type and layout classifiers.

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::sync::OnceLock;

static TYPES: OnceLock<Types> = OnceLock::new();

/// Resolved `DefId`s of well-known std *types* (ADTs), used by the ADT
/// type-name classifiers ([`crate::verify::api_classify::is_std_box`],
/// [`crate::verify::api_classify::is_std_vec`], …).
struct Types {
    box_types: Vec<DefId>,
    cstring_types: Vec<DefId>,
    string_types: Vec<DefId>,
    vec_types: Vec<DefId>,
    nonnull_types: Vec<DefId>,
    maybe_uninit_types: Vec<DefId>,
    ascii_char_types: Vec<DefId>,
    ordering_types: Vec<DefId>,
    iter_types: Vec<DefId>,
    rc_types: Vec<DefId>,
    sync_primitive_types: Vec<DefId>,
    index_range_types: Vec<DefId>,
    /// Negative auto-trait types (`Cell`/`UnsafeCell`/`RefCell`/`Ref`/`RefMut`/
    /// guards), keyed by short name — used by `ContainNoType` in Send/Sync obligations.
    negative_types: IndexMap<Box<str>, Vec<DefId>>,
}

pub fn init(tcx: TyCtxt) {
    TYPES.get_or_init(|| init_types(tcx));
}

fn init_types(tcx: TyCtxt) -> Types {
    let mut types = Types {
        box_types: Vec::new(),
        cstring_types: Vec::new(),
        string_types: Vec::new(),
        vec_types: Vec::new(),
        nonnull_types: Vec::new(),
        maybe_uninit_types: Vec::new(),
        ascii_char_types: Vec::new(),
        ordering_types: Vec::new(),
        iter_types: Vec::new(),
        rc_types: Vec::new(),
        sync_primitive_types: Vec::new(),
        index_range_types: Vec::new(),
        negative_types: IndexMap::new(),
    };

    // Real std types via diagnostic/lang items (`NonNull` only before rustc
    // 1.100, when it was still a diagnostic item).
    types.box_types.extend(tcx.lang_items().owned_box());
    types
        .cstring_types
        .extend(tcx.get_diagnostic_item(sym::cstring_type));
    types.vec_types.extend(tcx.get_diagnostic_item(sym::Vec));
    types.rc_types.extend(tcx.get_diagnostic_item(sym::Rc));
    // `core::cmp::Ordering` is `#[lang = "Ordering"]`.
    types
        .ordering_types
        .extend(tcx.lang_items().ordering_enum());
    // `core::mem::MaybeUninit` is `#[lang = "maybe_uninit"]`.
    types
        .maybe_uninit_types
        .extend(tcx.lang_items().maybe_uninit());
    // `core::cell::UnsafeCell` is `#[lang = "unsafe_cell"]`.
    if let Some(unsafe_cell) = tcx.lang_items().unsafe_cell_type() {
        types
            .negative_types
            .entry("UnsafeCell".into())
            .or_default()
            .push(unsafe_cell);
    }

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

    }

    // Standard-library ADTs with neither a lang nor a diagnostic item: `NonNull`
    // on newer toolchains (it became `#[lang = "non_null"]`, which has no
    // `LangItem` variant) and `slice::Iter`/`IterMut` (no diagnostic item).
    // Resolve by name-scanning the std crates' `adts()`.
    #[cfg(rapx_has_public_adts)]
    {
        for krate in std::iter::once(rustc_public::local_crate())
            .chain(rustc_public::external_crates())
            .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
        {
            for adt in krate.adts() {
                let did = rustc_internal::internal(tcx, adt.def_id());
                let path = type_path(tcx, did, &krate.name, krate.is_local);
                collect_type_by_path(&mut types, &path, did);
            }
        }
    }

    #[cfg(not(rapx_has_public_adts))]
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for fn_def in krate.fn_defs() {
            let did = rustc_internal::internal(tcx, fn_def.def_id());
            if let Some(adt_did) = assoc_self_adt_did(tcx, did) {
                let path = type_path(tcx, adt_did, &krate.name, krate.is_local);
                collect_type_by_path(&mut types, &path, adt_did);
            }
        }
    }

    types
}

fn type_path(tcx: TyCtxt<'_>, did: DefId, crate_name: &str, is_local: bool) -> String {
    let path = tcx.def_path_str(did);
    if is_local && !path.starts_with(&format!("{crate_name}::")) {
        format!("{crate_name}::{path}")
    } else {
        path
    }
}

fn collect_type_by_path(types: &mut Types, name: &str, did: DefId) {
    let Some(group) = classify_type_path(name) else {
        return;
    };
    let ids = match group {
        TypeGroup::Vec => &mut types.vec_types,
        TypeGroup::String => &mut types.string_types,
        TypeGroup::Iter => &mut types.iter_types,
        TypeGroup::NonNull => &mut types.nonnull_types,
        TypeGroup::MaybeUninit => &mut types.maybe_uninit_types,
        TypeGroup::IndexRange => &mut types.index_range_types,
        TypeGroup::AsciiChar => &mut types.ascii_char_types,
        TypeGroup::Rc => &mut types.rc_types,
        TypeGroup::SyncPrimitive => &mut types.sync_primitive_types,
        TypeGroup::Negative(name) => types.negative_types.entry(name.into()).or_default(),
    };
    if !ids.contains(&did) {
        ids.push(did);
    }
}

#[derive(Debug, PartialEq, Eq)]
enum TypeGroup {
    Vec,
    String,
    Iter,
    NonNull,
    MaybeUninit,
    IndexRange,
    AsciiChar,
    Rc,
    SyncPrimitive,
    Negative(&'static str),
}

fn classify_type_path(name: &str) -> Option<TypeGroup> {
    Some(match name {
        "alloc::vec::Vec" | "std::vec::Vec" => TypeGroup::Vec,
        "alloc::string::String" | "std::string::String" => TypeGroup::String,
        "core::slice::iter::Iter"
        | "core::slice::iter::IterMut"
        | "std::slice::Iter"
        | "std::slice::IterMut" => TypeGroup::Iter,
        "core::ptr::non_null::NonNull" | "std::ptr::NonNull" => TypeGroup::NonNull,
        "core::mem::maybe_uninit::MaybeUninit" | "std::mem::MaybeUninit" => TypeGroup::MaybeUninit,
        "core::ops::index_range::IndexRange"
        | "std::ops::index_range::IndexRange"
        | "std::ops::IndexRange" => TypeGroup::IndexRange,
        "core::ascii::ascii_char::AsciiChar" | "std::ascii::AsciiChar" => TypeGroup::AsciiChar,
        "alloc::rc::Rc" | "alloc::rcs::rc::Rc" | "std::rc::Rc" => TypeGroup::Rc,
        "core::cell::Cell" | "std::cell::Cell" => TypeGroup::Negative("Cell"),
        "core::cell::RefCell" | "std::cell::RefCell" => TypeGroup::Negative("RefCell"),
        "core::cell::Ref" | "std::cell::Ref" => TypeGroup::Negative("Ref"),
        "core::cell::RefMut" | "std::cell::RefMut" => TypeGroup::Negative("RefMut"),
        "std::sync::poison::mutex::Mutex"
        | "std::sync::nonpoison::mutex::Mutex"
        | "std::sync::poison::rwlock::RwLock"
        | "std::sync::nonpoison::rwlock::RwLock"
        | "std::sync::once_lock::OnceLock"
        | "std::sync::Mutex"
        | "std::sync::RwLock"
        | "std::sync::OnceLock" => TypeGroup::SyncPrimitive,
        "std::sync::poison::mutex::MutexGuard"
        | "std::sync::nonpoison::mutex::MutexGuard"
        | "std::sync::MutexGuard" => TypeGroup::Negative("MutexGuard"),
        "std::sync::poison::mutex::MappedMutexGuard"
        | "std::sync::nonpoison::mutex::MappedMutexGuard"
        | "std::sync::MappedMutexGuard" => TypeGroup::Negative("MappedMutexGuard"),
        "std::sync::poison::rwlock::RwLockWriteGuard"
        | "std::sync::nonpoison::rwlock::RwLockWriteGuard"
        | "std::sync::RwLockWriteGuard" => TypeGroup::Negative("RwLockWriteGuard"),
        _ if (name.starts_with("core::sync::atomic::")
            || name.starts_with("std::sync::atomic::"))
            && name.rsplit("::").next().is_some_and(|short| {
                matches!(
                    short,
                    "AtomicBool"
                        | "AtomicPtr"
                        | "AtomicI8"
                        | "AtomicI16"
                        | "AtomicI32"
                        | "AtomicI64"
                        | "AtomicI128"
                        | "AtomicIsize"
                        | "AtomicU8"
                        | "AtomicU16"
                        | "AtomicU32"
                        | "AtomicU64"
                        | "AtomicU128"
                        | "AtomicUsize"
                )
            }) =>
        {
            TypeGroup::SyncPrimitive
        }
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::{TypeGroup, classify_type_path};

    #[test]
    fn only_canonical_std_types_match() {
        assert_eq!(
            classify_type_path("core::slice::iter::Iter"),
            Some(TypeGroup::Iter)
        );
        assert_eq!(
            classify_type_path("std::slice::Iter"),
            Some(TypeGroup::Iter)
        );
        assert_eq!(
            classify_type_path("core::ptr::non_null::NonNull"),
            Some(TypeGroup::NonNull)
        );
        assert_eq!(
            classify_type_path("std::ptr::NonNull"),
            Some(TypeGroup::NonNull)
        );
        assert_eq!(classify_type_path("alloc::vec::Vec"), Some(TypeGroup::Vec));
        assert_eq!(classify_type_path("std::vec::Vec"), Some(TypeGroup::Vec));
        assert_eq!(classify_type_path("local::Vec"), None);
        assert_eq!(classify_type_path("local::NonNull"), None);
        assert_eq!(
            classify_type_path("alloc::collections::linked_list::Iter"),
            None
        );
        assert_eq!(
            classify_type_path("std::collections::hash::map::Iter"),
            None
        );
        assert_eq!(classify_type_path("core::ascii::Char"), None);
        assert_eq!(classify_type_path("local::AtomicCounter"), None);
    }
}

macro_rules! type_defs {
    ($( $(#[$attr:meta])* $name:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name() -> &'static [DefId] {
                &TYPES
                    .get()
                    .expect("Type DefIds haven't been initialized.")
                    .$name
            }
        )+
    };
}

type_defs! {
    /// `alloc::boxed::Box`.
    box_types,
    /// `alloc::ffi::CString`.
    cstring_types,
    /// `alloc::vec::Vec`.
    vec_types,
    /// `alloc::string::String`.
    string_types,
    /// `core::ptr::NonNull`.
    nonnull_types,
    /// `core::mem::MaybeUninit`.
    maybe_uninit_types,
    /// `core::ascii::ascii_char::AsciiChar`.
    ascii_char_types,
    /// `core::cmp::Ordering`.
    ordering_types,
    /// `core::slice::Iter` / `core::slice::IterMut` (the two-field `ptr`/`end`
    /// slice iterators).
    iter_types,
    /// `alloc::rc::Rc`.
    rc_types,
    /// Standard-library `Mutex`, `RwLock`, `OnceLock`, and atomic types.
    sync_primitive_types,
    /// `core::ops::index_range::IndexRange`.
    index_range_types,
}

/// Resolve a negative-type name (as written in `std-trait.json`) to its
/// resolved `DefId` set.  Unknown names resolve to an empty set (the checker
/// then reports `Unknown`).
pub fn negative_type_defs(name: &str) -> &'static [DefId] {
    match name {
        "Rc" => rc_types(),
        "NonNull" => nonnull_types(),
        _ => TYPES
            .get()
            .and_then(|t| t.negative_types.get(name))
            .map(Vec::as_slice)
            .unwrap_or(&[]),
    }
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
