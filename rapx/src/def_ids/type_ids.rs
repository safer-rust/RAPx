//! Resolved `DefId`s of standard-library types used by verification.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::collections::HashMap;
use std::sync::OnceLock;

static TYPES: OnceLock<HashMap<DefId, TypeGroup>> = OnceLock::new();

pub fn init(tcx: TyCtxt) {
    TYPES.get_or_init(|| init_types(tcx));
}

fn init_types(tcx: TyCtxt) -> HashMap<DefId, TypeGroup> {
    let mut types = HashMap::new();

    // Lang items.
    if let Some(did) = tcx.lang_items().owned_box() {
        types.insert(did, TypeGroup::Box);
    }
    if let Some(did) = tcx.lang_items().ordering_enum() {
        types.insert(did, TypeGroup::Ordering);
    }
    if let Some(did) = tcx.lang_items().maybe_uninit() {
        types.insert(did, TypeGroup::MaybeUninit);
    }
    if let Some(unsafe_cell) = tcx.lang_items().unsafe_cell_type() {
        types.insert(unsafe_cell, TypeGroup::Negative("UnsafeCell"));
    }

    // Diagnostic items.
    if let Some(did) = tcx.get_diagnostic_item(sym::cstring_type) {
        types.insert(did, TypeGroup::CString);
    }
    if let Some(did) = tcx.get_diagnostic_item(sym::Vec) {
        types.insert(did, TypeGroup::Vec);
    }
    if let Some(did) = tcx.get_diagnostic_item(sym::Rc) {
        types.insert(did, TypeGroup::Rc);
    }

    // Resolve types without lang or diagnostic items by their definition path.
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for adt in krate.adts() {
            let did = rustc_internal::internal(tcx, adt.def_id());
            let path = type_path(tcx, did, &krate.name, krate.is_local);
            if let Some(group) = classify_type_path(&path) {
                types.insert(did, group);
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TypeGroup {
    Box,
    CString,
    Vec,
    String,
    Ordering,
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
        "alloc::string::String" | "std::string::String" => TypeGroup::String,
        "core::slice::iter::Iter"
        | "core::slice::iter::IterMut"
        | "std::slice::Iter"
        | "std::slice::IterMut" => TypeGroup::Iter,
        "core::ptr::non_null::NonNull" | "std::ptr::NonNull" => TypeGroup::NonNull,
        "core::ops::index_range::IndexRange"
        | "std::ops::index_range::IndexRange"
        | "std::ops::IndexRange" => TypeGroup::IndexRange,
        "core::ascii::ascii_char::AsciiChar" | "std::ascii::AsciiChar" => TypeGroup::AsciiChar,
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

fn types() -> &'static HashMap<DefId, TypeGroup> {
    TYPES.get().expect("Type DefIds haven't been initialized.")
}

macro_rules! type_predicates {
    ($( $(#[$attr:meta])* $name:ident => $group:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name(did: DefId) -> bool {
                types().get(&did) == Some(&TypeGroup::$group)
            }
        )+
    };
}

type_predicates! {
    /// Whether this is `alloc::boxed::Box`.
    is_std_box => Box,
    /// Whether this is `alloc::ffi::CString`.
    is_std_cstring => CString,
    /// Whether this is `alloc::vec::Vec`.
    is_std_vec => Vec,
    /// Whether this is `alloc::string::String`.
    is_std_string => String,
    /// Whether this is `core::ptr::NonNull`.
    is_std_nonnull => NonNull,
    /// Whether this is `core::mem::MaybeUninit`.
    is_maybe_uninit_type => MaybeUninit,
    /// Whether this is `core::cmp::Ordering`.
    is_std_ordering => Ordering,
    /// Whether this is `core::slice::Iter` or `IterMut`.
    is_std_iter_or_itermut => Iter,
    /// Whether this is `alloc::rc::Rc`.
    is_std_rc => Rc,
    /// Whether this is a standard `Mutex`, `RwLock`, `OnceLock`, or atomic type.
    is_std_sync_primitive => SyncPrimitive,
    /// Whether this is the standard `IndexRange` type.
    is_index_range => IndexRange,
}

/// Resolve the `AsciiChar` definition used by contract type names.
pub fn get_ascii_char_def_id() -> Option<DefId> {
    types()
        .iter()
        .find_map(|(&did, &group)| (group == TypeGroup::AsciiChar).then_some(did))
}

/// Resolve a negative-type name (as written in `std-trait.json`) to its
/// resolved `DefId` set. Unknown or unresolved names return `None`.
pub fn negative_type_defs(name: &str) -> Option<Vec<DefId>> {
    let ids: Vec<_> = types()
        .iter()
        .filter_map(|(&did, &group)| {
            let matches = match group {
                TypeGroup::Rc => name == "Rc",
                TypeGroup::Negative(short) => name == short,
                _ => false,
            };
            matches.then_some(did)
        })
        .collect();
    (!ids.is_empty()).then_some(ids)
}
