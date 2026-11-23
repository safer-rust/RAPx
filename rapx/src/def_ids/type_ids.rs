//! Resolved `DefId`s of standard-library types used by verification.
//!
//! # Agent Rules
//!
//! Keep this module limited to resolving standard-library type identities
//! from rustc lang items, diagnostic items, and definition paths. Do not
//! depend on other RAPx modules.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_public::{CrateDef, rustc_internal};
use rustc_span::sym;
use std::collections::HashMap;
use std::sync::OnceLock;

static TYPES: OnceLock<HashMap<DefId, StdAdtType>> = OnceLock::new();

pub fn init(tcx: TyCtxt) {
    TYPES.get_or_init(|| init_types(tcx));
}

fn init_types(tcx: TyCtxt) -> HashMap<DefId, StdAdtType> {
    let mut types = HashMap::new();

    // Lang items.
    if let Some(did) = tcx.lang_items().owned_box() {
        types.insert(did, StdAdtType::Box);
    }
    if let Some(did) = tcx.lang_items().ordering_enum() {
        types.insert(did, StdAdtType::Ordering);
    }
    if let Some(did) = tcx.lang_items().maybe_uninit() {
        types.insert(did, StdAdtType::MaybeUninit);
    }
    if let Some(unsafe_cell) = tcx.lang_items().unsafe_cell_type() {
        types.insert(unsafe_cell, StdAdtType::UnsafeCell);
    }

    // Diagnostic items.
    if let Some(did) = tcx.get_diagnostic_item(sym::cstring_type) {
        types.insert(did, StdAdtType::CString);
    }
    if let Some(did) = tcx.get_diagnostic_item(sym::Vec) {
        types.insert(did, StdAdtType::Vec);
    }
    if let Some(did) = tcx.get_diagnostic_item(sym::Rc) {
        types.insert(did, StdAdtType::Rc);
    }

    // Resolve remaining public type identities by definition path.
    for krate in std::iter::once(rustc_public::local_crate())
        .chain(rustc_public::external_crates())
        .filter(|k| ["core", "std", "alloc"].iter().any(|n| *n == k.name))
    {
        for adt in krate.adts() {
            let did = rustc_internal::internal(tcx, adt.def_id());
            if let Some(group) = classify_type(tcx, did, &krate.name, krate.is_local) {
                types.insert(did, group);
            }
        }
    }

    types
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum StdAdtType {
    AsciiChar,
    Box,
    Cell,
    CString,
    IndexRange,
    Iter,
    MappedMutexGuard,
    MaybeUninit,
    MutexGuard,
    NonNull,
    Ordering,
    Rc,
    Ref,
    RefCell,
    RefMut,
    RwLockWriteGuard,
    String,
    SyncPrimitive,
    UnsafeCell,
    Vec,
}

/// Resolve names used by `ContainNoType` to known standard-library types.
pub(crate) fn negative_type_by_name(name: &str) -> Option<StdAdtType> {
    Some(match name {
        "Rc" => StdAdtType::Rc,
        "Cell" => StdAdtType::Cell,
        "UnsafeCell" => StdAdtType::UnsafeCell,
        "RefCell" => StdAdtType::RefCell,
        "Ref" => StdAdtType::Ref,
        "RefMut" => StdAdtType::RefMut,
        "MutexGuard" => StdAdtType::MutexGuard,
        "MappedMutexGuard" => StdAdtType::MappedMutexGuard,
        "RwLockWriteGuard" => StdAdtType::RwLockWriteGuard,
        _ => return None,
    })
}

fn classify_type(
    tcx: TyCtxt<'_>,
    did: DefId,
    crate_name: &str,
    is_local: bool,
) -> Option<StdAdtType> {
    let path = tcx.def_path_str(did);
    let path = if is_local && !path.starts_with(&format!("{crate_name}::")) {
        format!("{crate_name}::{path}")
    } else {
        path
    };
    let name = path.as_str();
    Some(match name {
        "alloc::string::String" | "std::string::String" => StdAdtType::String,
        "core::slice::iter::Iter"
        | "core::slice::iter::IterMut"
        | "std::slice::Iter"
        | "std::slice::IterMut" => StdAdtType::Iter,
        "core::ptr::non_null::NonNull" | "std::ptr::NonNull" => StdAdtType::NonNull,
        "core::ops::index_range::IndexRange"
        | "std::ops::index_range::IndexRange"
        | "std::ops::IndexRange" => StdAdtType::IndexRange,
        "core::ascii::ascii_char::AsciiChar" | "std::ascii::AsciiChar" => StdAdtType::AsciiChar,
        "alloc::rc::Rc" | "alloc::rcs::rc::Rc" | "std::rc::Rc" => StdAdtType::Rc,
        "std::sync::poison::mutex::Mutex"
        | "std::sync::nonpoison::mutex::Mutex"
        | "std::sync::nonpoison::Mutex"
        | "std::sync::poison::rwlock::RwLock"
        | "std::sync::nonpoison::rwlock::RwLock"
        | "std::sync::once_lock::OnceLock"
        | "std::sync::Mutex"
        | "std::sync::RwLock"
        | "std::sync::OnceLock"
        | "core::sync::atomic::Atomic"
        | "std::sync::atomic::Atomic" => StdAdtType::SyncPrimitive,
        "core::cell::Cell" | "std::cell::Cell" => StdAdtType::Cell,
        "core::cell::RefCell" | "std::cell::RefCell" => StdAdtType::RefCell,
        "core::cell::Ref" | "std::cell::Ref" => StdAdtType::Ref,
        "core::cell::RefMut" | "std::cell::RefMut" => StdAdtType::RefMut,
        "std::sync::poison::mutex::MutexGuard"
        | "std::sync::nonpoison::mutex::MutexGuard"
        | "std::sync::MutexGuard" => StdAdtType::MutexGuard,
        "std::sync::poison::mutex::MappedMutexGuard"
        | "std::sync::nonpoison::mutex::MappedMutexGuard"
        | "std::sync::MappedMutexGuard" => StdAdtType::MappedMutexGuard,
        "std::sync::poison::rwlock::RwLockWriteGuard"
        | "std::sync::nonpoison::rwlock::RwLockWriteGuard"
        | "std::sync::RwLockWriteGuard" => StdAdtType::RwLockWriteGuard,
        _ => return None,
    })
}

fn types() -> &'static HashMap<DefId, StdAdtType> {
    TYPES.get().expect("Type DefIds haven't been initialized.")
}

pub(crate) fn def_ids_for_type(group: StdAdtType) -> impl Iterator<Item = DefId> {
    types()
        .iter()
        .filter_map(move |(&did, &kind)| (kind == group).then_some(did))
}

macro_rules! type_predicates {
    ($( $(#[$attr:meta])* $name:ident => $group:ident ,)+) => {
        $(
            $(#[$attr])*
            pub fn $name(did: DefId) -> bool {
                types().get(&did) == Some(&StdAdtType::$group)
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
