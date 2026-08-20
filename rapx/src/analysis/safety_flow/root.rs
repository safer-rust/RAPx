use crate::helpers::mir_scan::{collect_global_local_pairs, get_rawptr_deref, get_unsafe_callees};
use rustc_hir::{BodyId, ItemKind, def_id::DefId};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Symbol;
use std::collections::HashSet;

use super::hir_visitor::ContainsUnsafe;

/// Kind of unsafe operation found in a function body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsafeOpKind {
    CallsUnsafeFn,
    DerefsRawPtr,
    AccessesStaticMut,
}

/// A function that contains unsafe operations — an "unsafe root".
///
/// This is the unified entry point for both the safetyflow analysis and the
/// verify module to determine whether a function needs safety verification.
#[derive(Debug, Clone)]
pub struct UnsafeRoot {
    pub def_id: DefId,
    pub kinds: Vec<UnsafeOpKind>,
    pub unsafe_callees: HashSet<DefId>,
    pub raw_ptr_locals: HashSet<Local>,
    pub static_muts: HashSet<DefId>,
}

/// Fast HIR-level pre-check: does this function contain `unsafe` blocks
/// or is it declared `unsafe fn`?
///
/// This is a cheap check that can quickly filter out functions that are
/// entirely safe and have no unsafe operations of any kind.
pub fn hir_contains_unsafe(tcx: TyCtxt<'_>, body_id: BodyId) -> bool {
    let (fn_unsafe, block_unsafe) = ContainsUnsafe::contains_unsafe(tcx, body_id);
    fn_unsafe || block_unsafe
}

/// Check if a struct has `#[rapx::invariant(...)]` annotations.
///
/// This is a cheap HIR attribute scan — it only checks for the presence of
/// the attribute path, without parsing the annotation arguments.
pub fn has_struct_invariant(tcx: TyCtxt<'_>, struct_def_id: DefId) -> bool {
    let Some(local_def_id) = struct_def_id.as_local() else {
        return false;
    };
    let rapx = Symbol::intern("rapx");
    let invariant = Symbol::intern("invariant");
    let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(local_def_id));
    attrs.iter().any(|attr| {
        if attr.is_doc_comment().is_some() {
            return false;
        }
        let path = attr.path();
        path.len() == 2 && path[0] == rapx && path[1] == invariant
    })
}

/// Quick check: does this function's owning struct have invariants?
pub fn function_has_struct_invariant(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    let Some(impl_id) = assoc_item.impl_container(tcx) else {
        return false;
    };
    let self_ty = tcx.type_of(impl_id).skip_binder();
    match self_ty.kind() {
        rustc_middle::ty::TyKind::Adt(adt_def, _) => has_struct_invariant(tcx, adt_def.did()),
        _ => false,
    }
}

/// Quick check: does this function's containing impl implement an `unsafe trait`?
///
/// This is a fast HIR-level pre-filter similar to [`function_has_struct_invariant`].
pub fn function_has_trait_ensurance(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    let Some(impl_id) = assoc_item.impl_container(tcx) else {
        return false;
    };

    let trait_def_id = {
        tcx.impl_opt_trait_ref(impl_id)
    };
    let Some(trait_ref) = trait_def_id else {
        return false;
    };
    let trait_def_id = trait_ref.skip_binder().def_id;

    let Some(local_id) = trait_def_id.as_local() else {
        return false;
    };

    // Check if the trait is declared `unsafe trait`
    let item = tcx.hir_expect_item(local_id);
    #[cfg(not(rapx_ge_99))]
    if let ItemKind::Trait(_, _, unsafety, _, _, _, _) = &item.kind {
        return matches!(unsafety, rustc_hir::Safety::Unsafe);
    }
    #[cfg(rapx_ge_99)]
    if let ItemKind::Trait { safety, .. } = &item.kind {
        return matches!(safety, rustc_hir::Safety::Unsafe);
    }

    false
}

/// Full MIR-level detection: scan the function body for all unsafe operations.
///
/// Returns `None` if the function has no unsafe callees, no raw pointer
/// dereferences, and no static mutable accesses.
pub fn scan_mir(tcx: TyCtxt<'_>, def_id: DefId) -> Option<UnsafeRoot> {
    if !tcx.is_mir_available(def_id) {
        return None;
    }

    let unsafe_callees = get_unsafe_callees(tcx, def_id);
    let raw_ptr_locals = get_rawptr_deref(tcx, def_id);
    let global_locals = collect_global_local_pairs(tcx, def_id);
    let static_muts: HashSet<DefId> = global_locals.keys().copied().collect();

    let global_locals_set: HashSet<Local> = global_locals.values().flatten().copied().collect();
    let raw_ptr_locals: HashSet<Local> = raw_ptr_locals
        .difference(&global_locals_set)
        .copied()
        .collect();

    if unsafe_callees.is_empty() && raw_ptr_locals.is_empty() && static_muts.is_empty() {
        return None;
    }

    let mut kinds = Vec::new();
    if !unsafe_callees.is_empty() {
        kinds.push(UnsafeOpKind::CallsUnsafeFn);
    }
    if !raw_ptr_locals.is_empty() {
        kinds.push(UnsafeOpKind::DerefsRawPtr);
    }
    if !static_muts.is_empty() {
        kinds.push(UnsafeOpKind::AccessesStaticMut);
    }

    Some(UnsafeRoot {
        def_id,
        kinds,
        unsafe_callees,
        raw_ptr_locals,
        static_muts,
    })
}
