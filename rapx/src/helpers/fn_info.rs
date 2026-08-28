use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    ty,
    ty::{AssocKind, Mutability, TyCtxt, TyKind},
};
use rustc_span::{kw, sym};
use std::{collections::HashSet, fmt::Debug, hash::Hash};
use syn::Expr;

pub use super::mir_scan::check_safety;
pub use super::name::get_cleaned_def_path_name;

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum FnKind {
    Fn,
    Method,
    Constructor,
    Intrinsic,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct FnInfo {
    pub def_id: DefId,
    pub fn_safety: Safety,
    pub fn_kind: FnKind,
}

impl FnInfo {
    pub fn new(def_id: DefId, fn_safety: Safety, fn_kind: FnKind) -> Self {
        FnInfo {
            def_id,
            fn_safety,
            fn_kind,
        }
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub struct AdtInfo {
    pub def_id: DefId,
    pub literal_cons_enabled: bool,
}

impl AdtInfo {
    pub fn new(def_id: DefId, literal_cons_enabled: bool) -> Self {
        AdtInfo {
            def_id,
            literal_cons_enabled,
        }
    }
}

pub fn check_visibility(tcx: TyCtxt, func_defid: DefId) -> bool {
    tcx.visibility(func_defid).is_public()
}

/// Returns true when `ty` denotes `Self`: either the generic `Self` param
/// (`ty.is_param(0)`) or a type equal to the impl's self type.
fn is_self_ty<'tcx>(tcx: TyCtxt<'tcx>, assoc_item: &ty::AssocItem, ty: ty::Ty<'tcx>) -> bool {
    if ty.is_param(0) {
        return true;
    }
    assoc_item
        .impl_container(tcx)
        .is_some_and(|impl_id| ty == tcx.type_of(impl_id).skip_binder())
}

pub fn get_type(tcx: TyCtxt<'_>, def_id: DefId) -> FnKind {
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return FnKind::Fn;
    };
    let AssocKind::Fn { has_self, .. } = assoc_item.kind else {
        return FnKind::Fn;
    };
    if has_self {
        return FnKind::Method;
    }
    let output = tcx.fn_sig(def_id).skip_binder().output().skip_binder();
    if is_self_ty(tcx, &assoc_item, output) {
        return FnKind::Constructor;
    }
    match output.kind() {
        TyKind::Ref(_, ref_ty, _) => {
            if is_self_ty(tcx, &assoc_item, *ref_ty) {
                return FnKind::Constructor;
            }
        }
        TyKind::Adt(adt_def, substs)
            if adt_def.is_enum()
                && (tcx.is_diagnostic_item(sym::Option, adt_def.did())
                    || tcx.is_diagnostic_item(sym::Result, adt_def.did())
                    || tcx.is_diagnostic_item(kw::Box, adt_def.did())) =>
        {
            if is_self_ty(tcx, &assoc_item, substs.type_at(0)) {
                return FnKind::Constructor;
            }
        }
        _ => {}
    }
    FnKind::Fn
}

/// Returns true when the function is a "wrapped" constructor that returns
/// `Option<Self>` / `Result<Self, _>` rather than a bare `Self`.
///
/// `get_type` classifies these as [`FnKind::Constructor`], but for the wrapped
/// forms the `None`/`Err` paths do not produce a `Self`, so a struct invariant
/// can only be meaningfully discharged on the `Some`/`Ok` paths. This helper
/// lets `verify_struct_invariants` skip the benign `Unknown` results on the
/// non-`Self` paths. (`Box<Self>` is intentionally *not* included: every path
/// still produces a `Self` behind the pointer.)
pub fn returns_wrapped_self(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc_item) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    if !matches!(
        assoc_item.kind,
        AssocKind::Fn {
            has_self: false,
            ..
        }
    ) {
        return false;
    }
    let fn_sig = tcx.fn_sig(def_id).skip_binder();
    let output = fn_sig.output().skip_binder();
    let TyKind::Adt(adt_def, substs) = output.kind() else {
        return false;
    };
    if !(adt_def.is_enum()
        && (tcx.is_diagnostic_item(sym::Option, adt_def.did())
            || tcx.is_diagnostic_item(sym::Result, adt_def.did())))
    {
        return false;
    }
    is_self_ty(tcx, &assoc_item, substs.type_at(0))
}

/// The `AdtDef` that `def_id`'s impl block is implemented for, if any.
fn self_adt_def(tcx: TyCtxt<'_>, def_id: DefId) -> Option<ty::AdtDef<'_>> {
    let assoc_item = tcx.opt_associated_item(def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    tcx.type_of(impl_id).skip_binder().ty_adt_def()
}

// result: adt_def_id, is_literal
pub fn get_adt_via_method(tcx: TyCtxt<'_>, method_def_id: DefId) -> Option<AdtInfo> {
    let adt_def = self_adt_def(tcx, method_def_id)?;
    let adt_def_id = adt_def.did();

    let total_count = adt_def.all_fields().count();

    if total_count == 0 {
        return Some(AdtInfo::new(adt_def_id, true));
    }

    let pub_count = public_field_indices(tcx, adt_def).len();

    if pub_count == 0 {
        return None;
    }
    Some(AdtInfo::new(adt_def_id, pub_count == total_count))
}
pub fn get_adt_def_id_by_adt_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    self_adt_def(tcx, def_id).map(|adt_def| adt_def.did())
}

/// Returns true when `def_id` is a method taking `&mut self` (a mutator).
///
/// Detection is based on the method signature rather than MIR, so it also
/// works for foreign (e.g. std) functions whose MIR is unavailable.
fn is_mut_self_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(assoc) = tcx.opt_associated_item(def_id) else {
        return false;
    };
    if !matches!(assoc.kind, AssocKind::Fn { has_self: true, .. }) {
        return false;
    }
    let fn_sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    let Some(first) = fn_sig.inputs_and_output.first().copied() else {
        return false;
    };
    matches!(first.kind(), TyKind::Ref(_, _, Mutability::Mut))
}

// Check each field's visibility, return the public fields vec
fn public_field_indices(tcx: TyCtxt<'_>, adt_def: ty::AdtDef<'_>) -> HashSet<usize> {
    adt_def
        .all_fields()
        .enumerate()
        .filter_map(|(index, field_def)| tcx.visibility(field_def.did).is_public().then_some(index))
        .collect()
}

/// parse expr into number.
pub fn parse_expr_into_number(expr: &Expr) -> Option<usize> {
    if let Expr::Lit(expr_lit) = expr {
        if let syn::Lit::Int(lit_int) = &expr_lit.lit {
            return lit_int.base10_parse::<usize>().ok();
        }
    }
    None
}

pub fn get_all_std_fns_by_rustc_public(tcx: TyCtxt) -> Vec<DefId> {
    let mut all_std_fn_def = Vec::new();
    let mut results = Vec::new();
    let mut core_fn_def: Vec<_> = rustc_public::find_crates("core")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    let mut std_fn_def: Vec<_> = rustc_public::find_crates("std")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    let mut alloc_fn_def: Vec<_> = rustc_public::find_crates("alloc")
        .iter()
        .flat_map(|krate| krate.fn_defs())
        .collect();
    all_std_fn_def.append(&mut core_fn_def);
    all_std_fn_def.append(&mut std_fn_def);
    all_std_fn_def.append(&mut alloc_fn_def);

    for fn_def in &all_std_fn_def {
        let def_id = crate::def_id::to_internal(fn_def, tcx);
        results.push(def_id);
    }
    results
}

/// Find `&mut self` methods (mutators) on the same struct as `src_def_id`.
///
/// For std types the mutators are located among the std library's public
/// functions; for user types they are the struct's inherent `&mut self` methods.
pub fn get_all_mutable_methods(tcx: TyCtxt, src_def_id: DefId) -> HashSet<DefId> {
    if get_type(tcx, src_def_id) == FnKind::Constructor {
        return HashSet::new();
    }
    let target_adt_def = get_adt_def_id_by_adt_method(tcx, src_def_id);
    let mut mutators = HashSet::new();
    let mut is_std = false;
    for def_id in get_all_std_fns_by_rustc_public(tcx) {
        let adt_def = get_adt_def_id_by_adt_method(tcx, def_id);
        if adt_def.is_some() && adt_def == target_adt_def && src_def_id != def_id {
            if is_mut_self_method(tcx, def_id) {
                mutators.insert(def_id);
            }
            is_std = true;
        }
    }
    if is_std {
        return mutators;
    }
    mutators.extend(get_muts(tcx, src_def_id));
    mutators
}

/// Associated function `DefId`s (inherent impls only) on the struct that
/// `def_id`'s impl block is implemented for.
fn assoc_fns_of_self(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let Some(adt_def) = self_adt_def(tcx, def_id) else {
        return Vec::new();
    };
    let mut fns = Vec::new();
    for impl_def_id in tcx.inherent_impls(adt_def.did()) {
        for item in tcx.associated_item_def_ids(*impl_def_id) {
            if matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn) {
                fns.push(*item);
            }
        }
    }
    fns
}

pub fn get_cons(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    if tcx.def_kind(def_id) == DefKind::Fn || get_type(tcx, def_id) == FnKind::Constructor {
        return Vec::new();
    }
    assoc_fns_of_self(tcx, def_id)
        .into_iter()
        .filter(|&item| get_type(tcx, item) == FnKind::Constructor)
        .collect()
}

/// Find `&mut self` methods (mutators) on the same struct as `def_id`.
///
/// A mutator is a method whose first parameter is a mutable reference to Self.
/// These methods can change struct fields and affect subsequent invariant checks.
pub fn get_muts(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    assoc_fns_of_self(tcx, def_id)
        .into_iter()
        .filter(|&item| is_mut_self_method(tcx, item))
        .collect()
}

pub fn append_fn_with_types(tcx: TyCtxt, def_id: DefId) -> FnInfo {
    FnInfo::new(def_id, check_safety(tcx, def_id), get_type(tcx, def_id))
}

pub fn get_ptr_deref_dummy_def_id(tcx: TyCtxt<'_>) -> Option<DefId> {
    tcx.hir_crate_items(()).free_items().find_map(|item_id| {
        let def_id = item_id.owner_id.to_def_id();
        let name = tcx.opt_item_name(def_id)?;

        (name.as_str() == "__raw_ptr_deref_dummy").then_some(def_id)
    })
}

/// Return field indices that a `&mut self` method writes to.
///
/// Scans the MIR body for assignments to `(*self).field_n` and returns the
/// set of field indices that are modified.  Used by --skip-invariant mode to know which
/// constructor-inherited invariants are invalidated by a mutator.
pub fn get_mutated_fields(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<usize> {
    use rustc_middle::mir::{ProjectionElem, StatementKind};

    let body = tcx.optimized_mir(def_id);
    let mut fields = Vec::new();

    for (_, data) in body.basic_blocks.iter().enumerate() {
        for statement in &data.statements {
            if let StatementKind::Assign(assign) = &statement.kind {
                let (place, _) = &**assign;
                if place.local.as_usize() != 1 {
                    continue;
                }
                let mut saw_deref = false;
                for proj in place.projection.iter() {
                    match proj {
                        ProjectionElem::Deref => {
                            saw_deref = true;
                        }
                        ProjectionElem::Field(index, _) if saw_deref => {
                            let idx = index.as_usize();
                            if !fields.contains(&idx) {
                                fields.push(idx);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    fields
}

pub fn is_externally_reachable(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return true;
    };
    tcx.effective_visibilities(()).is_reachable(local)
}
