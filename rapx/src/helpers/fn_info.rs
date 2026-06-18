use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::Local,
    ty,
    ty::{AssocKind, Mutability, Ty, TyCtxt, TyKind},
};
use rustc_span::{kw, sym};
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};
use syn::Expr;

pub use super::mir_scan::{
    check_safety, collect_global_local_pairs, get_rawptr_deref, get_unsafe_callees,
    place_has_raw_deref,
};
pub use super::name::{
    access_ident_recursive, find_generic_in_ty, find_generic_param, get_cleaned_def_path_name,
    get_known_std_names, get_std_api_signature_json, get_struct_name, match_primitive_type,
    match_ty_with_ident, parse_local_signature, parse_outside_signature, parse_signature,
};

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
    if !tcx.visibility(func_defid).is_public() {
        return false;
    }
    true
}

pub fn get_type(tcx: TyCtxt<'_>, def_id: DefId) -> FnKind {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self {
                    return FnKind::Method;
                } else {
                    let fn_sig = tcx.fn_sig(def_id).skip_binder();
                    let output = fn_sig.output().skip_binder();
                    // return type is 'Self'
                    if output.is_param(0) {
                        return FnKind::Constructor;
                    }
                    // return type is struct's name
                    if let Some(impl_id) = assoc_item.impl_container(tcx) {
                        let ty = tcx.type_of(impl_id).skip_binder();
                        if output == ty {
                            return FnKind::Constructor;
                        }
                    }
                    match output.kind() {
                        TyKind::Ref(_, ref_ty, _) => {
                            if ref_ty.is_param(0) {
                                return FnKind::Constructor;
                            }
                            if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                let ty = tcx.type_of(impl_id).skip_binder();
                                if *ref_ty == ty {
                                    return FnKind::Constructor;
                                }
                            }
                        }
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum()
                                && (tcx.is_diagnostic_item(sym::Option, adt_def.did())
                                    || tcx.is_diagnostic_item(sym::Result, adt_def.did())
                                    || tcx.is_diagnostic_item(kw::Box, adt_def.did()))
                            {
                                let inner_ty = substs.type_at(0);
                                if inner_ty.is_param(0) {
                                    return FnKind::Constructor;
                                }
                                if let Some(impl_id) = assoc_item.impl_container(tcx) {
                                    let ty_impl = tcx.type_of(impl_id).skip_binder();
                                    if inner_ty == ty_impl {
                                        return FnKind::Constructor;
                                    }
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => todo!(),
        }
    }
    return FnKind::Fn;
}
// result: adt_def_id, is_literal
pub fn get_adt_via_method(tcx: TyCtxt<'_>, method_def_id: DefId) -> Option<AdtInfo> {
    let assoc_item = tcx.opt_associated_item(method_def_id)?;
    let impl_id = assoc_item.impl_container(tcx)?;
    let ty = tcx.type_of(impl_id).skip_binder();
    let adt_def = ty.ty_adt_def()?;
    let adt_def_id = adt_def.did();

    let all_fields: Vec<_> = adt_def.all_fields().collect();
    let total_count = all_fields.len();

    if total_count == 0 {
        return Some(AdtInfo::new(adt_def_id, true));
    }

    let pub_count = all_fields
        .iter()
        .filter(|field| tcx.visibility(field.did).is_public())
        .count();

    if pub_count == 0 {
        return None;
    }
    Some(AdtInfo::new(adt_def_id, pub_count == total_count))
}
// return all the impls def id of corresponding struct
pub fn get_impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        if let rustc_hir::ItemKind::Impl(impl_details) = &item.kind {
            if let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                &impl_details.self_ty.kind
            {
                if let rustc_hir::def::Res::Def(_, def_id) = path.res {
                    if def_id == struct_def_id {
                        impls.push(item_id.owner_id.to_def_id());
                    }
                }
            }
        }
    }
    impls
}

pub fn get_adt_def_id_by_adt_method(tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            // get struct ty
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                return Some(adt_def.did());
            }
        }
    }
    None
}

// get the pointee or wrapped type
pub fn get_pointee(matched_ty: Ty<'_>) -> Ty<'_> {
    // progress_info!("get_pointee: > {:?} as type: {:?}", matched_ty, matched_ty.kind());
    let pointee = if let ty::RawPtr(ty_mut, _) = matched_ty.kind() {
        get_pointee(*ty_mut)
    } else if let ty::Ref(_, referred_ty, _) = matched_ty.kind() {
        get_pointee(*referred_ty)
    } else {
        matched_ty
    };
    pointee
}

pub fn is_ptr(matched_ty: Ty<'_>) -> bool {
    if let ty::RawPtr(_, _) = matched_ty.kind() {
        return true;
    }
    false
}

pub fn has_mut_self_param(tcx: TyCtxt, def_id: DefId) -> bool {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        match assoc_item.kind {
            AssocKind::Fn { has_self, .. } => {
                if has_self && tcx.is_mir_available(def_id) {
                    let body = tcx.optimized_mir(def_id);
                    let fst_arg = body.local_decls[Local::from_usize(1)].clone();
                    let ty = fst_arg.ty;
                    let is_mut_ref = matches!(ty.kind(), ty::Ref(_, _, Mutability::Mut));
                    return fst_arg.mutability.is_mut() || is_mut_ref;
                }
            }
            _ => (),
        }
    }
    false
}

// Check each field's visibility, return the public fields vec
pub fn get_public_fields(tcx: TyCtxt, def_id: DefId) -> HashSet<usize> {
    let adt_def = tcx.adt_def(def_id);
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

// Input the adt def id
// Return set of (mutable method def_id, fields can be modified)
pub fn get_all_mutable_methods(tcx: TyCtxt, src_def_id: DefId) -> HashMap<DefId, HashSet<usize>> {
    let mut std_results = HashMap::new();
    if get_type(tcx, src_def_id) == FnKind::Constructor {
        return std_results;
    }
    let all_std_fn_def = get_all_std_fns_by_rustc_public(tcx);
    let target_adt_def = get_adt_def_id_by_adt_method(tcx, src_def_id);
    let mut is_std = false;
    for &def_id in &all_std_fn_def {
        let adt_def = get_adt_def_id_by_adt_method(tcx, def_id);
        if adt_def.is_some() && adt_def == target_adt_def && src_def_id != def_id {
            if has_mut_self_param(tcx, def_id) {
                std_results.insert(def_id, HashSet::new());
            }
            is_std = true;
        }
    }
    if is_std {
        return std_results;
    }
    let mut results = HashMap::new();
    let public_fields = target_adt_def.map_or_else(HashSet::new, |def| get_public_fields(tcx, def));
    let impl_vec = target_adt_def.map_or_else(Vec::new, |def| get_impls_for_struct(tcx, def));
    for impl_id in impl_vec {
        if !matches!(tcx.def_kind(impl_id), rustc_hir::def::DefKind::Impl { .. }) {
            continue;
        }
        let associated_items = tcx.associated_items(impl_id);
        for item in associated_items.in_definition_order() {
            if let ty::AssocKind::Fn {
                name: _,
                has_self: _,
            } = item.kind
            {
                let item_def_id = item.def_id;
                if has_mut_self_param(tcx, item_def_id) {
                    let modified_fields = public_fields.clone();
                    results.insert(item_def_id, modified_fields);
                }
            }
        }
    }
    results
}

pub fn get_cons(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let mut cons = Vec::new();
    if tcx.def_kind(def_id) == DefKind::Fn || get_type(tcx, def_id) == FnKind::Constructor {
        return cons;
    }
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                let adt_def_id = adt_def.did();
                let impls = tcx.inherent_impls(adt_def_id);
                for impl_def_id in impls {
                    for item in tcx.associated_item_def_ids(*impl_def_id) {
                        if (tcx.def_kind(*item) == DefKind::Fn
                            || tcx.def_kind(*item) == DefKind::AssocFn)
                            && get_type(tcx, *item) == FnKind::Constructor
                        {
                            cons.push(*item);
                        }
                    }
                }
            }
        }
    }
    cons
}

/// Find `&mut self` methods (mutators) on the same struct as `def_id`.
///
/// A mutator is a method whose first parameter is a mutable reference to Self.
/// These methods can change struct fields and affect subsequent invariant checks.
pub fn get_muts(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<DefId> {
    let mut muts = Vec::new();
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            let ty = tcx.type_of(impl_id).skip_binder();
            if let Some(adt_def) = ty.ty_adt_def() {
                let adt_def_id = adt_def.did();
                let impls = tcx.inherent_impls(adt_def_id);
                for impl_def_id in impls {
                    for item in tcx.associated_item_def_ids(*impl_def_id) {
                        if !matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn) {
                            continue;
                        }
                        if get_type(tcx, *item) != FnKind::Method {
                            continue;
                        }
                        let Some(assoc) = tcx.opt_associated_item(*item) else {
                            continue;
                        };
                        if !matches!(assoc.kind, AssocKind::Fn { has_self: true, .. }) {
                            continue;
                        }
                        let fn_sig = tcx.fn_sig(*item).instantiate_identity().skip_binder();
                        let all = fn_sig.inputs_and_output;
                        let first_param = all.first().copied();
                        if let Some(TyKind::Ref(_, _, Mutability::Mut)) =
                            first_param.map(|ty| ty.kind())
                        {
                            muts.push(*item);
                        }
                    }
                }
            }
        }
    }
    muts
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
/// set of field indices that are modified.  Used by invless mode to know which
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
