use rustc_abi::FieldIdx;
use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty::{self, Ty, TyCtxt, TyKind},
};
use serde_json::Value;
use std::collections::HashSet;
use syn::Expr;

pub fn get_unsafe_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    let mut unsafe_callees = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                        if check_safety(tcx, *callee_def_id) == Safety::Unsafe {
                            unsafe_callees.insert(*callee_def_id);
                        }
                    }
                }
            }
        }
    }
    unsafe_callees
}

pub fn get_cleaned_def_path_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    let mut parts: Vec<&str> = def_id_str.split("::").collect();

    let mut remove_first = false;
    if let Some(first_part) = parts.get_mut(0) {
        if first_part.contains("core") {
            *first_part = "core";
        } else if first_part.contains("std") {
            *first_part = "std";
        } else if first_part.contains("alloc") {
            *first_part = "alloc";
        } else {
            remove_first = true;
        }
    }
    if remove_first && !parts.is_empty() {
        parts.remove(0);
    }

    let new_parts: Vec<String> = parts
        .into_iter()
        .filter_map(|s| {
            if s.contains("{") {
                if remove_first {
                    get_struct_name(tcx, def_id)
                } else {
                    None
                }
            } else {
                Some(s.to_string())
            }
        })
        .collect();

    let mut cleaned_path = new_parts.join("::");
    cleaned_path = cleaned_path.trim_end_matches(')').to_string();
    cleaned_path
}

pub fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(expr) {
        let (param_names, param_tys) = parse_signature(tcx, def_id);
        if param_names[0] == "0".to_string() {
            return None;
        }
        if let Some(param_index) = param_names.iter().position(|name| name == &base_ident) {
            let mut current_ty = param_tys[param_index];
            let mut field_indices = Vec::new();
            for field_name in fields {
                let peeled_ty = current_ty.peel_refs();
                if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
                    let variant = adt_def.non_enum_variant();
                    if let Ok(field_idx) = field_name.parse::<usize>() {
                        if field_idx < variant.fields.len() {
                            current_ty = variant.fields[FieldIdx::from_usize(field_idx)].ty(tcx, arg_list);
                            field_indices.push((field_idx, current_ty));
                            continue;
                        }
                    }
                    if let Some((idx, _)) = variant
                        .fields
                        .iter()
                        .enumerate()
                        .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
                    {
                        current_ty = variant.fields[FieldIdx::from_usize(idx)].ty(tcx, arg_list);
                        field_indices.push((idx, current_ty));
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            }
            return Some((param_index + 1, field_indices, current_ty));
        }
    }
    None
}

pub fn parse_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    if def_id.as_local().is_some() {
        parse_local_signature(tcx, def_id)
    } else {
        parse_outside_signature(tcx, def_id)
    }
}

pub fn parse_local_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let local_def_id = def_id.as_local().unwrap();
    let hir_body = tcx.hir_body_owned_by(local_def_id);
    if hir_body.params.is_empty() {
        return (vec!["0".to_string()], Vec::new());
    }

    let params = hir_body.params;
    let typeck_results = tcx.typeck_body(hir_body.id());
    let mut param_names = Vec::new();
    let mut param_tys = Vec::new();
    for param in params {
        match param.pat.kind {
            rustc_hir::PatKind::Binding(_, _, ident, _) => {
                param_names.push(ident.name.to_string());
                let ty = typeck_results.pat_ty(param.pat);
                param_tys.push(ty);
            }
            _ => {
                param_names.push(String::new());
                param_tys.push(typeck_results.pat_ty(param.pat));
            }
        }
    }
    (param_names, param_tys)
}

fn parse_outside_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();

    if let Some(args_name) = get_known_std_names(tcx, def_id) {
        return (args_name, param_tys);
    }

    let args_name = (0..param_tys.len()).map(|i| format!("{}", i)).collect();
    (args_name, param_tys)
}

fn get_known_std_names<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<String>> {
    let std_func_name = get_cleaned_def_path_name(tcx, def_id);
    let json_data = get_std_api_signature_json();

    if let Some(arg_info) = json_data.get(&std_func_name) {
        if let Some(args_name) = arg_info.as_array() {
            if args_name.is_empty() {
                return Some(vec!["0".to_string()]);
            }
            let mut result = Vec::new();
            for arg in args_name {
                if let Some(sp_name) = arg.as_str() {
                    result.push(sp_name.to_string());
                }
            }
            return Some(result);
        }
    }
    None
}

fn get_std_api_signature_json() -> Value {
    serde_json::from_str(include_str!("../utils/data/std_sig.json")).expect("Unable to parse JSON")
}

pub fn access_ident_recursive(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Path(syn::ExprPath { path, .. }) => {
            if path.segments.len() == 1 {
                let ident = path.segments[0].ident.to_string();
                Some((ident, Vec::new()))
            } else {
                None
            }
        }
        Expr::Field(syn::ExprField { base, member, .. }) => {
            let (base_ident, mut fields) = if let Some((base_ident, fields)) = access_ident_recursive(base) {
                (base_ident, fields)
            } else {
                return None;
            };
            let field_name = match member {
                syn::Member::Named(ident) => ident.to_string(),
                syn::Member::Unnamed(index) => index.index.to_string(),
            };
            fields.push(field_name);
            Some((base_ident, fields))
        }
        _ => None,
    }
}

pub fn parse_expr_into_number(expr: &Expr) -> Option<usize> {
    if let Expr::Lit(expr_lit) = expr {
        if let syn::Lit::Int(lit_int) = &expr_lit.lit {
            return lit_int.base10_parse::<usize>().ok();
        }
    }
    None
}

pub fn match_ty_with_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    if let Some(primitive_ty) = match_primitive_type(tcx, type_ident.clone()) {
        return Some(primitive_ty);
    }
    find_generic_param(tcx, def_id, type_ident)
}

fn match_primitive_type<'tcx>(tcx: TyCtxt<'tcx>, type_ident: String) -> Option<Ty<'tcx>> {
    match type_ident.as_str() {
        "i8" => Some(tcx.types.i8),
        "i16" => Some(tcx.types.i16),
        "i32" => Some(tcx.types.i32),
        "i64" => Some(tcx.types.i64),
        "i128" => Some(tcx.types.i128),
        "isize" => Some(tcx.types.isize),
        "u8" => Some(tcx.types.u8),
        "u16" => Some(tcx.types.u16),
        "u32" => Some(tcx.types.u32),
        "u64" => Some(tcx.types.u64),
        "u128" => Some(tcx.types.u128),
        "usize" => Some(tcx.types.usize),
        "f16" => Some(tcx.types.f16),
        "f32" => Some(tcx.types.f32),
        "f64" => Some(tcx.types.f64),
        "f128" => Some(tcx.types.f128),
        "bool" => Some(tcx.types.bool),
        "char" => Some(tcx.types.char),
        "str" => Some(tcx.types.str_),
        _ => None,
    }
}

fn find_generic_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    let (_, param_tys) = parse_signature(tcx, def_id);
    for &ty in &param_tys {
        if let Some(found) = find_generic_in_ty(tcx, ty, &type_ident) {
            return Some(found);
        }
    }
    None
}

fn find_generic_in_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    type_ident: &str,
) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::Param(param_ty) => {
            if param_ty.name.as_str() == type_ident {
                return Some(ty);
            }
        }
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) | TyKind::Slice(ty) | TyKind::Array(ty, _) => {
            if let Some(found) = find_generic_in_ty(tcx, *ty, type_ident) {
                return Some(found);
            }
        }
        TyKind::Tuple(tys) => {
            for tuple_ty in tys.iter() {
                if let Some(found) = find_generic_in_ty(tcx, tuple_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        TyKind::Adt(adt_def, substs) => {
            let name = tcx.item_name(adt_def.did()).to_string();
            if name == type_ident {
                return Some(ty);
            }
            for field in adt_def.all_fields() {
                let field_ty = field.ty(tcx, substs);
                if let Some(found) = find_generic_in_ty(tcx, field_ty, type_ident) {
                    return Some(found);
                }
            }
        }
        _ => {}
    }
    None
}

fn get_struct_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        if let Some(impl_id) = assoc_item.impl_container(tcx) {
            let ty = tcx.type_of(impl_id).skip_binder();
            let type_name = ty.to_string();
            let struct_name = type_name
                .split('<')
                .next()
                .unwrap_or("")
                .split("::")
                .last()
                .unwrap_or("")
                .to_string();
            return Some(struct_name);
        }
    }
    None
}

fn check_safety(tcx: TyCtxt<'_>, def_id: DefId) -> Safety {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety()
}
