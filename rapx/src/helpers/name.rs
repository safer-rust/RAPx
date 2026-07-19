use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgKind, Ty, TyCtxt, TyKind};
use serde_json::Value;
use syn::Expr;

/// Clean a `DefId` debug representation into a human-readable path.
///
/// The raw `{:?}` output of `DefId` includes crate hashes and
/// generic-parameter brackets.  This function normalises the leading
/// crate name (`core` / `std` / `alloc`) and replaces mangled generic
/// sections with the implementing struct name (via `get_struct_name`).
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

/// Extract the implementing struct name from a `DefId` that belongs to an
/// associated item (method / associated function).
pub fn get_struct_name(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
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

/// Return the resolved `self` type for a method whose `DefId` points to an
/// associated item that lives inside an `impl` block returning an ADT, or for
/// a struct/enum DefId directly (needed for parsing struct-invariant annotations).
pub fn get_struct_self_ty<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Ty<'tcx>> {
    if let Some(assoc_item) = tcx.opt_associated_item(def_id) {
        let impl_id = assoc_item.impl_container(tcx)?;
        let self_ty = tcx.type_of(impl_id).skip_binder();
        match self_ty.kind() {
            TyKind::Adt(_, _) => return Some(self_ty),
            _ => return None,
        }
    }
    let def_kind = tcx.def_kind(def_id);
    if matches!(def_kind, rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Enum) {
        let self_ty = tcx.type_of(def_id).skip_binder();
        match self_ty.kind() {
            TyKind::Adt(_, _) => return Some(self_ty),
            _ => {}
        }
    }
    None
}

/// Return the JSON value loaded from the pre-computed standard-library
/// signature map (`data/std_sig.json`).
pub fn get_std_api_signature_json() -> Value {
    serde_json::from_str(include_str!("data/std_sig.json")).expect("Unable to parse JSON")
}

/// Look up known argument names for standard-library APIs.
///
/// The lookup key is the cleaned `DefId` path (see
/// `get_cleaned_def_path_name`).  When no names are recorded the list is
/// filled with numeric defaults (`"0"`, `"1"`, …).
pub fn get_known_std_names<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<String>> {
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

/// Parse argument names and types from a local function's HIR body.
/// Recursively unwrap Ref/Paren patterns to find the inner binding identifier.
/// Needed because `&self` / `&mut self` produce PatKind::Ref(PatKind::Binding(...)).
fn extract_pat_ident(pat: &rustc_hir::Pat<'_>) -> Option<rustc_span::symbol::Ident> {
    match &pat.kind {
        rustc_hir::PatKind::Binding(_, _, ident, _) => Some(*ident),
        rustc_hir::PatKind::Ref(inner, ..) => extract_pat_ident(inner),
        _ => None,
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
        let ident = extract_pat_ident(&param.pat);
        match ident {
            Some(name) => {
                param_names.push(name.name.to_string());
            }
            None => {
                param_names.push(String::new());
            }
        }
        param_tys.push(typeck_results.pat_ty(param.pat));
    }
    (param_names, param_tys)
}

/// Parse argument names and types from an external function's type signature.
///
/// First tries the pre-defined standard-library names; falls back to
/// numeric indices (`"0"`, `"1"`, …).
pub fn parse_outside_signature<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> (Vec<String>, Vec<Ty<'tcx>>) {
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();

    if let Some(args_name) = get_known_std_names(tcx, def_id) {
        return (args_name, param_tys);
    }

    let args_name = (0..param_tys.len()).map(|i| format!("{}", i)).collect();
    (args_name, param_tys)
}

/// Extract parameter names from a HIR trait method declaration and pair them
/// with types from the function signature.  Handles `TraitFn::Required` (names
/// directly in the declaration) and `TraitFn::Provided` (names in the body).
fn parse_trait_fn_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Option<(Vec<String>, Vec<Ty<'tcx>>)> {
    let local_def_id = def_id.as_local()?;
    if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::AssocFn) {
        return None;
    }
    let trait_item_id = rustc_hir::TraitItemId {
        owner_id: rustc_hir::OwnerId { def_id: local_def_id },
    };
    let item = tcx.hir_trait_item(trait_item_id);
    let (_sig, trait_fn) = match &item.kind {
        rustc_hir::TraitItemKind::Fn(sig, tf) => (sig, tf),
        _ => return None,
    };
    let names: Vec<String> = match trait_fn {
        rustc_hir::TraitFn::Required(param_names) => param_names
            .iter()
            .filter_map(|opt| opt.map(|ident| ident.name.to_string()))
            .collect(),
        rustc_hir::TraitFn::Provided(body_id) => {
            let body = tcx.hir_body(*body_id);
            body.params
                .iter()
                .filter_map(|param| extract_pat_ident(&param.pat).map(|i| i.name.to_string()))
                .collect()
        }
    };
    let sig = tcx.fn_sig(def_id).skip_binder();
    let param_tys: Vec<Ty<'tcx>> = sig.inputs().skip_binder().iter().copied().collect();
    if names.len() == param_tys.len() {
        Some((names, param_tys))
    } else {
        None
    }
}

/// Dispatch argument-name/type parsing to either the local HIR path or the
/// external type-based path.
pub fn parse_signature<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> (Vec<String>, Vec<Ty<'tcx>>) {
    if def_id.as_local().is_some() && tcx.is_mir_available(def_id) {
        parse_local_signature(tcx, def_id)
    } else if def_id.is_local() {
        if let Some((names, tys)) = parse_trait_fn_sig(tcx, def_id) {
            return (names, tys);
        }
        if matches!(
            tcx.def_kind(def_id),
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
        ) {
            parse_outside_signature(tcx, def_id)
        } else {
            (vec!["0".to_string()], Vec::new())
        }
    } else {
        parse_outside_signature(tcx, def_id)
    }
}

/// Walk a `syn::Expr` and produce the root identifier together with any
/// field projections.
///
/// Examples:
/// - `ptr`         → `("ptr", [])`
/// - `region.size` → `("region", ["size"])`
/// - `tuple.0.val` → `("tuple", ["0", "val"])`
pub fn access_ident_recursive(expr: &Expr) -> Option<(String, Vec<String>)> {
    match expr {
        Expr::Path(syn::ExprPath { path, .. }) => {
            if path.segments.len() == 1 {
                rap_debug!("expr2 {:?}", expr);
                let ident = path.segments[0].ident.to_string();
                Some((ident, Vec::new()))
            } else {
                None
            }
        }
        Expr::Field(syn::ExprField { base, member, .. }) => {
            let (base_ident, mut fields) =
                if let Some((base_ident, fields)) = access_ident_recursive(base) {
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

/// Match a type-identifier string to a concrete `Ty`.
///
/// Checks in order:
/// 1. Primitive types (`u32`, `bool`, …)
/// 2. Generic type parameters in the function signature or `self` type
pub fn match_ty_with_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    if let Some(primitive_ty) = match_primitive_type(tcx, type_ident.clone()) {
        return Some(primitive_ty);
    }
    if let Some(param_ty) = find_declared_generic_param(tcx, def_id, &type_ident) {
        return Some(param_ty);
    }
    find_generic_param(tcx, def_id, type_ident)
}

fn find_declared_generic_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: &str,
) -> Option<Ty<'tcx>> {
    tcx.generics_of(def_id)
        .own_params
        .iter()
        .find(|param| param.name.as_str() == type_ident)
        .map(|param| {
            tcx.mk_ty_from_kind(TyKind::Param(rustc_middle::ty::ParamTy {
                index: param.index,
                name: param.name,
            }))
        })
}

/// Match a string against Rust's primitive types, returning the
/// corresponding `Ty` from the type context.
pub fn match_primitive_type<'tcx>(tcx: TyCtxt<'tcx>, type_ident: String) -> Option<Ty<'tcx>> {
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

/// Search function parameters (and the `self` type for methods) for a
/// generic type whose name matches `type_ident`.
pub fn find_generic_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    type_ident: String,
) -> Option<Ty<'tcx>> {
    rap_debug!(
        "Searching for generic param: {} in {:?}",
        type_ident,
        def_id
    );
    let (_, param_tys) = parse_signature(tcx, def_id);
    rap_debug!("Function parameter types: {:?} of {:?}", param_tys, def_id);
    for &ty in &param_tys {
        if let Some(found) = find_generic_in_ty(tcx, ty, &type_ident) {
            return Some(found);
        }
    }

    if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
        if let Some(found) = find_generic_in_ty(tcx, struct_ty, &type_ident) {
            return Some(found);
        }
    }

    None
}

/// Recursively walk a `Ty` tree looking for a type whose name matches
/// `type_ident`.
///
/// This handles parameter types, pointers, references, slices, arrays,
/// tuples, and ADT fields.
pub fn find_generic_in_ty<'tcx>(
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
        TyKind::RawPtr(ty, _)
        | TyKind::Ref(_, ty, _)
        | TyKind::Slice(ty)
        | TyKind::Array(ty, _) => {
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
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = field.ty(tcx, substs);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = field.ty(tcx, substs).skip_norm_wip();
                if let Some(found) = find_generic_in_ty(tcx, field_ty, type_ident) {
                    return Some(found);
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    if let Some(found) = find_generic_in_ty(tcx, subst_ty, type_ident) {
                        return Some(found);
                    }
                }
            }
        }
        _ => {}
    }
    None
}
