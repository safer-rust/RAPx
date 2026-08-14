//! Place resolution: `syn::Expr` → `ContractPlace`.
//!
//! Semantic resolution of contract places (arguments, locals, field
//! projections, `iter()`/`each_element()` element projection, `unwrap_some()`
//! enum downcast) against rustc's type context.  This layer depends only on
//! `types.rs` and crate helpers, so both the property builder (`builder.rs`)
//! and the pest-based expression converter (`pest_conv.rs`) can share it
//! without a dependency cycle.

use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use safety_parser::syn::Expr;

use crate::helpers::fn_info::{FnKind, get_type};
use crate::helpers::name::{access_ident_recursive, get_struct_self_ty, parse_signature};

use super::types::{ContractExpr, ContractPlace, ContractProjection, PlaceBase, PropertyArg};

pub(crate) fn parse_contract_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<ContractPlace<'tcx>> {
    // Handle .iter() / .each_element() — iterate over slice elements.
    if let Expr::MethodCall(expr_method) = expr {
        if (expr_method.method == "iter" || expr_method.method == "each_element")
            && expr_method.args.is_empty()
        {
            let mut place = parse_contract_place(tcx, def_id, &expr_method.receiver)?;
            place.projections.push(ContractProjection::IterElements);
            return Some(place);
        }
    }

    // Handle .unwrap_some() method call — downcast to the Some variant.
    if let Expr::MethodCall(expr_method) = expr {
        if expr_method.method == "unwrap_some" && expr_method.args.is_empty() {
            if let Some((base, fields, recv_ty)) =
                parse_expr_into_local_and_ty(tcx, def_id, &expr_method.receiver)
            {
                let peeled_ty = recv_ty.peel_refs();
                if let TyKind::Adt(adt_def, _) = peeled_ty.kind() {
                    if adt_def.is_enum() {
                        let some_variant =
                            adt_def.variants().iter_enumerated().find_map(|(vidx, v)| {
                                if v.name.to_string() == "Some" {
                                    Some(vidx.as_usize())
                                } else {
                                    None
                                }
                            });
                        if let Some(variant_index) = some_variant {
                            let mut projections: Vec<ContractProjection> = fields
                                .into_iter()
                                .map(|(index, ty)| ContractProjection::Field {
                                    index,
                                    ty: Some(ty),
                                })
                                .collect();
                            projections.push(ContractProjection::Downcast { variant_index });
                            let base_enum = if base == 0 {
                                PlaceBase::Return
                            } else {
                                PlaceBase::Local(base)
                            };
                            return Some(ContractPlace {
                                base: base_enum,
                                projections,
                            });
                        }
                    }
                }
            }
        }
    }

    if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
        return Some(ContractPlace::local(base, fields));
    }
    parse_named_place(expr)
}

fn parse_named_place<'tcx>(expr: &Expr) -> Option<ContractPlace<'tcx>> {
    if let Expr::Path(expr_path) = expr {
        if let Some(ident) = expr_path.path.get_ident() {
            let s = ident.to_string();
            if let Some(num_str) = s.strip_prefix("Arg_") {
                if let Ok(idx) = num_str.parse::<usize>() {
                    return Some(ContractPlace::arg(idx));
                }
            }
            if s == "return" {
                return Some(ContractPlace {
                    base: PlaceBase::Return,
                    projections: Vec::new(),
                });
            }
        }
    }
    None
}

pub(crate) fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    if let Some((base_ident, fields)) = access_ident_recursive(expr) {
        return resolve_place_from_ident(tcx, def_id, &base_ident, &fields);
    }
    None
}

/// Resolve a place given its base identifier and field-name list directly,
/// without going through a `syn` expression.  Used by the pest converter.
pub(crate) fn resolve_place_from_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    base_ident: &str,
    fields: &[String],
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let (param_names, param_tys) = parse_signature(tcx, def_id);
    if param_names[0] != "0" {
        if let Some(param_index) = param_names.iter().position(|name| name == base_ident) {
            return resolve_projection_from_base_ident(
                tcx,
                base_ident.to_string(),
                fields.to_vec(),
                param_index + 1,
                param_tys[param_index],
            );
        }
    }

    if let Some(struct_ty) = get_struct_self_ty(tcx, def_id) {
        return resolve_projection_from_struct_ident(
            tcx,
            def_id,
            base_ident.to_string(),
            fields.to_vec(),
            struct_ty,
        );
    }
    None
}

fn resolve_projection_from_base_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    _base_ident: String,
    fields: Vec<String>,
    base_local: usize,
    base_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let mut current_ty = base_ty;
    let mut field_indices = Vec::new();
    for field_name in fields {
        let Some((field_idx, field_ty)) = resolve_next_field(tcx, current_ty, &field_name) else {
            return None;
        };
        current_ty = field_ty;
        field_indices.push((field_idx, current_ty));
    }
    Some((base_local, field_indices, current_ty))
}

fn resolve_projection_from_struct_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    base_ident: String,
    fields: Vec<String>,
    struct_ty: Ty<'tcx>,
) -> Option<(usize, Vec<(usize, Ty<'tcx>)>, Ty<'tcx>)> {
    let Some((field_idx, field_ty)) = resolve_next_field(tcx, struct_ty, &base_ident) else {
        return None;
    };

    let mut current_ty = field_ty;
    let mut field_indices = vec![(field_idx, current_ty)];
    for field_name in fields {
        let Some((next_field_idx, next_field_ty)) =
            resolve_next_field(tcx, current_ty, &field_name)
        else {
            return None;
        };
        current_ty = next_field_ty;
        field_indices.push((next_field_idx, current_ty));
    }

    let base_local = if get_type(tcx, def_id) == FnKind::Constructor {
        0
    } else {
        1
    };

    Some((base_local, field_indices, current_ty))
}

fn resolve_next_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    base_ty: Ty<'tcx>,
    field_name: &str,
) -> Option<(usize, Ty<'tcx>)> {
    let peeled_ty = base_ty.peel_refs();
    if let TyKind::Adt(adt_def, arg_list) = *peeled_ty.kind() {
        if !adt_def.is_struct() && !adt_def.is_union() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Ok(field_idx) = field_name.parse::<usize>() {
            if field_idx < variant.fields.len() {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)].ty(tcx, arg_list);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = variant.fields[FieldIdx::from_usize(field_idx)]
                    .ty(tcx, arg_list)
                    .skip_norm_wip();
                return Some((field_idx, field_ty));
            }
        }
        if let Some((idx, _)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
        {
            #[cfg(not(rapx_rustc_ge_198))]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)].ty(tcx, arg_list);
            #[cfg(rapx_rustc_ge_198)]
            let field_ty = variant.fields[FieldIdx::from_usize(idx)]
                .ty(tcx, arg_list)
                .skip_norm_wip();
            return Some((idx, field_ty));
        }
    }
    None
}

/// Strip `IterElements` from a property arg and return the container place
/// (without the projection) if `IterElements` was present.
pub(crate) fn strip_iter_elements<'tcx>(
    arg: &mut PropertyArg<'tcx>,
) -> Option<ContractPlace<'tcx>> {
    if let PropertyArg::Expr(ContractExpr::Place(place)) = arg {
        if place.projections.iter().any(|p| matches!(p, ContractProjection::IterElements)) {
            let mut container = place.clone();
            container.projections.retain(|p| !matches!(p, ContractProjection::IterElements));
            place.projections.retain(|p| !matches!(p, ContractProjection::IterElements));
            return Some(container);
        }
    }
    None
}

/// Check if the given expression refers to a function parameter whose type is
/// an array.  If so, return a `ContractPlace` for that parameter to be used as
/// the `for_each` container.
pub(crate) fn detect_array_for_each<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<ContractPlace<'tcx>> {
    let place = parse_contract_place(tcx, def_id, expr)?;
    let param_idx = match place.base {
        PlaceBase::Arg(n) => n,
        PlaceBase::Local(n) => {
            // Local 0 = return, locals 1.. = parameters
            n.checked_sub(1)?
        }
        _ => return None,
    };
    let fn_sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    if let Some(arg_ty) = fn_sig.inputs().get(param_idx) {
        if matches!(arg_ty.kind(), TyKind::Array(..)) {
            return Some(ContractPlace {
                base: PlaceBase::Arg(param_idx),
                projections: vec![],
            });
        }
    }
    None
}
