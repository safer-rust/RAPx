//! Place resolution: `syn::Expr` → `ContractPlace`.
//!
//! Resolve contract places against rustc types and bind them to MIR locals.

use crate::util::mir_utils;
use rustc_abi::FieldIdx;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use syn::Expr;

use crate::util::fn_info::{FnKind, get_type};
use crate::util::name::{access_ident_recursive, get_adt_self_ty, parse_signature};

use super::{ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, PropertyArg, PropertyKind};

type PlacePath<'tcx> = (usize, Vec<usize>, Ty<'tcx>);

/// Extract the bound slice and index locals from an `InBound` property.
pub(crate) fn index_access_locals(property: &Property<'_>) -> Option<(Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::InBound { return None }
    let Some(ContractExpr::IndexAccess { slice, index }) = atom.args.first().and_then(PropertyArg::expr)
    else { return None };
    let (ContractExpr::Place(slice), ContractExpr::Place(index)) = (slice.as_ref(), index.as_ref())
    else { return None };
    (slice.projections.is_empty() && index.projections.is_empty())
        .then(|| (slice.base.to_local(), index.base.to_local()))
}

/// Extract the bound result, base, and index locals from a `SliceOffset` property.
pub(crate) fn slice_offset_locals(property: &Property<'_>) -> Option<(Local, Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::SliceOffset { return None }
    let locals: Option<Vec<Local>> = atom.args.iter().map(|arg| {
        let Some(ContractExpr::Place(place)) = arg.expr() else { return None };
        place.projections.is_empty().then(|| place.base.to_local())
    }).collect();
    let locals = locals?;
    let [dest, base, index] = locals.as_slice() else { return None };
    Some((*dest, *base, *index))
}

/// Bind a callee property to the caller's argument and return locals.
pub(crate) fn bind_call_property<'tcx>(property: &mut Property<'tcx>, args: &[Option<Local>], destination: Local) -> bool {
    let mut bound = true;
    map_property_places(property, &mut |base| {
        let local = match *base {
            PlaceBase::Return | PlaceBase::Local(0) => Some(destination),
            PlaceBase::Arg(index) => args.get(index).copied().flatten(),
            PlaceBase::Local(index) => args.get(index - 1).copied().flatten(),
        };
        if let Some(local) = local {
            *base = PlaceBase::Local(local.as_usize());
        } else {
            bound = false;
        }
    });
    bound
}

/// Rebind every place in a struct invariant to a MIR local.
pub(crate) fn rebind_property_place<'tcx>(property: &mut Property<'tcx>, local: Local) {
    map_property_places(property, &mut |base| *base = PlaceBase::Local(local.as_usize()));
}

fn map_property_places<'tcx>(property: &mut Property<'tcx>, map: &mut impl FnMut(&mut PlaceBase)) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                match arg {
                    PropertyArg::Expr(expr) | PropertyArg::ForEach(expr) => map_expr_places(expr, map),
                    PropertyArg::Predicates(preds) => {
                        for pred in preds {
                            map_expr_places(&mut pred.lhs, map);
                            map_expr_places(&mut pred.rhs, map);
                        }
                    }
                    _ => {}
                }
            }
        }
        Property::And(and) => {
            for conjunct in &mut and.conjuncts { map_property_places(conjunct, map) }
        }
        Property::Or(or) => {
            for disjunct in &mut or.disjuncts { map_property_places(disjunct, map) }
        }
    }
}

fn map_expr_places<'tcx>(expr: &mut ContractExpr<'tcx>, map: &mut impl FnMut(&mut PlaceBase)) {
    match expr {
        ContractExpr::Place(cp) => map(&mut cp.base),
        ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) | ContractExpr::Unary { expr: inner, .. } => {
            map_expr_places(inner, map)
        }
        ContractExpr::IndexAccess { slice, index } => {
            map_expr_places(slice, map);
            map_expr_places(index, map);
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            map_expr_places(lhs, map);
            map_expr_places(rhs, map);
        }
        ContractExpr::MethodCall { receiver, args, .. } => {
            map_expr_places(receiver, map);
            for arg in args { map_expr_places(arg, map) }
        }
        ContractExpr::If { cond, then_expr, else_expr } => {
            map_expr_places(&mut cond.lhs, map);
            map_expr_places(&mut cond.rhs, map);
            map_expr_places(then_expr, map);
            map_expr_places(else_expr, map);
        }
        _ => {}
    }
}

pub(crate) fn parse_contract_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<ContractPlace> {
    if let Expr::MethodCall(expr_method) = expr
        && (expr_method.method == "iter" || expr_method.method == "each_element")
            && expr_method.args.is_empty()
        {
            let mut place = parse_contract_place(tcx, def_id, &expr_method.receiver)?;
            place.projections.push(ContractProjection::ForEach);
            return Some(place);
        }

    if let Expr::MethodCall(expr_method) = expr
        && expr_method.method == "unwrap_some" && expr_method.args.is_empty()
            && let Some((base, fields, recv_ty)) =
                parse_expr_into_local_and_ty(tcx, def_id, &expr_method.receiver)
            {
                let peeled_ty = recv_ty.peel_refs();
                if let TyKind::Adt(adt_def, _) = peeled_ty.kind()
                    && adt_def.is_enum() {
                        let some_variant =
                            adt_def.variants().iter_enumerated().find_map(|(vidx, v)| {
                                if v.name.to_string() == "Some" {
                                    Some(vidx.as_usize())
                                } else {
                                    None
                                }
                            });
                        if let Some(variant_index) = some_variant {
                            let mut place = ContractPlace::local(base, fields);
                            place
                                .projections
                                .push(ContractProjection::Downcast { variant_index });
                            return Some(place);
                        }
                    }
            }

    if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
        return Some(ContractPlace::local(base, fields));
    }
    parse_return_field_place(tcx, def_id, expr).or_else(|| parse_named_place(expr))
}

/// Resolve a place rooted at the function's return value with field projections
/// (`return.0`, `return.pointer`). `parse_named_place` only handles a *bare*
/// `return` (no projections); this walks the field chain against the return type.
fn parse_return_field_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<ContractPlace> {
    let mut field_names: Vec<String> = Vec::new();
    let mut cur = expr;
    loop {
        match cur {
            Expr::Return(expr_return) if expr_return.expr.is_none() => break,
            Expr::Field(expr_field) => {
                field_names.push(match &expr_field.member {
                    syn::Member::Named(ident) => ident.to_string(),
                    syn::Member::Unnamed(index) => index.index.to_string(),
                });
                cur = &expr_field.base;
            }
            _ => return None,
        }
    }
    if field_names.is_empty() {
        return None;
    }
    field_names.reverse();
    let ret_ty = tcx.fn_sig(def_id).skip_binder().output().skip_binder();
    let (field_indices, _) = walk_fields(tcx, ret_ty, Vec::new(), &field_names)?;
    Some(ContractPlace::local(0, field_indices))
}

fn parse_named_place(expr: &Expr) -> Option<ContractPlace> {
    // A bare `return` parses as `syn::Expr::Return { expr: None }` (a keyword,
    // not an `Expr::Path`), so `parse_named_place`'s `Expr::Path` arm below
    // never sees it.  Resolve it to the return-value place here so it works
    // inside nested numeric expressions (e.g. the slice invariant's
    // `Allocated($self, $elem, $self.len())` for the return type, whose `$self`
    // is substituted with the `return` placeholder).
    if let Expr::Return(expr_return) = expr
        && expr_return.expr.is_none()
    {
        return Some(ContractPlace {
            base: PlaceBase::Return,
            projections: Vec::new(),
        });
    }
    if let Expr::Path(expr_path) = expr
        && let Some(ident) = expr_path.path.get_ident() {
            let s = ident.to_string();
            if let Some(num_str) = s.strip_prefix("Arg_")
                && let Ok(idx) = num_str.parse::<usize>() {
                    return Some(ContractPlace::arg(idx));
                }
        }
    None
}

pub(crate) fn parse_expr_into_local_and_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<PlacePath<'tcx>> {
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
) -> Option<PlacePath<'tcx>> {
    let (param_names, param_tys) = parse_signature(tcx, def_id);
    if param_names.first().is_some_and(|name| name != "0")
        && let Some(param_index) = param_names.iter().position(|name| name == base_ident) {
            return resolve_projection_from_base_ident(
                tcx,
                fields.to_vec(),
                param_index + 1,
                param_tys[param_index],
            );
        }

    if let Some(struct_ty) = get_adt_self_ty(tcx, def_id) {
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

/// Walk field names, retaining their indices and the final type.
fn walk_fields<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut current_ty: Ty<'tcx>,
    mut field_indices: Vec<usize>,
    fields: &[String],
) -> Option<(Vec<usize>, Ty<'tcx>)> {
    for field_name in fields {
        let (field_idx, field_ty) = resolve_next_field(tcx, current_ty, field_name)?;
        current_ty = field_ty;
        field_indices.push(field_idx);
    }
    Some((field_indices, current_ty))
}

fn resolve_projection_from_base_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    fields: Vec<String>,
    base_local: usize,
    base_ty: Ty<'tcx>,
) -> Option<PlacePath<'tcx>> {
    let (field_indices, current_ty) = walk_fields(tcx, base_ty, Vec::new(), &fields)?;
    Some((base_local, field_indices, current_ty))
}

fn resolve_projection_from_struct_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    base_ident: String,
    fields: Vec<String>,
    struct_ty: Ty<'tcx>,
) -> Option<PlacePath<'tcx>> {
    let (field_idx, field_ty) = resolve_next_field(tcx, struct_ty, &base_ident)?;
    let (mut field_indices, current_ty) = walk_fields(tcx, field_ty, vec![field_idx], &fields)?;

    let base_local = if get_type(tcx, def_id) == FnKind::Constructor {
        0
    } else {
        1
    };

    // For a "wrapped" constructor (`Result<Self>` / `Option<Self>`), the struct
    // lives inside the `Ok`/`Some` variant (field 0 of the enum). Prepend that
    // field access so the invariant's place resolves through the variant's data
    // (e.g. `ptr` -> `Return.Field(0).Field(0)`).
    if base_local == 0 && crate::util::fn_info::returns_wrapped_self(tcx, def_id) {
        field_indices.insert(0, 0);
    }

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
        if let Ok(field_idx) = field_name.parse::<usize>()
            && field_idx < variant.fields.len() {
                let field_ty = mir_utils::field_ty(
                    tcx,
                    &variant.fields[FieldIdx::from_usize(field_idx)],
                    arg_list,
                );
                return Some((field_idx, field_ty));
            }
        if let Some((idx, _)) = variant
            .fields
            .iter()
            .enumerate()
            .find(|(_, f)| f.ident(tcx).name.to_string() == field_name)
        {
            let field_ty = mir_utils::field_ty(
                tcx,
                &variant.fields[FieldIdx::from_usize(idx)],
                arg_list,
            );
            return Some((idx, field_ty));
        }
    }
    None
}

/// Strip a `ForEach` projection from a property argument.
pub(crate) fn strip_for_each<'tcx>(arg: &mut PropertyArg<'tcx>) -> bool {
    if let PropertyArg::Expr(ContractExpr::Place(place)) = arg
        && place
            .projections
            .iter()
            .any(|p| matches!(p, ContractProjection::ForEach))
        {
            place
                .projections
                .retain(|p| !matches!(p, ContractProjection::ForEach));
            return true;
        }
    false
}

/// Check if the given expression refers to a function parameter whose type is
/// an array whose elements should be checked individually.
pub(crate) fn is_array_for_each<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> bool {
    let Some(place) = parse_contract_place(tcx, def_id, expr) else { return false };
    let param_idx = match place.base {
        PlaceBase::Arg(n) => n,
        PlaceBase::Local(n) => match n.checked_sub(1) { Some(n) => n, None => return false },
        _ => return false,
    };
    let fn_sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    fn_sig.inputs().get(param_idx).is_some_and(|ty| matches!(ty.kind(), TyKind::Array(..)))
}

/// The field name selected by the first `Field` projection of `place` on
/// `adt_def_id` (e.g. `ptr` in `self.ptr`), if any.
pub(crate) fn field_name_from_place<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def_id: DefId,
    place: &ContractPlace,
) -> Option<String> {
    // `adt_def_id` may be a function/impl def-id (e.g. from a `requires`
    // annotation on a method); only resolve fields on real ADTs.
    if !matches!(
        tcx.def_kind(adt_def_id),
        DefKind::Struct | DefKind::Enum | DefKind::Union
    ) {
        return None;
    }
    let idx = place.projections.iter().find_map(|p| match p {
        ContractProjection::Field { index } => Some(*index),
        _ => None,
    })?;
    let adt = tcx.adt_def(adt_def_id);
    let field = adt
        .non_enum_variant()
        .fields
        .get(FieldIdx::from_usize(idx))?;
    Some(field.name.to_string())
}

/// The field name targeted by an `Allocated`/`Owning`-style property argument,
/// whether it was parsed as a bare identifier or as a resolved place.
pub(crate) fn field_name_from_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def_id: DefId,
    arg: &PropertyArg<'tcx>,
) -> Option<String> {
    match arg {
        PropertyArg::Ident(s) => Some(s.clone()),
        PropertyArg::Expr(ContractExpr::Place(place)) | PropertyArg::ForEach(ContractExpr::Place(place)) => {
            field_name_from_place(tcx, adt_def_id, place)
        }
        _ => None,
    }
}
