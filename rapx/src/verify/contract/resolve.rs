//! Expression / argument resolution: `syn::Expr` → semantic values.
//!
//! The numeric-expression layer is parsed by the pest grammar (`pest_conv.rs`);
//! everything that still needs rustc's type context or `syn` structure lives
//! here: places (via `place.rs`), const generics, builtin integer bounds, the
//! `x.len()` sugar, tag argument types/targets, and `ValidNum` predicates.

use quote::ToTokens;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericParamDefKind, Ty, TyCtxt};
use safety_parser::syn::{Expr, Lit};

use crate::helpers::fn_info::parse_expr_into_number;
use crate::helpers::name::{access_ident_recursive, match_ty_with_ident};

use super::place;
use super::types::{ContractExpr, NumericPredicate, PropertyArg, RelOp};

pub(crate) fn parse_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
    sp: &str,
) -> ContractExpr<'tcx> {
    // `x.len` / `x.len()` sugar -> len(x).
    if let Expr::Field(expr_field) = expr
        && matches!(&expr_field.member, safety_parser::syn::Member::Named(ident) if ident == "len")
    {
        return ContractExpr::Len(Box::new(parse_contract_expr(
            tcx,
            def_id,
            &expr_field.base,
            sp,
        )));
    }
    if let Expr::MethodCall(expr_method) = expr
        && expr_method.method == "len"
        && expr_method.args.is_empty()
    {
        return ContractExpr::Len(Box::new(parse_contract_expr(
            tcx,
            def_id,
            &expr_method.receiver,
            sp,
        )));
    }

    // A place (fields, projections), a const generic, or a builtin constant.
    if let Some(place) = place::parse_contract_place(tcx, def_id, expr) {
        return ContractExpr::Place(place);
    }
    if let Some(e) = parse_const_param(tcx, def_id, expr) {
        return e;
    }
    if let Some(value) = parse_builtin_const(tcx, expr) {
        return ContractExpr::Const(value);
    }
    if let Some(value) = parse_expr_into_number(expr) {
        return ContractExpr::new_value(value);
    }
    rap_debug!(
        "Numeric expression in {:?} could not be resolved: {:?}",
        sp,
        expr
    );
    ContractExpr::Unknown
}

pub(crate) fn resolve_type_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str) -> Option<Ty<'tcx>> {
    if name == "Self" {
        let sig = tcx.fn_sig(def_id).skip_binder();
        return sig.inputs().skip_binder().first().copied();
    }
    match_ty_with_ident(tcx, def_id, name.to_string())
}

pub(crate) fn int_type_min_max<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u128, u128)> {
    use rustc_middle::ty::IntTy;
    use rustc_middle::ty::UintTy;
    let bits: u32 = match ty.kind() {
        rustc_middle::ty::TyKind::Uint(ut) => match ut {
            UintTy::U8 => 8,
            UintTy::U16 => 16,
            UintTy::U32 => 32,
            UintTy::U64 => 64,
            UintTy::U128 => 128,
            UintTy::Usize => tcx.data_layout.pointer_size().bits() as u32,
        },
        rustc_middle::ty::TyKind::Int(it) => match it {
            IntTy::I8 => 8,
            IntTy::I16 => 16,
            IntTy::I32 => 32,
            IntTy::I64 => 64,
            IntTy::I128 => 128,
            IntTy::Isize => tcx.data_layout.pointer_size().bits() as u32,
        },
        _ => return None,
    };
    if bits == 0 {
        return None;
    }
    match ty.kind() {
        rustc_middle::ty::TyKind::Uint(_) => {
            let max = if bits == 128 {
                u128::MAX
            } else {
                (1u128 << bits) - 1
            };
            Some((0, max))
        }
        rustc_middle::ty::TyKind::Int(_) => {
            let max = (1u128 << (bits - 1)) - 1;
            let min = max + 1;
            Some((min, max))
        }
        _ => None,
    }
}

fn parse_builtin_const<'tcx>(tcx: TyCtxt<'tcx>, expr: &Expr) -> Option<u128> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };
    let mut segments = expr_path.path.segments.iter();
    let first = segments.next()?.ident.to_string();
    let second = segments.next()?.ident.to_string();
    if segments.next().is_some() || second != "MAX" {
        return None;
    }

    let pointer_bits = tcx.data_layout.pointer_size().bits();
    match first.as_str() {
        "isize" => Some((1_u128 << (pointer_bits - 1)) - 1),
        "usize" => Some((1_u128 << pointer_bits) - 1),
        _ => None,
    }
}

fn parse_const_param<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<ContractExpr<'tcx>> {
    let Expr::Path(expr_path) = expr else {
        return None;
    };
    let ident = expr_path.path.get_ident()?.to_string();
    let mut generics = Some(tcx.generics_of(def_id));
    while let Some(current) = generics {
        if let Some(param) = current.own_params.iter().find(|param| {
            matches!(param.kind, GenericParamDefKind::Const { .. })
                && param.name.as_str() == ident
        }) {
            return Some(ContractExpr::ConstParam {
                index: param.index,
                name: ident,
            });
        }
        generics = current.parent.map(|parent| tcx.generics_of(parent));
    }
    None
}

pub(crate) fn parse_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
    sp: &str,
) -> Option<Ty<'tcx>> {
    let ty_ident_full = access_ident_recursive(expr);
    if ty_ident_full.is_none() {
        rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
        return None;
    }
    let ty_ident = ty_ident_full.unwrap().0;
    let ty = match_ty_with_ident(tcx, def_id, ty_ident);
    if ty.is_none() {
        rap_debug!("Cannot get type in {:?} Tag!", sp);
    }
    ty
}

pub(crate) fn parse_target_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> PropertyArg<'tcx> {
    // For simple identifiers that aren't local variables (e.g., lifetime param
    // 'a parsed as ident `a`), store as Ident rather than Expr (which would
    // become Unknown).
    if let Expr::Path(expr_path) = expr {
        if let Some(ident) = expr_path.path.get_ident() {
            let s = ident.to_string();
            if s != "return"
                && !s.starts_with("Arg_")
                && place::parse_expr_into_local_and_ty(tcx, def_id, expr).is_none()
            {
                return PropertyArg::Ident(s);
            }
        }
    }
    place::parse_contract_place(tcx, def_id, expr)
        .map(|p| PropertyArg::Expr(ContractExpr::Place(p)))
        .unwrap_or_else(|| PropertyArg::Expr(parse_contract_expr(tcx, def_id, expr, "target")))
}

pub(crate) fn parse_valid_num<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    exprs: &[Expr],
) -> Vec<NumericPredicate<'tcx>> {
    match exprs {
        [] => Vec::new(),
        [expr] => parse_numeric_predicate(tcx, def_id, expr).into_iter().collect(),
        [value, range, ..] => {
            if let Some(predicates) = parse_interval_predicates(tcx, def_id, value, range) {
                predicates
            } else {
                parse_numeric_predicate(tcx, def_id, value)
                    .into_iter()
                    .collect()
            }
        }
    }
}

fn parse_numeric_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<NumericPredicate<'tcx>> {
    let text = expr.to_token_stream().to_string();
    super::pest_conv::parse_predicate_pest(tcx, def_id, &text)
}

pub(crate) fn expr_to_pest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> ContractExpr<'tcx> {
    let text = expr.to_token_stream().to_string();
    super::pest_conv::parse_expr_pest(tcx, def_id, &text)
}

fn parse_interval_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    value: &Expr,
    range: &Expr,
) -> Option<Vec<NumericPredicate<'tcx>>> {
    match range {
        Expr::Array(array) if array.elems.len() == 2 => {
            let mut elems = array.elems.iter();
            let lower = elems.next().unwrap();
            let upper = elems.next().unwrap();
            Some(build_interval_predicates(
                tcx, def_id, value, lower, true, upper, true,
            ))
        }
        Expr::Lit(expr_lit) => {
            let Lit::Str(range_lit) = &expr_lit.lit else {
                return None;
            };
            parse_string_interval(tcx, def_id, value, &range_lit.value())
        }
        _ => None,
    }
}

fn parse_string_interval<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    value: &Expr,
    raw_range: &str,
) -> Option<Vec<NumericPredicate<'tcx>>> {
    let trimmed = raw_range.trim();
    if trimmed.len() < 5 {
        return None;
    }

    let lower_inclusive = trimmed.starts_with('[');
    let upper_inclusive = trimmed.ends_with(']');
    if !(lower_inclusive || trimmed.starts_with('('))
        || !(upper_inclusive || trimmed.ends_with(')'))
    {
        return None;
    }

    let body = &trimmed[1..trimmed.len() - 1];
    let (lower_raw, upper_raw) = body.split_once(',')?;
    let lower = safety_parser::syn::parse_str::<Expr>(lower_raw.trim()).ok()?;
    let upper = safety_parser::syn::parse_str::<Expr>(upper_raw.trim()).ok()?;

    Some(build_interval_predicates(
        tcx,
        def_id,
        value,
        &lower,
        lower_inclusive,
        &upper,
        upper_inclusive,
    ))
}

fn build_interval_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    value: &Expr,
    lower: &Expr,
    lower_inclusive: bool,
    upper: &Expr,
    upper_inclusive: bool,
) -> Vec<NumericPredicate<'tcx>> {
    let value_expr = expr_to_pest(tcx, def_id, value);
    let lower_expr = expr_to_pest(tcx, def_id, lower);
    let upper_expr = expr_to_pest(tcx, def_id, upper);
    vec![
        NumericPredicate::new(
            lower_expr,
            if lower_inclusive {
                RelOp::Le
            } else {
                RelOp::Lt
            },
            value_expr.clone(),
        ),
        NumericPredicate::new(
            value_expr,
            if upper_inclusive {
                RelOp::Le
            } else {
                RelOp::Lt
            },
            upper_expr,
        ),
    ]
}

/// Extract the inner type from an `Expr::Array` (the `[T]` notation in
/// `SplitTransmute([T], [U])`), then resolve it via `parse_type`.
pub(crate) fn unwrap_array_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> Option<Ty<'tcx>> {
    if let Expr::Array(arr) = expr
        && arr.elems.len() == 1
    {
        return parse_type(tcx, def_id, &arr.elems[0], "SplitTransmute");
    }
    parse_type(tcx, def_id, expr, "SplitTransmute")
}
