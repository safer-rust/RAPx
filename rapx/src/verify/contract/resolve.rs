//! Expression / argument resolution: `syn::Expr` → semantic values.
//!
//! The numeric-expression layer is parsed by the pest grammar (`pest.rs`);
//! everything that still needs rustc's type context or `syn` structure lives
//! here: places (via `place.rs`), const generics, builtin integer bounds, the
//! length calls, tag argument types/targets, and `ValidNum` predicates.

use crate::helpers::{
    fn_info::parse_expr_into_number,
    mir_utils,
    name::{access_ident_recursive, match_ty_with_ident},
};
use quote::ToTokens;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{GenericParamDefKind, IntTy, Ty, TyCtxt, UintTy};
use syn::{Expr, Lit};

use super::place;
use super::types::{ContractExpr, ContractPlace, NumericPredicate, PlaceBase, PropertyArg, RelOp};

pub(crate) fn parse_contract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
    sp: &str,
) -> ContractExpr<'tcx> {
    if let Expr::MethodCall(expr_method) = expr
        && let Some(method) = resolve_self_method(
            tcx,
            def_id,
            &expr_method.receiver,
            &expr_method.method.to_string(),
        )
        && method.is_local()
        && crate::def_ids::other_api::slice_len() != Some(method)
    {
        return ContractExpr::MethodCall {
            receiver: Box::new(parse_contract_expr(tcx, def_id, &expr_method.receiver, sp)),
            method,
            args: expr_method
                .args
                .iter()
                .map(|arg| parse_contract_expr(tcx, def_id, arg, sp))
                .collect(),
        };
    }
    if let Expr::MethodCall(expr_method) = expr
        && expr_method.method == "len"
        && expr_method.args.is_empty()
    {
        return parse_len_call(tcx, def_id, &expr_method.receiver, sp);
    }

    // A place (fields, projections) or a const generic.
    if let Some(place) = place::parse_contract_place(tcx, def_id, expr) {
        return ContractExpr::Place(place);
    }
    if let Some(e) = parse_const_param(tcx, def_id, expr) {
        return e;
    }
    if let Some(value) = parse_expr_into_number(expr) {
        return ContractExpr::new_value(value);
    }
    // A `const` item (e.g. `CAPACITY` in `ValidNum(len <= CAPACITY)`).
    if let Expr::Path(expr_path) = expr
        && let Some(ident) = expr_path.path.get_ident()
        && let Some(value) = mir_utils::resolve_const_item_value(tcx, &ident.to_string())
    {
        return ContractExpr::Const(value);
    }
    rap_warn!(
        "Numeric expression in {:?} could not be resolved: {:?} (in {})",
        sp,
        expr,
        tcx.def_path_str(def_id)
    );
    ContractExpr::Unknown
}

pub(crate) fn parse_len_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    receiver: &Expr,
    sp: &str,
) -> ContractExpr<'tcx> {
    let method = resolve_self_method(tcx, def_id, receiver, "len");
    ContractExpr::Len(
        Box::new(parse_contract_expr(tcx, def_id, receiver, sp)),
        method,
    )
}

pub(crate) fn parse_is_empty_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    receiver_text: &str,
    sp: &str,
) -> ContractExpr<'tcx> {
    let receiver = syn::parse_str::<Expr>(receiver_text).ok();
    let method = receiver
        .as_ref()
        .and_then(|receiver| resolve_self_method(tcx, def_id, receiver, "is_empty"));
    let inner = match receiver_text {
        "return" => ContractExpr::Place(ContractPlace {
            base: PlaceBase::Return,
            projections: Vec::new(),
        }),
        s if s.starts_with("Arg_") => s[4..]
            .parse::<usize>()
            .map(|index| ContractExpr::Place(ContractPlace::arg(index)))
            .unwrap_or(ContractExpr::Unknown),
        _ => receiver
            .as_ref()
            .map(|receiver| parse_contract_expr(tcx, def_id, receiver, sp))
            .unwrap_or(ContractExpr::Unknown),
    };
    ContractExpr::IsEmpty(
        Box::new(inner),
        method,
    )
}

fn resolve_self_method(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    receiver: &Expr,
    name: &str,
) -> Option<DefId> {
    if matches!(receiver, Expr::Path(path) if path.path.is_ident("self")) {
        tcx.opt_associated_item(def_id)
            .and_then(|assoc| assoc.impl_container(tcx))
            .and_then(|impl_id| {
                tcx.associated_items(impl_id)
                    .in_definition_order()
                    .find(|item| item.name().as_str() == name)
                    .map(|item| item.def_id)
            })
    } else {
        None
    }
}

pub(crate) fn resolve_type_name<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    name: &str,
) -> Option<Ty<'tcx>> {
    if name == "Self" {
        // `Self` refers to the type owning `def_id`: for an ADT (struct/enum/
        // union) it is the type itself (`tcx.type_of`), for a function it is
        // the receiver (the first input of the signature).
        return match tcx.def_kind(def_id) {
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                Some(tcx.type_of(def_id).skip_binder())
            }
            _ => {
                let sig = tcx.fn_sig(def_id).skip_binder();
                sig.inputs().skip_binder().first().copied()
            }
        };
    }
    match_ty_with_ident(tcx, def_id, name.to_string())
}

pub(crate) fn int_type_min_max<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<(u128, u128)> {
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
            matches!(param.kind, GenericParamDefKind::Const { .. }) && param.name.as_str() == ident
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
    if let Expr::Path(path) = expr
        && path.path.segments.len() == 2
        && path.path.segments[0].ident == "Self"
        && path.path.segments[1].ident == "Output"
    {
        let output = tcx.fn_sig(def_id).skip_binder().output().skip_binder();
        return mir_utils::pointee_ty(output);
    }
    if let Expr::Verbatim(ts) = expr {
        let syn_ty = syn::parse2::<syn::Type>(ts.clone()).ok();
        // A slice type `[T]` (e.g. `ValidTransmute([u8], str)`): resolve the
        // element type and rebuild it as `TyKind::Slice`.
        if let Some(syn::Type::Slice(slice)) = &syn_ty {
            let Some(elem_name) = outermost_type_ident(&slice.elem) else {
                rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
                return None;
            };
            let Some(elem) = resolve_ty_ident(tcx, def_id, &elem_name) else {
                rap_debug!("Cannot get type in {:?} Tag!", sp);
                return None;
            };
            return Some(Ty::new_slice(tcx, elem));
        }
        // An array type `[T; N]` (e.g. `ValidTransmute([MaybeUninit<T>; N], [T; N])`):
        // resolve the element type; the const length is kept symbolic (0), which
        // `check_valid_transmute` handles by treating size 0 as "trust".
        if let Some(syn::Type::Array(array)) = &syn_ty {
            let Some(elem_name) = outermost_type_ident(&array.elem) else {
                rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
                return None;
            };
            let Some(elem) = resolve_ty_ident(tcx, def_id, &elem_name) else {
                rap_debug!("Cannot get type in {:?} Tag!", sp);
                return None;
            };
            return Some(Ty::new_array(tcx, elem, 0));
        }
        let name = syn_ty.and_then(|ty| outermost_type_ident(&ty));
        let Some(name) = name else {
            rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
            return None;
        };
        let ty = resolve_ty_ident(tcx, def_id, &name);
        if ty.is_none() {
            rap_debug!("Cannot get type in {:?} Tag!", sp);
        }
        return ty;
    }

    if let Expr::Path(expr_path) = expr
        && expr_path.path.segments.len() > 1
        && let Some(last) = expr_path.path.segments.last()
    {
        return resolve_ty_ident(tcx, def_id, &last.ident.to_string());
    }

    let Some((ty_ident, _)) = access_ident_recursive(expr) else {
        rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
        return None;
    };
    let ty = resolve_ty_ident(tcx, def_id, &ty_ident);
    if ty.is_none() {
        rap_debug!("Cannot get type in {:?} Tag!", sp);
    }
    ty
}

/// Resolve a type identifier to a `Ty`, handling the `Self` keyword (which
/// [`match_ty_with_ident`] does not understand) by delegating to
/// [`resolve_type_name`].
fn resolve_ty_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str) -> Option<Ty<'tcx>> {
    if name == "Self" {
        resolve_type_name(tcx, def_id, name)
    } else {
        match_ty_with_ident(tcx, def_id, name.to_string())
    }
}

/// Extract the outermost path segment name from a `syn::Type`, e.g. `Option`
/// from `Option<NonZero<T>>` or `NonZero` from `NonZero<T>`.
fn outermost_type_ident(ty: &syn::Type) -> Option<String> {
    match ty {
        syn::Type::Path(tp) if tp.qself.is_none() => {
            tp.path.segments.last().map(|s| s.ident.to_string())
        }
        _ => None,
    }
}

pub(crate) fn parse_target_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> PropertyArg<'tcx> {
    // `return` parses as `syn::Expr::Return { expr: None }` (a bare `return`),
    // which the place parser below does not recognise — handle it directly.
    if matches!(expr, Expr::Return(_)) {
        return PropertyArg::Expr(ContractExpr::Place(ContractPlace {
            base: PlaceBase::Return,
            projections: Vec::new(),
        }));
    }
    // For simple identifiers that aren't local variables (e.g., lifetime param
    // 'a parsed as ident `a`), store as Ident rather than Expr (which would
    // become Unknown).
    if let Expr::Path(expr_path) = expr
        && let Some(ident) = expr_path.path.get_ident()
    {
        let s = ident.to_string();
        if s != "return"
            && !s.starts_with("Arg_")
            && place::parse_expr_into_local_and_ty(tcx, def_id, expr).is_none()
        {
            return PropertyArg::Ident(s);
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
        [expr] => parse_numeric_predicate(tcx, def_id, expr)
            .into_iter()
            .collect(),
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
    let has_method_operand = matches!(expr, Expr::Binary(binary)
        if matches!(&*binary.left, Expr::MethodCall(_))
            || matches!(&*binary.right, Expr::MethodCall(_)));
    if !has_method_operand {
        if let Some(predicate) = super::pest::parse_predicate_pest(tcx, def_id, &text) {
            return Some(predicate);
        }
    }
    let Expr::Binary(binary) = expr else {
        return None;
    };
    let op = match binary.op {
        syn::BinOp::Le(_) => RelOp::Le,
        syn::BinOp::Lt(_) => RelOp::Lt,
        syn::BinOp::Ge(_) => RelOp::Ge,
        syn::BinOp::Gt(_) => RelOp::Gt,
        syn::BinOp::Eq(_) => RelOp::Eq,
        syn::BinOp::Ne(_) => RelOp::Ne,
        _ => return None,
    };
    let parse_operand = |operand: &Expr| {
        if matches!(operand, Expr::MethodCall(_)) {
            parse_contract_expr(tcx, def_id, operand, "predicate")
        } else {
            super::pest::parse_expr_pest(tcx, def_id, &operand.to_token_stream().to_string())
        }
    };
    let lhs = parse_operand(&binary.left);
    let rhs = parse_operand(&binary.right);
    (!matches!(lhs, ContractExpr::Unknown) && !matches!(rhs, ContractExpr::Unknown))
        .then(|| NumericPredicate::new(lhs, op, rhs))
}

pub(crate) fn expr_to_pest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    expr: &Expr,
) -> ContractExpr<'tcx> {
    let text = expr.to_token_stream().to_string();
    super::pest::parse_expr_pest(tcx, def_id, &text)
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
        Expr::Lit(expr_lit) => match &expr_lit.lit {
            Lit::Str(range_lit) => parse_string_interval(tcx, def_id, value, &range_lit.value()),
            Lit::Int(int_lit) => {
                // A bare integer `ValidNum(v, n)` is shorthand for the singleton
                // interval `[n, n]`, i.e. `v == n`.
                let n = int_lit.base10_parse::<u64>().ok()?;
                let n_expr = syn::parse_str::<Expr>(&n.to_string()).ok()?;
                Some(build_interval_predicates(
                    tcx, def_id, value, &n_expr, true, &n_expr, true,
                ))
            }
            _ => None,
        },
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
    if trimmed.len() < 3 {
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
    let lower_raw = lower_raw.trim();
    let upper_raw = upper_raw.trim();

    // An unbounded side is written as an empty bound, e.g. `[1,)` (no upper
    // bound) or `(,5]` (no lower bound). Reject an entirely empty interval.
    if lower_raw.is_empty() && upper_raw.is_empty() {
        return None;
    }

    let value_expr = expr_to_pest(tcx, def_id, value);
    let mut predicates = Vec::with_capacity(2);

    if !lower_raw.is_empty() {
        let lower = syn::parse_str::<Expr>(lower_raw).ok()?;
        predicates.push(NumericPredicate::new(
            expr_to_pest(tcx, def_id, &lower),
            if lower_inclusive {
                RelOp::Le
            } else {
                RelOp::Lt
            },
            value_expr.clone(),
        ));
    }

    if !upper_raw.is_empty() {
        let upper = syn::parse_str::<Expr>(upper_raw).ok()?;
        predicates.push(NumericPredicate::new(
            value_expr,
            if upper_inclusive {
                RelOp::Le
            } else {
                RelOp::Lt
            },
            expr_to_pest(tcx, def_id, &upper),
        ));
    }

    Some(predicates)
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

/// Extract the inner type from `[T]` (the `SplitTransmute([T], [U])` notation),
/// then resolve it via `parse_type`.  The `[T]` argument arrives as either
/// `Expr::Array` (JSON path, parsed via `syn::parse_str::<Expr>`) or
/// `Expr::Verbatim` (source annotation path, where `parse_property_arg`'s
/// type-first parse turns `Type::Slice` into `Verbatim`); both are unwrapped to
/// the element type `T`.
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
    if let Expr::Verbatim(ts) = expr
        && let Ok(syn::Type::Slice(slice)) = syn::parse2::<syn::Type>(ts.clone())
        && let Some(name) = outermost_type_ident(slice.elem.as_ref())
    {
        return resolve_ty_ident(tcx, def_id, &name);
    }
    parse_type(tcx, def_id, expr, "SplitTransmute")
}
