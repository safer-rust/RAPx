//! Semantic converter: pest `Pairs<Rule>` → `ContractExpr` / `NumericPredicate`.
//!
//! This is the phase-2 counterpart to `pest_grammar.rs`.  It turns the
//! structured parse tree produced by the pest grammar into the same AST the
//! hand-written `parser.rs` produces, so the two can be cross-checked for
//! equivalence.
//!
//! Places (fields, projections) are bridged through the existing
//! `parser::Property` helpers via a `syn` round-trip, since resolving a field
//! name to a `Ty` still needs the rustc type context.  The arithmetic / call /
//! if / constant layers are converted directly from the pest tree.

use pest::iterators::Pair;
use pest::Parser;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use super::pest_grammar::{ContractParser, Rule};
use super::parser::resolve_place_from_ident;
use super::types::{
    ContractExpr, ContractPlace, NumericOp, NumericPredicate, NumericUnaryOp, PlaceBase, Property,
    RelOp,
};
use crate::helpers::name::match_ty_with_ident;

fn only_child(pair: Pair<Rule>) -> Pair<Rule> {
    pair.into_inner().next().expect("expected a single child pair")
}

fn relop_from_str(s: &str) -> Option<RelOp> {
    match s {
        "==" => Some(RelOp::Eq),
        "!=" => Some(RelOp::Ne),
        "<" => Some(RelOp::Lt),
        "<=" => Some(RelOp::Le),
        ">" => Some(RelOp::Gt),
        ">=" => Some(RelOp::Ge),
        _ => None,
    }
}

/// Parse a numeric expression (no comparison) into a `ContractExpr`.
pub fn parse_expr_pest<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, text: &str) -> ContractExpr<'tcx> {
    let Ok(mut pairs) = ContractParser::parse(Rule::expr, text) else {
        rap_debug!("contract expression not supported by grammar: {text}");
        return ContractExpr::Unknown;
    };
    conv_expr(tcx, def_id, pairs.next().expect("expr pair"))
}

/// Parse a predicate (comparison / `!x.is_empty()` / bare expr) into a
/// `NumericPredicate`.
pub fn parse_predicate_pest<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    text: &str,
) -> Option<NumericPredicate<'tcx>> {
    let Ok(mut pairs) = ContractParser::parse(Rule::expr, text) else {
        rap_debug!("contract predicate not supported by grammar: {text}");
        return None;
    };
    conv_predicate(tcx, def_id, pairs.next().expect("expr pair"))
}

fn conv_expr<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::expr => conv_expr(tcx, def_id, only_child(pair)),
        Rule::if_expr => conv_if(tcx, def_id, pair),
        Rule::cmp => {
            // Expression layer carries no comparison operator.
            let mut inner = pair.into_inner();
            let lhs = conv_bit_or(tcx, def_id, inner.next().expect("cmp lhs"));
            if inner.next().is_some() {
                ContractExpr::Unknown
            } else {
                lhs
            }
        }
        Rule::bit_or | Rule::bit_xor | Rule::bit_and | Rule::additive | Rule::multiplicative => {
            conv_bit_or(tcx, def_id, pair)
        }
        Rule::unary => conv_unary(tcx, def_id, pair),
        Rule::primary => conv_primary(tcx, def_id, pair),
        Rule::call => conv_call(tcx, def_id, pair),
        Rule::place => conv_place_bridge(tcx, def_id, pair),
        Rule::const_path => conv_const_path(tcx, def_id, pair),
        Rule::int => ContractExpr::Const(pair.as_str().parse::<u128>().unwrap_or(0)),
        _ => ContractExpr::Unknown,
    }
}

fn conv_predicate<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    pair: Pair<Rule>,
) -> Option<NumericPredicate<'tcx>> {
    match pair.as_rule() {
        Rule::expr | Rule::cond => conv_predicate(tcx, def_id, only_child(pair)),
        Rule::cmp => {
            let mut inner = pair.into_inner();
            let lhs = conv_bit_or(tcx, def_id, inner.next()?);
            match inner.next() {
                Some(relop_pair) => {
                    let op = relop_from_str(relop_pair.as_str())?;
                    let rhs = conv_bit_or(tcx, def_id, inner.next()?);
                    Some(NumericPredicate::new(lhs, op, rhs))
                }
                // Bare expression → `expr != 0`.
                None => Some(NumericPredicate::new(lhs, RelOp::Ne, ContractExpr::Const(0))),
            }
        }
        Rule::not_is_empty => {
            let mut inner = pair.into_inner();
            let base_text = inner.next()?.as_str().to_string();
            let place = conv_base(tcx, def_id, &base_text);
            Some(NumericPredicate::new(
                ContractExpr::Len(Box::new(place)),
                RelOp::Ne,
                ContractExpr::Const(0),
            ))
        }
        _ => None,
    }
}

fn conv_if<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    let mut inner = pair.into_inner();
    let cond_pair = inner.next().expect("if cond");
    let then_pair = inner.next().expect("if then");
    let else_pair = inner.next().expect("if else");
    let Some(cond) = conv_predicate(tcx, def_id, cond_pair) else {
        return ContractExpr::Unknown;
    };
    let then_expr = conv_expr(tcx, def_id, then_pair);
    let else_expr = conv_expr(tcx, def_id, else_pair);
    ContractExpr::If {
        cond: Box::new(cond),
        then_expr: Box::new(then_expr),
        else_expr: Box::new(else_expr),
    }
}

fn op_from_str(op: &str) -> Option<NumericOp> {
    match op {
        "+" => Some(NumericOp::Add),
        "-" => Some(NumericOp::Sub),
        "*" => Some(NumericOp::Mul),
        "/" => Some(NumericOp::Div),
        "%" => Some(NumericOp::Rem),
        "&" => Some(NumericOp::BitAnd),
        "|" => Some(NumericOp::BitOr),
        "^" => Some(NumericOp::BitXor),
        _ => None,
    }
}

fn conv_left_assoc<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    pair: Pair<Rule>,
    operand: impl Fn(TyCtxt<'tcx>, DefId, Pair<Rule>) -> ContractExpr<'tcx>,
) -> ContractExpr<'tcx> {
    let mut inner = pair.into_inner();
    let mut acc = operand(tcx, def_id, inner.next().expect("first operand"));
    while let Some(op_pair) = inner.next() {
        let Some(op) = op_from_str(op_pair.as_str()) else {
            return ContractExpr::Unknown;
        };
        let rhs = operand(tcx, def_id, inner.next().expect("rhs operand"));
        acc = ContractExpr::Binary {
            op,
            lhs: Box::new(acc),
            rhs: Box::new(rhs),
        };
    }
    acc
}

fn conv_bit_or<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::bit_or => conv_left_assoc(tcx, def_id, pair, conv_bit_xor),
        _ => conv_bit_xor(tcx, def_id, pair),
    }
}

fn conv_bit_xor<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::bit_xor => conv_left_assoc(tcx, def_id, pair, conv_bit_and),
        _ => conv_bit_and(tcx, def_id, pair),
    }
}

fn conv_bit_and<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::bit_and => conv_left_assoc(tcx, def_id, pair, conv_additive),
        _ => conv_additive(tcx, def_id, pair),
    }
}

fn conv_additive<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::additive => conv_left_assoc(tcx, def_id, pair, conv_multiplicative),
        _ => conv_multiplicative(tcx, def_id, pair),
    }
}

fn conv_multiplicative<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    pair: Pair<Rule>,
) -> ContractExpr<'tcx> {
    match pair.as_rule() {
        Rule::multiplicative => conv_left_assoc(tcx, def_id, pair, conv_unary),
        _ => conv_unary(tcx, def_id, pair),
    }
}

fn conv_unary<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    let mut inner = pair.into_inner();
    let first = inner.next().expect("unary operand");
    match first.as_rule() {
        Rule::unop => {
            let op = match first.as_str() {
                "!" => NumericUnaryOp::Not,
                "-" => NumericUnaryOp::Neg,
                _ => return ContractExpr::Unknown,
            };
            let operand = conv_unary(tcx, def_id, inner.next().expect("unary inner"));
            ContractExpr::Unary {
                op,
                expr: Box::new(operand),
            }
        }
        _ => conv_primary(tcx, def_id, first),
    }
}

fn conv_primary<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    let inner = only_child(pair);
    match inner.as_rule() {
        Rule::int => ContractExpr::Const(inner.as_str().parse::<u128>().unwrap_or(0)),
        Rule::call => conv_call(tcx, def_id, inner),
        Rule::const_path => conv_const_path(tcx, def_id, inner),
        Rule::place => conv_place_bridge(tcx, def_id, inner),
        Rule::expr => conv_expr(tcx, def_id, inner),
        _ => ContractExpr::Unknown,
    }
}

fn conv_call<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, pair: Pair<Rule>) -> ContractExpr<'tcx> {
    let mut inner = pair.into_inner();
    let builtin = inner.next().expect("builtin").as_str().to_string();
    // `call = builtin "(" arg_list? ")"`; arg_list's children are the `arg`s.
    let args: Vec<Pair<Rule>> = match inner.next() {
        Some(arg_list) => arg_list.into_inner().collect(),
        None => Vec::new(),
    };
    match builtin.as_str() {
        "size_of" | "align_of" => {
            let ty_name = args
                .first()
                .map(|a| a.as_str().trim().to_string())
                .unwrap_or_default();
            let Some(ty) = match_ty_with_ident(tcx, def_id, ty_name) else {
                return ContractExpr::Unknown;
            };
            match builtin.as_str() {
                "size_of" => ContractExpr::SizeOf(ty),
                _ => ContractExpr::AlignOf(ty),
            }
        }
        "len" => {
            let Some(arg) = args.first() else {
                return ContractExpr::Unknown;
            };
            ContractExpr::Len(Box::new(conv_arg_expr(tcx, def_id, arg.clone())))
        }
        "min" | "max" => {
            if args.len() != 2 {
                return ContractExpr::Unknown;
            }
            let a = conv_arg_expr(tcx, def_id, args[0].clone());
            let b = conv_arg_expr(tcx, def_id, args[1].clone());
            match builtin.as_str() {
                "min" => ContractExpr::Min {
                    a: Box::new(a),
                    b: Box::new(b),
                },
                _ => ContractExpr::Max {
                    a: Box::new(a),
                    b: Box::new(b),
                },
            }
        }
        "index_access" => {
            if args.len() != 2 {
                return ContractExpr::Unknown;
            }
            let slice = conv_arg_expr(tcx, def_id, args[0].clone());
            let index = conv_arg_expr(tcx, def_id, args[1].clone());
            ContractExpr::IndexAccess {
                slice: Box::new(slice),
                index: Box::new(index),
            }
        }
        _ => ContractExpr::Unknown,
    }
}

fn conv_arg_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    arg: Pair<Rule>,
) -> ContractExpr<'tcx> {
    let inner = only_child(arg);
    match inner.as_rule() {
        Rule::expr => conv_expr(tcx, def_id, inner),
        _ => ContractExpr::Unknown,
    }
}

fn conv_const_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    pair: Pair<Rule>,
) -> ContractExpr<'tcx> {
    let text = pair.as_str();
    let Some((ty_name, which)) = text.rsplit_once("::") else {
        return ContractExpr::Unknown;
    };
    let ty_name = ty_name.trim();
    let which = which.trim();
    let Some(ty) = Property::resolve_type_name(tcx, def_id, ty_name) else {
        return ContractExpr::Unknown;
    };
    let Some((min, max)) = Property::int_type_min_max(tcx, ty) else {
        return ContractExpr::Unknown;
    };
    ContractExpr::Const(if which == "MIN" { min } else { max })
}

/// Bridge a place through the existing syn-based parser (handles field
/// projections, `unwrap_some`, `iter`, and `x.len` sugar uniformly).
fn conv_place_bridge<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    pair: Pair<Rule>,
) -> ContractExpr<'tcx> {
    let text = pair.as_str();
    let Ok(expr) = safety_parser::syn::parse_str::<safety_parser::syn::Expr>(text) else {
        return ContractExpr::Unknown;
    };
    Property::parse_contract_expr(tcx, def_id, &expr, "pest")
}

/// Convert a `not_is_empty` base (`self` / `return` / `Arg_N` / ident) into a
/// place expression.
fn conv_base<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, base_text: &str) -> ContractExpr<'tcx> {
    match base_text {
        "return" => ContractExpr::Place(ContractPlace {
            base: PlaceBase::Return,
            projections: Vec::new(),
        }),
        s if s.starts_with("Arg_") => {
            let idx = s[4..].parse::<usize>().unwrap_or(0);
            ContractExpr::Place(ContractPlace::arg(idx))
        }
        _ => {
            let Some((base, fields, _)) = resolve_place_from_ident(tcx, def_id, base_text, &[]) else {
                return ContractExpr::Unknown;
            };
            ContractExpr::Place(ContractPlace::local(base, fields))
        }
    }
}
