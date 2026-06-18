#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]
use rust_intervals::NothingBetween;

use crate::analysis::range_analysis::domain::ConstraintGraph::ConstraintGraph;
use crate::analysis::range_analysis::domain::domain::{
    ConstConvert, IntervalArithmetic, VarNode, VarNodes,
};
use crate::analysis::range_analysis::{Range, RangeType};
use crate::compat::FxHashMap;
use crate::{rap_debug, rap_trace};
use num_traits::{Bounded, CheckedAdd, CheckedSub, One, ToPrimitive, Zero, ops};
use rustc_abi::Size;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::coverage::Op;
use rustc_middle::mir::{
    BasicBlock, BinOp, BorrowKind, CastKind, Const, Local, LocalDecl, Operand, Place, Rvalue,
    Statement, StatementKind, Terminator, UnOp,
};
use rustc_middle::ty::{ScalarInt, Ty};
use rustc_span::sym::no_default_passes;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, Mul, Sub};
use std::rc::Rc;
use std::{fmt, mem};
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum BoundMode {
    Lower,
    Upper,
}

impl BoundMode {
    fn flip(self) -> Self {
        match self {
            BoundMode::Lower => BoundMode::Upper,
            BoundMode::Upper => BoundMode::Lower,
        }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SymbExpr<'tcx> {
    Constant(Const<'tcx>),

    Place(&'tcx Place<'tcx>),

    Binary(BinOp, Box<SymbExpr<'tcx>>, Box<SymbExpr<'tcx>>),

    Unary(UnOp, Box<SymbExpr<'tcx>>),

    Cast(CastKind, Box<SymbExpr<'tcx>>, Ty<'tcx>),

    Unknown,
}
impl<'tcx> fmt::Display for SymbExpr<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
impl<'tcx> SymbExpr<'tcx> {
    pub fn from_operand(op: &'tcx Operand<'tcx>, place_ctx: &Vec<&'tcx Place<'tcx>>) -> Self {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                let found_base = place_ctx
                    .iter()
                    .find(|&&p| p.local == place.local && p.projection.is_empty());

                match found_base {
                    Some(&base_place) => SymbExpr::Place(base_place),

                    None => SymbExpr::Place(place),
                }
            }
            Operand::Constant(c) => SymbExpr::Constant(c.const_),
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => SymbExpr::Unknown,
        }
    }

    pub fn from_rvalue(rvalue: &'tcx Rvalue<'tcx>, place_ctx: Vec<&'tcx Place<'tcx>>) -> Self {
        match rvalue {
            Rvalue::Use(op, ..) => Self::from_operand(op, &place_ctx),
            Rvalue::BinaryOp(bin_op, pair) => {
                let (lhs, rhs) = &**pair;
                let left = Self::from_operand(lhs, &place_ctx);
                let right = Self::from_operand(rhs, &place_ctx);

                if matches!(left, SymbExpr::Unknown) || matches!(right, SymbExpr::Unknown) {
                    return SymbExpr::Unknown;
                }

                SymbExpr::Binary(*bin_op, Box::new(left), Box::new(right))
            }
            Rvalue::UnaryOp(un_op, op) => {
                let expr = Self::from_operand(op, &place_ctx);
                if matches!(expr, SymbExpr::Unknown) {
                    return SymbExpr::Unknown;
                }
                SymbExpr::Unary(*un_op, Box::new(expr))
            }
            Rvalue::Cast(kind, op, ty) => {
                let expr = Self::from_operand(op, &place_ctx);
                if matches!(expr, SymbExpr::Unknown) {
                    return SymbExpr::Unknown;
                }
                SymbExpr::Cast(*kind, Box::new(expr), *ty)
            }
            Rvalue::Ref(..)
            | Rvalue::ThreadLocalRef(..)
            | Rvalue::Aggregate(..)
            | Rvalue::Repeat(..)
            | Rvalue::Discriminant(..)
            | Rvalue::CopyForDeref(..) => SymbExpr::Unknown,
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(..) | Rvalue::NullaryOp(..) => SymbExpr::Unknown,
            #[cfg(rapx_rustc_ge_198)]
            Rvalue::Reborrow(..) => SymbExpr::Unknown,
            Rvalue::RawPtr(raw_ptr_kind, place) => todo!(),
            Rvalue::WrapUnsafeBinder(operand, ty) => todo!(),
        }
    }

    // pub fn eval<T: IntervalArithmetic + ConstConvert + Debug>(
    //     &self,
    //     vars: &VarNodes<'tcx, T>,
    // ) -> Range<T> {
    //     match self {
    //         SymbExpr::Unknown => Range::new(T::min_value(), T::max_value(), RangeType::Regular),

    //         SymbExpr::Constant(c) => {
    //             if let Some(val) = T::from_const(c) {
    //                 Range::new(val, val, RangeType::Regular)
    //             } else {
    //                 Range::new(T::min_value(), T::max_value(), RangeType::Regular)
    //             }
    //         }

    //         SymbExpr::Place(place) => {
    //             if let Some(node) = vars.get(place) {
    //                 node.get_range().clone()
    //             } else {
    //                 Range::new(T::min_value(), T::max_value(), RangeType::Regular)
    //             }
    //         }

    //         SymbExpr::Binary(op, lhs, rhs) => {
    //             let l_range = lhs.eval(vars);
    //             let r_range = rhs.eval(vars);

    //             match op {
    //                 BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
    //                     l_range.add(&r_range)
    //                 }
    //                 BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => {
    //                     l_range.sub(&r_range)
    //                 }
    //                 BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => {
    //                     l_range.mul(&r_range)
    //                 }

    //                 _ => Range::new(T::min_value(), T::max_value(), RangeType::Regular),
    //             }
    //         }

    //         SymbExpr::Unary(op, inner) => {
    //             let _inner_range = inner.eval(vars);
    //             match op {
    //                 UnOp::Neg => Range::new(T::min_value(), T::max_value(), RangeType::Regular),
    //                 UnOp::Not | UnOp::PtrMetadata => {
    //                     Range::new(T::min_value(), T::max_value(), RangeType::Regular)
    //                 }
    //             }
    //         }

    //         SymbExpr::Cast(kind, inner, _target_ty) => {
    //             let inner_range = inner.eval(vars);
    //             match kind {
    //                 CastKind::IntToInt => inner_range,

    //                 _ => Range::new(T::min_value(), T::max_value(), RangeType::Regular),
    //             }
    //         }
    //     }
    // }
    pub fn resolve_upper_bound<T: IntervalArithmetic + ConstConvert + Debug + Clone + PartialEq>(
        &mut self,
        vars: &VarNodes<'tcx, T>,
    ) {
        self.resolve_recursive(vars, 0, BoundMode::Upper);
    }
    pub fn resolve_lower_bound<T: IntervalArithmetic + ConstConvert + Debug + Clone + PartialEq>(
        &mut self,
        vars: &VarNodes<'tcx, T>,
    ) {
        self.resolve_recursive(vars, 0, BoundMode::Lower);
    }

    fn resolve_recursive<T: IntervalArithmetic + ConstConvert + Debug + Clone + PartialEq>(
        &mut self,
        vars: &VarNodes<'tcx, T>,
        depth: usize,
        mode: BoundMode,
    ) {
        const MAX_DEPTH: usize = 10;
        if depth > MAX_DEPTH {
            *self = SymbExpr::Unknown;
            return;
        }

        match self {
            SymbExpr::Binary(op, lhs, rhs) => {
                lhs.resolve_recursive(vars, depth + 1, mode);

                match op {
                    BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                        rhs.resolve_recursive(vars, depth + 1, mode);
                    }
                    BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => {
                        rhs.resolve_recursive(vars, depth + 1, mode.flip());
                    }
                    _ => rhs.resolve_recursive(vars, depth + 1, mode),
                }
            }
            SymbExpr::Unary(op, inner) => match op {
                UnOp::Neg => {
                    inner.resolve_recursive(vars, depth + 1, mode.flip());
                }
                _ => inner.resolve_recursive(vars, depth + 1, mode),
            },
            SymbExpr::Cast(_, inner, _) => {
                inner.resolve_recursive(vars, depth + 1, mode);
            }
            _ => {}
        }

        // self.try_fold_constants::<T>();
        rap_trace!("symexpr {}", self);
        if let SymbExpr::Place(place) = self {
            if let Some(node) = vars.get(place) {
                if let IntervalType::Basic(basic) = &node.interval {
                    rap_trace!("node {:?}", *node);

                    let target_expr = if basic.lower == basic.upper {
                        &basic.upper
                    } else {
                        match mode {
                            BoundMode::Upper => &basic.upper,
                            BoundMode::Lower => &basic.lower,
                        }
                    };

                    match target_expr {
                        SymbExpr::Unknown => *self = SymbExpr::Unknown,
                        SymbExpr::Constant(c) => *self = SymbExpr::Constant(c.clone()),
                        expr => {
                            if let SymbExpr::Place(target_place) = expr {
                                if target_place == place {
                                    return;
                                }
                            }

                            *self = expr.clone();
                            self.resolve_recursive(vars, depth + 1, mode);
                        }
                    }
                }
            }
        }
    }
    pub fn simplify(&mut self) {
        match self {
            SymbExpr::Binary(_, lhs, rhs) => {
                lhs.simplify();
                rhs.simplify();
            }
            SymbExpr::Unary(_, inner) => {
                inner.simplify();
            }
            SymbExpr::Cast(_, inner, _) => {
                inner.simplify();
            }
            _ => {}
        }

        if let SymbExpr::Binary(op, lhs, rhs) = self {
            match op {
                BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => {
                    if let SymbExpr::Binary(inner_op, inner_lhs, inner_rhs) = lhs.as_ref() {
                        match inner_op {
                            BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                                if inner_lhs == rhs {
                                    *self = *inner_rhs.clone();
                                } else if inner_rhs == rhs {
                                    *self = *inner_lhs.clone();
                                }
                            }
                            _ => {}
                        }
                    }
                }
                BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                    if let SymbExpr::Binary(inner_op, inner_lhs, inner_rhs) = lhs.as_ref() {
                        match inner_op {
                            BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => {
                                if inner_rhs == rhs {
                                    *self = *inner_lhs.clone();
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }
}
#[derive(Debug, Clone)]
pub enum IntervalType<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    Basic(BasicInterval<'tcx, T>),
    Symb(SymbInterval<'tcx, T>),
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> fmt::Display for IntervalType<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntervalType::Basic(b) => write!(
                f,
                "BasicInterval: {:?} {:?} {:?} ",
                b.get_range(),
                b.lower,
                b.upper
            ),
            IntervalType::Symb(b) => write!(
                f,
                "SymbInterval: {:?} {:?} {:?} ",
                b.get_range(),
                b.lower,
                b.upper
            ),
        }
    }
}
pub trait IntervalTypeTrait<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    fn get_range(&self) -> &Range<T>;
    fn set_range(&mut self, new_range: Range<T>);
    fn get_lower_expr(&self) -> &SymbExpr<'tcx>;
    fn get_upper_expr(&self) -> &SymbExpr<'tcx>;
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<'tcx, T>
    for IntervalType<'tcx, T>
{
    fn get_range(&self) -> &Range<T> {
        match self {
            IntervalType::Basic(b) => b.get_range(),
            IntervalType::Symb(s) => s.get_range(),
        }
    }

    fn set_range(&mut self, new_range: Range<T>) {
        match self {
            IntervalType::Basic(b) => b.set_range(new_range),
            IntervalType::Symb(s) => s.set_range(new_range),
        }
    }
    fn get_lower_expr(&self) -> &SymbExpr<'tcx> {
        match self {
            IntervalType::Basic(b) => b.get_lower_expr(),
            IntervalType::Symb(s) => s.get_lower_expr(),
        }
    }

    fn get_upper_expr(&self) -> &SymbExpr<'tcx> {
        match self {
            IntervalType::Basic(b) => b.get_upper_expr(),
            IntervalType::Symb(s) => s.get_upper_expr(),
        }
    }
}
#[derive(Debug, Clone)]

pub struct BasicInterval<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub range: Range<T>,
    pub lower: SymbExpr<'tcx>,
    pub upper: SymbExpr<'tcx>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> BasicInterval<'tcx, T> {
    pub fn new(range: Range<T>) -> Self {
        Self {
            range,
            lower: SymbExpr::Unknown,
            upper: SymbExpr::Unknown,
        }
    }
    pub fn new_symb(range: Range<T>, lower: SymbExpr<'tcx>, upper: SymbExpr<'tcx>) -> Self {
        Self {
            range,
            lower,
            upper,
        }
    }
    pub fn default() -> Self {
        Self {
            range: Range::default(T::min_value()),
            lower: SymbExpr::Unknown,
            upper: SymbExpr::Unknown,
        }
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<'tcx, T>
    for BasicInterval<'tcx, T>
{
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::BasicIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
        if self.range.get_lower() > self.range.get_upper() {
            self.range.set_empty();
        }
    }
    fn get_lower_expr(&self) -> &SymbExpr<'tcx> {
        &self.lower
    }

    fn get_upper_expr(&self) -> &SymbExpr<'tcx> {
        &self.upper
    }
}

#[derive(Debug, Clone)]

pub struct SymbInterval<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    range: Range<T>,
    symbound: &'tcx Place<'tcx>,
    predicate: BinOp,
    lower: SymbExpr<'tcx>,
    upper: SymbExpr<'tcx>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> SymbInterval<'tcx, T> {
    pub fn new(range: Range<T>, symbound: &'tcx Place<'tcx>, predicate: BinOp) -> Self {
        Self {
            range,
            symbound,
            predicate,
            lower: SymbExpr::Unknown,
            upper: SymbExpr::Unknown,
        }
    }

    // pub fn refine(&mut self, vars: &VarNodes<'tcx, T>) {
    //     if let SymbExpr::Unknown = self.lower {
    //     } else {
    //         let low_range = self.lower.eval(vars);
    //         if low_range.get_lower() > self.range.get_lower() {
    //             let new_range = Range::new(
    //                 low_range.get_lower(),
    //                 self.range.get_upper(),
    //                 RangeType::Regular,
    //             );
    //             self.range = new_range;
    //         }
    //     }

    //     if let SymbExpr::Unknown = self.upper {
    //         // Do nothing
    //     } else {
    //         let high_range = self.upper.eval(vars);
    //         if high_range.get_upper() < self.range.get_upper() {
    //             let new_range = Range::new(
    //                 self.range.get_lower(),
    //                 high_range.get_upper(),
    //                 RangeType::Regular,
    //             );
    //             self.range = new_range;
    //         }
    //     }
    // }

    pub fn get_operation(&self) -> BinOp {
        self.predicate
    }

    pub fn get_bound(&self) -> &'tcx Place<'tcx> {
        self.symbound
    }

    pub fn sym_fix_intersects(
        &self,
        bound: &VarNode<'tcx, T>,
        sink: &VarNode<'tcx, T>,
    ) -> Range<T> {
        let l = bound.get_range().get_lower().clone();
        let u = bound.get_range().get_upper().clone();

        let lower = sink.get_range().get_lower().clone();
        let upper = sink.get_range().get_upper().clone();

        match self.predicate {
            BinOp::Eq => Range::new(l, u, RangeType::Regular),

            BinOp::Le => Range::new(lower, u, RangeType::Regular),

            BinOp::Lt => {
                if u != T::max_value() {
                    let u_minus_1 = u.checked_sub(&T::one()).unwrap_or(u);
                    Range::new(lower, u_minus_1, RangeType::Regular)
                } else {
                    Range::new(lower, u, RangeType::Regular)
                }
            }

            BinOp::Ge => Range::new(l, upper, RangeType::Regular),

            BinOp::Gt => {
                if l != T::min_value() {
                    let l_plus_1 = l.checked_add(&T::one()).unwrap_or(l);
                    Range::new(l_plus_1, upper, RangeType::Regular)
                } else {
                    Range::new(l, upper, RangeType::Regular)
                }
            }

            BinOp::Ne => Range::new(T::min_value(), T::max_value(), RangeType::Regular),

            _ => Range::new(T::min_value(), T::max_value(), RangeType::Regular),
        }
    }
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> IntervalTypeTrait<'tcx, T>
    for SymbInterval<'tcx, T>
{
    // fn get_value_id(&self) -> IntervalId {
    //     IntervalId::SymbIntervalId
    // }

    fn get_range(&self) -> &Range<T> {
        &self.range
    }

    fn set_range(&mut self, new_range: Range<T>) {
        self.range = new_range;
    }
    fn get_lower_expr(&self) -> &SymbExpr<'tcx> {
        &self.lower
    }

    fn get_upper_expr(&self) -> &SymbExpr<'tcx> {
        &self.upper
    }
}
