#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(dead_code)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]
use rust_intervals::NothingBetween;

use crate::analysis::range_analysis::domain::ConstraintGraph;
use crate::analysis::range_analysis::domain::symbolic_expr::{
    BasicInterval, IntervalType, IntervalTypeTrait, SymbExpr,
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
use rustc_middle::ty::ScalarInt;
use rustc_span::sym::no_default_passes;
use std::cell::RefCell;
use std::cmp::PartialEq;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Add, Mul, Sub};
use std::rc::Rc;
pub trait ConstConvert: Sized {
    fn from_const(c: &Const) -> Option<Self>;
}

macro_rules! impl_const_convert {
    ($t:ty) => {
        impl ConstConvert for $t {
            fn from_const(c: &Const) -> Option<Self> {
                c.try_to_scalar_int().map(|s| s.to_bits(s.size()) as $t)
            }
        }
    };
}

impl_const_convert!(u32);
impl_const_convert!(usize);
impl_const_convert!(i32);
impl_const_convert!(i64);
impl_const_convert!(i128);
impl_const_convert!(u64);
impl_const_convert!(u128);
impl_const_convert!(i8);
impl_const_convert!(i16);
impl_const_convert!(u8);
impl_const_convert!(u16);

pub trait IntervalArithmetic:
    PartialOrd
    + Clone
    + Bounded
    + Zero
    + Copy
    + One
    + CheckedAdd
    + CheckedSub
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + core::fmt::Debug
    + PartialOrd
    + PartialEq
    + NothingBetween
{
}

macro_rules! impl_interval_arith {
    ($t:ty) => {
        impl IntervalArithmetic for $t {}
    };
}

impl_interval_arith!(i32);
impl_interval_arith!(usize);
impl_interval_arith!(i64);
impl_interval_arith!(u64);
impl_interval_arith!(u128);
impl_interval_arith!(i8);
impl_interval_arith!(i16);
impl_interval_arith!(u8);
impl_interval_arith!(u16);
use rustc_middle::ty::Ty;

#[derive(Debug, Clone)]
pub enum BasicOpKind<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    Unary(UnaryOp<'tcx, T>),
    Binary(BinaryOp<'tcx, T>),
    Essa(EssaOp<'tcx, T>),
    ControlDep(ControlDep<'tcx, T>),
    Phi(PhiOp<'tcx, T>),
    Use(UseOp<'tcx, T>),
    Call(CallOp<'tcx, T>),
    Ref(RefOp<'tcx, T>),
    Aggregate(AggregateOp<'tcx, T>),
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> fmt::Display for BasicOpKind<'tcx, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BasicOpKind::Unary(op) => write!(
                f,
                "UnaryOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",
                op.intersect, op.sink, op.source, op.inst
            ),
            BasicOpKind::Binary(op) => write!(
                f,
                "BinaryOp: intersect {} sink:{:?} source1:{:?} source2:{:?} inst:{:?} const_value:{} ",
                op.intersect,
                op.sink,
                op.source1,
                op.source2,
                op.inst,
                op.const_value.clone().unwrap()
            ),
            BasicOpKind::Essa(op) => write!(
                f,
                "EssaOp: intersect {} sink:{:?} source:{:?} inst:{:?} unresolved:{:?} ",
                op.intersect, op.sink, op.source, op.inst, op.unresolved
            ),
            BasicOpKind::ControlDep(op) => write!(
                f,
                "ControlDep: intersect {} sink:{:?} source:{:?} inst:{:?}  ",
                op.intersect, op.sink, op.source, op.inst
            ),
            BasicOpKind::Phi(op) => write!(
                f,
                "PhiOp: intersect {} sink:{:?} source:{:?} inst:{:?}  ",
                op.intersect, op.sink, op.sources, op.inst
            ),
            BasicOpKind::Use(op) => write!(
                f,
                "UseOp: intersect {} sink:{:?} source:{:?} inst:{:?} ",
                op.intersect, op.sink, op.source, op.inst
            ),
            BasicOpKind::Call(op) => write!(
                f,
                "CallOp: intersect {} sink:{:?} args:{:?} inst:{:?}",
                op.intersect, op.sink, op.args, op.inst
            ),
            BasicOpKind::Ref(op) => write!(
                f,
                "RefOp: intersect {} sink:{:?} source:{:?} inst:{:?} borrowkind:{:?}",
                op.intersect, op.sink, op.source, op.inst, op.borrowkind
            ),
            BasicOpKind::Aggregate(op) => write!(
                f,
                "AggregateOp: intersect {} sink:{:?} operands:{:?} inst:{:?}",
                op.intersect, op.sink, op.operands, op.inst
            ),
        }
    }
}
macro_rules! basic_op_match {
    ($self:expr, |$op:ident| $body:expr) => {
        match $self {
            BasicOpKind::Unary($op) => $body,
            BasicOpKind::Binary($op) => $body,
            BasicOpKind::Essa($op) => $body,
            BasicOpKind::ControlDep($op) => $body,
            BasicOpKind::Phi($op) => $body,
            BasicOpKind::Use($op) => $body,
            BasicOpKind::Call($op) => $body,
            BasicOpKind::Ref($op) => $body,
            BasicOpKind::Aggregate($op) => $body,
        }
    };
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> BasicOpKind<'tcx, T> {
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        match self {
            BasicOpKind::Unary(op) => op.eval(),
            BasicOpKind::Binary(op) => op.eval(vars),
            BasicOpKind::Essa(op) => op.eval(vars),
            BasicOpKind::ControlDep(op) => op.eval(),
            BasicOpKind::Phi(op) => op.eval(vars),
            BasicOpKind::Use(op) => op.eval(vars),
            BasicOpKind::Call(op) => op.eval(vars),
            BasicOpKind::Ref(op) => op.eval(vars),
            BasicOpKind::Aggregate(op) => op.eval(vars),
        }
    }

    pub fn eval_interproc(
        &self,
        vars: &VarNodes<'tcx, T>,
        cg_map: &FxHashMap<DefId, Rc<RefCell<ConstraintGraph<'tcx, T>>>>,
        vars_map: &mut FxHashMap<DefId, Vec<RefCell<VarNodes<'tcx, T>>>>,
    ) -> Range<T> {
        match self {
            BasicOpKind::Call(call_op) => call_op.eval_call(vars, cg_map, vars_map),
            _ => self.eval(vars),
        }
    }
    pub fn get_type_name(&self) -> &'static str {
        match self {
            BasicOpKind::Unary(_) => "Unary",
            BasicOpKind::Binary(_) => "Binary",
            BasicOpKind::Essa(_) => "Essa",
            BasicOpKind::ControlDep(_) => "ControlDep",
            BasicOpKind::Phi(_) => "Phi",
            BasicOpKind::Use(_) => "Use",
            BasicOpKind::Call(_) => "Call",
            BasicOpKind::Ref(_) => "Ref",
            BasicOpKind::Aggregate(_) => "Aggregate",
        }
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        basic_op_match!(self, |op| op.sink)
    }
    pub fn get_instruction(&self) -> Option<&'tcx Statement<'tcx>> {
        match self {
            BasicOpKind::Unary(op) => Some(op.inst),
            BasicOpKind::Binary(op) => Some(op.inst),
            BasicOpKind::Essa(op) => Some(op.inst),
            BasicOpKind::ControlDep(op) => Some(op.inst),
            BasicOpKind::Phi(op) => Some(op.inst),
            BasicOpKind::Use(op) => Some(op.inst),
            BasicOpKind::Call(op) => None,
            BasicOpKind::Ref(op) => Some(op.inst),
            BasicOpKind::Aggregate(op) => Some(op.inst),
        }
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        basic_op_match!(self, |op| &op.intersect)
    }
    pub fn op_fix_intersects(&mut self, v: &VarNode<'tcx, T>, sink: &VarNode<'tcx, T>) {
        let intersect = self.get_intersect_mut();

        if let IntervalType::Symb(symbi) = intersect {
            let range = symbi.sym_fix_intersects(v, sink);
            rap_trace!(
                "from {:?} to {:?} fix_intersects: {:} -> {:?}\n",
                v.get_value().clone(),
                sink.get_value().clone(),
                intersect.clone(),
                range
            );
            self.set_intersect(range);
        }
    }
    pub fn set_sink(&mut self, new_sink: &'tcx Place<'tcx>) {
        basic_op_match!(self, |op| { op.sink = new_sink })
    }
    pub fn set_intersect(&mut self, new_intersect: Range<T>) {
        basic_op_match!(self, |op| op.intersect.set_range(new_intersect))
    }
    pub fn get_intersect_mut(&mut self) -> &mut IntervalType<'tcx, T> {
        basic_op_match!(self, |op| &mut op.intersect)
    }
    pub fn get_sources(&self) -> Vec<&'tcx Place<'tcx>> {
        match self {
            BasicOpKind::Unary(op) => vec![op.source],
            BasicOpKind::Binary(op) => {
                let mut sources = Vec::new();

                if let Some(src1) = op.source1 {
                    sources.push(src1);
                }

                if let Some(src2) = op.source2 {
                    sources.push(src2);
                }

                sources
            }
            BasicOpKind::Essa(op) => vec![op.source],
            BasicOpKind::ControlDep(op) => vec![op.source],
            BasicOpKind::Phi(op) => op.sources.clone(),
            BasicOpKind::Use(op) => {
                let mut sources = Vec::new();

                if let Some(src1) = op.source {
                    sources.push(src1);
                }

                sources
            }
            BasicOpKind::Call(op) => op.sources.clone(),
            BasicOpKind::Ref(op) => vec![op.source],
            BasicOpKind::Aggregate(_) => vec![],
        }
    }
}
#[derive(Debug, Clone)]
pub struct CallOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Terminator<'tcx>,
    pub args: Vec<Operand<'tcx>>,
    pub def_id: DefId,
    pub fun_path: String,
    pub sources: Vec<&'tcx Place<'tcx>>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> CallOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Terminator<'tcx>,
        args: Vec<Operand<'tcx>>,
        def_id: DefId,
        fun_path: String,
        sources: Vec<&'tcx Place<'tcx>>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            args,
            sources,
            def_id,
            fun_path,
        }
    }

    pub fn eval(&self, caller_vars: &VarNodes<'tcx, T>) -> Range<T> {
        return Range::bottom();
    }
}
#[derive(Debug, Clone)]
pub enum AggregateOperand<'tcx> {
    Place(&'tcx Place<'tcx>),
    Const(Const<'tcx>),
}
#[derive(Debug, Clone)]

pub struct AggregateOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub operands: Vec<AggregateOperand<'tcx>>,
    pub unique_adt: usize,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> AggregateOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        operands: Vec<AggregateOperand<'tcx>>,
        unique_adt: usize,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            operands,
            unique_adt,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        if self.operands.is_empty() {
            return self.intersect.get_range().clone();
        }

        let mut result: Range<T> = Range::bottom();
        match self.unique_adt {
            0 => {
                // If unique_adt is 0, we assume it's a regular array or slice.
                // We can use the first operand's range as the initial result.
                match self.operands.first() {
                    Some(AggregateOperand::Place(place)) => {
                        let range = vars[*place].get_range().clone();
                        result = range;
                    }
                    Some(AggregateOperand::Const(c)) => {
                        result = Range::new(
                            T::from_const(c).unwrap_or(T::min_value()),
                            T::from_const(c).unwrap_or(T::max_value()),
                            RangeType::Regular,
                        );
                    }
                    None => {}
                }
            }
            1 => {
                // If unique_adt is 1, we assume it's a Range with two operands.
                let mut lower = T::min_value();
                let mut upper = T::max_value();
                match self.operands.first() {
                    Some(AggregateOperand::Place(place)) => {
                        lower = vars[*place].get_range().get_lower().clone();
                    }
                    Some(AggregateOperand::Const(c)) => {
                        lower = T::from_const(c).unwrap_or(T::min_value());
                    }
                    None => {}
                }
                match self.operands.last() {
                    Some(AggregateOperand::Place(place)) => {
                        upper = vars[*place].get_range().get_upper().clone();
                    }
                    Some(AggregateOperand::Const(c)) => {
                        upper = T::from_const(c).unwrap_or(T::max_value());
                    }
                    None => {}
                }

                result = Range::new(lower, upper, RangeType::Regular);
            }
            _ => {}
        }
        result
    }
}

#[derive(Debug, Clone)]
pub struct UseOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: Option<&'tcx Place<'tcx>>,
    pub const_value: Option<Const<'tcx>>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> UseOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: Option<&'tcx Place<'tcx>>,
        const_value: Option<Const<'tcx>>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            const_value,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        if let Some(source) = self.source {
            let range = vars[source].get_range().clone();
            let mut result = Range::bottom();
            if range.is_regular() {
                result = range
            } else {
            }
            result
        } else {
            // If no source is provided, return the intersect range
            self.intersect.get_range().clone()
        }
    }
}
#[derive(Debug, Clone)]
pub struct UnaryOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub op: UnOp,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> UnaryOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        op: UnOp,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            op,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::bottom()
    }
}
#[derive(Debug, Clone)]

pub struct EssaOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub unresolved: bool,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> EssaOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        unresolved: bool,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            unresolved,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let source_range = vars[self.source].get_range().clone();
        let result = source_range.intersectwith(self.intersect.get_range());
        rap_trace!(
            "EssaOp eval: {:?} {:?} intersectwith {:?} -> {:?}\n",
            self.source,
            self.intersect.get_range(),
            source_range,
            result
        );
        result
    }
    pub fn get_source(&self) -> &'tcx Place<'tcx> {
        self.source
    }
    pub fn get_instruction(&self) -> &'tcx Statement<'tcx> {
        self.inst
    }
    pub fn get_sink(&self) -> &'tcx Place<'tcx> {
        self.sink
    }
    pub fn is_unresolved(&self) -> bool {
        self.unresolved
    }

    pub fn mark_resolved(&mut self) {
        self.unresolved = false;
    }

    pub fn mark_unresolved(&mut self) {
        self.unresolved = true;
    }
    pub fn get_intersect(&self) -> &IntervalType<'tcx, T> {
        &self.intersect
    }
}
#[derive(Debug, Clone)]
pub struct BinaryOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source1: Option<&'tcx Place<'tcx>>,
    pub source2: Option<&'tcx Place<'tcx>>,
    pub const_value: Option<Const<'tcx>>,
    pub op: BinOp,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> BinaryOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source1: Option<&'tcx Place<'tcx>>,
        source2: Option<&'tcx Place<'tcx>>,
        const_value: Option<Const<'tcx>>,

        op: BinOp,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source1,
            source2,
            const_value, // Default value, can be set later
            op,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let op1 = vars[self.source1.unwrap()].get_range().clone();
        let mut op2 = Range::bottom();
        if let Some(const_value) = &self.const_value {
            // If const_value is provided, use it as the second operand
            let value = T::from_const(const_value).unwrap();
            op2 = Range::new(value, value, RangeType::Regular);
        } else {
            op2 = vars[self.source2.unwrap()].get_range().clone();
        }
        let mut result = Range::bottom();
        match &self.inst.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                match rvalue {
                    Rvalue::BinaryOp(binop, _) => match binop {
                        BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => {
                            result = op1.add(&op2);
                        }

                        BinOp::SubUnchecked | BinOp::SubWithOverflow | BinOp::Sub => {
                            result = op1.sub(&op2);
                        }

                        BinOp::MulUnchecked | BinOp::MulWithOverflow | BinOp::Mul => {
                            result = op1.mul(&op2);
                        }

                        _ => {}
                    },
                    _ => {}
                }
            }
            _ => {}
        }

        result
    }
}
#[derive(Debug, Clone)]

pub struct PhiOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub sources: Vec<&'tcx Place<'tcx>>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> PhiOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            sources: vec![],
        }
    }

    pub fn add_source(&mut self, src: &'tcx Place<'tcx>) {
        self.sources.push(src);
    }
    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let first = self.sources[0];
        let mut result = vars[first].get_range().clone();
        for &phisource in self.sources.iter() {
            let node = &vars[phisource];
            result = result.unionwith(node.get_range());
            rap_trace!(
                "PhiOp eval:  {:?} unionwith {:?} -> {:?}\n",
                vars[first].get_range().clone(),
                node.get_range(),
                result
            );
        }
        result
    }
    pub fn get_sources(&self) -> &[&'tcx Place<'tcx>] {
        &self.sources
    }
}
#[derive(Debug, Clone)]
pub struct RefOp<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
    pub borrowkind: BorrowKind,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> RefOp<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
        borrowkind: BorrowKind,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
            borrowkind,
        }
    }

    pub fn eval(&self, vars: &VarNodes<'tcx, T>) -> Range<T> {
        let var_node = vars.get(self.source);
        rap_trace!("RefOp eval: searching for {:?}\n", var_node);
        if let Some(var_node) = var_node {
            let range = var_node.get_range().clone();

            rap_trace!(
                "RefOp eval: {:?} {:?} intersectwith {:?}\n",
                self.source,
                self.intersect.get_range(),
                range
            );

            range
        } else {
            rap_trace!(
                "RefOp eval: {:?} not found, returning intersect {:?}\n",
                self.source,
                self.intersect.get_range()
            );
            self.intersect.get_range().clone()
        }
    }
}
#[derive(Debug, Clone)]

pub struct ControlDep<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub intersect: IntervalType<'tcx, T>,
    pub sink: &'tcx Place<'tcx>,
    pub inst: &'tcx Statement<'tcx>,
    pub source: &'tcx Place<'tcx>,
}

impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> ControlDep<'tcx, T> {
    pub fn new(
        intersect: IntervalType<'tcx, T>,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        source: &'tcx Place<'tcx>,
    ) -> Self {
        Self {
            intersect,
            sink,
            inst,
            source,
        }
    }

    pub fn eval(&self) -> Range<T> {
        Range::bottom()
    }
}

#[derive(Debug, Clone)]
pub struct VarNode<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    pub v: &'tcx Place<'tcx>,
    pub interval: IntervalType<'tcx, T>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> VarNode<'tcx, T> {
    pub fn new(v: &'tcx Place<'tcx>) -> Self {
        Self {
            v,
            interval: IntervalType::Basic(BasicInterval::default()),
        }
    }
    pub fn new_symb(v: &'tcx Place<'tcx>, symb_expr: SymbExpr<'tcx>) -> Self {
        Self {
            v,
            interval: IntervalType::Basic(BasicInterval::new_symb(
                Range::bottom(),
                symb_expr.clone(),
                symb_expr.clone(),
            )),
        }
    }
    pub fn get_range(&self) -> &Range<T> {
        self.interval.get_range()
    }

    pub fn set_range(&mut self, new_interval: Range<T>) {
        self.interval.set_range(new_interval);
    }

    pub fn set_interval(&mut self, new_interval: IntervalType<'tcx, T>) {
        self.interval = new_interval;
    }

    pub fn get_interval(&self) -> &IntervalType<'tcx, T> {
        &self.interval
    }

    pub fn set_default(&mut self) {
        let mut range = Range::bottom();
        range.set_default();
        self.interval.set_range(range);
    }
    pub fn get_value(&self) -> &'tcx Place<'tcx> {
        self.v
    }
}

#[derive(Debug, Clone)]
pub struct ValueBranchMap<'tcx, T: IntervalArithmetic + ConstConvert + Debug> {
    v: &'tcx Place<'tcx>,         // The value associated with the branch
    bb_true: &'tcx BasicBlock,    // True side of the branch
    bb_false: &'tcx BasicBlock,   // False side of the branch
    itv_t: IntervalType<'tcx, T>, // Interval for the true side
    itv_f: IntervalType<'tcx, T>,
}
impl<'tcx, T: IntervalArithmetic + ConstConvert + Debug> ValueBranchMap<'tcx, T> {
    pub fn new(
        v: &'tcx Place<'tcx>,
        bb_false: &'tcx BasicBlock,
        bb_true: &'tcx BasicBlock,
        itv_f: IntervalType<'tcx, T>,
        itv_t: IntervalType<'tcx, T>,
    ) -> Self {
        Self {
            v,
            bb_false,
            bb_true,
            itv_f,
            itv_t,
        }
    }

    /// Get the "false side" of the branch
    pub fn get_bb_false(&self) -> &BasicBlock {
        self.bb_false
    }

    /// Get the "true side" of the branch
    pub fn get_bb_true(&self) -> &BasicBlock {
        self.bb_true
    }

    /// Get the interval associated with the true side of the branch
    pub fn get_itv_t(&self) -> IntervalType<'tcx, T> {
        self.itv_t.clone()
    }

    /// Get the interval associated with the false side of the branch
    pub fn get_itv_f(&self) -> IntervalType<'tcx, T> {
        self.itv_f.clone()
    }

    /// Get the value associated with the branch
    pub fn get_v(&self) -> &'tcx Place<'tcx> {
        self.v
    }

    // pub fn set_itv_t(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_t = itv;
    // }

    // /// Change the interval associated with the false side of the branch
    // pub fn set_itv_f(&mut self, itv: &IntervalType<'tcx, T>) {
    //     self.itv_f = itv;
    // }

    // pub fn clear(&mut self) {
    //     self.itv_t = Box::new(EmptyInterval::new());
    //     self.itv_f = Box::new(EmptyInterval::new());
    // }
}

pub type VarNodes<'tcx, T> = HashMap<&'tcx Place<'tcx>, VarNode<'tcx, T>>;
pub type GenOprs<'tcx, T> = Vec<BasicOpKind<'tcx, T>>;
pub type UseMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type SymbMap<'tcx> = HashMap<&'tcx Place<'tcx>, HashSet<usize>>;
pub type DefMap<'tcx> = HashMap<&'tcx Place<'tcx>, usize>;
pub type ValuesBranchMap<'tcx, T> = HashMap<&'tcx Place<'tcx>, ValueBranchMap<'tcx, T>>;
