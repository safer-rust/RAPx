//! Checker for `ValidNum`: numeric-interval and predicate reasoning.
//!
//! Evaluates each `NumericPredicate` to a Z3 comparison and discharges it with
//! `assert_all` plus guarded Euclidean-division identities for mathematical
//! contract expressions. Machine-integer relations come from the VM itself.

use crate::def_ids::intrinsic_api;
use crate::verify::call_summary;
use crate::verify::checkpoint::Checkpoint;
use crate::contract::{
    ContractExpr, BinOp, PlaceBase, Property, PropertyArg, PropertyKind, RelOp,
};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::vm::state::VmExecutor;
use rustc_middle::mir::Operand;
use z3::{
    SatResult, Solver, Tactic,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    /// Check all numeric disjuncts against one shared counterexample.
    pub(super) fn check_valid_num_disjunction<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<CheckResult> {
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        let mut disjuncts = Vec::new();
        for disjunct in property.disjuncts() {
            let Property::Atom(atom) = disjunct else {
                return None;
            };
            if atom.kind != PropertyKind::ValidNum {
                return None;
            }
            let Some(PropertyArg::Predicates(predicates)) = atom.args.first() else {
                return None;
            };
            let mut conjuncts = Vec::new();
            for pred in predicates {
                let (lhs, is_range) =
                    match self.range_end_of_lhs(vm_state, Some(checkpoint), &pred.lhs) {
                        Some(end) => (end, true),
                        None => (
                            self.eval_contract_expr(vm_state, Some(checkpoint), &pred.lhs)?,
                            false,
                        ),
                    };
                let rhs = self.eval_contract_expr(vm_state, Some(checkpoint), &pred.rhs)?;
                let op = if is_range && matches!(pred.op, RelOp::Lt) {
                    RelOp::Le
                } else {
                    pred.op
                };
                conjuncts.push(vm_state.contract_relop_bool(op, &lhs, &rhs));
                self.inject_nia_axioms(vm_state, &solver, Some(checkpoint), &pred.lhs);
                self.inject_nia_axioms(vm_state, &solver, Some(checkpoint), &pred.rhs);
                self.inject_int_range_axioms(vm_state, &solver, Some(checkpoint), &pred.lhs);
                self.inject_int_range_axioms(vm_state, &solver, Some(checkpoint), &pred.rhs);
            }
            if conjuncts.is_empty() {
                return None;
            }
            let parts: Vec<_> = conjuncts.iter().collect();
            disjuncts.push(Bool::and(vm_state.z3_ctx, &parts));
        }
        let parts: Vec<_> = disjuncts.iter().collect();
        let condition = Bool::or(vm_state.z3_ctx, &parts);
        solver.assert(&condition.not());
        Some(match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => CheckResult::Failed,
            SatResult::Unknown => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        })
    }

    pub(super) fn check_valid_num<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        if intrinsic_api::intrinsic_name(vm_state.tcx, checkpoint.callee)
            .is_some_and(|name| name.as_str() == "float_to_int_unchecked")
            && let (Some(input), Some(dest)) = (checkpoint.args.first(), checkpoint.destination)
            && call_summary::constant_float_to_int(
                vm_state.tcx, input, vm_state.body().local_decls[dest].ty).is_some()
        {
            return CheckResult::ProvedByRule;
        }
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
            if self.all_predicates_are_slice_size_invariant(vm_state, checkpoint, predicates) {
                return CheckResult::ProvedByRule;
            }
            for pred in predicates {
                match self.eval_numeric_predicate(vm_state, &solver, Some(checkpoint), pred) {
                    Some(r) if !r.is_proved() => return r,
                    None => {
                        return CheckResult::Unknown(UnknownReason::Unimplemented);
                    }
                    _ => {}
                }
            }
            return CheckResult::ProvedByRule;
        }
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if let Some(layout) = property
            .try_type_arg_at(1)
            .and_then(|ty| vm_state.integer_layout(ty))
        {
            solver.push();
            solver.assert(&layout.in_domain(vm_state.z3_ctx, &value.z3_term).not());
            let result = match solver.check() {
                SatResult::Unsat => CheckResult::ProvedBySmt,
                SatResult::Sat => CheckResult::Failed,
                _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
            };
            solver.pop(1);
            return result;
        }
        CheckResult::ProvedByRule
    }

    /// If `expr` is a `SliceIndex` range parameter (e.g. `..n`), return its
    /// *exclusive* end term, so `ValidNum(index < CAPACITY)` compares `n` (not
    /// the opaque range value).
    fn range_end_of_lhs<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        let cp = match expr {
            ContractExpr::Place(cp) => cp,
            _ => return None,
        };
        if !cp.projections.is_empty() {
            return None;
        }
        let ck = checkpoint?;
        let op: Option<&Operand<'tcx>> = match cp.base {
            PlaceBase::Arg(n) => ck.args.get(n),
            PlaceBase::Local(n) => vm_state.callsite_operand_for_local(ck, n),
            _ => None,
        };
        let op = op?;
        let end = self.extract_range_end(vm_state, op)?;
        Some(end.z3_term.clone())
    }

    pub(super) fn eval_numeric_predicate<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        pred: &crate::contract::NumericPredicate<'tcx>,
    ) -> Option<CheckResult> {
        // For a `SliceIndex` range (e.g. `..n`), `ValidNum(index < CAPACITY)`
        // must compare the range's *exclusive end* (`n <= CAPACITY`) rather than
        // the opaque range value. Detect ranges and adjust `<` to `<=`.
        let (lhs, is_range) = match self.range_end_of_lhs(vm_state, checkpoint, &pred.lhs) {
            Some(end) => (end, true),
            None => (
                self.eval_contract_expr(vm_state, checkpoint, &pred.lhs)?,
                false,
            ),
        };
        let rhs = self.eval_contract_expr(vm_state, checkpoint, &pred.rhs)?;
        let op = if is_range && matches!(pred.op, RelOp::Lt) {
            RelOp::Le
        } else {
            pred.op
        };
        let condition = vm_state.contract_relop_bool(op, &lhs, &rhs);
        solver.push();
        vm_state.assert_all(solver);
        // A predicate argument can be a boolean, so it cannot be equated with
        // an iterator's numeric offset. Use only relations from the VM path.
        // NIA helper: inject Euclidean division identity for div operands
        // to help Z3 prove (X/N)*N <= X via X = (X/N)*N + X%N, X%N >= 0.
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.lhs);
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.rhs);
        // The VM already supplies machine-integer division semantics. Rebuilding
        // its terms with mathematical division would change signed rounding.
        self.inject_int_range_axioms(vm_state, solver, checkpoint, &pred.lhs);
        self.inject_int_range_axioms(vm_state, solver, checkpoint, &pred.rhs);
        if matches!(pred.op, RelOp::Ne) && rhs.as_u64() == Some(0) {
            vm_state.assert_all(solver);
        }
        solver.assert(&condition.not());
        let r0 = solver.check();
        let mut unknown_reason =
            (r0 == SatResult::Unknown).then(|| UnknownReason::from_solver(solver));
        let mut r = match r0 {
            SatResult::Unsat => Some(CheckResult::ProvedBySmt),
            SatResult::Sat => Some(CheckResult::Failed),
            _ => None,
        };
        if matches!(r, Some(CheckResult::Failed))
            && matches!(pred.op, RelOp::Le | RelOp::Ge | RelOp::Lt | RelOp::Gt)
        {
            solver.pop(1);
            solver.push();
            vm_state.assert_all(solver);
            self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.lhs);
            self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.rhs);
            self.inject_int_range_axioms(vm_state, solver, checkpoint, &pred.lhs);
            self.inject_int_range_axioms(vm_state, solver, checkpoint, &pred.rhs);
            solver.assert(&condition.not());
            r = match solver.check() {
                SatResult::Unsat => Some(CheckResult::ProvedBySmt),
                SatResult::Sat => Some(CheckResult::Failed),
                _ => r,
            };
        }
        solver.pop(1);
        // If NIA left the check inconclusive and the predicate involves a
        // multiplication, retry with bit-blasting (`nla2bv`), which is decidable
        // for the bounded integer variables the range axioms pin down.
        if r.is_none() && (self.expr_has_mul(&pred.lhs) || self.expr_has_mul(&pred.rhs)) {
            let bv_solver = Tactic::new(vm_state.z3_ctx, "nla2bv").solver();
            vm_state.assert_all(&bv_solver);
            self.inject_nia_axioms(vm_state, &bv_solver, checkpoint, &pred.lhs);
            self.inject_nia_axioms(vm_state, &bv_solver, checkpoint, &pred.rhs);
            self.inject_int_range_axioms(vm_state, &bv_solver, checkpoint, &pred.lhs);
            self.inject_int_range_axioms(vm_state, &bv_solver, checkpoint, &pred.rhs);
            bv_solver.assert(&condition.not());
            r = match bv_solver.check() {
                SatResult::Unsat => Some(CheckResult::ProvedBySmt),
                SatResult::Sat => Some(CheckResult::Failed),
                SatResult::Unknown => {
                    unknown_reason = Some(UnknownReason::from_solver(&bv_solver));
                    r
                }
            };
        }
        r.or_else(|| {
            Some(CheckResult::Unknown(
                unknown_reason.unwrap_or(UnknownReason::Unimplemented),
            ))
        })
    }

    fn expr_has_mul<'tcx>(&self, expr: &ContractExpr<'tcx>) -> bool {
        match expr {
            ContractExpr::Binary {
                op: BinOp::Mul,
                ..
            } => true,
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.expr_has_mul(lhs) || self.expr_has_mul(rhs)
            }
            ContractExpr::Unary { expr, .. } => self.expr_has_mul(expr),
            ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
                self.expr_has_mul(inner)
            }
            ContractExpr::MethodCall { receiver, args, .. } => {
                self.expr_has_mul(receiver) || args.iter().any(|arg| self.expr_has_mul(arg))
            }
            ContractExpr::If {
                then_expr,
                else_expr,
                ..
            } => self.expr_has_mul(then_expr) || self.expr_has_mul(else_expr),
            _ => false,
        }
    }

    /// Inject `T::MIN <= term <= T::MAX` for every integer-typed place in
    /// `expr`, so that range-redundant bounds (e.g. `lhs - rhs <= u32::MAX`
    /// for `unchecked_sub`) become provable from the operands' types alone.
    fn inject_int_range_axioms<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) {
        match expr {
            ContractExpr::Place(_) => {
                let Some(v) = vm_state.eval_contract_expr_to_value(checkpoint, expr) else {
                    return;
                };
                let Some(layout) = vm_state.integer_layout(v.ty) else {
                    return;
                };
                let Some(term) = self.eval_contract_expr(vm_state, checkpoint, expr) else {
                    return;
                };
                solver.assert(&layout.in_domain(vm_state.z3_ctx, &term));
            }
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.inject_int_range_axioms(vm_state, solver, checkpoint, lhs);
                self.inject_int_range_axioms(vm_state, solver, checkpoint, rhs);
            }
            ContractExpr::Unary { expr, .. } => {
                self.inject_int_range_axioms(vm_state, solver, checkpoint, expr);
            }
            ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
                self.inject_int_range_axioms(vm_state, solver, checkpoint, inner);
            }
            ContractExpr::MethodCall { receiver, args, .. } => {
                self.inject_int_range_axioms(vm_state, solver, checkpoint, receiver);
                for arg in args {
                    self.inject_int_range_axioms(vm_state, solver, checkpoint, arg);
                }
            }
            ContractExpr::If {
                then_expr,
                else_expr,
                ..
            } => {
                self.inject_int_range_axioms(vm_state, solver, checkpoint, then_expr);
                self.inject_int_range_axioms(vm_state, solver, checkpoint, else_expr);
            }
            _ => {}
        }
    }

    pub(super) fn inject_nia_axioms<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) {
        match expr {
            ContractExpr::Binary {
                op: BinOp::Div,
                lhs,
                rhs,
            } => {
                if let (Some(l), Some(r)) = (
                    self.eval_contract_expr(vm_state, checkpoint, lhs),
                    self.eval_contract_expr(vm_state, checkpoint, rhs),
                ) {
                    let zero = Int::from_u64(vm_state.z3_ctx, 0);
                    let mul_term = Int::mul(vm_state.z3_ctx, &[&l.div(&r), &r]);
                    // Contract division is mathematical Z3 Int division, whose
                    // matching remainder is modulo, including negative divisors.
                    // No identity is valid for a zero divisor.
                    let rem_term = l.modulo(&r);
                    let sum_term = Int::add(vm_state.z3_ctx, &[&mul_term, &rem_term]);
                    let nonzero = r._eq(&zero).not();
                    solver.assert(&nonzero.implies(&l._eq(&sum_term)));
                    solver.assert(&nonzero.implies(&rem_term.ge(&zero)));
                }
            }
            ContractExpr::Binary {
                op: BinOp::Mul,
                lhs,
                rhs,
            } => {
                self.inject_nia_axioms(vm_state, solver, checkpoint, lhs);
                self.inject_nia_axioms(vm_state, solver, checkpoint, rhs);
            }
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.inject_nia_axioms(vm_state, solver, checkpoint, lhs);
                self.inject_nia_axioms(vm_state, solver, checkpoint, rhs);
            }
            ContractExpr::Unary { expr: inner, .. } => {
                self.inject_nia_axioms(vm_state, solver, checkpoint, inner);
            }
            _ => {}
        }
    }
}
