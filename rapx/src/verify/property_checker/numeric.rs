//! Checker for `ValidNum`: numeric-interval and predicate reasoning.
//!
//! Evaluates each `NumericPredicate` to a Z3 comparison and discharges it with
//! `assert_all` plus Euclidean-division (NIA) axioms injected for both the
//! contract expression and the VM's computed terms.

use crate::helpers::def_use::PlaceKey;
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::{
    ContractExpr, NumericBinOp, PlaceBase, Property, PropertyArg, RelOp,
};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::VmState;
use rustc_hash::FxHashSet;
use rustc_middle::{mir::Operand, ty::TyKind};
use z3::{
    SatResult, Solver, Tactic,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_valid_num<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
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
        let ty = property.ty_arg(1);
        if let Some(ty) = ty {
            let size_bits = vm_state.size_of_ty(ty) * 8;
            if size_bits > 0 && size_bits < 128 {
                if let TyKind::Int(_) = ty.kind() {
                    let half = 1u128 << (size_bits - 1);
                    let min = -(half as i128);
                    let max = (half - 1) as i128;
                    solver.push();
                    let below = value
                        .z3_term
                        .lt(&Int::from_i64(vm_state.z3_ctx, min as i64));
                    let above = value
                        .z3_term
                        .gt(&Int::from_i64(vm_state.z3_ctx, max as i64));
                    solver.assert(&Bool::or(vm_state.z3_ctx, &[&below, &above]));
                    let r = match solver.check() {
                        SatResult::Unsat => CheckResult::ProvedBySmt,
                        SatResult::Sat => CheckResult::Failed,
                        _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
                    };
                    solver.pop(1);
                    return r;
                }
                let max = Int::from_u64(
                    vm_state.z3_ctx,
                    ((1u128 << size_bits) - 1).min(u64::MAX as u128) as u64,
                );
                solver.push();
                solver.assert(&value.z3_term.gt(&max));
                let r = match solver.check() {
                    SatResult::Unsat => CheckResult::ProvedBySmt,
                    SatResult::Sat => CheckResult::Failed,
                    _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
                };
                solver.pop(1);
                return r;
            }
        }
        CheckResult::ProvedByRule
    }

    /// If `expr` is a `SliceIndex` range parameter (e.g. `..n`), return its
    /// *exclusive* end term, so `ValidNum(index < CAPACITY)` compares `n` (not
    /// the opaque range value).
    fn range_end_of_lhs<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
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
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
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
        // Div/Rem producers are recorded by the VM, outside ContractExpr.
        self.inject_vm_div_axioms(vm_state, solver, &pred.lhs);
        self.inject_vm_div_axioms(vm_state, solver, &pred.rhs);
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
            self.inject_vm_div_axioms(vm_state, solver, &pred.lhs);
            self.inject_vm_div_axioms(vm_state, solver, &pred.rhs);
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
                op: NumericBinOp::Mul,
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
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) {
        match expr {
            ContractExpr::Place(_) => {
                let Some(v) = vm_state.eval_contract_expr_to_value(checkpoint, expr) else {
                    return;
                };
                let bits = vm_state.size_of_ty(v.ty) * 8;
                if !(bits > 0 && bits < 128) {
                    return;
                }
                let Some((min, max)) =
                    crate::verify::contract::resolve::int_type_min_max(vm_state.tcx, v.ty)
                else {
                    return;
                };
                let Some(term) = self.eval_contract_expr(vm_state, checkpoint, expr) else {
                    return;
                };
                match v.ty.kind() {
                    TyKind::Int(_) => {
                        solver.assert(
                            &term.ge(&Int::from_i64(vm_state.z3_ctx, -(min as i128) as i64)),
                        );
                        solver.assert(&term.le(&Int::from_i64(vm_state.z3_ctx, max as i64)));
                    }
                    TyKind::Uint(_) => {
                        solver.assert(&term.ge(&Int::from_u64(vm_state.z3_ctx, 0)));
                        solver.assert(&term.le(&Int::from_u64(vm_state.z3_ctx, max as u64)));
                    }
                    _ => {}
                }
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
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) {
        match expr {
            ContractExpr::Binary {
                op: NumericBinOp::Div,
                lhs,
                rhs,
            } => {
                if let (Some(l), Some(r)) = (
                    self.eval_contract_expr(vm_state, checkpoint, lhs),
                    self.eval_contract_expr(vm_state, checkpoint, rhs),
                ) {
                    let zero = Int::from_u64(vm_state.z3_ctx, 0);
                    let mul_term = Int::mul(vm_state.z3_ctx, &[&l.div(&r), &r]);
                    let rem_term = l.rem(&r);
                    let sum_term = Int::add(vm_state.z3_ctx, &[&mul_term, &rem_term]);
                    solver.assert(&l._eq(&sum_term));
                    solver.assert(&rem_term.ge(&zero));
                }
            }
            ContractExpr::Binary {
                op: NumericBinOp::Mul,
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

    pub(super) fn inject_vm_div_axioms<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        expr: &ContractExpr<'tcx>,
    ) {
        let Some(val) = self.eval_contract_expr(vm_state, None, expr) else {
            return;
        };
        self.inject_div_axioms_for_term(vm_state, solver, &val, 4);
    }

    pub(super) fn inject_div_axioms_for_term<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        target: &Int<'z3>,
        depth: usize,
    ) {
        if depth == 0 {
            return;
        }

        let op_sources: Vec<(Option<PlaceKey>, Option<PlaceKey>)> = {
            let mut src: Vec<(Option<PlaceKey>, Option<PlaceKey>)> = Vec::new();
            for (_, val) in vm_state.all_local_values() {
                if let Some((lhs, rhs, _)) = val.source.operands()
                    && val.z3_term == *target
                {
                    src.push((lhs.clone(), rhs.clone()));
                }
            }
            src
        };

        let mut already_seen = FxHashSet::default();

        // whose term equals target, and for each binary-op entry
        // that *consumes* that local as an operand, walk the destination.
        for local_idx in 0..vm_state.body().local_decls.len() {
            let local = rustc_middle::mir::Local::from_usize(local_idx);
            let Some(val) = vm_state.local_value(local) else {
                continue;
            };
            if val.z3_term != *target {
                continue;
            }

            for (_, dest_val) in vm_state.all_local_values() {
                let Some((lhs, rhs, _)) = dest_val.source.operands() else {
                    continue;
                };
                let lhs_local = lhs.as_ref().and_then(|pk| pk.local());
                let rhs_local = rhs.as_ref().and_then(|pk| pk.local());
                if (lhs_local == Some(local) || rhs_local == Some(local))
                    && !already_seen.contains(&dest_val.z3_term)
                {
                    already_seen.insert(dest_val.z3_term.clone());
                    self.inject_div_axioms_for_term(vm_state, solver, &dest_val.z3_term, depth - 1);
                }
            }
        }

        for (lhs_pk, rhs_pk) in &op_sources {
            let (Some(lhs_pk), Some(rhs_pk)) = (lhs_pk, rhs_pk) else {
                continue;
            };
            let (Some(lhs_local), Some(rhs_local)) = (lhs_pk.local(), rhs_pk.local()) else {
                continue;
            };
            let (Some(lhs_val), Some(rhs_val)) = (
                vm_state.local_value(lhs_local),
                vm_state.local_value(rhs_local),
            ) else {
                continue;
            };

            if let Some((div_lhs_pk, div_rhs_pk)) = lhs_pk
                .local()
                .and_then(|l| vm_state.local_value(l))
                .and_then(|v| v.source.operands().map(|(l, r, _)| (l.clone(), r.clone())))
            {
                let Some(div_lhs_local) = div_lhs_pk.and_then(|pk| pk.local()) else {
                    continue;
                };
                let Some(div_rhs_local) = div_rhs_pk.and_then(|pk| pk.local()) else {
                    continue;
                };
                let Some(div_lhs_val) = vm_state.local_value(div_lhs_local) else {
                    continue;
                };
                let Some(div_rhs_val) = vm_state.local_value(div_rhs_local) else {
                    continue;
                };

                let quot = div_lhs_val.z3_term.div(&div_rhs_val.z3_term);
                let rem = div_lhs_val.z3_term.rem(&div_rhs_val.z3_term);
                let mul_term = Int::mul(vm_state.z3_ctx, &[&quot, &div_rhs_val.z3_term]);
                let sum_term = Int::add(vm_state.z3_ctx, &[&mul_term, &rem]);
                solver.assert(&div_lhs_val.z3_term._eq(&sum_term));
                let zero = Int::from_u64(vm_state.z3_ctx, 0);
                solver.assert(&rem.ge(&zero));
                solver.assert(&mul_term.le(&div_lhs_val.z3_term));
            }

            self.inject_div_axioms_for_term(vm_state, solver, &lhs_val.z3_term, depth - 1);
            self.inject_div_axioms_for_term(vm_state, solver, &rhs_val.z3_term, depth - 1);
        }
    }
}
