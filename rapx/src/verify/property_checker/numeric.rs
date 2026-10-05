//! Checker for `ValidNum`: numeric-interval and predicate reasoning.
//!
//! Evaluates each `NumericPredicate` to a Z3 comparison and discharges it with
//! `assert_all` plus Euclidean-division (NIA) axioms injected for both the
//! contract expression and the VM's computed terms.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::api_classify;
use crate::verify::contract::{
    ContractExpr, NumericBinOp, PlaceBase, Property, PropertyArg, RelOp,
};
use crate::verify::def_use::PlaceKey;
use crate::verify::report::CheckResult;
use crate::verify::vm::state::VmState;
use rustc_hash::FxHashSet;
use rustc_middle::mir::Operand;
use rustc_middle::ty::TyKind;
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_valid_num<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
            if self.all_predicates_are_slice_size_invariant(vm_state, checkpoint, predicates) {
                return CheckResult::ProvedByRule;
            }
            for pred in predicates {
                if let Some(r) =
                    self.eval_numeric_predicate(vm_state, solver, Some(checkpoint), pred)
                {
                    if !r.is_proved() {
                        return r;
                    }
                }
            }
            return CheckResult::ProvedByRule;
        }
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        let ty = Self::ty_arg(property, 1);
        if let Some(ty) = ty {
            let size_bits = vm_state.size_of_ty(ty) * 8;
            if size_bits > 0 && size_bits < 128 {
                if let TyKind::Int(_) = ty.kind() {
                    let half = 1u128 << (size_bits - 1);
                    let min = -(half as i128);
                    let max = (half - 1) as i128;
                    solver.push();
                    let below = value.z3_term.lt(&Int::from_i64(vm_state.z3_ctx, min as i64));
                    let above = value.z3_term.gt(&Int::from_i64(vm_state.z3_ctx, max as i64));
                    solver.assert(&Bool::or(vm_state.z3_ctx, &[&below, &above]));
                    let r = match solver.check() {
                        SatResult::Unsat => CheckResult::ProvedBySmt,
                        SatResult::Sat => CheckResult::Failed,
                        _ => CheckResult::Unknown,
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
                    _ => CheckResult::Unknown,
                };
                solver.pop(1);
                return r;
            }
            return CheckResult::ProvedByRule;
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
            PlaceBase::Local(n) => super::util::local_param_operand(vm_state, ck, n),
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
        let condition = match pred.op {
            RelOp::Le => lhs.le(&rhs),
            RelOp::Lt if is_range => lhs.le(&rhs),
            RelOp::Lt => lhs.lt(&rhs),
            RelOp::Ge => lhs.ge(&rhs),
            RelOp::Gt => lhs.gt(&rhs),
            RelOp::Eq => lhs._eq(&rhs),
            RelOp::Ne => lhs._eq(&rhs).not(),
        };
        solver.push();
        vm_state.assert_all(solver);
        // Bridge the iter_ptr_offset (tracked by post_inc_start) to the
        // predicate's LHS (typically the loop counter `i` in position).
        // At the assert_unchecked(i < n) point, tracked_offset == i + 1
        // because post_inc_start(1) was just called before the check.
        for (_, (off, _)) in vm_state.constraints.term_caches.iter_ptr_offset.iter() {
            let one = Int::from_u64(vm_state.z3_ctx, 1);
            solver.assert(&off._eq(&Int::add(vm_state.z3_ctx, &[&lhs, &one])));
        }
        // For Iter/IterMut Le predicates with rhs computed from fields,
        // inject a lower-bound: the field-based len is >= 1 when the
        // struct's entry contract contains !self.is_empty().
        // Without this, Z3 cannot deduce (end-ptr)/sz >= 1 from != 0.
        if matches!(pred.op, RelOp::Le) {
            if let Some(term) = self.try_get_iter_len_term(vm_state, &pred.rhs) {
                if let Some(one) = lhs.as_u64().or(rhs.as_u64()) {
                    if one == 1 {
                        let one_term = Int::from_u64(vm_state.z3_ctx, 1);
                        solver.assert(&term.ge(&one_term));
                    }
                }
            }
        }
        // NIA helper: inject Euclidean division identity for div operands
        // to help Z3 prove (X/N)*N <= X via X = (X/N)*N + X%N, X%N >= 0.
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.lhs);
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.rhs);
        // Walk VM binary op sources for Div/Rem terms used in the
        // predicate — these are not visible in the ContractExpr tree.
        self.inject_vm_div_axioms(vm_state, solver, &pred.lhs);
        self.inject_vm_div_axioms(vm_state, solver, &pred.rhs);
        // For Ne(pred != 0): assert path conditions so that layout
        // constants (e.g. align_of >= 1) constrain the solver,
        // while regular parameters remain unconstrained.
        if matches!(pred.op, RelOp::Ne) && rhs.as_u64() == Some(0) {
            // Concrete 0 from compiler-evaluated AlignOf/SizeOf for
            // generic types — semantically always >= 1 for non-ZST.
            if lhs.as_u64() == Some(0) {
                return Some(CheckResult::ProvedByRule);
            }
            vm_state.assert_all(solver);
        }
        solver.assert(&condition.not());
        let r0 = solver.check();
        let mut r = match r0 {
            SatResult::Unsat => Some(CheckResult::ProvedBySmt),
            SatResult::Sat => Some(CheckResult::Failed),
            _ => None,
        };
        // If Le/Ge check failed, inject a path-condition-level NIA axiom
        // based on the VM's binary op sources and retry.
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
            solver.assert(&condition.not());
            r = match solver.check() {
                SatResult::Unsat => Some(CheckResult::ProvedBySmt),
                SatResult::Sat => Some(CheckResult::Failed),
                _ => r,
            };
        }
        solver.pop(1);
        r
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
                // Recurse into mul operands in case one is a div
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

        // Walk binary-op producers (recorded on the value) for destinations
        // whose term matches target.
        let op_sources: Vec<(Option<PlaceKey>, Option<PlaceKey>)> = {
            let mut src: Vec<(Option<PlaceKey>, Option<PlaceKey>)> = Vec::new();
            for val in vm_state.current_frame.locals.values() {
                if let Some((lhs, rhs, _)) = val.source.operands() {
                    if val.z3_term == *target {
                        src.push((lhs.clone(), rhs.clone()));
                    }
                }
            }
            src
        };

        let mut already_seen = FxHashSet::default();

        // ── Also recurse through Use / Cast chains: search ALL locals
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

            for dest_val in vm_state.current_frame.locals.values() {
                let Some((lhs, rhs, _)) = dest_val.source.operands() else {
                    continue;
                };
                let lhs_local = lhs.as_ref().and_then(|pk| pk.local());
                let rhs_local = rhs.as_ref().and_then(|pk| pk.local());
                if (lhs_local == Some(local) || rhs_local == Some(local))
                    && !already_seen.contains(&dest_val.z3_term)
                {
                    already_seen.insert(dest_val.z3_term.clone());
                    self.inject_div_axioms_for_term(
                        vm_state,
                        solver,
                        &dest_val.z3_term,
                        depth - 1,
                    );
                }
            }
        }

        // ── Process direct matches ──
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

            // Check if lhs is itself a Div / Rem result
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

            // Recurse into operands
            self.inject_div_axioms_for_term(vm_state, solver, &lhs_val.z3_term, depth - 1);
            self.inject_div_axioms_for_term(vm_state, solver, &rhs_val.z3_term, depth - 1);
        }
    }

    pub(super) fn try_get_iter_len_term<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        let ContractExpr::Len(_) = expr else {
            return None;
        };
        for (_, val) in vm_state.current_frame.locals.iter() {
            let is_iter = match val.ty.kind() {
                TyKind::Ref(_, pointee, _) => match pointee.kind() {
                    TyKind::Adt(adt_def, _) => api_classify::is_std_iter_or_itermut(adt_def.did()),
                    _ => false,
                },
                _ => false,
            };
            if !is_iter {
                continue;
            }
            let alloc_id = val.provenance_alloc_id()?;
            for (&l, lv) in vm_state.current_frame.locals.iter() {
                if lv.provenance_alloc_id() != Some(alloc_id) {
                    continue;
                }
                if let (Some(ptr), Some(end)) =
                    (vm_state.field_value(l, &[0]), vm_state.field_value(l, &[1]))
                {
                    if let Some(len) = vm_state.iter_len_from_ptrs(ptr, end) {
                        return Some(len);
                    }
                }
            }
        }
        None
    }

    pub(super) fn try_iter_len_from_fields<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        use rustc_middle::mir::Place;
        let ContractExpr::Place(cp) = expr else {
            return None;
        };
        let op: &Operand<'tcx> = match cp.base {
            PlaceBase::Arg(n) => checkpoint.args.get(n)?,
            PlaceBase::Local(n) => {
                let callee = checkpoint.callee?;
                let idx = crate::helpers::mir_utils::callee_param_index_for_local(
                    vm_state.tcx,
                    callee,
                    n,
                )?;
                checkpoint.args.get(idx)?
            }
            _ => return None,
        };
        let place: &Place<'tcx> = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let local = place.local;
        let local_val = vm_state.current_frame.locals.get(&local)?;
        let is_iter = match local_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => api_classify::is_std_iter_or_itermut(adt_def.did()),
                _ => false,
            },
            _ => false,
        };
        if !is_iter {
            return None;
        }
        // Direct lookup first, then scan by alloc_id for temp copies.
        if let (Some(ptr), Some(end)) = (
            vm_state.field_value(local, &[0]),
            vm_state.field_value(local, &[1]),
        ) {
            if let Some(len) = vm_state.iter_len_from_ptrs(ptr, end) {
                return Some(len);
            }
        }
        // Fallback: scan all locals for one with same struct alloc.
        let target_alloc = local_val.provenance_alloc_id()?;
        for (&scan_local, scan_val) in vm_state.current_frame.locals.iter() {
            if scan_val.provenance_alloc_id() != Some(target_alloc) {
                continue;
            }
            if let (Some(ptr), Some(end)) = (
                vm_state.field_value(scan_local, &[0]),
                vm_state.field_value(scan_local, &[1]),
            ) {
                if let Some(len) = vm_state.iter_len_from_ptrs(ptr, end) {
                    return Some(len);
                }
            }
        }
        None
    }
}
