//! Transfer functions for MIR terminators.

use rustc_middle::mir::{BasicBlock, Operand, Place, SwitchTargets};
use z3::ast::{Ast, Int};

use super::super::state::{ValueSource, VmState};
use crate::helpers::def_use::PlaceKey;

pub(crate) fn exec_switch_int<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    discr: &Operand<'tcx>,
    targets: &SwitchTargets,
    switch_succ: Option<BasicBlock>,
) {
    let discr_val = state.value_of_operand(discr);
    let known_value = match &discr_val.source {
        ValueSource::Comparison { cond, .. } => cond.simplify().as_bool().map(u64::from),
        ValueSource::CallsiteConst | ValueSource::KnownDiscriminant(_) => {
            discr_val.z3_term.simplify().as_u64()
        }
        _ => None,
    };
    if !state.unsupported_mir
        && !state.incomplete_inline_branch
        && let Some(value) = known_value
        && let Some(chosen) = switch_succ
    {
        let actual = targets
            .iter()
            .find(|(candidate, _)| *candidate == value as u128)
            .map(|(_, target)| target)
            .unwrap_or_else(|| targets.otherwise());
        if actual != chosen {
            state.path_infeasible = true;
            return;
        }
    }
    if VmState::term_involves(&state.inline.opaque_intrinsic_terms, &discr_val.z3_term) {
        state.record_opaque_control_flow("SwitchInt");
    }

    // If the discriminator is a comparison result, record the direct boolean
    // condition alongside the ite-encoded `discr == value` fact, so the SMT
    // solver can reason about `offset <= len` directly.
    let cmp_cond = discr_val.bool_cond().cloned();

    if let Some(chosen) = switch_succ {
        for (value, target) in targets.iter() {
            if target == chosen {
                let val_term = Int::from_u64(state.z3_ctx, value as u64);
                state
                    .constraints
                    .assertions
                    .push(discr_val.z3_term._eq(&val_term));
                if value != 0 {
                    if let Some(ref cond) = cmp_cond {
                        state.constraints.assertions.push(cond.clone());
                    }
                    state.infer_switch_guard(discr);
                } else if let Some(ref cond) = cmp_cond {
                    state.constraints.assertions.push(cond.not());
                }
                return;
            }
        }
        if targets.otherwise() == chosen {
            for (value, _) in targets.iter() {
                let val_term = Int::from_u64(state.z3_ctx, value as u64);
                state
                    .constraints
                    .assertions
                    .push(discr_val.z3_term._eq(&val_term).not());
            }
            if let Some(ref cond) = cmp_cond {
                // For a boolean discriminator, `otherwise` means the comparison
                // result is *not* any explicit value:
                //   - targets include 0 → `discr != 0` → comparison true;
                //   - targets include 1 → `discr != 1` → comparison false.
                if targets.iter().any(|(v, _)| v == 0) {
                    state.constraints.assertions.push(cond.clone());
                } else if targets.iter().any(|(v, _)| v == 1) {
                    state.constraints.assertions.push(cond.not());
                }
            }
        }
    }
}

pub(crate) fn exec_assert<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
) {
    let cond_val = state.value_of_operand(cond);
    if VmState::term_involves(&state.inline.opaque_intrinsic_terms, &cond_val.z3_term) {
        state.record_opaque_control_flow("Assert");
    }
    // If the asserted operand is a comparison result, record the direct boolean
    // condition (`idx < len`) alongside the ite-encoded fact, so the SMT solver
    // can unfold it (mirrors `exec_switchint`).
    let cmp_cond = cond_val.bool_cond().cloned();
    let zero = Int::from_u64(state.z3_ctx, 0);
    if expected {
        state
            .constraints
            .assertions
            .push(cond_val.z3_term._eq(&zero).not());
        if let Some(c) = &cmp_cond {
            state.constraints.assertions.push(c.clone());
        }
    } else {
        state
            .constraints
            .assertions
            .push(cond_val.z3_term._eq(&zero));
        if let Some(c) = &cmp_cond {
            state.constraints.assertions.push(c.not());
        }
    }

    state.infer_guard_non_null(cond, expected);
    // Infer alignment from == 0 guards on Rem expressions
    state.infer_guard_align(cond, expected);
}

pub(crate) fn exec_drop<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
) {
    if let Some(alloc_id) = state.current_frame.local_alloc.get(&place.local).copied() {
        state.alloc_mut(alloc_id).facts.dead = true;
        let is_param = place.local.as_usize() <= state.body().arg_count;
        if !is_param {
            let ty = state.body().local_decls[place.local].ty;
            if let Some(data_id) = state.container_data_alloc(alloc_id, ty) {
                state.alloc_mut(data_id).facts.dead = true;
            }
        }
    }
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// The `(lhs, rhs, op)` of the binary-op/comparison source recorded on the
    /// value bound to `pk`'s local, if any.
    fn op_source_of(
        &self,
        pk: &PlaceKey,
    ) -> Option<(Option<PlaceKey>, Option<PlaceKey>, rustc_middle::mir::BinOp)> {
        let local = pk.local()?;
        let val = self.local_value(local)?;
        val.source
            .operands()
            .map(|(l, r, o)| (l.clone(), r.clone(), o))
    }

    /// The `PlaceKey` of a `Copy`/`Move` operand.
    fn operand_place_key(op: &Operand<'tcx>) -> Option<PlaceKey> {
        match op {
            Operand::Copy(p) | Operand::Move(p) => Some(PlaceKey::from_mir_place(p)),
            _ => None,
        }
    }

    /// Infer alignment constraints from guards of the form `(x % n) == 0`.
    fn infer_guard_align(&mut self, cond: &Operand<'tcx>, expected: bool) {
        if !expected {
            return;
        }
        let Some(cond_pk) = Self::operand_place_key(cond) else {
            return;
        };

        if let Some((lhs_pk, rhs_pk, _)) = self.op_source_of(&cond_pk) {
            let inner_pk = match (&lhs_pk, &rhs_pk) {
                (Some(pk), None) => pk.clone(),
                (None, Some(pk)) => pk.clone(),
                _ => return,
            };
            if let Some((div_lhs, div_rhs, inner_op)) = self.op_source_of(&inner_pk) {
                match inner_op {
                    // `x % n == 0`: div_rhs is the concrete divisor constant.
                    rustc_middle::mir::BinOp::Rem => {
                        if let Some(divisor) = resolve_u64_from_place_key(&div_rhs, self)
                            && divisor > 0 {
                                self.mark_align_n(&div_lhs, Int::from_u64(self.z3_ctx, divisor));
                            }
                    }
                    // `x & (align-1) == 0`: the mask is `align-1` (symbolic for a
                    // generic `T`), so `align = mask + 1`.
                    rustc_middle::mir::BinOp::BitAnd => {
                        if let Some(rhs_local) = div_rhs.as_ref().and_then(|pk| pk.local())
                            && let Some(rhs_val) = self.local_value(rhs_local) {
                                let one = Int::from_u64(self.z3_ctx, 1);
                                let align = Int::add(self.z3_ctx, &[&rhs_val.z3_term, &one]);
                                self.mark_align_n(&div_lhs, align);
                            }
                    }
                    _ => {}
                }
            }
        }
    }

    fn mark_align_n(&mut self, src_pk: &Option<PlaceKey>, align: Int<'z3>) {
        if let Some(src_pk) = src_pk
            && let Some(local) = src_pk.local()
                && let Some(mut val) = self.local_value(local).cloned() {
                    val.facts.align_n = Some(align);
                    self.set_local(local, val);
                }
    }

    /// Infer non_null invariants from branch guards.
    fn infer_guard_non_null(&mut self, cond: &Operand<'tcx>, expected: bool) {
        if !expected {
            return;
        }
        let Some(cond_pk) = Self::operand_place_key(cond) else {
            return;
        };

        // Check if cond was defined by BinaryOp(Ne, (ptr, 0)) or similar:
        // mark the non-constant side as non-null.  Only `Ne` guards imply
        // non-nullness; an `Eq` guard (`assert (addr & mask) == 0`, the
        // alignment check) means the value *is* zero, not non-null.
        if let Some((lhs_pk, rhs_pk, op)) = self.op_source_of(&cond_pk) {
            if op != rustc_middle::mir::BinOp::Ne {
                return;
            }
            if rhs_pk.is_none() {
                self.mark_guard_pointer(&lhs_pk, &None);
            }
            if lhs_pk.is_none() {
                self.mark_guard_pointer(&rhs_pk, &None);
            }
        }
    }

    /// Infer non_null from SwitchInt discriminant.
    fn infer_switch_guard(&mut self, discr: &Operand<'tcx>) {
        let Some(pk) = Self::operand_place_key(discr) else {
            return;
        };
        if let Some((lhs_pk, rhs_pk, _)) = self.op_source_of(&pk) {
            self.mark_guard_pointer(&lhs_pk, &rhs_pk);
        }
    }

    fn mark_guard_pointer(&mut self, lhs: &Option<PlaceKey>, rhs: &Option<PlaceKey>) {
        for pk in [lhs, rhs].into_iter().flatten() {
            if let Some(local) = pk.local()
                && let Some(mut val) = self.local_value(local).cloned() {
                    val.facts.non_null = true;
                    self.set_local(local, val);
                }
        }
    }

}

/// Try to resolve a u64 constant from a PlaceKey's source in the VM state.
fn resolve_u64_from_place_key<'z3, 'tcx>(
    pk: &Option<PlaceKey>,
    state: &VmState<'z3, 'tcx>,
) -> Option<u64> {
    let pk = pk.as_ref()?;
    let local = pk.local()?;
    let val = state.local_value(local)?;
    val.z3_term.as_u64()
}
