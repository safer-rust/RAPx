//! Checker for `ValidString`: UTF-8 validity of tracked byte buffers.

use crate::verify::checkpoint::Checkpoint;
use crate::contract::Property;
use crate::verify::report::{CheckResult, UnknownReason};
use crate::vm::state::VmExecutor;
use z3::{SatResult, Solver};

use super::PropertyChecker;

impl PropertyChecker {
    /// Check tracked UTF-8 bytes, separating proved validity, proved
    /// invalidity, and unresolved symbolic contents.
    fn check_utf8_alloc<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        solver: &Solver<'z3>,
        alloc_id: crate::vm::state::AllocId,
    ) -> CheckResult {
        if vm_state.alloc(alloc_id).facts.dead {
            return CheckResult::Failed;
        }
        if vm_state.is_utf8_trusted(alloc_id) {
            return CheckResult::ProvedByRule;
        }
        let Some(valid) = vm_state.utf8_validity(alloc_id) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };

        solver.push();
        solver.assert(&valid);
        let r = solver.check();
        let unknown_reason = (r == SatResult::Unknown).then(|| UnknownReason::from_solver(solver));
        solver.pop(1);
        if r == SatResult::Unsat {
            return CheckResult::Failed;
        }
        if r == SatResult::Unknown {
            return CheckResult::Unknown(unknown_reason.unwrap());
        }
        solver.push();
        solver.assert(&valid.not());
        let r = solver.check();
        let unknown_reason = (r == SatResult::Unknown).then(|| UnknownReason::from_solver(solver));
        solver.pop(1);
        match r {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => CheckResult::Unknown(UnknownReason::Unimplemented),
            SatResult::Unknown => CheckResult::Unknown(unknown_reason.unwrap()),
        }
    }

    pub(super) fn check_valid_string<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        // Empty byte range: trivially valid UTF-8.
        if let Some(count) = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            && count.as_u64() == Some(0) {
                return CheckResult::ProvedByRule;
            }

        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if let Some(alloc_id) = value.provenance_alloc_id() {
            return self.check_utf8_alloc(vm_state, &solver, alloc_id);
        }

        // A one-argument `ValidString(iter)` targets an `Iterator<Item = u8>`:
        // trace the (possibly `Cloned`/`Rev`-wrapped) iterator to the backing
        // byte buffer of its innermost `Iter`/`IterMut` and UTF-8-check that.
        if let Some(local) = vm_state.find_local_by_address(&value.z3_term)
            && let Some((alloc_id, _end_offset)) = vm_state.iter_utf8_buffer(local) {
                return self.check_utf8_alloc(vm_state, &solver, alloc_id);
            }
        CheckResult::Unknown(UnknownReason::Unimplemented)
    }
}
