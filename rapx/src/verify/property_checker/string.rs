//! Checker for `ValidString`: UTF-8 validity of tracked byte buffers.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::Property;
use crate::verify::report::CheckResult;
use crate::verify::vm::state::VmState;
use z3::{SatResult, Solver};

use super::PropertyChecker;

impl PropertyChecker {
    /// Shared UTF-8 byte check: prove the tracked buffer bytes of `alloc_id` are
    /// *not* valid UTF-8 (i.e. disprove the DFA), reporting `Failed` when the
    /// solver proves they cannot be valid.
    fn check_utf8_alloc<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        alloc_id: crate::verify::vm::state::AllocId,
    ) -> CheckResult {
        if vm_state.alloc(alloc_id).facts.dead {
            return CheckResult::Failed;
        }
        if vm_state.is_utf8_trusted(alloc_id) {
            return CheckResult::ProvedByRule;
        }
        let Some(valid) = vm_state.utf8_validity(alloc_id) else {
            return CheckResult::ProvedByRule; // no byte-level info → trust
        };

        solver.push();
        solver.assert(&valid);
        let r = solver.check();
        solver.pop(1);
        match r {
            SatResult::Unsat => CheckResult::Failed,
            _ => CheckResult::ProvedByRule,
        }
    }

    pub(super) fn check_valid_string<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Empty byte range: trivially valid UTF-8.
        if let Some(count) = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
        {
            if count.as_u64() == Some(0) {
                return CheckResult::ProvedByRule;
            }
        }

        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::ProvedByRule;
        };
        if let Some(alloc_id) = value.provenance_alloc_id() {
            return self.check_utf8_alloc(vm_state, solver, alloc_id);
        }

        // A one-argument `ValidString(iter)` targets an `Iterator<Item = u8>`:
        // trace the (possibly `Cloned`/`Rev`-wrapped) iterator to the backing
        // byte buffer of its innermost `Iter`/`IterMut` and UTF-8-check that.
        if let Some(local) = vm_state.find_local_by_address(&value.z3_term) {
            if let Some((alloc_id, _end_offset)) = vm_state.iter_utf8_buffer(local) {
                return self.check_utf8_alloc(vm_state, solver, alloc_id);
            }
        }
        CheckResult::ProvedByRule
    }
}
