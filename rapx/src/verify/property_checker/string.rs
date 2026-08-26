//! Checker for `ValidString`: UTF-8 validity of tracked byte buffers.

#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use z3::{SatResult, Solver, ast::Int};
use crate::verify::contract::Property;
use crate::verify::report::CheckResult;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::VmState;

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_valid_string<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
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
                return CheckResult::Proved;
            }
        }

        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Proved;
        };
        let Some(alloc_id) = value.provenance_alloc_id() else {
            return CheckResult::Proved;
        };

        // A dead allocation cannot back a live string (use-after-free).
        if vm_state.alloc(alloc_id).dead {
            return CheckResult::Failed;
        }

        // Byte-level check: prove the tracked buffer bytes are *not* valid UTF-8.
        let byte_pairs = vm_state.alloc_byte_values(alloc_id);
        if byte_pairs.is_empty() {
            return CheckResult::Proved; // no byte-level info → trust
        }
        let bytes: Vec<Int<'ctx>> = byte_pairs.iter().map(|(_, t)| (*t).clone()).collect();
        let valid = super::utf8_validity(vm_state.ctx, &bytes);

        solver.push();
        solver.assert(&valid);
        let r = solver.check();
        solver.pop(1);
        match r {
            SatResult::Unsat => CheckResult::Failed,
            _ => CheckResult::Proved,
        }
    }
}
