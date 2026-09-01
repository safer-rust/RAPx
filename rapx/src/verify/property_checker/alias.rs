//! Checkers for `Alias` and `Owning` properties.
//!
//! `Alias` delegates to [`crate::verify::vm::alias::check_alias_vm`]; `Owning`
//! is a simple liveness check on the target allocation.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::Property;
use crate::verify::report::CheckResult;
use crate::verify::vm::state::VmState;
use z3::Solver;

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_alias<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        match crate::verify::vm::alias::check_alias_vm(vm_state, checkpoint, property) {
            crate::verify::vm::alias::VmAliasResult::Proved => CheckResult::Proved,
            crate::verify::vm::alias::VmAliasResult::Failed(_msg) => CheckResult::Failed,
            crate::verify::vm::alias::VmAliasResult::Unknown => CheckResult::Unknown,
        }
    }

    pub(super) fn check_owning<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        if let Some(id) = value.provenance_alloc_id() {
            if vm_state.alloc(id).dead {
                return CheckResult::Failed;
            }
            return CheckResult::Proved;
        }
        CheckResult::Unknown
    }
}
