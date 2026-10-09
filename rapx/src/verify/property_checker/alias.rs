//! Checkers for `Alias` and `Owning` properties.
//!
//! `Alias` delegates to [`crate::verify::vm::alias::check_alias_vm`]; `Owning`
//! is a simple liveness check on the target allocation.

use crate::helpers::mir_utils;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::Property;
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::VmState;

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_alias<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> CheckResult {
        match crate::verify::vm::alias::check_alias_vm(vm_state, checkpoint) {
            crate::verify::vm::alias::VmAliasResult::Proved => CheckResult::ProvedByRule,
            crate::verify::vm::alias::VmAliasResult::Failed(_msg) => CheckResult::Failed,
            crate::verify::vm::alias::VmAliasResult::Unknown => {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            }
        }
    }

    pub(super) fn check_owning<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let value = self.resolve_pointer_provenance(vm_state, value);
        // `p` may be a pointer just derived from an owner (`Box::into_raw` /
        // `as_mut_ptr`), whose term still points at the owner's address but whose
        // own provenance slot is empty. Fall back to the owner's field provenance.
        let alloc_id = value.provenance_alloc_id().or_else(|| {
            vm_state
                .find_local_by_address(&value.z3_term)
                .and_then(|owner| vm_state.owner_ptr_field(owner))
                .and_then(|v| v.provenance_alloc_id())
        });
        let Some(alloc_id) = alloc_id else {
            return CheckResult::ProvedByRule;
        };
        // `Owning(container.iter())` for_each: every element pointer is the
        // sole owner of its pointee, so a pointer loaded from the container
        // (whose provenance names the container allocation) is a valid owner.
        if vm_state.alloc(alloc_id).facts.for_each.owning {
            return CheckResult::ProvedByRule;
        }
        // Owning(p): p is the sole carrier of *p's ownership. A live `needs_drop`
        // owner whose buffer aliases `alloc_id` means a second owner will drop the
        // same allocation — a double free. The reconstructed owner (the call's
        // destination) is not a violation, so exclude it.
        let dest_local = checkpoint.destination.or_else(|| {
            let body = vm_state.tcx.optimized_mir(checkpoint.caller);
            match &body.basic_blocks[checkpoint.block].terminator().kind {
                rustc_middle::mir::TerminatorKind::Call { destination, .. } => {
                    Some(destination.local)
                }
                _ => None,
            }
        });
        // The local the `Owning(p)` argument names (e.g. `raw` in
        // `Box::from_raw(raw)`), resolved to the caller's local.
        let raw_local = property.target_place().and_then(|cp| match cp.base {
            crate::verify::contract::PlaceBase::Arg(n) => checkpoint
                .args
                .get(n)
                .and_then(|op| mir_utils::operand_mir_place(op).map(|p| p.local)),
            crate::verify::contract::PlaceBase::Local(n) => {
                Some(rustc_middle::mir::Local::from_usize(n))
            }
            crate::verify::contract::PlaceBase::Return => None,
        });
        let live = crate::verify::vm::alias_hazard::live_locals_at(
            vm_state.tcx,
            checkpoint.caller,
            checkpoint.block,
            // `Owning` fires at a call terminator; scan the whole block so a
            // `StorageDead` of a consumed parameter (`Box::into_raw(value)`) in
            // the same block still counts as dead.
            usize::MAX,
            true,
            true,
        );
        let typing_env =
            rustc_middle::ty::TypingEnv::non_body_analysis(vm_state.tcx, checkpoint.caller);
        // `p`'s term often points at the owner's address (e.g. `s.as_mut_ptr()`
        // yields a term `addr__1` for `s`). Trace it back to the owner local and
        // report a second owner directly, without needing its field provenance.
        // A moved-out source still has the same term but its owner-field
        // provenance has been invalidated, so it is not counted as an owner.
        if let Some(owner) = vm_state.find_local_by_address(&value.z3_term) {
            if live.contains(&owner)
                && Some(owner) != dest_local
                && Some(owner) != raw_local
                && vm_state
                    .owner_ptr_field(owner)
                    .is_some_and(|f| f.provenance_alloc_id() == Some(alloc_id))
            {
                let oty = vm_state.body().local_decls[owner].ty;
                if oty.needs_drop(vm_state.tcx, typing_env) {
                    return CheckResult::Failed;
                }
            }
        }
        for local in vm_state.current_frame.local_alloc.keys() {
            if Some(*local) == dest_local {
                continue;
            }
            if !live.contains(local) {
                continue;
            }
            let ty = vm_state.body().local_decls[*local].ty;
            if !ty.needs_drop(vm_state.tcx, typing_env) {
                continue;
            }
            for path in vm_state.field_paths(*local) {
                let Some(val) = vm_state.field_value(*local, &path) else {
                    continue;
                };
                if val.provenance_alloc_id() != Some(alloc_id) {
                    continue;
                }
                return CheckResult::Failed;
            }
        }
        CheckResult::ProvedByRule
    }
}


