//! VM adapters for type-level `Send`/`Sync` property checks.

use crate::verify::auto_trait::{
    atomic_update_check, contain_no_type_check, no_internal_mut_check, no_raw_ptr_check,
    ref_send_check, uni_internal_mut_check,
};
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::{Property, PropertyArg};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::VmExecutor;

use super::PropertyChecker;

impl PropertyChecker {
    /// `ContainNoType(T, bad1, bad2, ...)`: `T` must not structurally contain any of
    /// the named negative types.
    pub(super) fn check_contain_no_type<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let negatives: Vec<String> = property.args()[1..]
            .iter()
            .filter_map(|a| match a {
                PropertyArg::Ident(name) => Some(name.clone()),
                _ => None,
            })
            .collect();
        if negatives.is_empty() {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        contain_no_type_check(vm_state.tcx, ty, &negatives, checkpoint.caller, false)
    }

    /// `NoRawPtr(T)`: `T` must have no raw pointers.
    pub(super) fn check_no_raw_ptr<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        no_raw_ptr_check(vm_state.tcx, ty, checkpoint.caller, false)
    }

    /// `NoInternalMut(T)`: `T` must have no interior mutation through raw pointers.
    pub(super) fn check_no_internal_mut<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        _checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        no_internal_mut_check(vm_state.tcx, ty)
    }

    /// `UniInternalMut(T)`: `T`'s interior mutation must be unique (exclusive
    /// owner, no aliasing `Clone`).
    pub(super) fn check_uni_internal_mut<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        _checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        uni_internal_mut_check(vm_state.tcx, ty)
    }

    /// `AtomicUpdate(T)`: `T`'s raw-pointer updates are guarded by a
    /// synchronization primitive (`Mutex`/`RwLock`) or performed atomically
    /// (`Atomic*`).
    pub(super) fn check_atomic_update<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        atomic_update_check(vm_state.tcx, ty, checkpoint.caller, false)
    }

    /// `RefSend(T)`: every interior-mutability (`UnsafeCell`) / raw-pointer
    /// field of `T` must be guarded by a synchronization primitive.
    pub(super) fn check_ref_send<'z3, 'tcx>(
        &self,
        vm_state: &VmExecutor<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.try_type_arg_at(0) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        ref_send_check(vm_state.tcx, ty, checkpoint.caller, true)
    }
}
