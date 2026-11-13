//! Checkers for `Alias` and `Owning` properties.

use crate::helpers::mir_utils;
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::Property;
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::VmState;
use rustc_middle::{
    mir::{Operand, ProjectionElem, Rvalue, StatementKind},
    ty::TyKind,
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_ref_count_share<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(owner) = checkpoint.callee.and_then(|did| {
            crate::verify::vm::alias_hazard::reconstructed_owner(vm_state.tcx, did)
                .map(|(_, owner)| owner)
                .or_else(|| {
                    let owner_ty = crate::helpers::name::get_struct_self_ty(vm_state.tcx, did)?;
                    let TyKind::Adt(adt, _) = owner_ty.kind() else {
                        return None;
                    };
                    Some(adt.did())
                })
        }) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let Some(value) = self
            .target_value(vm_state, checkpoint, property)
            .map(|value| vm_state.resolve_pointer_provenance(value))
        else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        match vm_state.ownership_share(&value, owner) {
            Some(0) => CheckResult::Failed,
            Some(_) => CheckResult::ProvedByRule,
            None => CheckResult::Unknown(UnknownReason::Unimplemented),
        }
    }

    pub(super) fn check_alias<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        _property: &Property<'tcx>,
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
        let value = vm_state.resolve_pointer_provenance(value);
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
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        // `Owning(container.iter())` for_each: every element pointer is the
        // sole owner of its pointee, so a pointer loaded from the container
        // (whose provenance names the container allocation) is a valid owner.
        if vm_state.alloc(alloc_id).facts.for_each.owning {
            return CheckResult::ProvedByRule;
        }
        let origin = vm_state.resolve_origin(&value);
        let target_place = property.target_place();
        let arg_place = target_place
            .and_then(|place| match place.base {
                crate::verify::contract::PlaceBase::Arg(n) => checkpoint.args.get(n),
                _ => None,
            })
            .and_then(mir_utils::operand_mir_place);
        let owning_invariant_field = arg_place.and_then(|arg_place| {
            let tree =
                crate::verify::vm::alias_tree::AliasTree::build(vm_state.tcx, checkpoint.caller);
            let (root, fields) = tree.resolve_local_to_root(arg_place.local);
            let field = fields.first().copied().or_else(|| {
                arg_place
                    .projection
                    .iter()
                    .find_map(|projection| match projection {
                        rustc_middle::mir::ProjectionElem::Field(index, _) => {
                            Some(index.as_usize())
                        }
                        _ => None,
                    })
            })?;
            let root_ty =
                vm_state.body().local_decls[rustc_middle::mir::Local::from_usize(root)].ty;
            let root_ty = match root_ty.kind() {
                rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                _ => root_ty,
            };
            let rustc_middle::ty::TyKind::Adt(adt, _) = root_ty.kind() else {
                return None;
            };
            Some((adt.did(), field))
        });
        let owns_field_by_invariant = owning_invariant_field.is_some_and(|(adt_id, field)| {
            crate::verify::target::get_struct_invariants_from_annotation(
                vm_state.tcx,
                adt_id,
                adt_id,
            )
            .iter()
            .any(|p| {
                p.kind() == Some(crate::verify::contract::PropertyKind::Owning)
                    && p.target_place().is_some_and(|place| {
                        place
                            .projections
                            .iter()
                            .find_map(|projection| match projection {
                                crate::verify::contract::ContractProjection::Field {
                                    index,
                                    ..
                                } => Some(*index),
                                _ => None,
                            })
                            == Some(field)
                    })
            })
        });
        let internal_alloc = !vm_state.alloc(alloc_id).is_external();
        let local_alloc = vm_state
            .current_frame
            .local_alloc
            .values()
            .any(|id| *id == alloc_id);
        let untrusted_raw_origin = origin.as_ref().is_none_or(|origin| match origin.kind {
            crate::verify::vm::alias::VmOriginKind::RawPtr
            | crate::verify::vm::alias::VmOriginKind::SharedRef
            | crate::verify::vm::alias::VmOriginKind::Unknown => true,
            crate::verify::vm::alias::VmOriginKind::MutRef => !owns_field_by_invariant,
            crate::verify::vm::alias::VmOriginKind::Owned(def_id) => {
                !(crate::verify::api_classify::is_std_box(def_id)
                    || crate::verify::api_classify::is_std_vec(def_id)
                    || crate::verify::api_classify::is_std_cstring(def_id)
                    || owns_field_by_invariant
                    || (internal_alloc && !local_alloc))
            }
        });
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
        let matches_owning_precondition = vm_state
            .alloc(alloc_id)
            .facts
            .owning
            .as_ref()
            .is_some_and(|owner| owner == &value.z3_term);
        let declared_field_owner = origin.as_ref().is_some_and(|origin| {
            vm_state
                .local_value(origin.local)
                .is_some_and(|local| local.z3_term == value.z3_term)
                && owning_field_source(vm_state.tcx, checkpoint.caller, origin.local)
        });
        if untrusted_raw_origin && !matches_owning_precondition && !declared_field_owner {
            let fresh_internal = origin.is_none() && internal_alloc && !local_alloc;
            let local_manually_drop =
                crate::verify::api_classify::is_manually_drop_drop(vm_state.tcx, checkpoint.callee)
                    && internal_alloc
                    && local_alloc
                    && origin.as_ref().is_some_and(|origin| {
                        matches!(
                            origin.kind,
                            crate::verify::vm::alias::VmOriginKind::MutRef
                                | crate::verify::vm::alias::VmOriginKind::Owned(_)
                        )
                    });
            if fresh_internal || local_manually_drop {
                CheckResult::ProvedByRule
            } else {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            }
        } else {
            CheckResult::ProvedByRule
        }
    }
}

fn owning_field_source(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: rustc_hir::def_id::DefId,
    local: rustc_middle::mir::Local,
) -> bool {

    let body = tcx.optimized_mir(caller);
    let mut source = None;
    let mut written_fields = Vec::new();
    for block in body.basic_blocks.iter() {
        if let rustc_middle::mir::TerminatorKind::Call { destination, .. } =
            &block.terminator().kind
            && destination.local == local
            && destination.projection.is_empty()
        {
            return false;
        }
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (destination, rvalue) = &**assign;
            if let [ProjectionElem::Deref, ProjectionElem::Field(field, _)] =
                destination.projection.as_ref()
                && let TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) =
                    body.local_decls[destination.local].ty.kind()
                && let TyKind::Adt(adt, _) = inner.kind()
            {
                written_fields.push((adt.did(), field.as_usize()));
            }
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            if source.is_some() {
                return false;
            }
            let Rvalue::Use(Operand::Copy(place), _) = rvalue else {
                return false;
            };
            let [ProjectionElem::Deref, ProjectionElem::Field(field, _)] =
                place.projection.as_ref()
            else {
                return false;
            };
            let owner_ty = match body.local_decls[place.local].ty.kind() {
                TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                _ => return false,
            };
            let TyKind::Adt(adt, _) = owner_ty.kind() else {
                return false;
            };
            source = Some((adt.did(), field.as_usize()));
        }
    }
    let Some((adt_id, field)) = source else {
        return false;
    };
    if written_fields.contains(&(adt_id, field)) {
        return false;
    }
    let invariants =
        crate::verify::target::get_struct_invariants_from_annotation(tcx, adt_id, adt_id);
    [crate::verify::contract::PropertyKind::Allocated, crate::verify::contract::PropertyKind::Typed, crate::verify::contract::PropertyKind::Owning]
        .into_iter()
        .all(|kind| invariants.iter().any(|property| {
            property.kind() == Some(kind)
                && property.target_place().is_some_and(|place| matches!(
                    place.projections.first(),
                    Some(crate::verify::contract::ContractProjection::Field { index, .. }) if *index == field
                ))
        }))
}
