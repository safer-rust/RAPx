//! Shared rustc call-instance resolution and trait impl enumeration.
//!
//! `resolve_callee_instance` preserves compiler shims; the `DefId` helper only
//! substitutes resolved item methods.
//! Enumerating impl methods does not check callsite types or trait obligations;
//! consumers must treat the result as possible targets, not a resolved call.

use crate::compat::GenericArgsRef;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Operand,
    ty::{
        Const, ConstKind, GenericParamDefKind, Instance, InstanceKind, ShimKind, TyCtxt, TyKind,
        TypeFlags, TypeSuperVisitable, TypeVisitable, TypeVisitableExt, TypeVisitor,
    },
};
use std::ops::ControlFlow;

/// Resolve a `FnDef(def_id, args)` (already `skip_binder`d by the caller) to
/// its monomorphized [`Instance`] in `caller`'s post-analysis typing env.
pub(crate) fn resolve_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> Option<Instance<'tcx>> {
    if has_unresolved_const_args(tcx, caller, args) {
        return None;
    }
    let typing_env = crate::compat::typing_env_post_analysis(tcx, caller);
    Instance::try_resolve(tcx, typing_env, def_id, args)
        .ok()
        .flatten()
}

pub(crate) fn has_unresolved_const_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    args: GenericArgsRef<'tcx>,
) -> bool {
    if !args.has_type_flags(TypeFlags::HAS_CT_PARAM) {
        return false;
    }
    struct UnboundConstParam<'tcx> {
        tcx: TyCtxt<'tcx>,
        caller: DefId,
    }
    impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for UnboundConstParam<'tcx> {
        type Result = ControlFlow<()>;

        fn visit_const(&mut self, ct: Const<'tcx>) -> Self::Result {
            if let ConstKind::Param(param) = ct.kind() {
                let generics = self.tcx.generics_of(self.caller);
                let index = param.index as usize;
                if index >= generics.count() {
                    return ControlFlow::Break(());
                }
                let definition = generics.param_at(index, self.tcx);
                if !matches!(definition.kind, GenericParamDefKind::Const { .. })
                    || definition.name != param.name
                {
                    return ControlFlow::Break(());
                }
            }
            ct.super_visit_with(self)
        }
    }
    args.visit_with(&mut UnboundConstParam { tcx, caller })
        .is_break()
}

/// Map a resolved [`Instance`] to its concrete target `DefId` and whether the
/// dispatch is virtual. `None` for kinds with no single target (e.g. a closure's
/// `Clone` shim).
pub(crate) fn instance_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> (Option<DefId>, bool) {
    let mut is_virtual = false;
    let def_id = match instance.def {
        InstanceKind::Item(def_id) => Some(def_id),
        InstanceKind::Intrinsic(def_id) => Some(def_id),
        InstanceKind::Virtual(def_id, _) => {
            is_virtual = true;
            Some(def_id)
        }
        InstanceKind::Shim(shim_kind) => match shim_kind {
            ShimKind::VTable(def_id) => Some(def_id),
            ShimKind::Reify(def_id, _) => Some(def_id),
            ShimKind::FnPtr(def_id, _) => Some(def_id),
            ShimKind::ClosureOnce { call_once, .. } => Some(call_once),
            ShimKind::ConstructCoroutineInClosure {
                coroutine_closure_def_id,
                ..
            } => Some(coroutine_closure_def_id),
            ShimKind::ThreadLocal(def_id) => Some(def_id),
            ShimKind::DropGlue(def_id, _) => Some(def_id),
            ShimKind::FnAddrAsPtr(def_id, _) => Some(def_id),
            ShimKind::AsyncDropGlueCtor(def_id, _) => Some(def_id),
            ShimKind::Clone(def_id, _) => {
                if !tcx.is_closure_like(def_id) {
                    Some(def_id)
                } else {
                    None
                }
            }
            _ => todo!(),
        },
        #[allow(unreachable_patterns)]
        _ => None,
    };
    (def_id, is_virtual)
}

/// Enumerate all impl overrides of a trait method without callsite filtering.
pub(crate) fn all_trait_impl_methods(tcx: TyCtxt<'_>, method_def_id: DefId) -> Vec<DefId> {
    let mut candidates = Vec::new();
    if let Some(trait_def_id) = tcx.trait_of_assoc(method_def_id) {
        for impl_id in tcx.all_impls(trait_def_id) {
            let impl_map = tcx.impl_item_implementor_ids(impl_id);
            if let Some(candidate_def_id) = impl_map.get(&method_def_id) {
                candidates.push(*candidate_def_id);
            }
        }
    }
    candidates
}

/// Resolve a call `func` operand to its monomorphized [`Instance`].
pub(crate) fn resolve_callee_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<Instance<'tcx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, callee_args) = c.const_.ty().kind() else {
        return None;
    };
    let callee_args = callee_args.skip_binder();
    resolve_instance(tcx, caller, *def_id, callee_args)
}

/// Return the call's `DefId`, using the selected impl method's `DefId` when
/// available. Otherwise return the `DefId` from the operand.
pub(crate) fn resolve_callee_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<DefId> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, callee_args) = c.const_.ty().kind() else {
        return None;
    };
    let callee_def_id = *def_id;
    let callee_args = callee_args.skip_binder();
    let resolved = tcx
        .opt_associated_item(callee_def_id)
        .and_then(|item| item.trait_container(tcx))
        .and_then(|_| resolve_instance(tcx, caller, callee_def_id, callee_args))
        .and_then(|instance| match instance.def {
            InstanceKind::Item(def_id) => Some(def_id),
            _ => None,
        });
    Some(resolved.unwrap_or(callee_def_id))
}

