//! Shared rustc call-instance resolution and trait impl enumeration.
//!
//! `resolve_callee_instance` preserves compiler shims; the `DefId` helper only
//! substitutes resolved item methods.
//! Enumerating impl methods does not prove trait obligations; consumers must
//! treat the result as possible targets, not a resolved call.

use crate::compat::GenericArgsRef;
use crate::def_ids::lang_api::{self, LangItem};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Operand,
    ty::{
        fast_reject::DeepRejectCtxt, ImplPolarity,
        Const, ConstKind, EarlyBinder, GenericParamDefKind, Instance, InstanceKind, ShimKind, TyCtxt, TyKind,
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

/// An impl method or a trait default method, instantiated when an impl is known.
#[derive(Clone, Copy)]
pub(crate) struct TraitCallTarget<'tcx> {
    pub def_id: DefId,
    pub instance: Option<Instance<'tcx>>,
}

/// Possible targets of an unresolved trait call, filtered by its trait
/// arguments. A virtual receiver has no known concrete self type, so that
/// argument is excluded. Fast rejection may retain extra impls but must not
/// discard a possible target. `None` means a matching impl cannot be expanded.
pub(crate) fn possible_trait_impl_methods<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    method: DefId,
    func: &Operand<'tcx>,
    is_virtual: bool,
) -> Option<Vec<TraitCallTarget<'tcx>>> {
    let trait_id = tcx.trait_of_assoc(method)?;
    let Operand::Constant(constant) = func else { return None };
    let TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else { return None };
    if *def_id != method {
        return None;
    }
    let trait_arg_count = tcx.generics_of(trait_id).count();
    let args = args.skip_binder();
    if args.len() < trait_arg_count {
        return None;
    }
    let requested = tcx.mk_args_from_iter(args.iter().take(trait_arg_count).skip(usize::from(is_virtual)));
    let reject = DeepRejectCtxt::relate_infer_infer(tcx);
    let mut candidates = Vec::new();
    for impl_id in tcx.all_impls(trait_id) {
        if tcx.impl_polarity(impl_id) != ImplPolarity::Positive {
            continue;
        }
        let implemented = tcx.impl_trait_ref(impl_id).skip_binder();
        let available = tcx.mk_args_from_iter(implemented.args.iter().skip(usize::from(is_virtual)));
        if !reject.args_may_unify(requested, available) {
            continue;
        }
        let target = if let Some(&def_id) = tcx.impl_item_implementor_ids(impl_id).get(&method) {
            TraitCallTarget { def_id, instance: None }
        } else {
            // An impl without an override calls the trait's provided method.
            if !tcx.is_mir_available(method) {
                return None;
            }
            let method_args = tcx.mk_args_from_iter(implemented.args.iter().chain(args.iter().skip(trait_arg_count)));
            let instance = resolve_instance(tcx, impl_id, method, method_args)?;
            if !matches!(instance.def, InstanceKind::Item(def_id) if def_id == method)
                || instance.try_instantiate_mir_and_normalize_erasing_regions(
                    tcx,
                    crate::compat::typing_env_post_analysis(tcx, caller),
                    EarlyBinder::bind(tcx, tcx.optimized_mir(method).clone()),
                ).is_err()
            {
                return None;
            }
            TraitCallTarget { def_id: method, instance: Some(instance) }
        };
        if !tcx.is_mir_available(target.def_id) {
            return None;
        }
        candidates.push(target);
    }
    // With no known implementor, the provided method is still one possible
    // target for a future impl that does not override it.
    if candidates.is_empty() && tcx.is_mir_available(method) {
        candidates.push(TraitCallTarget { def_id: method, instance: None });
    }
    candidates.sort_by_cached_key(|target| tcx.def_path_str(target.def_id));
    Some(candidates)
}

/// Compiler callable traits use generated call shims, not arbitrary impl MIR.
pub(crate) fn is_compiler_callable_trait_method(tcx: TyCtxt<'_>, method: DefId) -> bool {
    tcx.trait_of_assoc(method).is_some_and(|trait_id| {
        lang_api::is_fn_trait(tcx, trait_id)
            || lang_api::matches(tcx, trait_id, LangItem::FnPtrTrait)
            || lang_api::matches(tcx, trait_id, LangItem::FnAddrTrait)
    })
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

