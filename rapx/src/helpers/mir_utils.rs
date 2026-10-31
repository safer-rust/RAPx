use crate::def_ids::lang_api::{self, LangItem};
#[cfg(rapx_attr_requires_ext)]
use rustc_ast::attr::AttributeExt;
use rustc_hir::{
    ItemKind,
    def_id::{DefId, LocalDefId},
};
#[cfg(rapx_ge_99)]
use rustc_middle::ty::ShimKind;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{
    mir::interpret::{AllocId, GlobalAlloc},
    mir::{
        BasicBlock, Body, ConstValue, Local, Operand, Place, Rvalue, StatementKind, SwitchTargets,
        TerminatorKind,
    },
    ty::{
        ConstKind, FieldDef, GenericArgKind, GenericArgs, GenericArgsRef, GenericParamDefKind,
        Instance, InstanceKind, PseudoCanonicalInput, ScalarInt, Ty, TyCtxt, TyKind,
        TypeVisitableExt, TypingEnv,
    },
};
use rustc_span::{DUMMY_SP, Symbol};

use std::collections::HashSet;

#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;

use crate::compat::FxHashMap;
use crate::def_ids::other_api;
use crate::def_ids::type_ids;

use super::def_use::PlaceKey;

pub(crate) fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        // `NonNull<T>` is a raw-pointer wrapper; unwrap it so pointer-arith
        // effects (`NonNull::add`/`sub`/`offset`) keep their provenance.
        TyKind::Adt(adt, args) if type_ids::nonnull_types().contains(&adt.did()) => {
            args.types().next()
        }
        _ => None,
    }
}

pub(crate) fn dep_callee_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = c.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

/// Whether `def_id` is `core::ptr::drop_in_place`.
pub(crate) fn is_drop_in_place(def_id: DefId) -> bool {
    other_api::drop_in_place() == Some(def_id)
}

/// Whether `def_id` is a diverging call target: a `panic*` lang item or the
/// `unreachable`/`abort` intrinsics.
fn is_diverging_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    crate::def_ids::lang_api::is_panic_family(tcx, def_id)
        || tcx.intrinsic(def_id).is_some_and(|i| {
            i.name == rustc_span::sym::unreachable || i.name == rustc_span::sym::abort
        })
}

/// Whether a `SwitchInt`'s non-`otherwise` targets all lead straight to
/// `panic`/`unreachable` (a `debug_assert!`/`assert!` dispatch).  Such a switch
/// is dead on the normal path and can be inlined by following only the
/// `otherwise` edge.
pub(crate) fn switch_targets_unreachable<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    targets: &SwitchTargets,
) -> bool {
    targets.iter().all(|(_, target)| {
        let mut cur = target;
        let mut seen = HashSet::new();
        loop {
            if !seen.insert(cur) {
                return false;
            }
            let bb = &body.basic_blocks[cur];
            let term = bb.terminator();
            match &term.kind {
                TerminatorKind::Unreachable => return true,
                TerminatorKind::Call { func, .. } => {
                    let Some(callee) = dep_callee_def_id(func) else {
                        return false;
                    };
                    return is_diverging_call(tcx, callee);
                }
                TerminatorKind::Goto { target: next, .. } => {
                    cur = *next;
                }
                // A bare `return` with no statements is a drop-flag skip (dead
                // on the normal path); a `return` preceded by real statements
                // computes a different value, so it is a semantic branch and
                // must not be ignored.
                TerminatorKind::Return => return bb.statements.is_empty(),
                _ => return false,
            }
        }
    })
}

/// Resolve a `cfg!`-style runtime-check flag (`UbChecks`, `ContractChecks`,
/// `OverflowChecks`) to a constant `u64`. We fold to the *no-check* edge (`0`):
/// the check only panics on a violated precondition, and its branchy body would
/// otherwise corrupt field/Typed propagation during inlining. Older rustc lowers
/// these to `Rvalue::NullaryOp(NullOp::RuntimeChecks)`; newer rustc lowers them
/// to `Operand::RuntimeChecks`.
pub(crate) fn rvalue_runtime_checks_value(rvalue: &Rvalue<'_>) -> Option<u64> {
    #[cfg(rapx_rvalue_has_nullary_op)]
    {
        if let Rvalue::NullaryOp(rustc_middle::mir::NullOp::RuntimeChecks(_)) = rvalue {
            return Some(0);
        }
    }
    #[cfg(not(rapx_rvalue_has_nullary_op))]
    {
        if let Rvalue::Use(Operand::RuntimeChecks(_), ..) = rvalue {
            return Some(0);
        }
    }
    None
}

/// The concrete `core::ops::Range*` struct a `DefId` denotes.
pub(crate) enum RangeKind {
    RangeTo,
    RangeFrom,
    Range,
    RangeInclusive,
    Other,
}

/// Classify a `DefId` as one of the `core::ops::Range*` structs.
pub(crate) fn range_kind(tcx: TyCtxt<'_>, def_id: DefId) -> RangeKind {
    if lang_api::matches(tcx, def_id, LangItem::RangeTo) {
        RangeKind::RangeTo
    } else if lang_api::matches(tcx, def_id, LangItem::RangeFrom) {
        RangeKind::RangeFrom
    } else if lang_api::matches(tcx, def_id, LangItem::RangeInclusiveStruct) {
        RangeKind::RangeInclusive
    } else if lang_api::matches(tcx, def_id, LangItem::Range) {
        RangeKind::Range
    } else {
        RangeKind::Other
    }
}

/// Resolve a `FnDef(def_id, args)` (already `skip_binder`d by the caller) to
/// its monomorphized [`Instance`] in `caller`'s post-analysis typing env.
pub(crate) fn resolve_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    def_id: DefId,
    args: GenericArgsRef<'tcx>,
) -> Option<Instance<'tcx>> {
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    Instance::try_resolve(tcx, typing_env, def_id, args)
        .ok()
        .flatten()
}

/// Map a resolved [`Instance`] to its concrete target `DefId` and whether the
/// dispatch is virtual. `None` for kinds with no single target (e.g. a closure's
/// `Clone` shim).
pub(crate) fn instance_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance: Instance<'tcx>,
) -> (Option<DefId>, bool) {
    let mut is_virtual = false;
    #[cfg(rapx_ge_99)]
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
            #[cfg(rapx_has_fnptr_asptr)]
            ShimKind::FnPtrAsPtr(def_id, _) => Some(def_id),
            #[cfg(not(rapx_has_fnptr_asptr))]
            ShimKind::FnPtrAddr(def_id, _) => Some(def_id),
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
    #[cfg(not(rapx_ge_99))]
    let def_id = match instance.def {
        InstanceKind::Item(def_id) => Some(def_id),
        InstanceKind::Intrinsic(def_id) => Some(def_id),
        InstanceKind::VTableShim(def_id) => Some(def_id),
        InstanceKind::ReifyShim(def_id, _) => Some(def_id),
        InstanceKind::FnPtrShim(def_id, _) => Some(def_id),
        InstanceKind::Virtual(def_id, _) => {
            is_virtual = true;
            Some(def_id)
        }
        InstanceKind::ClosureOnceShim { call_once, .. } => Some(call_once),
        InstanceKind::ConstructCoroutineInClosureShim {
            coroutine_closure_def_id,
            ..
        } => Some(coroutine_closure_def_id),
        InstanceKind::ThreadLocalShim(def_id) => Some(def_id),
        InstanceKind::DropGlue(def_id, _) => Some(def_id),
        InstanceKind::FnPtrAddrShim(def_id, _) => Some(def_id),
        InstanceKind::AsyncDropGlueCtorShim(def_id, _) => Some(def_id),
        InstanceKind::CloneShim(def_id, _) => {
            if !tcx.is_closure_like(def_id) {
                Some(def_id)
            } else {
                None
            }
        }
        _ => todo!(),
    };
    (def_id, is_virtual)
}

/// Enumerate the concrete impl methods that could be dispatched for a trait
/// method (the set of targets behind a trait-object / virtual call). Each
/// returned `DefId` is an impl's override of `method_def_id`.
pub(crate) fn trait_impl_candidates(tcx: TyCtxt<'_>, method_def_id: DefId) -> Vec<DefId> {
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

/// Build a partially-monomorphized [`Instance`] for `def_id`, replacing the type
/// parameter named `param_name` with `concrete_ty` and leaving every other
/// parameter (const params in particular) as `Param`. Returns `None` when
/// `def_id` has no such type parameter.
pub(crate) fn monomorphize_instance<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_name: Symbol,
    concrete_ty: Ty<'tcx>,
) -> Option<Instance<'tcx>> {
    let mut replaced = false;
    let args = GenericArgs::for_item(tcx, def_id, |param, _| {
        if matches!(param.kind, GenericParamDefKind::Type { .. }) && param.name == param_name {
            replaced = true;
            concrete_ty.into()
        } else {
            tcx.mk_param_from_def(param)
        }
    });
    replaced.then(|| Instance::new_raw(def_id, args))
}

/// Enumerate the concrete self types implementing a type parameter's trait
/// bounds. Chooses the bound with the fewest concrete (non-generic) impls —
/// the "small" helper trait that usually pins the supported types (e.g.
/// `GetDisjointMutIndex` over the generic `SliceIndex`/`Clone` bounds) — and
/// returns its concrete impl self types.
pub(crate) fn type_param_impl_tys<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    param_ty: Ty<'tcx>,
) -> Vec<Ty<'tcx>> {
    if !matches!(param_ty.kind(), TyKind::Param(_)) {
        return Vec::new();
    }
    let param_env = tcx.param_env(def_id);
    let mut best: Option<Vec<Ty<'tcx>>> = None;
    for clause in param_env.caller_bounds() {
        let Some(trait_clause) = clause.as_trait_clause() else {
            continue;
        };
        let self_ty = trait_clause.self_ty().skip_binder();
        if self_ty != param_ty {
            continue;
        }
        let impl_tys: Vec<Ty<'tcx>> = tcx
            .all_impls(trait_clause.def_id())
            .map(|impl_def_id| tcx.type_of(impl_def_id).skip_binder())
            // Only concrete self types are usable as monomorphization candidates
            // (a generic `impl<T: Clone> Clone for Range<T>` must not count).
            .filter(|ty| !ty_has_type_param(*ty))
            .collect();
        if impl_tys.is_empty() {
            continue;
        }
        best = Some(match best {
            None => impl_tys,
            Some(prev) if impl_tys.len() < prev.len() => impl_tys,
            Some(prev) => prev,
        });
    }
    best.unwrap_or_default()
}

/// Enumerate partially-monomorphized instances of a generic function by
/// replacing its first unbound type parameter with each concrete impl of that
/// parameter's bounds (see [`type_param_impl_tys`]), capped at `limit`. Empty
/// for non-generic functions or when the parameter has no enumerable impls.
pub(crate) fn enumerate_mono_instances<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    limit: usize,
) -> Vec<Instance<'tcx>> {
    let generics = tcx.generics_of(def_id);
    let Some(type_param) = generics
        .own_params
        .iter()
        .find(|p| matches!(p.kind, GenericParamDefKind::Type { .. }))
    else {
        return Vec::new();
    };
    let param_ty = tcx.mk_param_from_def(type_param).expect_ty();
    let impl_tys = type_param_impl_tys(tcx, def_id, param_ty);
    if impl_tys.is_empty() {
        return Vec::new();
    }
    impl_tys
        .into_iter()
        .take(limit)
        .filter_map(|ty| monomorphize_instance(tcx, def_id, type_param.name, ty))
        .collect()
}

/// Whether `def_id`'s body (or any callee it would inline) contains a
/// trait-method call with no executable MIR (a still-generic `T: Bound` or
/// virtual dispatch) *and* no symbolic model — i.e. a call whose opaque
/// fallback would lose dataflow and therefore benefits from caller
/// monomorphization.
pub(crate) fn has_unmodeled_generic_call<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let mut visited = HashSet::default();
    has_unmodeled_generic_call_rec(tcx, def_id, &mut visited)
}

pub(crate) fn has_generic_const_call_argument(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    tcx.optimized_mir(def_id).basic_blocks.iter().any(|bb| {
        let TerminatorKind::Call { args, .. } = &bb.terminator().kind else {
            return false;
        };
        args.iter().any(|arg| {
            let Operand::Constant(constant) = &arg.node else {
                return false;
            };
            match constant.const_ {
                rustc_middle::mir::Const::Ty(_, value) => value.has_param(),
                rustc_middle::mir::Const::Unevaluated(value, _) => value.args.has_param(),
                _ => false,
            }
        })
    })
}

/// A callee may need its own MIR instantiated when an immediate trait call
/// can change target after substituting the caller's type arguments.
pub(crate) fn has_direct_unmodeled_generic_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.iter().any(|bb| {
        let TerminatorKind::Call { func, destination, .. } = &bb.terminator().kind else {
            return false;
        };
        let Some(callee) = dep_callee_def_id(func) else {
            return false;
        };
        tcx.opt_associated_item(callee)
            .and_then(|item| item.trait_container(tcx))
            .is_some()
            && dep_callee_resolved_def_id(tcx, def_id, func)
                .is_none_or(|target| !tcx.is_mir_available(target))
            && !has_callback_effect(tcx, callee, body.local_decls[destination.local].ty)
            && !crate::verify::call_summary::effects::has_registry_entry(Some(callee))
    })
}

fn has_unmodeled_generic_call_rec<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    visited: &mut HashSet<DefId>,
) -> bool {
    if !visited.insert(def_id) || !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, destination, .. } = &term.kind else {
            continue;
        };
        let Some(callee) = dep_callee_def_id(func) else {
            continue;
        };
        let is_trait_method = tcx
            .opt_associated_item(callee)
            .and_then(|a| a.trait_container(tcx))
            .is_some();
        if is_trait_method {
            // A resolved `Instance` may still be virtual or name the trait
            // method itself. What matters is whether the actual target has
            // executable MIR after resolving this call.
            if dep_callee_resolved_def_id(tcx, def_id, func)
                .is_none_or(|target| !tcx.is_mir_available(target))
                && !has_callback_effect(tcx, callee, body.local_decls[destination.local].ty)
                && !crate::verify::call_summary::effects::has_registry_entry(Some(callee))
            {
                return true;
            }
            continue;
        }
        // A concrete callee gets inlined, so recurse to surface its own
        // unmodeled generic trait calls.
        if has_unmodeled_generic_call_rec(tcx, callee, visited) {
            return true;
        }
    }
    false
}

fn has_callback_effect(tcx: TyCtxt<'_>, callee: DefId, result_ty: Ty<'_>) -> bool {
    tcx.trait_of_assoc(callee)
        .is_some_and(|trait_id| lang_api::is_fn_trait(tcx, trait_id))
        && crate::verify::call_summary::callback::supports_result(result_ty)
}

/// Resolve a trait-method callee to its concrete impl `DefId`. Returns `None`
/// when it is not a trait method or has no distinct concrete target (e.g. still
/// generic/virtual).
pub(crate) fn resolve_callee_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    callee_def_id: DefId,
    callee_args: GenericArgsRef<'tcx>,
) -> Option<DefId> {
    let assoc = tcx.opt_associated_item(callee_def_id)?;
    assoc.trait_container(tcx)?;
    let instance = resolve_instance(tcx, caller_def_id, callee_def_id, callee_args)?;
    let resolved = match instance.def {
        InstanceKind::Item(def_id) => def_id,
        _ => return None,
    };
    if resolved == callee_def_id {
        None
    } else {
        Some(resolved)
    }
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
    #[cfg(rapx_ge_99)]
    let callee_args = callee_args.skip_binder();
    resolve_instance(tcx, caller, *def_id, callee_args)
}

/// Like [`dep_callee_def_id`], but resolves trait-method callees to the concrete
/// impl (whose MIR is what actually gets inlined).
pub(crate) fn dep_callee_resolved_def_id<'tcx>(
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
    #[cfg(rapx_ge_99)]
    let callee_args = callee_args.skip_binder();
    resolve_callee_impl(tcx, caller, callee_def_id, callee_args).or(Some(callee_def_id))
}

/// Collect all return basic block indices for a function body.
pub fn collect_return_block_indices(tcx: TyCtxt<'_>, def_id: DefId) -> Vec<BasicBlock> {
    let mut blocks = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return blocks;
    }
    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if matches!(data.terminator().kind, TerminatorKind::Return) {
            blocks.push(bb);
        }
    }
    blocks
}

/// Whether `block` ends in a `Return` terminator (a normal exit point).
pub fn is_return_block(tcx: TyCtxt<'_>, def_id: DefId, block: BasicBlock) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks
        .get(block)
        .is_some_and(|data| matches!(data.terminator().kind, TerminatorKind::Return))
}

/// Return the callee argument index represented by a MIR local.
///
/// Contract annotations written with parameter names are parsed in the callee's
/// local namespace.  MIR local `_0` is the return place and argument locals are
/// `_1..=_arg_count`, so callee local `_1` denotes checkpoint argument `0`.
pub fn callee_param_index_for_local(tcx: TyCtxt<'_>, callee: DefId, local: usize) -> Option<usize> {
    let arg_count = if tcx.is_mir_available(callee) {
        tcx.optimized_mir(callee).arg_count
    } else {
        tcx.fn_sig(callee)
            .skip_binder()
            .inputs()
            .skip_binder()
            .len()
    };
    arg_of_local(Local::from_usize(local), arg_count)
}

pub fn is_std_crate_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(
        tcx.crate_name(def_id.krate).as_str(),
        "core" | "std" | "alloc"
    )
}

pub fn is_trait_unsafe(tcx: TyCtxt<'_>, trait_def_id: DefId) -> bool {
    let Some(local_id) = trait_def_id.as_local() else {
        return false;
    };
    let item = tcx.hir_expect_item(local_id);

    #[cfg(not(rapx_ge_99))]
    if let ItemKind::Trait(_, _, unsafety, _, _, _, _) = &item.kind {
        return matches!(unsafety, rustc_hir::Safety::Unsafe);
    }
    #[cfg(rapx_ge_99)]
    if let ItemKind::Trait { safety, .. } = &item.kind {
        return matches!(safety, rustc_hir::Safety::Unsafe);
    }

    false
}

pub fn resolve_impl_self_ty_def_id(item: &rustc_hir::Item<'_>) -> Option<DefId> {
    let ItemKind::Impl(rustc_hir::Impl { self_ty, .. }) = &item.kind else {
        return None;
    };
    match &self_ty.kind {
        rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Def(
                rustc_hir::def::DefKind::Struct
                | rustc_hir::def::DefKind::Enum
                | rustc_hir::def::DefKind::Union,
                def_id,
            ) => Some(def_id),
            _ => None,
        },
        _ => None,
    }
}

/// Whether a local item carries a `#[rapx::<name>(...)]` attribute.
pub(crate) fn has_rapx_attr(tcx: TyCtxt<'_>, def_id: LocalDefId, name: Symbol) -> bool {
    let hir_id = tcx.local_def_id_to_hir_id(def_id);

    let rapx = Symbol::intern("rapx");
    let attrs = tcx.hir_attrs(hir_id);

    attrs.iter().any(|attr| {
        if attr.is_doc_comment().is_some() {
            return false;
        }

        let path = attr.path();

        path.len() == 2 && path[0] == rapx && path[1] == name
    })
}

pub fn has_rapx_verify_attr(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    has_rapx_attr(tcx, def_id, Symbol::intern("verify"))
}

/// True when a type transitively contains a const-generic parameter or
/// an associated type alias (which may be layout-ambiguous).
fn ty_has_param_const(ty: Ty<'_>) -> bool {
    for arg in ty.walk() {
        match arg.kind() {
            GenericArgKind::Const(c) if matches!(c.kind(), ConstKind::Param(_)) => return true,
            GenericArgKind::Type(inner_ty) if matches!(inner_ty.kind(), TyKind::Alias(..)) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

/// Run `f` inside `catch_unwind`, returning either the result or the
/// downcasted panic message.
pub(crate) fn catch_panic<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).map_err(|e| {
        e.downcast_ref::<String>()
            .cloned()
            .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
            .unwrap_or_else(|| "<rustc ICE>".to_string())
    })
}

/// Return a stable, human-readable name for a MIR call operand.
pub fn call_name(tcx: TyCtxt<'_>, func: &Operand<'_>) -> String {
    dep_callee_def_id(func)
        .map(|def_id| tcx.def_path_str(def_id))
        .unwrap_or_else(|| format!("{func:?}"))
}

/// Return the zero-based argument index of `local`, if it is a MIR argument.
///
/// MIR local `_0` is the return place; argument locals start at `_1`.
pub fn arg_of_local(local: Local, arg_count: usize) -> Option<usize> {
    let i = local.as_usize();
    if i >= 1 && i <= arg_count {
        Some(i - 1)
    } else {
        None
    }
}

pub fn has_crate(tcx: TyCtxt<'_>, name: &str) -> bool {
    for num in tcx.crates(()) {
        if tcx.crate_name(*num) == Symbol::intern(name) {
            return true;
        }
    }
    false
}

/// Extracts the source `Place` from an rvalue for simple forwarding operations
/// (copy, move, cast, reference, raw-pointer, copy-for-deref).
pub fn rvalue_source_place<'a, 'tcx>(
    rvalue: &'a Rvalue<'tcx>,
) -> Option<&'a rustc_middle::mir::Place<'tcx>> {
    use rustc_middle::mir::{Operand, Rvalue};
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
}

// ── PlaceKey / operand utilities ─────────────────────────────────

/// Extract a PlaceKey from a MIR operand.
pub fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    operand_mir_place(operand).map(PlaceKey::from_mir_place)
}

/// Extract the MIR Place from an operand.
pub fn operand_mir_place<'a, 'tcx>(operand: &'a Operand<'tcx>) -> Option<&'a Place<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }
}

// ── Place resolution utilities ───────────────────────────────────

// ── Block reachability ───────────────────────────────────────────

/// Collect all basic blocks reachable after a call block's normal return, or —
/// for a non-call block such as a raw-pointer deref statement — after the block
/// itself (all of its successors).
pub fn blocks_reachable_after_call(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
) -> HashSet<BasicBlock> {
    let body = tcx.optimized_mir(caller);
    let mut starts = Vec::new();
    if let TerminatorKind::Call { target, .. } = &body.basic_blocks[call_block].terminator().kind
        && let Some(target) = target
    {
        starts.push(*target);
    } else {
        starts.extend(body.basic_blocks[call_block].terminator().successors());
    }

    let mut seen = HashSet::new();
    let mut stack = starts;
    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let terminator = body.basic_blocks[block].terminator();
        for successor in terminator.successors() {
            stack.push(successor);
        }
    }
    seen
}

// ── MIR place alias mapping ──────────────────────────────────────

// ── Rvalue place scanning ────────────────────────────────────────

/// Check whether any MIR place used in an rvalue matches a predicate.
pub fn rvalue_any_place_matching<'tcx>(
    rvalue: &Rvalue<'tcx>,
    pred: &mut impl FnMut(&Place<'tcx>) -> bool,
) -> bool {
    match rvalue {
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => pred(place),
            Operand::Constant(_) => false,
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => rvalue_source_place(rvalue).is_some_and(pred),
    }
}

// ── Pointer arithmetic origin tracing ────────────────────────────

/// Resolve a `const` item (e.g. `const CAPACITY: usize = 2 * B - 1`) by name in
/// the local crate to its evaluated unsigned-integer value, for use in the
/// contract DSL (`ValidNum(len <= CAPACITY)`).
pub(crate) fn resolve_const_item_value<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Option<u128> {
    for item_id in tcx.hir_crate_items(()).free_items() {
        let def_id = item_id.owner_id.to_def_id();
        let Some(item_name) = tcx.opt_item_name(def_id) else {
            continue;
        };
        if item_name.as_str() != name {
            continue;
        }
        #[cfg(rapx_defkind_const_struct)]
        if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Const { .. }) {
            continue;
        }
        #[cfg(not(rapx_defkind_const_struct))]
        if !matches!(tcx.def_kind(def_id), rustc_hir::def::DefKind::Const) {
            continue;
        }
        let instance = rustc_middle::ty::Instance::mono(tcx, def_id);
        let cid = rustc_middle::mir::interpret::GlobalId {
            instance,
            promoted: None,
        };
        let Ok(val) = tcx.const_eval_global_id(TypingEnv::fully_monomorphized(), cid, DUMMY_SP)
        else {
            continue;
        };
        let Some(scalar) = val.try_to_scalar_int() else {
            continue;
        };
        return Some(scalar.to_bits(scalar.size()));
    }
    None
}

/// Extract raw bytes from a `ConstValue`, following reference indirection.
fn const_value_bytes<'tcx>(tcx: TyCtxt<'tcx>, value: ConstValue, depth: usize) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    match value {
        ConstValue::Slice { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        ConstValue::Scalar(scalar) => {
            #[cfg(rapx_scalar_to_pointer_interp_result)]
            let ptr = scalar.to_pointer(&tcx).discard_err()?;
            #[cfg(not(rapx_scalar_to_pointer_interp_result))]
            let ptr = scalar.to_pointer(&tcx);
            let alloc_id = ptr.provenance?.alloc_id();
            alloc_id_bytes(tcx, alloc_id, depth)
        }
        ConstValue::Indirect { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        _ => None,
    }
}

/// Read bytes from a global allocation.
fn alloc_id_bytes<'tcx>(tcx: TyCtxt<'tcx>, alloc_id: AllocId, depth: usize) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    let alloc = match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(alloc) => alloc,
        GlobalAlloc::Static(def_id) => tcx.eval_static_initializer(def_id).ok()?,
        _ => return None,
    };
    let alloc = alloc.inner();
    let provenance = alloc.provenance().ptrs();
    if let Some((_, prov)) = provenance.iter().next() {
        return alloc_id_bytes(tcx, prov.alloc_id(), depth + 1);
    }
    Some(
        alloc
            .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
            .to_vec(),
    )
}

// ── Type layout helpers ───────────────────────────────────────────

/// If `constant` is a promoted `offset_of!(Container, field)` constant (an
/// unevaluated `Const` whose body is a call to the `offset_of` intrinsic),
/// return the container type.
///
/// Used by the verifier to recognise `byte_add(offset_of!(Container, ..))` and
/// prove the resulting pointer stays within the container allocation.
pub(crate) fn offset_of_container<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
) -> Option<Ty<'tcx>> {
    let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant else {
        return None;
    };
    // `mir_for_ctfe` only accepts const-like defs; unevaluated consts may also
    // reference plain functions, so gate on the def kind first.
    if !is_const_def_kind(tcx, uneval.def) {
        return None;
    }
    // `mir_for_ctfe` panics for cross-crate constants (e.g. `char::MAX` from
    // `core`), since it only serves local, CTFE-able definitions. `offset_of!`
    // always expands to a local `AnonConst`, so rejecting external defs loses
    // nothing but avoids the ICE.
    if !uneval.def.is_local() {
        return None;
    }
    let body = tcx.mir_for_ctfe(uneval.def);
    for bb in body.basic_blocks.iter() {
        if let Some(term) = &bb.terminator
            && let TerminatorKind::Call { func, .. } = &term.kind
            && let Some(ty) = offset_of_ty_from_func(tcx, func)
        {
            return Some(ty);
        }
    }
    None
}

/// Whether `def` is a `SizedTypeProperties::<ASSOC>` associated const — a
/// compiler-internal layout constant (`SIZE`, `ALIGN`, `IS_ZST`) that has no
/// lang/diagnostic item, so it is matched by its def-path suffix.
pub(crate) fn is_sized_type_property(tcx: TyCtxt<'_>, def: DefId, assoc: &str) -> bool {
    tcx.def_path_str(def)
        .ends_with(&format!("SizedTypeProperties::{assoc}"))
}

/// Whether a `DefId` is a const-like item that `mir_for_ctfe` accepts.
fn is_const_def_kind(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    use rustc_hir::def::DefKind;
    #[cfg(rapx_defkind_const_struct)]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const { .. }
            | DefKind::Static { .. }
            | DefKind::AssocConst { .. }
            | DefKind::AnonConst
    );
    #[cfg(not(rapx_defkind_const_struct))]
    let base = matches!(
        tcx.def_kind(def_id),
        DefKind::Const | DefKind::Static { .. } | DefKind::AssocConst | DefKind::AnonConst
    );
    #[cfg(rapx_ge_99)]
    {
        base
    }
    #[cfg(not(rapx_ge_99))]
    {
        base || matches!(tcx.def_kind(def_id), DefKind::InlineConst)
    }
}

/// Extract the first `Type` generic argument of an `FnDef` call operand.
///
/// Many monomorphized std APIs have the interesting type (the receiver or
/// container element) as their first generic argument.
pub(crate) fn fn_def_first_type_arg<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else {
        return None;
    };
    args.iter().find_map(|a| {
        #[cfg(rapx_ge_99)]
        let a = a.skip_binder();
        match a.kind() {
            GenericArgKind::Type(t) => Some(t),
            _ => None,
        }
    })
}

fn offset_of_ty_from_func<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = c.const_.ty().kind() else {
        return None;
    };
    if !lang_api::matches(tcx, *def_id, LangItem::OffsetOf) {
        return None;
    }
    fn_def_first_type_arg(func)
}

pub fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) {
        return None;
    }
    match layout_of_ty(tcx, caller, ty) {
        Some(l) => Some((l.align.abi.bytes(), l.size.bytes())),
        None if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        None => None,
    }
}

/// Compute the full type layout, catching rustc panics and layout errors.
/// Shared by `type_layout` and the symbolic VM's size/align/field-offset
/// queries so the `layout_of` call and its panic-guard live in one place.
pub fn layout_of_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
) -> Option<rustc_abi::TyAndLayout<'tcx, Ty<'tcx>>> {
    let env = TypingEnv::post_analysis(tcx, caller);
    catch_panic(|| {
        tcx.layout_of(PseudoCanonicalInput {
            typing_env: env,
            value: ty,
        })
    })
    .ok()
    .and_then(|r| r.ok())
}

/// Byte offset of a struct field within its container type (0 on failure).
pub fn field_offset_in_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
    field_idx: usize,
) -> u64 {
    let Some(layout) = layout_of_ty(tcx, caller, ty) else {
        return 0;
    };
    if let rustc_abi::FieldsShape::Arbitrary { ref offsets, .. } = layout.fields {
        let idx = rustc_abi::FieldIdx::from_usize(field_idx);
        if idx.as_usize() < offsets.len() {
            return offsets[idx].bytes();
        }
    }
    0
}

/// Whether `ty` mentions a (type) generic parameter anywhere in its structure,
/// e.g. `T`, `*mut T`, `Option<T>`.
pub(crate) fn ty_has_type_param(ty: Ty<'_>) -> bool {
    ty.walk().any(|t| {
        matches!(
            t.kind(),
            GenericArgKind::Type(inner) if matches!(inner.kind(), TyKind::Param(_))
        )
    })
}

pub fn pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    dest: Option<Local>,
) -> Option<(u64, String)> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let pointee = pointee_ty(ty).or(Some(ty))?;
    if let Some((a, _)) = type_layout(tcx, caller, pointee) {
        return Some((a, format!("{pointee:?}")));
    }
    if let TyKind::Array(e, _) = pointee.kind()
        && let Some((a, _)) = type_layout(tcx, caller, *e)
    {
        return Some((a, format!("{pointee:?}")));
    }
    Some((0, format!("{pointee:?}")))
}

// ── Constant scalar / byte-string extraction ───────────────────

/// Parse an integer from a MIR constant's `Debug` text. Handles decimal,
/// `0x` hex, and `Value(...)` forms.
pub fn const_int_from_debug(text: &str) -> Option<u64> {
    if let Ok(v) = text.parse::<u64>() {
        return Some(v);
    }
    if let Some(start) = text.find("0x") {
        let hex_part = &text[start..];
        let end = hex_part
            .find(|c: char| !c.is_ascii_hexdigit() && c != 'x')
            .unwrap_or(hex_part.len());
        u64::from_str_radix(&hex_part[2..end], 16).ok()
    } else if let Some(start) = text.find("Value(") {
        let inner = &text[start + 6..];
        if let Some(end) = inner.find(')') {
            inner[..end].parse::<u64>().ok()
        } else {
            None
        }
    } else {
        None
    }
}

/// Resolve a MIR constant to a concrete integer, falling back from the cheap
/// debug-text parse to full const evaluation.
///
/// Layout constants (`offset_of!(Container, field)`) and the `T::{BITS,MAX,MIN}`
/// associated constants of *small* integer types (`u8`..`u32`, `i8`..`i32`) are
/// evaluated here.  Arbitrary unevaluated consts — and the wide bounds
/// `usize::MAX` / `u64::MAX` / `u128::MAX` — are deliberately left symbolic:
/// forcing them to a concrete `u64` would overflow downstream size arithmetic.
pub fn eval_const_scalar_int<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
    text: &str,
) -> Option<i128> {
    if let Some(v) = const_int_from_debug(text) {
        return Some(v as i128);
    }
    // Resolve `T::{BITS,MAX,MIN}` associated constants of small integer types,
    // used in numeric bounds (`u32::MAX`) and shift-width masks (`u32::BITS`).
    let is_num_bound = text.contains("::BITS") || text.contains("::MAX") || text.contains("::MIN");
    // An unevaluated `const` item (e.g. `const CAPACITY: usize = 2 * B - 1`)
    // must be const-evaluated to its scalar value, so comparisons like
    // `idx < CAPACITY` are modeled as `idx < 11` rather than an opaque symbol.
    let is_unevaluated = matches!(*constant, rustc_middle::mir::Const::Unevaluated(..));
    if !is_num_bound && !is_unevaluated && offset_of_container(tcx, constant).is_none() {
        return None;
    }
    let typing_env = TypingEnv::fully_monomorphized();
    let val = constant.eval(tcx, typing_env, rustc_span::DUMMY_SP).ok()?;
    let scalar = val.try_to_scalar_int()?;
    // Keep wide bounds (`u64::MAX`, `usize::MAX`, `u128::MAX`) symbolic so
    // they don't overflow downstream size arithmetic.
    if scalar.to_bits(scalar.size()) > u32::MAX as u128 {
        return None;
    }
    Some(scalar_int_value(scalar, constant.ty()))
}

pub(crate) fn const_destructure<'tcx>(
    tcx: TyCtxt<'tcx>,
    constant: &rustc_middle::mir::Const<'tcx>,
) -> Option<(Option<u64>, Vec<(ConstValue, Ty<'tcx>)>)> {
    let ty = constant.ty();
    match ty.kind() {
        TyKind::Tuple(_) => {}
        TyKind::Adt(adt_def, _) if !adt_def.is_union() => {}
        _ => return None,
    }
    let val = constant
        .eval(tcx, TypingEnv::fully_monomorphized(), DUMMY_SP)
        .ok()?;
    let destructured = tcx.try_destructure_mir_constant_for_user_output(val, ty)?;
    Some((
        destructured.variant.map(|v| v.as_u32() as u64),
        destructured.fields.to_vec(),
    ))
}

pub(crate) fn scalar_int_value<'tcx>(scalar: ScalarInt, ty: Ty<'tcx>) -> i128 {
    let bits = scalar.size().bits() as u32;
    let raw = scalar.to_bits(scalar.size()) as i128;
    if let TyKind::Int(_) = ty.kind() {
        let sign = 1i128 << (bits - 1);
        if raw >= sign {
            raw - (1i128 << bits)
        } else {
            raw
        }
    } else {
        raw
    }
}

/// Resolve an array length const (`ty::Const`) to a concrete `u64`. Unlike
/// `try_to_target_usize`, this also evaluates unevaluated const expressions
/// (e.g. `[MaybeUninit<K>; CAPACITY]` where `CAPACITY = 2 * B - 1`), so the
/// VM can allocate the array with its true element count instead of a
/// collapsed zero-size fallback.
pub(crate) fn eval_array_len<'tcx>(
    tcx: TyCtxt<'tcx>,
    c: &rustc_middle::ty::Const<'tcx>,
) -> Option<u64> {
    if let Some(v) = c.try_to_target_usize(tcx) {
        return Some(v);
    }
    // An unevaluated array length (`[MaybeUninit<K>; CAPACITY]` where
    // `CAPACITY = 2 * B - 1`) is an anonymous const. Its `ConstKind`
    // representation differs across toolchains: `Unevaluated` before the
    // `Alias` rename (~2026-07), `Alias` afterwards.
    #[cfg(rapx_constkind_alias)]
    let def_id = {
        let ConstKind::Alias(_, alias_const) = c.kind() else {
            return None;
        };
        #[cfg(not(rapx_alias_const_inherent_self))]
        let def_id = alias_const.kind.opt_def_id()?;
        #[cfg(rapx_alias_const_inherent_self)]
        let def_id = {
            use rustc_middle::ty::AliasConstKind;
            match alias_const.kind {
                AliasConstKind::Projection { def_id } => def_id,
                AliasConstKind::InherentSelf { def_id } => def_id,
                AliasConstKind::InherentImpl { def_id } => def_id,
                AliasConstKind::Free { def_id } => def_id,
                AliasConstKind::Anon { def_id } => def_id,
            }
        };
        def_id
    };
    #[cfg(not(rapx_constkind_alias))]
    let def_id = {
        let ConstKind::Unevaluated(uneval) = c.kind() else {
            return None;
        };
        uneval.def
    };
    let instance = rustc_middle::ty::Instance::mono(tcx, def_id);
    let cid = rustc_middle::mir::interpret::GlobalId {
        instance,
        promoted: None,
    };
    if let Ok(val) = tcx.const_eval_global_id(TypingEnv::fully_monomorphized(), cid, DUMMY_SP)
        && let Some(scalar) = val.try_to_scalar_int()
    {
        return Some(scalar.to_target_usize(tcx));
    }
    None
}

/// Try to extract raw bytes from a MIR constant operand that is a reference
/// to a byte array/slice (e.g. `b"hello\0"`). Returns the byte values.
/// Used by the VM to populate byte-level tracking for constant C strings.
pub fn const_operand_bytes<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>) -> Option<Vec<u8>> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    let ty = constant.const_.ty();
    let inner_ty = match ty.kind() {
        TyKind::Ref(_, inner, _) => *inner,
        _ => return None,
    };
    // Peel through nested references (e.g. &&[u8])
    let inner_ty = if let TyKind::Ref(_, innermost, _) = inner_ty.kind() {
        *innermost
    } else {
        inner_ty
    };
    if !matches!(inner_ty.kind(), TyKind::Array(..) | TyKind::Slice(..)) {
        return None;
    }

    // Evaluate the MIR constant to get a ConstValue
    let typing_env = TypingEnv::fully_monomorphized();
    let value = constant
        .const_
        .eval(tcx, typing_env, rustc_span::DUMMY_SP)
        .ok()?;

    const_value_bytes(tcx, value, 0)
}

/// Extract the bare local from a Copy/Move operand with no projection.
pub fn extract_local(operand: &Operand<'_>) -> Option<Local> {
    operand_mir_place(operand)
        .filter(|place| place.projection.is_empty())
        .map(|place| place.local)
}

/// Extract a constant u64 value from an operand, if it's a known constant.
pub fn operand_const_u64(operand: &Operand<'_>) -> Option<u64> {
    operand_scalar_int(operand).map(|v| v as u64)
}

/// Whether a type is a `u8` array (`[u8; N]`) or `u8` slice (`[u8]`).
pub fn is_u8_array_or_slice(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Array(elem_ty, _) => {
            matches!(elem_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8))
        }
        TyKind::Slice(elem_ty) => {
            matches!(elem_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8))
        }
        _ => false,
    }
}

/// Whether a type transitively contains a reference.
///
/// This is a shallow check: it recurses only through `Adt` generic arguments,
/// not through tuple elements or `Adt` fields. See [`type_contains_raw_ptr`]
/// for a deeper check that also matches raw pointers.
pub fn type_contains_reference(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Ref(..) => true,
        TyKind::Adt(_, substs) => substs.types().any(type_contains_reference),
        _ => false,
    }
}

/// Whether a type transitively contains a raw pointer, recursing through tuple
/// elements and `Adt` fields. Unlike [`type_contains_reference`], this does not
/// match references — a method returning `&*self.raw` re-borrows the pointee
/// (safe) rather than leaking the raw pointer value itself (unsafe).
pub fn type_contains_raw_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::RawPtr(_, _) => true,
        TyKind::Tuple(elems) => elems.iter().any(|t| type_contains_raw_ptr(tcx, t)),
        TyKind::Adt(def, args) => {
            if args.iter().any(|arg| {
                if let Some(t) = arg.as_type() {
                    type_contains_raw_ptr(tcx, t)
                } else {
                    false
                }
            }) {
                return true;
            }
            let adt = tcx.adt_def(def.did());
            adt.all_fields()
                .any(|field| type_contains_raw_ptr(tcx, field_ty(tcx, field, args)))
        }
        _ => false,
    }
}

/// Resolve a struct field's type, normalizing where the rustc version requires it.
///
/// On newer rustc `field.ty(tcx, args)` returns an `Unnormalized<Ty>` that must
/// be `.skip_norm_wip()`-ed; on older toolchains the `SkipNormWip` shim makes
/// the same call a no-op, so this is version-independent.
pub fn field_ty<'tcx>(tcx: TyCtxt<'tcx>, field: &FieldDef, args: GenericArgsRef<'tcx>) -> Ty<'tcx> {
    field.ty(tcx, args).skip_norm_wip()
}

/// Whether `def_id` is a single-field struct wrapping a raw pointer (i.e.
/// `NonNull`-shaped).  Used by alias/ownership reasoning to recognize pointer
/// wrappers — including local re-implementations — by their structure rather
/// than by a std `DefId`.
pub fn is_raw_ptr_wrapper<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let adt = tcx.adt_def(def_id);
    let variant = adt.non_enum_variant();
    if variant.fields.len() != 1 {
        return false;
    }
    let args = rustc_middle::ty::GenericArgs::identity_for_item(tcx, def_id);
    let field = variant.fields.iter().next().unwrap();
    let field_ty = field_ty(tcx, field, args);
    matches!(field_ty.kind(), TyKind::RawPtr(..))
}

/// Collect the layouts of every concrete implementor of a generic type
/// parameter's trait bounds (empty for non-param types).
fn generic_param_impl_layouts<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    ty: Ty<'tcx>,
) -> Vec<rustc_abi::TyAndLayout<'tcx, Ty<'tcx>>> {
    if !matches!(ty.kind(), TyKind::Param(_)) {
        return Vec::new();
    }
    let param_env = tcx.param_env(caller);
    let typing_env = TypingEnv::post_analysis(tcx, caller);
    for clause in param_env.caller_bounds() {
        let Some(trait_clause) = clause.as_trait_clause() else {
            continue;
        };
        let self_ty = trait_clause.self_ty().skip_binder();
        if self_ty != ty {
            continue;
        }
        let mut layouts = Vec::new();
        for impl_def_id in tcx.all_impls(trait_clause.def_id()) {
            let impl_ty = tcx.type_of(impl_def_id).skip_binder();
            if ty_has_param_const(impl_ty) {
                continue;
            }
            let Ok(Ok(layout)) = catch_panic(|| {
                tcx.layout_of(PseudoCanonicalInput {
                    typing_env,
                    value: impl_ty,
                })
            }) else {
                continue;
            };
            layouts.push(layout);
        }
        return layouts;
    }
    Vec::new()
}

/// Max `size_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn size_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    generic_param_impl_layouts(tcx, caller, ty)
        .into_iter()
        .map(|l| l.size.bytes())
        .max()
        .unwrap_or(0)
}

/// Min `align_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types).
pub fn min_align_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    generic_param_impl_layouts(tcx, caller, ty)
        .into_iter()
        .map(|l| l.align.abi.bytes())
        .min()
        .unwrap_or(0)
}

/// Max `align_of` over all implementors of a generic type parameter's trait
/// bounds (0 for non-param types or a parameter without a bounded set of
/// implementors).
pub fn max_align_of_generic_param<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> u64 {
    generic_param_impl_layouts(tcx, caller, ty)
        .into_iter()
        .map(|l| l.align.abi.bytes())
        .max()
        .unwrap_or(0)
}

/// Follow a `parents` map (built by `verify::property_checker::cstr`'s
/// `body_parents`) from `start` to its root local, guarding against cycles.
pub fn follow_parents(parents: &FxHashMap<Local, Local>, start: Local) -> Local {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let Some(next) = parents.get(&current) else {
            break;
        };
        current = *next;
    }
    current
}

/// Resolve a local through `Cast` assignments back to its non-cast source.
pub fn resolve_through_casts<'tcx>(body: &Body<'tcx>, local: Local) -> Local {
    let mut current = local;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let found = body.basic_blocks.iter().any(|data| {
            data.statements.iter().any(|stmt| {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    return false;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != current || !target.projection.is_empty() {
                    return false;
                }
                if let Rvalue::Cast(_, operand, _) = rvalue {
                    #[allow(unreachable_patterns)]
                    match operand {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            current = p.local;
                            return true;
                        }
                        _ => {}
                    }
                }
                false
            })
        });
        if !found {
            break;
        }
    }
    current
}

// ── Constant byte recovery from MIR ─────────────────────────────

fn operand_scalar_int(operand: &Operand<'_>) -> Option<u128> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    constant
        .const_
        .try_to_scalar_int()
        .map(|s| s.to_uint(s.size()))
        .or_else(|| const_int_from_debug(&format!("{:?}", constant.const_)).map(|v| v as u128))
}

fn rvalue_const_bytes<'tcx>(tcx: TyCtxt<'tcx>, rvalue: &Rvalue<'tcx>) -> Option<Vec<u8>> {
    let constant = match rvalue {
        Rvalue::Use(Operand::Constant(constant), ..)
        | Rvalue::Cast(_, Operand::Constant(constant), _) => constant,
        _ => return None,
    };
    let value = constant
        .const_
        .eval(tcx, TypingEnv::fully_monomorphized(), DUMMY_SP)
        .ok()?;
    const_value_bytes(tcx, value, 0)
}

pub fn collect_all_const_bytes_worklist<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Vec<Vec<u8>> {
    let mut results: Vec<Vec<u8>> = Vec::new();
    let mut worklist: Vec<Local> = vec![root];
    let mut visited: std::collections::HashSet<Local> = std::collections::HashSet::new();

    while let Some(local) = worklist.pop() {
        if !visited.insert(local) {
            continue;
        }

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != local || !target.projection.is_empty() {
                    continue;
                }

                if let Rvalue::Ref(_, _, place) = rvalue {
                    if let Some(bytes) = const_bytes_for_local(tcx, body, place.local) {
                        results.push(bytes);
                    }
                    continue;
                }

                if let Rvalue::Use(operand, ..) = rvalue {
                    #[allow(unreachable_patterns)]
                    match operand {
                        Operand::Copy(p) | Operand::Move(p) => {
                            worklist.push(p.local);
                            if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                                results.push(bytes);
                            }
                            continue;
                        }
                        Operand::Constant(_) => {}
                        _ => continue,
                    }
                }

                if let Some(bytes) = rvalue_const_bytes(tcx, rvalue) {
                    results.push(bytes);
                }
            }
        }

        for data in body.basic_blocks.iter() {
            if let Some(terminator) = &data.terminator
                && let TerminatorKind::Call {
                    destination,
                    func,
                    args,
                    ..
                } = &terminator.kind
            {
                let dlocal = destination.local;
                if dlocal != local {
                    continue;
                }
                if !destination.projection.is_empty() {
                    continue;
                }
                let did = dep_callee_def_id(func);
                if did.is_some_and(|d| other_api::as_ptr_like_fns().contains(&d)) {
                    for arg in args {
                        if let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &arg.node) {
                            results.push(bytes);
                        }
                    }
                }
                if did.is_some_and(|d| other_api::ptr_add_fns().contains(&d))
                    && let Some(offset) = args.get(1).and_then(|a| operand_scalar_int(&a.node))
                    && let Some(base) = args.first()
                    && let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &base.node)
                {
                    let start = offset as usize;
                    if start < bytes.len() {
                        results.push(bytes[start..].to_vec());
                    }
                }
                #[cfg(rapx_ge_99)]
                if did.is_some_and(|d| other_api::box_assume_init_into_vec_unsafe() == Some(d))
                    && let Some(box_op) = args.first()
                    && let Operand::Copy(p) | Operand::Move(p) = &box_op.node
                    && p.projection.is_empty()
                {
                    worklist.push(p.local);
                }
            }
        }
    }

    collect_aggregate_const_bytes(tcx, body, &mut results);
    collect_as_ptr_const_bytes(tcx, body, &mut results);

    results
}

fn collect_aggregate_const_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    results: &mut Vec<Vec<u8>>,
) {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (_, rvalue) = assign.as_ref();
            let Rvalue::Aggregate(_, operands) = rvalue else {
                continue;
            };
            if operands.len() < 2 {
                continue;
            }
            let last_op = operands.iter().last().unwrap();
            if !is_constant_zero(last_op) {
                continue;
            }
            let mut all_nonzero = true;
            for op in operands.iter().take(operands.len() - 1) {
                if !aggregate_op_is_nonzero(tcx, body, op) {
                    all_nonzero = false;
                    break;
                }
            }
            if all_nonzero {
                let len = operands.len();
                let mut bytes = vec![b'x'; len - 1];
                bytes.push(0);
                results.push(bytes);
            }
        }
    }
}

fn collect_as_ptr_const_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    results: &mut Vec<Vec<u8>>,
) {
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call { func, args, .. } = &terminator.kind
            && dep_callee_def_id(func).is_some_and(|d| other_api::as_ptr_like_fns().contains(&d))
        {
            for arg in args {
                if let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &arg.node) {
                    results.push(bytes);
                }
            }
        }
    }
}

fn trace_const_bytes_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Vec<u8>> {
    if let Some(bytes) = const_operand_bytes(tcx, operand) {
        return Some(bytes);
    }
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                return Some(bytes);
            }
            const_bytes_from_call_dest(tcx, body, p.local)
        }
        _ => None,
    }
}

fn const_bytes_from_call_dest<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call {
                destination,
                func,
                args,
                ..
            } = &terminator.kind
        {
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            if dep_callee_def_id(func).is_some_and(|d| other_api::as_ptr_like_fns().contains(&d)) {
                for arg in args {
                    if let Some(bytes) = trace_const_bytes_from_operand(tcx, body, &arg.node) {
                        return Some(bytes);
                    }
                }
            }
        }
    }
    None
}

pub fn const_bytes_for_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != root || !target.projection.is_empty() {
                continue;
            }
            if let Rvalue::Ref(_, _, place) = rvalue {
                let deref_local = place.local;
                if let Some(bytes) = const_bytes_for_local(tcx, body, deref_local) {
                    return Some(bytes);
                }
                continue;
            }
            if let Rvalue::Use(operand, ..) = rvalue {
                #[allow(unreachable_patterns)]
                match operand {
                    Operand::Copy(p) | Operand::Move(p) => {
                        if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                            return Some(bytes);
                        }
                        if let Some(bytes) = const_bytes_from_call_dest(tcx, body, p.local) {
                            return Some(bytes);
                        }
                        continue;
                    }
                    Operand::Constant(_) => {}
                    _ => continue,
                }
            }
            if let Rvalue::Cast(_, operand, _) = rvalue {
                if let Operand::Copy(p) | Operand::Move(p) = operand
                    && p.projection.is_empty()
                    && let Some(bytes) = const_bytes_for_local(tcx, body, p.local)
                {
                    return Some(bytes);
                }
                continue;
            }
            return rvalue_const_bytes(tcx, rvalue);
        }
    }
    None
}

fn aggregate_op_is_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    if is_constant_zero(operand) {
        return false;
    }
    if const_operand_bytes(tcx, operand).is_some() {
        return true;
    }
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            for data in body.basic_blocks.iter() {
                if let Some(terminator) = &data.terminator
                    && let TerminatorKind::Call {
                        destination, func, ..
                    } = &terminator.kind
                    && destination.local == p.local
                    && destination.projection.is_empty()
                {
                    return fn_always_returns_nonzero(tcx, func);
                }
            }
            false
        }
        Operand::Constant(_) => operand_scalar_int(operand).is_some_and(|v| v != 0),
        _ => false,
    }
}

fn is_constant_zero(operand: &Operand<'_>) -> bool {
    operand_scalar_int(operand) == Some(0)
}

fn fn_always_returns_nonzero<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
    let Some(fn_def_id) = dep_callee_def_id(func) else {
        return false;
    };
    let callee_body = tcx.optimized_mir(fn_def_id);

    let mut has_return = false;
    for bb_data in callee_body.basic_blocks.iter() {
        if let Some(terminator) = &bb_data.terminator
            && matches!(terminator.kind, TerminatorKind::Return)
        {
            has_return = true;
        }
        for stmt in &bb_data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != Local::from_usize(0) || !target.projection.is_empty() {
                continue;
            }
            if !rvalue_is_nonzero(rvalue) {
                return false;
            }
        }
    }

    has_return
}

fn rvalue_is_nonzero(rvalue: &Rvalue<'_>) -> bool {
    match rvalue {
        #[allow(unreachable_patterns)]
        Rvalue::Use(operand, ..) => match operand {
            Operand::Constant(_) => operand_scalar_int(operand).is_some_and(|v| v != 0),
            Operand::Copy(_) | Operand::Move(_) => true,
            _ => false,
        },
        _ => false,
    }
}
