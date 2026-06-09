#![allow(warnings, unused)]

use super::graph::TyWrapper;
use super::utils::{self, fn_sig_with_generic_args};
use crate::analysis::utils::def_path::path_str_def_id;
use crate::{rap_debug, rap_trace};
use rand::Rng;
use rand::seq::SliceRandom;
use rustc_hir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_infer::infer::DefineOpaqueTypes;
use rustc_infer::infer::{InferCtxt, TyCtxtInferExt};
use rustc_infer::traits::{ImplSource, Obligation, ObligationCause};
use rustc_middle::ty::{self, GenericArgsRef, Ty, TyCtxt, TypeVisitableExt, TypingEnv};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use std::collections::HashSet;

static MAX_STEP_SET_SIZE: usize = 1000;

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct Mono<'tcx> {
    pub value: Vec<ty::GenericArg<'tcx>>,
}

impl<'tcx> FromIterator<ty::GenericArg<'tcx>> for Mono<'tcx> {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = ty::GenericArg<'tcx>>,
    {
        Mono {
            value: iter.into_iter().collect(),
        }
    }
}

impl<'tcx> Mono<'tcx> {
    pub fn new(identity: &[ty::GenericArg<'tcx>]) -> Self {
        Mono {
            value: Vec::from(identity),
        }
    }

    fn has_infer_types(&self) -> bool {
        self.value.iter().any(|arg| match arg.kind() {
            ty::GenericArgKind::Type(ty) => ty.has_infer_types(),
            _ => false,
        })
    }

    fn mut_arg_at(&mut self, idx: usize) -> &mut ty::GenericArg<'tcx> {
        &mut self.value[idx]
    }

    fn merge(&self, other: &Mono<'tcx>, tcx: TyCtxt<'tcx>) -> Option<Mono<'tcx>> {
        assert!(self.value.len() == other.value.len());
        let mut res = Vec::new();
        for i in 0..self.value.len() {
            let arg = self.value[i];
            let other_arg = other.value[i];
            let new_arg = if let Some(ty) = arg.as_type() {
                let other_ty = other_arg.expect_ty();
                if ty.is_ty_var() && other_ty.is_ty_var() {
                    arg
                } else if ty.is_ty_var() {
                    other_arg
                } else if other_ty.is_ty_var() {
                    arg
                } else if utils::is_ty_eq(ty, other_ty, tcx) {
                    arg
                } else {
                    return None;
                }
            } else {
                arg
            };
            res.push(new_arg);
        }
        Some(Mono { value: res })
    }

    fn fill_unbound_var(&self, tcx: TyCtxt<'tcx>) -> Vec<Mono<'tcx>> {
        let candidates = get_unbound_generic_candidates(tcx);
        let mut res = vec![self.clone()];
        rap_trace!("fill unbound: {:?}", self);

        for (i, arg) in self.value.iter().enumerate() {
            if let Some(ty) = arg.as_type() {
                if ty.is_ty_var() {
                    let mut last = Vec::new();
                    std::mem::swap(&mut res, &mut last);
                    last.into_iter().for_each(|mono| {
                        for candidate in &candidates {
                            let mut new_mono = mono.clone();
                            *new_mono.mut_arg_at(i) = (*candidate).into();
                            res.push(new_mono);
                        }
                    });
                }
            }
        }
        res
    }
}

#[derive(Clone, Debug, Default)]
pub struct MonoSet<'tcx> {
    pub monos: Vec<Mono<'tcx>>,
}

impl<'tcx> MonoSet<'tcx> {
    pub fn all(identity: &[ty::GenericArg<'tcx>]) -> MonoSet<'tcx> {
        MonoSet {
            monos: vec![Mono::new(identity)],
        }
    }

    pub fn empty() -> MonoSet<'tcx> {
        MonoSet { monos: Vec::new() }
    }

    pub fn count(&self) -> usize {
        self.monos.len()
    }

    pub fn at(&self, no: usize) -> &Mono<'tcx> {
        &self.monos[no]
    }

    pub fn is_empty(&self) -> bool {
        self.monos.is_empty()
    }

    pub fn new() -> MonoSet<'tcx> {
        MonoSet { monos: Vec::new() }
    }

    pub fn insert(&mut self, mono: Mono<'tcx>) {
        self.monos.push(mono);
    }

    pub fn merge(&mut self, other: &MonoSet<'tcx>, tcx: TyCtxt<'tcx>) -> MonoSet<'tcx> {
        let mut res = MonoSet::new();

        for args in self.monos.iter() {
            for other_args in other.monos.iter() {
                let merged = args.merge(other_args, tcx);
                if let Some(mono) = merged {
                    res.insert(mono);
                }
            }
        }
        res
    }

    fn filter_unbound_solution(mut self) -> Self {
        self.monos.retain(|mono| mono.has_infer_types());
        self
    }

    // if the unbound generic type is still exist (this could happen
    // if `T` has no trait bounds at all)
    // we substitute the unbound generic type with predefined type candidates
    fn instantiate_unbound(&self, tcx: TyCtxt<'tcx>) -> Self {
        let mut res = MonoSet::new();
        for mono in &self.monos {
            let filled = mono.fill_unbound_var(tcx);
            res.monos.extend(filled);
        }
        res
    }

    fn erase_region_var(&mut self, tcx: TyCtxt<'tcx>) {
        for mono in &mut self.monos {
            mono.value
                .iter_mut()
                .for_each(|arg| *arg = tcx.erase_and_anonymize_regions(*arg))
        }
    }

    pub fn filter(mut self, f: impl Fn(&Mono<'tcx>) -> bool) -> Self {
        self.monos.retain(|args| f(args));
        self
    }

    pub fn random_sample<R: Rng>(&mut self, rng: &mut R) {
        if self.monos.len() <= MAX_STEP_SET_SIZE {
            return;
        }
        self.monos.shuffle(rng);
        self.monos.truncate(MAX_STEP_SET_SIZE);
    }
}

/// try to unfiy lhs = rhs,
/// e.g.,
/// try_unify(Vec<T>, Vec<i32>, ...) = Some(i32)
/// try_unify(Vec<T>, i32, ...) = None
fn unify_ty<'tcx>(
    lhs: Ty<'tcx>,
    rhs: Ty<'tcx>,
    identity: &[ty::GenericArg<'tcx>],
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> Option<Mono<'tcx>> {
    // rap_info!("check {} = {}", lhs, rhs);
    infcx.probe(|_| {
        match infcx
            .at(cause, param_env)
            .eq(DefineOpaqueTypes::Yes, lhs, rhs)
        {
            Ok(_infer_ok) => {
                // rap_trace!("[infer_ok] {} = {} : {:?}", lhs, rhs, infer_ok);
                let mono = identity
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Lifetime(region) => {
                            infcx.resolve_vars_if_possible(region).into()
                        }
                        ty::GenericArgKind::Type(ty) => infcx.resolve_vars_if_possible(ty).into(),
                        ty::GenericArgKind::Const(ct) => infcx.resolve_vars_if_possible(ct).into(),
                    })
                    .collect();
                Some(mono)
            }
            Err(_e) => {
                // rap_trace!("[infer_err] {} = {} : {:?}", lhs, rhs, e);
                None
            }
        }
    })
}

fn is_args_fit_trait_bound<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> bool {
    let args = tcx.mk_args(args);
    rap_trace!(
        "fn: {:?} args: {:?} identity: {:?}",
        fn_did,
        args,
        ty::GenericArgs::identity_for_item(tcx, fn_did)
    );
    let infcx = tcx.infer_ctxt().build(ty::TypingMode::PostAnalysis);
    let pred = tcx.predicates_of(fn_did);
    let inst_pred = pred.instantiate(tcx, args);
    let param_env = tcx.param_env(fn_did);
    rap_trace!(
        "[trait bound] check {}",
        tcx.def_path_str_with_args(fn_did, args)
    );

    for pred in inst_pred.predicates.iter() {
        let obligation = Obligation::new(
            tcx,
            ObligationCause::dummy(),
            param_env,
            pred.as_predicate(),
        );
        rap_trace!("[trait bound] check pred: {:?}", pred);

        let res = infcx.evaluate_obligation(&obligation);
        match res {
            Ok(eva) => {
                if !eva.may_apply() {
                    rap_trace!("[trait bound] check fail for {pred:?}");
                    return false;
                }
            }
            Err(_) => {
                rap_trace!("[trait bound] check fail for {pred:?}");
                return false;
            }
        }
    }
    rap_trace!("[trait bound] check succ");
    true
}

fn is_fn_solvable<'tcx>(fn_did: DefId, tcx: TyCtxt<'tcx>) -> bool {
    for pred in tcx
        .predicates_of(fn_did)
        .instantiate_identity(tcx)
        .predicates
    {
        if let Some(pred) = pred.as_trait_clause() {
            let trait_did = pred.skip_binder().trait_ref.def_id;
            if tcx.is_lang_item(trait_did, LangItem::Fn)
                || tcx.is_lang_item(trait_did, LangItem::FnMut)
                || tcx.is_lang_item(trait_did, LangItem::FnOnce)
            {
                return false;
            }
        }
    }
    true
}

fn get_mono_set<'tcx>(
    fn_did: DefId,
    available_ty: &HashSet<TyWrapper<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    let mut rng = rand::rng();

    // sample from reachable types
    rap_debug!("[get_mono_set] solve {}", tcx.def_path_str(fn_did));
    let identity = ty::GenericArgs::identity_for_item(tcx, fn_did);
    let infcx = tcx
        .infer_ctxt()
        .ignoring_regions()
        .build(ty::TypingMode::PostAnalysis);
    let param_env = tcx.param_env(fn_did);
    let dummy_cause = ObligationCause::dummy();
    let fresh_args = infcx.fresh_args_for_item(DUMMY_SP, fn_did);
    // this replace generic types in fn_sig to infer var, e.g. fn(Vec<T>, i32) => fn(Vec<?0>, i32)
    let fn_sig = fn_sig_with_generic_args(fn_did, fresh_args, tcx);
    let identity_fnsig = fn_sig_with_generic_args(fn_did, identity, tcx);
    let generics = tcx.generics_of(fn_did);

    // print fresh_args for debugging
    for i in 0..fresh_args.len() {
        rap_trace!(
            "[get_mono_set] arg#{}: {:?} -> {:?}",
            i,
            generics.param_at(i, tcx).name,
            fresh_args[i]
        );
    }

    let mut s = MonoSet::all(&fresh_args);

    rap_trace!("[get_mono_set] initialize s: {:?}", s);

    for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
        if !input_ty.has_infer_types() {
            continue;
        }
        rap_debug!(
            "[get_mono_set] input_ty#{}: {}",
            no,
            identity_fnsig.inputs()[no]
        );

        let reachable_set = available_ty
            .iter()
            .fold(MonoSet::new(), |mut reachable_set, ty| {
                if let Some(mono) = unify_ty(
                    *input_ty,
                    (*ty).into(),
                    &fresh_args,
                    &infcx,
                    &dummy_cause,
                    param_env,
                ) {
                    reachable_set.insert(mono);
                }
                reachable_set
            });
        // reachable_set.random_sample(&mut rng);
        rap_debug!(
            "[get_mono_set] size of s: {}, size of input: {}",
            s.count(),
            reachable_set.count()
        );
        rap_trace!("[get_mono_set] input = {:?}", reachable_set);
        s = s.merge(&reachable_set, tcx);
        s.random_sample(&mut rng);
        rap_trace!("[get_mono_set] after merge s = {:?}", reachable_set);
    }

    rap_debug!(
        "[get_mono_set] after input filter, size of s: {}",
        s.count()
    );

    let mut res = MonoSet::new();

    for mono in s.monos {
        solve_unbound_type_generics(
            fn_did,
            mono,
            &mut res,
            // &fresh_args,
            &infcx,
            &dummy_cause,
            param_env,
            tcx,
        );
    }

    // erase infer region var
    res.erase_region_var(tcx);

    // if there is still unbound generic type, we try to instantiate it with predefined candidates
    res.instantiate_unbound(tcx)
}

fn solve_unbound_type_generics<'tcx>(
    did: DefId,
    mono: Mono<'tcx>,
    res: &mut MonoSet<'tcx>,
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
) {
    if !mono.has_infer_types() {
        res.insert(mono);
        return;
    }
    let args = tcx.mk_args(&mono.value);
    let preds = tcx.predicates_of(did).instantiate(tcx, args);
    let mut mset = MonoSet::all(args);
    rap_debug!("[solve_unbound] did = {did:?}, mset={mset:?}");
    for pred in preds.predicates.iter() {
        rap_debug!("[solve_unbound] pred = {:?}", pred);
        if let Some(trait_pred) = pred.as_trait_clause() {
            let trait_pred = trait_pred.skip_binder();

            rap_trace!("[solve_unbound] pred: {:?}", trait_pred);

            let trait_def_id = trait_pred.trait_ref.def_id;
            // ignore Sized trait
            if tcx.is_lang_item(trait_def_id, LangItem::Sized)
                || tcx.is_lang_item(trait_def_id, LangItem::Copy)
            {
                continue;
            }

            let mut p = MonoSet::new();

            for impl_did in tcx.all_impls(trait_def_id)
            // .chain(tcx.inherent_impls(trait_def_id).iter().map(|did| *did))
            {
                // format: <arg0 as Trait<arg1, arg2>>
                let impl_trait_ref = tcx.impl_trait_ref(impl_did).skip_binder();

                // filter irrelevant implementation. We only consider implementation that:
                // 1. it is local
                // 2. it is not local, but its' self_ty is a primitive
                if !impl_did.is_local() && !impl_trait_ref.self_ty().is_primitive() {
                    continue;
                }

                if let Some(mono) = unify_trait(
                    trait_pred.trait_ref,
                    impl_trait_ref,
                    args,
                    &infcx,
                    &cause,
                    param_env,
                    tcx,
                ) {
                    p.insert(mono);
                }
            }
            mset = mset.merge(&p, tcx);
            rap_trace!("[solve_unbound] mset: {:?}", mset);
        }
    }

    rap_trace!("[solve_unbound] (final) mset: {:?}", mset);
    for mono in mset.monos {
        res.insert(mono);
    }
}

/// only handle the case that rhs does not have any infer types
/// e.g., `<T as Into<U>> == <Foo as Into<Bar>> => Some(T=Foo, U=Bar))`
fn unify_trait<'tcx>(
    lhs: ty::TraitRef<'tcx>,
    rhs: ty::TraitRef<'tcx>,
    identity: &[ty::GenericArg<'tcx>],
    infcx: &InferCtxt<'tcx>,
    cause: &ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<Mono<'tcx>> {
    rap_trace!("[unify_trait] lhs: {:?}, rhs: {:?}", lhs, rhs);
    if lhs.def_id != rhs.def_id {
        return None;
    }

    assert!(lhs.args.len() == rhs.args.len());
    let mut s = Mono::new(identity);
    for (lhs_arg, rhs_arg) in lhs.args.iter().zip(rhs.args.iter()) {
        if let (Some(lhs_ty), Some(rhs_ty)) = (lhs_arg.as_type(), rhs_arg.as_type()) {
            if rhs_ty.has_infer_types() || rhs_ty.has_param() {
                // if rhs has infer types, we cannot unify it with lhs
                return None;
            }
            let mono = unify_ty(lhs_ty, rhs_ty, identity, infcx, cause, param_env)?;
            rap_trace!("[unify_trait] unified mono: {:?}", mono);
            s = s.merge(&mono, tcx)?;
        }
    }
    Some(s)
}

pub fn resolve_mono_apis<'tcx>(
    fn_did: DefId,
    available_ty: &HashSet<TyWrapper<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> MonoSet<'tcx> {
    // 1. check solvable condition
    if !is_fn_solvable(fn_did, tcx) {
        return MonoSet::empty();
    }

    // 2. get mono set from available types
    let ret = get_mono_set(fn_did, &available_ty, tcx);

    // 3. check trait bound & ty is stable
    let ret = ret.filter(|mono| {
        is_args_fit_trait_bound(fn_did, &mono.value, tcx)
            && mono.value.iter().all(|arg| {
                if let Some(ty) = arg.as_type() {
                    !utils::is_ty_unstable(ty, tcx)
                } else {
                    true
                }
            })
    });

    rap_debug!(
        "[resolve_mono_apis] fn_did: {:?}, size of mono: {:?}",
        fn_did,
        ret.count()
    );

    ret
}

pub fn add_transform_tys<'tcx>(available_ty: &mut HashSet<TyWrapper<'tcx>>, tcx: TyCtxt<'tcx>) {
    let mut new_tys = Vec::new();
    available_ty.iter().for_each(|ty| {
        new_tys.push(
            Ty::new_ref(
                tcx,
                tcx.lifetimes.re_erased,
                (*ty).into(),
                ty::Mutability::Not,
            )
            .into(),
        );
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            (*ty).into(),
            ty::Mutability::Mut,
        ));
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            Ty::new_slice(tcx, (*ty).into()),
            ty::Mutability::Not,
        ));
        new_tys.push(Ty::new_ref(
            tcx,
            tcx.lifetimes.re_erased,
            Ty::new_slice(tcx, (*ty).into()),
            ty::Mutability::Mut,
        ));
    });

    new_tys.into_iter().for_each(|ty| {
        available_ty.insert(ty.into());
    });
}

pub fn eliminate_infer_var<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> Vec<ty::GenericArg<'tcx>> {
    let mut res = Vec::new();
    let identity = ty::GenericArgs::identity_for_item(tcx, fn_did);
    for (i, arg) in args.iter().enumerate() {
        if let Some(ty) = arg.as_type() {
            if ty.is_ty_var() {
                res.push(identity[i]);
            } else {
                res.push(*arg);
            }
        } else {
            res.push(*arg);
        }
    }
    res
}

/// if type parameter is unbound, e.g., `T` in `fn foo<T>()`,
/// we use some predefined types to substitute it
pub fn get_unbound_generic_candidates<'tcx>(tcx: TyCtxt<'tcx>) -> Vec<ty::Ty<'tcx>> {
    vec![
        tcx.types.bool,
        tcx.types.char,
        tcx.types.u8,
        tcx.types.i8,
        tcx.types.i32,
        tcx.types.u32,
        // tcx.types.i64,
        // tcx.types.u64,
        tcx.types.f32,
        // tcx.types.f64,
        Ty::new_imm_ref(
            tcx,
            tcx.lifetimes.re_erased,
            Ty::new_slice(tcx, tcx.types.u8),
        ),
        Ty::new_mut_ref(
            tcx,
            tcx.lifetimes.re_erased,
            Ty::new_slice(tcx, tcx.types.u8),
        ),
    ]
}

// calculate the complexity of monomorphic solution,
// complexity = sum of complexity of each type argument
pub fn get_mono_complexity<'tcx>(args: &GenericArgsRef<'tcx>) -> usize {
    args.iter().fold(0, |acc, arg| {
        if let Some(ty) = arg.as_type() {
            acc + utils::ty_complexity(ty)
        } else {
            acc
        }
    })
}

pub fn get_impls<'tcx>(
    tcx: TyCtxt<'tcx>,
    fn_did: DefId,
    args: GenericArgsRef<'tcx>,
) -> HashSet<DefId> {
    rap_debug!(
        "get impls for fn: {:?} args: {:?}",
        tcx.def_path_str_with_args(fn_did, args),
        args
    );
    let mut impls = HashSet::new();
    let preds = tcx.predicates_of(fn_did).instantiate(tcx, args);
    for (pred, _) in preds {
        if let Some(trait_pred) = pred.as_trait_clause() {
            let trait_ref: rustc_type_ir::TraitRef<TyCtxt<'tcx>> = tcx
                .liberate_late_bound_regions(fn_did, trait_pred)
                .trait_ref;

            let res = tcx.codegen_select_candidate(
                TypingEnv::fully_monomorphized().as_query_input(trait_ref),
            );
            if let Ok(source) = res {
                match source {
                    ImplSource::UserDefined(data) => {
                        if data.impl_def_id.is_local() {
                            impls.insert(data.impl_def_id);
                        }
                    }
                    _ => {}
                }
            }
            // rap_debug!("{:?} => {:?}", trait_ref, res);
        }
    }
    rap_trace!("fn: {:?} args: {:?} impls: {:?}", fn_did, args, impls);
    impls
}
