//! Collection of verification targets and their contract obligations.
//!
//! [`VerifyTargetCollector`] walks the current crate in targeted or scan mode.
//! It collects function checkpoints, their required contracts, invariants, and
//! obligations from unsafe trait implementations.

use crate::analysis::Analysis;
use crate::analysis::safety_flow::root::{
    function_has_trait_ensurance, hir_contains_unsafe,
};
use crate::verify::config::VerifyMode;
use crate::compat::FxHashMap;
use crate::contract::{
    ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind,
    ensures::get_trait_method_ensures, type_invariants::build_type_invariants_from_params,
};
use crate::def_ids::{
    intrinsic_api,
    lang_api::{self, LangItem},
};
use crate::util::name::short_fn_name;
use crate::util::resolve;
use crate::verify::checkpoint::{
    collect_raw_ptr_deref_checkpoints, collect_static_mut_checkpoints,
};
use rustc_hir::{
    BodyId, FnDecl, ItemKind,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::{
    hir::nested_filter,
    mir::{Body, NonDivergingIntrinsic, StatementKind, TerminatorKind},
    ty::{Const, EarlyBinder, GenericArgs, GenericParamDefKind, Instance, InstanceKind, Ty, TyCtxt, TyKind, TypeFlags, TypeVisitableExt},
};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::{
    config::VerifyConfig,
    path::{CalleeBodies, PathExtractor},
    trait_ensurance::{
        MarkerTraitKind, TraitEnsurance, TraitEnsuranceKind, build_marker_trait_obligations,
        marker_trait_kind,
    },
};
use crate::util::fn_info::get_adt_def_id_by_adt_method;
use crate::util::mir_utils::{
    collect_return_block_indices, has_rapx_verify_attr, is_std_crate_def_id, is_trait_unsafe,
    resolve_impl_self_ty_def_id,
};
use crate::verify::checkpoint::{Checkpoint, CheckpointKind, collect_unsafe_callsites};

use crate::contract::annotation::{bind_alive_regions, function_has_rapx_struct_invariant, get_contract_from_annotation, get_struct_invariants_from_annotation, get_trait_method_requires};

/// Preconditions associated with a function or unsafe callee.
pub(crate) type FnContracts<'tcx> = Vec<Property<'tcx>>;

/// Invariants declared on a struct.
pub(crate) type StructInvariants<'tcx> = Vec<Property<'tcx>>;

fn has_symbolic_array_length(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Array(elem, len) => len.has_type_flags(TypeFlags::HAS_CT_PARAM) || has_symbolic_array_length(*elem),
        TyKind::Slice(elem) | TyKind::Ref(_, elem, _) | TyKind::RawPtr(elem, _) => has_symbolic_array_length(*elem),
        TyKind::Tuple(fields) => fields.iter().any(has_symbolic_array_length),
        _ => false,
    }
}

/// Checkpoints, contracts, and invariants for one function.
///
/// The collector records unsafe calls, raw pointer dereferences, and static mut
/// accesses as checkpoints. It attaches callee preconditions and the caller's
/// entry assumptions, then passes the target to the path and verification stages.
#[derive(Clone, Debug)]
pub(crate) struct FunctionTarget<'tcx> {
    /// The function being verified.
    pub def_id: DefId,

    /// Instantiated MIR shared by path extraction, slicing, and symbolic replay.
    pub body: Option<&'tcx rustc_middle::mir::Body<'tcx>>,

    /// This instance checks one length in a bounded array const generic sweep.
    pub array_length_limited: bool,

    /// Unique direct generic callees instantiated in the root's parameter environment.
    pub callee_bodies: CalleeBodies<'tcx>,

    /// Owning struct for an associated method; `None` for a free function.
    pub owner_struct_def_id: Option<DefId>,

    /// Unsafe call checkpoints found in the function's MIR.
    pub checkpoints: Vec<Checkpoint<'tcx>>,

    /// Preconditions for each direct unsafe callee, keyed by its `DefId`.
    /// Sources include annotations, bundled JSON, and inherited call contracts.
    pub callee_requires: HashMap<DefId, FnContracts<'tcx>>,

    /// Entry assumptions from this function's preconditions and invariants.
    pub caller_requires: FnContracts<'tcx>,

    /// Declared struct invariants and built-in invariants for checked functions.
    pub invariants: Vec<Property<'tcx>>,

    /// Checkpoints and obligations for raw pointer dereferences.
    /// Obligations include `Allocated`, `InBound`, and `Align`, plus `Typed`
    /// for reads and extra checks when creating a reference from a pointer.
    pub raw_ptr_deref_checks: Vec<Checkpoint<'tcx>>,

    /// Checkpoints and obligations for static mut accesses.
    /// Each requires `Allocated`, `InBound`, `Align`, and `Init`.
    pub static_mut_checks: Vec<Checkpoint<'tcx>>,
}

impl<'tcx> FunctionTarget<'tcx> {
    pub(crate) fn has_checkable_checkpoint(&self) -> bool {
        self.all_checkpoints().any(|checkpoint| {
            !self.properties_for_callsite(checkpoint).is_empty()
                || (checkpoint.kind == crate::verify::checkpoint::CheckpointKind::UnsafeCall
                    && checkpoint.callee.is_none())
        })
    }

    pub(crate) fn all_checkpoints(&self) -> impl Iterator<Item = &Checkpoint<'tcx>> + '_ {
        self.checkpoints
            .iter()
            .chain(self.raw_ptr_deref_checks.iter())
            .chain(self.static_mut_checks.iter())
    }

    pub(crate) fn properties_for_callsite<'a>(
        &'a self,
        checkpoint: &'a Checkpoint<'tcx>,
    ) -> &'a [Property<'tcx>] {
        if !checkpoint.requires.is_empty() {
            &checkpoint.requires
        } else {
            checkpoint
                .callee
                .and_then(|callee| self.callee_requires.get(&callee))
                .map(Vec::as_slice)
                .unwrap_or(&[])
        }
    }
}

/// Invariants and selected methods for one struct.
pub(crate) struct StructTarget<'tcx> {
    /// Struct that owns the selected methods.
    pub def_id: DefId,

    /// Parsed invariants declared on the struct.
    pub invariants: StructInvariants<'tcx>,

    /// Methods selected for verification.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
}

/// Trace a call operand through unique copies or shared reborrows to an outer parameter.
///
/// Reject reassigned locals: without a reaching-definition check, selecting one
/// of several writes could attach the wrong precondition to the wrapper.
fn call_arg_to_outer_param(
    op: &rustc_middle::mir::Operand<'_>,
    body: &rustc_middle::mir::Body<'_>,
) -> Option<usize> {
    let local = match op {
        rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p)
            if p.projection.is_empty() =>
        {
            p.local
        }
        _ => return None,
    };
    let mut current = local;
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current) {
            return None;
        }
        let mut source = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != current {
                    continue;
                }
                if !dest.projection.is_empty() || source.is_some() {
                    return None;
                }
                source = match rvalue {
                    rustc_middle::mir::Rvalue::Use(
                        rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p),
                        ..,
                    ) if p.projection.is_empty() => Some(p.local),
                    rustc_middle::mir::Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, p)
                        if p.projection.as_ref() == [rustc_middle::mir::ProjectionElem::Deref]
                            && body.local_decls[p.local].ty == body.local_decls[current].ty =>
                    {
                        Some(p.local)
                    }
                    _ => return None,
                };
            }
            if let rustc_middle::mir::TerminatorKind::Call { destination, .. } = &bb.terminator().kind
                && destination.local == current
            {
                return None;
            }
        }
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return source.is_none().then_some(cidx - 1);
        }
        current = source?;
    }
}

/// Rebind a callee contract to parameters of its enclosing function.
///
/// Returns `false` when an argument cannot be traced to a parameter. The
/// caller drops that property because it cannot express it as a precondition.
fn rebind_property_to_args<'tcx>(
    prop: &mut Property<'tcx>,
    args: &[rustc_middle::mir::Operand<'tcx>],
    callee_args: &rustc_middle::ty::GenericArgs<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    match prop {
        Property::Atom(atom) => {
            let mut ok = true;
            for arg in &mut atom.args {
                if !rebind_property_arg(arg, args, callee_args, body) {
                    ok = false;
                }
            }
            ok
        }
        Property::And(and) => {
            let mut ok = true;
            for conjunct in &mut and.conjuncts {
                if !rebind_property_to_args(conjunct, args, callee_args, body) {
                    ok = false;
                }
            }
            ok
        }
        Property::Or(or) => {
            // Unlike `And`, an `Or` whose disjuncts were individually filtered
            // would leave orphaned place-less disjuncts (e.g. `ValidPtr`'s
            // `Size(T, 0) || Deref(p)` keeps `Size` after `Deref` is dropped,
            // and `Size(u8, 0)` then reads as `Failed`).  Treat `Or` as
            // all-or-nothing too: if any disjunct cannot be restated, drop the
            // whole disjunction.
            let mut ok = true;
            for disjunct in &mut or.disjuncts {
                if !rebind_property_to_args(disjunct, args, callee_args, body) {
                    ok = false;
                }
            }
            ok
        }
    }
}

fn rebind_property_arg<'tcx>(
    arg: &mut PropertyArg<'tcx>,
    args: &[rustc_middle::mir::Operand<'tcx>],
    callee_args: &rustc_middle::ty::GenericArgs<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    match arg {
        PropertyArg::Expr(expr) => rebind_expr(expr, args, callee_args, body),
        PropertyArg::ForEach(expr) => rebind_expr(expr, args, callee_args, body),
        PropertyArg::Predicates(preds) => {
            let mut ok = true;
            for p in preds {
                if !rebind_expr(&mut p.lhs, args, callee_args, body) {
                    ok = false;
                }
                if !rebind_expr(&mut p.rhs, args, callee_args, body) {
                    ok = false;
                }
            }
            ok
        }
        // Resolve the leaf callee's type parameter to the concrete type
        // argument passed at the call site (e.g. `NonNull::<Node<T>>::as_mut`'s
        // `Ptr2Ref(self, T)` -> `Ptr2Ref(self, Node<T>)`).
        PropertyArg::Ty(ty) => {
            rebind_ty(ty, callee_args);
            true
        }
        _ => true,
    }
}

fn rebind_expr<'tcx>(
    expr: &mut ContractExpr<'tcx>,
    args: &[rustc_middle::mir::Operand<'tcx>],
    callee_args: &rustc_middle::ty::GenericArgs<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    match expr {
        ContractExpr::Place(place) => rebind_place(place, args, body),
        ContractExpr::MethodCall { receiver, args: method_args, .. } => {
            let mut ok = rebind_expr(receiver, args, callee_args, body);
            for arg in method_args {
                ok &= rebind_expr(arg, args, callee_args, body);
            }
            ok
        }
        ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
            rebind_expr(inner, args, callee_args, body)
        }
        ContractExpr::SizeOf(ty) => {
            rebind_ty(ty, callee_args);
            true
        }
        ContractExpr::AlignOf(ty) => {
            rebind_ty(ty, callee_args);
            true
        }
        ContractExpr::IndexAccess { slice, index } => {
            let a = rebind_expr(slice, args, callee_args, body);
            let b = rebind_expr(index, args, callee_args, body);
            a && b
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            let a = rebind_expr(lhs, args, callee_args, body);
            let b = rebind_expr(rhs, args, callee_args, body);
            a && b
        }
        ContractExpr::Unary { expr, .. } => rebind_expr(expr, args, callee_args, body),
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            let a = rebind_expr(&mut cond.lhs, args, callee_args, body);
            let b = rebind_expr(&mut cond.rhs, args, callee_args, body);
            let c = rebind_expr(then_expr, args, callee_args, body);
            let d = rebind_expr(else_expr, args, callee_args, body);
            a && b && c && d
        }
        _ => true,
    }
}

/// Replace a leaf callee's type parameter (`TyKind::Param`) with the concrete
/// type argument passed at the call site.
fn rebind_ty<'tcx>(
    ty: &mut rustc_middle::ty::Ty<'tcx>,
    callee_args: &rustc_middle::ty::GenericArgs<'tcx>,
) {
    if let rustc_middle::ty::TyKind::Param(param) = ty.kind()
        && let Some(actual) = callee_args
            .get(param.index as usize)
            .and_then(|a| a.as_type())
    {
        *ty = actual;
    }
}

fn rebind_place<'tcx>(
    place: &mut ContractPlace,
    args: &[rustc_middle::mir::Operand<'tcx>],
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    rebind_base(&mut place.base, args, body)
}

fn rebind_base<'tcx>(
    base: &mut PlaceBase,
    args: &[rustc_middle::mir::Operand<'tcx>],
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    // A contract references the leaf callee's arguments either as a 0-based
    // `Arg(i)` (std JSON contracts) or as a MIR `Local(k)` (inline
    // `#[rapx::requires]`, where local 1..=arg_count are the parameters). Map
    // both onto the argument index, then trace that argument back to this
    // callee's parameter. `Local(0)`/`Return` name the return value and cannot
    // be restated as a precondition.
    let arg_idx = match *base {
        PlaceBase::Arg(i) => Some(i),
        PlaceBase::Local(k) if k >= 1 => Some(k - 1),
        _ => return false,
    };
    match arg_idx
        .and_then(|i| args.get(i))
        .and_then(|op| call_arg_to_outer_param(op, body))
    {
        Some(outer) => {
            *base = PlaceBase::Arg(outer);
            true
        }
        None => false,
    }
}

/// Collect preconditions inherited through an unsafe callee's call chain.
///
/// For an unannotated wrapper, inspect its unsafe calls and rebind their
/// contracts to the wrapper's parameters. Continue recursively through
/// unannotated callees.
///
/// `visited` tracks the active recursion path and prevents cycles.
fn resolve_chain_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    visited: &mut HashSet<DefId>,
) -> FnContracts<'tcx> {
    if !visited.insert(callee_def_id) {
        return Vec::new();
    }

    if !tcx.is_mir_available(callee_def_id) {
        visited.remove(&callee_def_id);
        return Vec::new();
    }

    let body = tcx.optimized_mir(callee_def_id);
    let mut contracts = Vec::new();

    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else {
            continue;
        };
        if let rustc_middle::mir::TerminatorKind::Call { func, args, .. } = &terminator.kind
            && let rustc_middle::mir::Operand::Constant(c) = func
        {
            let rustc_middle::ty::TyKind::FnDef(sub_def_id, callee_args) = c.const_.ty().kind()
            else {
                continue;
            };
            let sub_def_id = *sub_def_id;

            let fn_sig = tcx.fn_sig(sub_def_id).skip_binder();
            if fn_sig.safety() != rustc_hir::Safety::Unsafe {
                continue;
            }

            let mut reqs = get_contract_from_annotation(tcx, sub_def_id);

            if reqs.is_empty() {
                reqs = get_trait_method_requires(tcx, sub_def_id);
            }

            if reqs.is_empty() && is_std_crate_def_id(tcx, sub_def_id) {
                reqs = crate::contract::json::query_json_contracts(tcx, sub_def_id);
            }

            if reqs.is_empty() {
                reqs = resolve_chain_contracts(tcx, sub_def_id, visited);
            }

            // Rebind the leaf callee's argument references onto this
            // callee's parameters (e.g. `ptr::write`'s `self` -> this
            // callee's pointer argument), dropping contracts whose arguments
            // are internal temporaries that can't be restated on this
            // callee's parameters. Also resolve the leaf's type parameters
            // to the concrete type arguments passed at the call site.
            let arg_operands: Vec<_> = args.iter().map(|a| a.node.clone()).collect();
            let callee_args = callee_args.skip_binder();
            reqs.retain_mut(|req| rebind_property_to_args(req, &arg_operands, &callee_args, body));

            contracts.extend(reqs);
        }
    }

    visited.remove(&callee_def_id);
    contracts
}

/// Visitor that collects targets annotated with `#[rapx::verify]`.
pub(crate) struct VerifyTargetCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    config: Rc<VerifyConfig>,
    crate_filter_matched: bool,
    module_filter_matched: bool,
    /// All function targets to verify collected from the current crate.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
    /// All struct targets to verify collected from the current crate.
    pub struct_targets: HashMap<DefId, StructTarget<'tcx>>,
    /// All trait impls to verify (marker traits and unsafe traits), one entry
    /// per `impl` block.
    pub trait_targets: Vec<TraitEnsurance<'tcx>>,
    /// Cached contracts for each callee function so repeated callees are parsed once.
    fn_contract_cache: HashMap<(DefId, bool), FnContracts<'tcx>>,
}

impl<'tcx> VerifyTargetCollector<'tcx> {
    /// Collect verification targets from the crate currently being compiled.
    pub(crate) fn collect_all(tcx: TyCtxt<'tcx>, config: Rc<VerifyConfig>) -> Self {
        let mut collector = Self {
            tcx,
            config,
            crate_filter_matched: false,
            module_filter_matched: false,
            function_targets: Vec::new(),
            struct_targets: HashMap::new(),
            trait_targets: Vec::new(),
            fn_contract_cache: HashMap::new(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut collector);
        collector.check_module_filter_result();
        collector
    }

    /// Resolve and cache preconditions for a callee.
    ///
    /// Resolution order: callee annotations, trait-method annotations, bundled
    /// standard-library JSON, then inherited call-chain contracts when
    /// `follow_chain` is enabled. If none applies, an `Unknown` property records
    /// the missing contract unless an empty contract is explicitly allowed.
    ///
    /// Call-site obligations use `follow_chain = true`. A function's own entry
    /// assumptions use `false` so its internal calls cannot add assumptions.
    fn get_fn_contracts(&mut self, callee_def_id: DefId, follow_chain: bool) -> FnContracts<'tcx> {
        let is_std = is_std_crate_def_id(self.tcx, callee_def_id);

        let trait_requires = get_trait_method_requires(self.tcx, callee_def_id);

        self.fn_contract_cache
            .entry((callee_def_id, follow_chain))
            .or_insert_with(|| {
                let mut requires = get_contract_from_annotation(self.tcx, callee_def_id);

                if requires.is_empty() && !trait_requires.is_empty() {
                    requires = trait_requires.clone();
                }

                if requires.is_empty() && is_std {
                    requires = crate::contract::json::query_json_contracts(self.tcx, callee_def_id);
                }

                if requires.is_empty() && follow_chain {
                    let mut visited = HashSet::new();
                    requires = resolve_chain_contracts(self.tcx, callee_def_id, &mut visited);
                    if requires.is_empty() {
                        // Safe callees, intrinsics, and verified bodies need no JSON contract.
                        let is_intrinsic =
                            crate::def_ids::intrinsic_api::is_intrinsic(self.tcx, callee_def_id);
                        let has_json_entry = is_std
                            && crate::contract::json::get_std_contracts_from_json(
                                self.tcx,
                                callee_def_id,
                            )
                            .is_some();
                        let is_verify_target = callee_def_id
                            .as_local()
                            .is_some_and(|id| has_rapx_verify_attr(self.tcx, id));
                        if self.tcx.fn_sig(callee_def_id).skip_binder().safety()
                            == rustc_hir::Safety::Unsafe
                            && !is_intrinsic
                            && !has_json_entry
                            && !is_verify_target
                        {
                            let path = crate::util::name::get_cleaned_def_path_name(
                                self.tcx,
                                callee_def_id,
                            );
                            rap_warn!("no safety contracts found for callee \"{path}\"");
                        }
                    } else {
                        let path = crate::util::name::get_cleaned_def_path_name(
                            self.tcx,
                            callee_def_id,
                        );
                        rap_debug!(
                            "resolved {} safety contract(s) for callee \"{path}\" via call chain",
                            requires.len()
                        );
                    }
                }

                if requires.is_empty() {
                    // An empty JSON contract or a verified body without obligations needs no requirements.
                    let has_json_entry = is_std
                        && crate::contract::json::get_std_contracts_from_json(
                            self.tcx,
                            callee_def_id,
                        )
                        .is_some();
                    let is_verify_target = callee_def_id
                        .as_local()
                        .is_some_and(|id| has_rapx_verify_attr(self.tcx, id));
                    let verified_body_has_no_obligations = follow_chain
                        && is_verify_target
                        && self.tcx.is_mir_available(callee_def_id)
                        && !function_has_rapx_struct_invariant(self.tcx, callee_def_id)
                        && collect_unsafe_callsites(self.tcx, callee_def_id).is_empty()
                        && collect_raw_ptr_deref_checkpoints(self.tcx, callee_def_id).is_empty()
                        && collect_static_mut_checkpoints(self.tcx, callee_def_id).is_empty();
                    if !has_json_entry && (!is_verify_target || (follow_chain && !verified_body_has_no_obligations)) {
                        requires.push(Property::new(self.tcx, callee_def_id, "Unknown", &[]));
                    }
                }

                requires
            })
            .clone()
    }

    /// Builds a function target to verify from a function definition.
    pub(crate) fn build_function_target(
        &mut self,
        def_id: DefId,
        instance: Option<Instance<'tcx>>,
    ) -> FunctionTarget<'tcx> {
        let body: Option<&'tcx Body<'tcx>> = instance
            .filter(|inst| !resolve::has_unresolved_const_args(self.tcx, def_id, inst.args))
            .and_then(|inst| {
                let mir = self.tcx.optimized_mir(def_id);
                inst.try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    crate::compat::typing_env_post_analysis(self.tcx, def_id),
                    rustc_middle::ty::EarlyBinder::bind(self.tcx, mir.clone()),
                )
                .ok()
                .map(|body| &*self.tcx.arena.alloc(body))
            });
        let mut callee_bodies = CalleeBodies::default();
        if let Some(root_body) = body {
            let mut instances = FxHashMap::default();
            let mut conflicting = HashSet::new();
            for block in root_body.basic_blocks.iter() {
                let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                    continue;
                };
                let Some(callee) = resolve::resolve_callee_def_id(
                    self.tcx, def_id, func,
                ) else {
                    continue;
                };
                if !self.tcx.is_mir_available(callee)
                    || !crate::util::mir_utils::has_direct_unmodeled_generic_call(self.tcx, callee)
                {
                    continue;
                }
                let Some(inst) = resolve::resolve_callee_instance(
                    self.tcx, def_id, func,
                ) else {
                    continue;
                };
                if !matches!(inst.def, InstanceKind::Item(_)) || inst.def_id() != callee {
                    continue;
                }
                if resolve::has_unresolved_const_args(self.tcx, def_id, inst.args) {
                    continue;
                }
                if let Some(previous) = instances.insert(callee, inst)
                    && previous != inst
                {
                    conflicting.insert(callee);
                }
            }
            for (callee, inst) in instances {
                if conflicting.contains(&callee) {
                    continue;
                }
                let mir = self.tcx.optimized_mir(callee).clone();
                let Ok(instantiated) = inst.try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    crate::compat::typing_env_post_analysis(self.tcx, def_id),
                    EarlyBinder::bind(self.tcx, mir),
                ) else {
                    continue;
                };
                callee_bodies.insert(callee, &*self.tcx.arena.alloc(instantiated));
            }
        }
        let mut checkpoints = collect_unsafe_callsites(self.tcx, def_id);
        for checkpoint in &mut checkpoints {
            let mir = self.tcx.optimized_mir(def_id);
            let Some(statement) = mir.basic_blocks[checkpoint.block]
                .statements
                .get(checkpoint.stmt_index)
            else {
                continue;
            };
            let StatementKind::Intrinsic(intrinsic) = &statement.kind else {
                continue;
            };
            let path = intrinsic_api::lowered_mir_path(intrinsic);
            let signature_def_id = match &**intrinsic {
                NonDivergingIntrinsic::Assume(_) => Some(def_id),
                NonDivergingIntrinsic::CopyNonOverlapping(_) => checkpoint.callee,
            };
            checkpoint.requires = signature_def_id
                .map(|did| crate::contract::json::query_json_contracts_at_path(self.tcx, did, path))
                .filter(|requires| !requires.is_empty())
                .unwrap_or_else(|| vec![Property::new_atom(PropertyKind::Unknown, Vec::new())]);
        }
        let unsafe_callees: HashSet<_> = checkpoints
            .iter()
            .filter(|checkpoint| checkpoint.kind == CheckpointKind::UnsafeCall)
            .filter(|checkpoint| checkpoint.requires.is_empty())
            .filter_map(|checkpoint| checkpoint.callee)
            .collect();
        let callee_requires = unsafe_callees
            .iter()
            .map(|callee_def_id| {
                let contracts = self.get_fn_contracts(*callee_def_id, true);
                (*callee_def_id, contracts)
            })
            .collect();

        let mut caller_requires = self.get_fn_contracts(def_id, false);
        // Bind entry lifetimes here; callee lifetimes bind at the call site.
        for contract in &mut caller_requires {
            bind_alive_regions(self.tcx, def_id, contract);
        }

        let raw_ptr_deref_checks = collect_raw_ptr_deref_checkpoints(self.tcx, def_id);
        let static_mut_checks = collect_static_mut_checkpoints(self.tcx, def_id);

        let owner_struct_def_id = get_adt_def_id_by_adt_method(self.tcx, def_id);
        let mut struct_invariants = owner_struct_def_id
            .map(|struct_def_id| {
                get_struct_invariants_from_annotation(self.tcx, struct_def_id, def_id)
            })
            .unwrap_or_default();

        // Hazard atoms belong at pointer use sites, not among entry facts.
        struct_invariants = struct_invariants
            .into_iter()
            .filter_map(|inv| inv.strip_hazards())
            .collect();

        // Methods inherit struct invariants as entry facts.
        caller_requires.extend(struct_invariants.clone());

        // Destructors may dismantle struct invariants.
        if is_drop_impl(self.tcx, def_id) {
            struct_invariants.clear();
        }

        let mut target = FunctionTarget {
            def_id,
            body,
            array_length_limited: false,
            callee_bodies,
            owner_struct_def_id,
            checkpoints,
            callee_requires,
            caller_requires,
            invariants: struct_invariants,
            raw_ptr_deref_checks,
            static_mut_checks,
        };
        // Built-in invariants are entry facts, but exit obligations only when
        // this function contains a checkable unsafe operation.
        let type_invariants = build_type_invariants_from_params(self.tcx, def_id);
        target.caller_requires.extend(type_invariants.iter().cloned());
        if target.has_checkable_checkpoint() {
            target.invariants.extend(type_invariants);
        }
        target
    }

    /// Check small concrete array lengths, or monomorphize unmodeled trait calls.
    fn build_function_targets(&mut self, def_id: DefId) -> Vec<FunctionTarget<'tcx>> {
        let unmodeled_generic_call = crate::util::mir_utils::has_unmodeled_generic_call(self.tcx, def_id);
        if self.tcx.is_mir_available(def_id) {
            let params: Vec<_> = std::iter::successors(Some(def_id), |id| self.tcx.generics_of(*id).parent)
                .flat_map(|id| self.tcx.generics_of(id).own_params.iter())
                .collect();
            let has_type_params = params.iter().any(|param| matches!(param.kind, GenericParamDefKind::Type { .. }));
            let const_params: Vec<_> = params.iter().copied()
                .filter(|param| matches!(param.kind, GenericParamDefKind::Const { .. })).collect();
            let body = self.tcx.optimized_mir(def_id);
            if !has_type_params && let [param] = const_params.as_slice()
                && self.tcx.type_of(param.def_id).instantiate_identity().skip_norm_wip() == self.tcx.types.usize
                && body.local_decls.iter().any(|decl| has_symbolic_array_length(decl.ty))
            {
                let mut targets = Vec::new();
                let mut needs_generic = false;
                for length in 0..=self.config.array_length_limit() {
                    let args = GenericArgs::for_item(self.tcx, def_id, |candidate, _| {
                        if candidate.def_id == param.def_id {
                            Const::from_target_usize(self.tcx, length as u64).into()
                        } else {
                            self.tcx.mk_param_from_def(candidate)
                        }
                    });
                    let instance = Instance::new_raw(def_id, args);
                    let mut target = self.build_function_target(def_id, Some(instance));
                    if target.body.is_some() {
                        target.array_length_limited = true;
                        targets.push(target);
                    } else {
                        needs_generic = true;
                    }
                }
                if needs_generic {
                    targets.push(self.build_function_target(def_id, None));
                }
                return targets;
            }
        }
        if !unmodeled_generic_call {
            return vec![self.build_function_target(def_id, None)];
        }
        let instances = crate::util::mir_utils::enumerate_mono_instances(
            self.tcx,
            def_id,
            self.config.trait_impl_limit(),
        );
        let mut targets = Vec::new();
        let mut needs_generic = instances.is_empty();
        for inst in instances {
            let target = self.build_function_target(def_id, Some(inst));
            if target.body.is_some() {
                targets.push(target);
            } else {
                needs_generic = true;
            }
        }
        if needs_generic {
            targets.push(self.build_function_target(def_id, None));
        }
        targets
    }

    /// Adds a function target and updates its owning struct target when applicable.
    fn push_function_target(&mut self, function_target: FunctionTarget<'tcx>) {
        self.function_targets.push(function_target.clone());

        if let Some(struct_def_id) = function_target.owner_struct_def_id {
            self.struct_targets
                .entry(struct_def_id)
                .or_insert_with(|| StructTarget {
                    def_id: struct_def_id,
                    invariants: get_struct_invariants_from_annotation(
                        self.tcx,
                        struct_def_id,
                        function_target.def_id,
                    ),
                    function_targets: Vec::new(),
                })
                .function_targets
                .push(function_target);
        }
    }

    fn crate_name_matches(&self, def_id: DefId) -> bool {
        match &self.config.crate_filter {
            None => true,
            Some(filter) => {
                let crate_name = self.tcx.crate_name(def_id.krate);
                if crate_name.as_str() == *filter {
                    return true;
                }
                if let Ok(pkg_name) = std::env::var("CARGO_PKG_NAME")
                    && pkg_name == *filter
                {
                    return true;
                }
                false
            }
        }
    }

    fn module_path_matches(&self, def_id: DefId) -> bool {
        let Some(ref filter) = self.config.module_filter else {
            return true;
        };
        let crate_name = self.tcx.crate_name(def_id.krate);
        let crate_prefix = format!("{}::", crate_name.as_str());
        let matches = |path: &str| {
            path == filter
                || path.starts_with(&format!("{filter}::"))
                || filter.strip_prefix(&crate_prefix).is_some_and(|inner| {
                    path == inner || path.starts_with(&format!("{inner}::"))
                })
                || path.strip_prefix(&crate_prefix).is_some_and(|inner| {
                    inner == filter || inner.starts_with(&format!("{filter}::"))
                })
        };
        matches(&self.tcx.def_path_str(def_id))
            || (matches!(self.tcx.def_kind(def_id), rustc_hir::def::DefKind::Impl { .. })
                && self.tcx.impl_opt_trait_ref(def_id).is_some_and(|trait_ref| {
                    matches(&self.tcx.def_path_str(trait_ref.skip_binder().def_id))
                }))
    }

    pub(crate) fn check_module_filter_result(&self) {
        if let Some(ref filter) = self.config.crate_filter
            && !self.crate_filter_matched
        {
            rap_warn!("[rapx::verify] --crate \"{filter}\" matched no targets");
        }
        if let Some(ref filter) = self.config.module_filter
            && !self.module_filter_matched
        {
            rap_warn!("[rapx::verify] --module \"{filter}\" matched no functions in the crate");
        }
    }
}

impl<'tcx> Visitor<'tcx> for VerifyTargetCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    /// Collect obligations from `Send`, `Sync`, and other unsafe trait impls.
    ///
    /// Targeted mode requires `#[rapx::verify]` on the impl block. Scan mode
    /// visits all matching impl blocks in the current crate.
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        if let ItemKind::Impl(rustc_hir::Impl { of_trait, .. }) = &item.kind
            && of_trait.is_some()
        {
            if matches!(self.config.mode, VerifyMode::Targeted)
                && !has_rapx_verify_attr(self.tcx, item.owner_id.def_id)
            {
                rustc_hir::intravisit::walk_item(self, item);
                return;
            }

            let impl_def_id = item.owner_id.to_def_id();

            if !self.crate_name_matches(impl_def_id) {
                rustc_hir::intravisit::walk_item(self, item);
                return;
            }
            self.crate_filter_matched = true;

            if !self.module_path_matches(impl_def_id) {
                rustc_hir::intravisit::walk_item(self, item);
                return;
            }
            self.module_filter_matched = true;

            let trait_ref = { self.tcx.impl_opt_trait_ref(impl_def_id) };

            if let Some(trait_ref) = trait_ref {
                let trait_def_id = trait_ref.skip_binder().def_id;

                let self_ty_def_id = resolve_impl_self_ty_def_id(item);

                if let Some(kind) = marker_trait_kind(self.tcx, trait_def_id) {
                    let obligations =
                        build_marker_trait_obligations(self.tcx, self_ty_def_id, kind);
                    self.trait_targets.push(TraitEnsurance {
                        def_id: trait_def_id,
                        impl_def_id,
                        self_ty_def_id,
                        kind: TraitEnsuranceKind::Marker(kind, obligations),
                    });
                } else if is_trait_unsafe(self.tcx, trait_def_id) {
                    let ensures = get_trait_contracts_from_annotation(self.tcx, trait_def_id);

                    self.trait_targets.push(TraitEnsurance {
                        def_id: trait_def_id,
                        impl_def_id,
                        self_ty_def_id,
                        kind: TraitEnsuranceKind::Unsafe(ensures),
                    });
                }
            }
        }

        rustc_hir::intravisit::walk_item(self, item);
    }

    /// Collect verification targets from a function body.
    ///
    /// Targeted mode requires `#[rapx::verify]`. Scan mode first checks HIR
    /// for unsafe operations, struct invariants, or trait obligations before
    /// building the MIR target.
    fn visit_fn(
        &mut self,
        _: FnKind<'tcx>,
        _: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if matches!(self.config.mode, VerifyMode::Targeted) && !has_rapx_verify_attr(self.tcx, id) {
            return;
        }

        let def_id = id.to_def_id();

        if let rustc_hir::def::DefKind::Fn = self.tcx.def_kind(def_id) {
            let fn_sig = self.tcx.fn_sig(def_id).skip_binder();
            if matches!(
                fn_sig.output().skip_binder().kind(),
                rustc_type_ir::TyKind::Never
            ) {
                return;
            }
        }

        if !matches!(self.config.mode, VerifyMode::Targeted)
            && !hir_contains_unsafe(self.tcx, body_id)
            && !function_has_rapx_struct_invariant(self.tcx, def_id)
            && !function_has_trait_ensurance(self.tcx, def_id)
        {
            return;
        }

        if !self.crate_name_matches(def_id) {
            return;
        }
        self.crate_filter_matched = true;

        if !self.module_path_matches(def_id) {
            return;
        }
        self.module_filter_matched = true;

        let function_targets = self.build_function_targets(def_id);

        match self.config.mode {
            VerifyMode::Targeted => {}
            VerifyMode::Scan => {
                if let Some(first) = function_targets.first()
                    && first.checkpoints.is_empty()
                    && first.raw_ptr_deref_checks.is_empty()
                    && first.static_mut_checks.is_empty()
                {
                    if !first.invariants.is_empty() {
                        if self.config.skip_invariant {
                            return;
                        }
                    } else {
                        let root = crate::analysis::safety_flow::root::scan_mir(self.tcx, def_id);
                        if root.is_none() {
                            return;
                        }
                    }
                }
            }
        }

        for function_target in function_targets {
            self.push_function_target(function_target);
        }
    }
}

/// Analysis pass that lists the collected verification targets and contracts.
///
/// The collector applies the selected mode and filters; this pass prints the
/// resulting functions, structs, trait impls, and their obligations.
pub(crate) struct PrepareTargets<'tcx> {
    tcx: TyCtxt<'tcx>,
    config: Rc<VerifyConfig>,
}

impl<'tcx> Analysis for PrepareTargets<'tcx> {
    fn run(&mut self) {
        let collector = VerifyTargetCollector::collect_all(self.tcx, Rc::clone(&self.config));

        let free_targets: Vec<_> = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_none())
            .collect();
        for target in &free_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_info!("============================================================");
            rap_info!(
                "[rapx::verify] prepare targets for free function: {}",
                target_path
            );
            rap_info!("============================================================");
            self.log_free_function_unsafe_callees(target);
            rap_info!("");
        }

        let mut struct_ids: Vec<_> = collector.struct_targets.keys().copied().collect();
        struct_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for struct_def_id in struct_ids {
            let Some(struct_target) = collector.struct_targets.get(&struct_def_id) else {
                continue;
            };
            let struct_path = self.tcx.def_path_str(struct_target.def_id);

            rap_info!("============================================================");
            rap_info!("[rapx::verify] prepare targets for struct: {}", struct_path);
            rap_info!("============================================================");

            self.log_struct_invariants(struct_target);

            for target in &struct_target.function_targets {
                self.log_method_target(target);
            }
        }

        let mut trait_targets: Vec<_> = collector.trait_targets.iter().collect();
        trait_targets.sort_by_key(|t| self.tcx.def_path_str(t.def_id));

        for trait_target in trait_targets {
            let trait_path = self.tcx.def_path_str(trait_target.def_id);

            match &trait_target.kind {
                TraitEnsuranceKind::Unsafe(_) => {
                    rap_info!("============================================================");
                    rap_info!(
                        "[rapx::verify] prepare targets for unsafe trait: {}",
                        trait_path
                    );
                    rap_info!("============================================================");

                    self.log_trait_ensurance(trait_target);
                }
                TraitEnsuranceKind::Marker(kind, obligations) => {
                    let name = match kind {
                        MarkerTraitKind::Send => "Send",
                        MarkerTraitKind::Sync => "Sync",
                    };
                    rap_info!("============================================================");
                    rap_info!("[rapx::verify] prepare targets for marker trait: {}", name);
                    rap_info!("============================================================");

                    self.log_marker_trait(trait_target, obligations);
                }
            }

            rap_info!("");
        }

        let total_free = free_targets.len();
        let total_method = collector
            .function_targets
            .iter()
            .filter(|target| target.owner_struct_def_id.is_some())
            .count();
        let total_struct = collector.struct_targets.len();
        let total_trait = collector.trait_targets.len();

        rap_info!("============================================================");
        rap_info!(
            "[rapx::verify] total: {} free function(s), {} method(s), {} struct(s), {} trait(s)",
            total_free,
            total_method,
            total_struct,
            total_trait
        );
        rap_info!("============================================================");
    }
}

impl<'tcx> PrepareTargets<'tcx> {
    pub(crate) fn new(tcx: TyCtxt<'tcx>, config: Rc<VerifyConfig>) -> Self {
        Self { tcx, config }
    }

    fn log_struct_invariants(&self, struct_target: &StructTarget<'tcx>) {
        if struct_target.invariants.is_empty() {
            rap_info!("  struct invariants: <none>");
        } else {
            rap_info!("  struct invariants:");
            for property in
                crate::verify::display::dedup_compound_props(struct_target.invariants.iter())
            {
                rap_info!(
                    "    - {}",
                    property.display_for_report(self.tcx, Some(struct_target.def_id), None,)
                );
            }
        }
    }

    fn log_trait_ensurance(&self, trait_target: &TraitEnsurance<'tcx>) {
        if let Some(self_ty) = trait_target.self_ty_def_id {
            rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
        } else {
            rap_info!("  impl: {}", self.tcx.def_path_str(trait_target.impl_def_id));
        }
        let TraitEnsuranceKind::Unsafe(ensures) = &trait_target.kind else {
            return;
        };
        if ensures.is_empty() {
            rap_info!("  ensures: <none>");
        } else {
            rap_info!("  ensures (implementor must satisfy):");
            for (method_name, contracts) in ensures {
                rap_info!("    fn {}:", method_name);
                for property in crate::verify::display::dedup_compound_props(contracts.iter()) {
                    let (call, _meaning) = crate::verify::display::fmt_contract_expanded(
                        self.tcx,
                        property,
                        trait_target.self_ty_def_id,
                        None,
                    );
                    rap_info!("      - {call}");
                }
            }
        }
    }

    fn log_marker_trait(
        &self,
        trait_target: &TraitEnsurance<'tcx>,
        obligations: &[Property<'tcx>],
    ) {
        if let Some(self_ty) = trait_target.self_ty_def_id {
            rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
        }
        if obligations.is_empty() {
            rap_info!("  obligations: <none>");
        } else {
            rap_info!("  obligations:");
            for property in obligations {
                let (call, _meaning) = crate::verify::display::fmt_contract_expanded(
                    self.tcx,
                    property,
                    trait_target.self_ty_def_id,
                    None,
                );
                rap_info!("    - {call}");
            }
        }
    }

    fn log_method_target(&self, target: &FunctionTarget<'tcx>) {
        let name = short_fn_name(self.tcx, target.def_id);
        let dashes = 62usize.saturating_sub(10 + name.len());
        rap_info!("  --- method: {name} {}", "-".repeat(dashes));

        let return_blocks = collect_return_block_indices(self.tcx, target.def_id);
        rap_info!(
            "      return checkpoints: {} block(s) {:?}",
            return_blocks.len(),
            return_blocks
                .iter()
                .map(|bb| bb.as_usize())
                .collect::<Vec<_>>()
        );

        let path_map = self.build_checkpoint_path_map(target);
        self.log_unsafe_callees_and_contracts(target, &path_map);
    }

    fn log_free_function_unsafe_callees(&self, target: &FunctionTarget<'tcx>) {
        let path_map = self.build_checkpoint_path_map(target);
        self.log_unsafe_callees_and_contracts(target, &path_map);
    }

    fn log_unsafe_callees_and_contracts(
        &self,
        target: &FunctionTarget<'tcx>,
        path_map: &FxHashMap<DefId, Vec<(usize, Vec<String>)>>,
    ) {
        if target.callee_requires.is_empty() {
            rap_info!("      unsafe checkpoints: <none>");
            return;
        }

        let mut unsafe_callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        unsafe_callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for unsafe_callee_def_id in unsafe_callee_ids {
            let fn_sig = self.tcx.fn_sig(unsafe_callee_def_id).skip_binder();
            let unsafe_callee_path = self.tcx.def_path_str(unsafe_callee_def_id);
            let inputs: Vec<String> = fn_sig
                .inputs()
                .skip_binder()
                .iter()
                .map(|ty| format!("{}", ty))
                .collect();
            let output = format!("{}", fn_sig.output().skip_binder());
            rap_info!(
                "      unsafe callee: {}({}) -> {}",
                unsafe_callee_path,
                inputs.join(", "),
                output,
            );

            if let Some(requires) = target.callee_requires.get(&unsafe_callee_def_id) {
                if requires.is_empty() {
                    rap_info!("        safety contracts: <none>");
                } else {
                    rap_info!("        safety contracts:");
                    for property in crate::verify::display::dedup_compound_props(requires.iter()) {
                        rap_info!(
                            "          - {}",
                            property.display_for_report(
                                self.tcx,
                                target.owner_struct_def_id,
                                Some(unsafe_callee_def_id),
                            )
                        );
                    }
                }
            }

            if let Some(path_entries) = path_map.get(&unsafe_callee_def_id) {
                for (_block_idx, path_strings) in path_entries {
                    if path_strings.is_empty() {
                        rap_info!("        path: <none>");
                    } else {
                        for desc in path_strings {
                            rap_info!("        path: shortest path: {desc}");
                        }
                    }
                }
            }
        }
    }

    fn build_checkpoint_path_map(
        &self,
        target: &FunctionTarget<'tcx>,
    ) -> FxHashMap<DefId, Vec<(usize, Vec<String>)>> {
        let mut path_map: FxHashMap<DefId, Vec<(usize, Vec<String>)>> = FxHashMap::default();

        if target.checkpoints.is_empty() {
            return path_map;
        }

        let tree = PathExtractor::new_with_body(self.tcx, Rc::clone(&self.config), target.def_id, 0, target.body)
            .with_callee_bodies(target.callee_bodies.clone())
            .run();

        for checkpoint in &target.checkpoints {
            if let Some(callee_def_id) = checkpoint.callee {
                let block_idx = checkpoint.block.as_usize();
                let mut path_strings: Vec<String> = Vec::new();
                let _ = tree.walk_prefixes(
                    checkpoint.block.as_usize(),
                    &mut |prefix: &[usize]| -> bool {
                        let desc = prefix
                            .iter()
                            .map(usize::to_string)
                            .collect::<Vec<_>>()
                            .join(" -> ");
                        path_strings.push(desc);
                        true
                    },
                );

                path_map
                    .entry(callee_def_id)
                    .or_default()
                    .push((block_idx, path_strings));
            }
        }

        path_map
    }
}

/// Collects method `ensures` from trait annotations or the bundled std trait
/// contracts, grouped by method name.
fn get_trait_contracts_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
) -> Vec<(String, FnContracts<'tcx>)> {
    let mut ensures: Vec<(String, FnContracts<'tcx>)> = Vec::new();
    for trait_item in tcx.associated_items(trait_def_id).in_definition_order() {
        let trait_item_def_id = trait_item.def_id;
        let method_name = tcx.def_path_str(trait_item_def_id);
        let method_ensures = get_trait_method_ensures(tcx, trait_item_def_id);

        if !method_ensures.is_empty() {
            ensures.push((method_name, method_ensures));
        }
    }

    ensures
}

fn is_drop_impl(tcx: TyCtxt<'_>, fn_did: DefId) -> bool {
    let Some(impl_id) = tcx.trait_impl_of_assoc(fn_did) else {
        return false;
    };
    let trait_did = tcx.impl_trait_id(impl_id);
    lang_api::matches(tcx, trait_did, LangItem::Drop)
}
