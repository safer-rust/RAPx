//! Discovery of verification targets and their contract obligations.
//!
//! `VerifyTargetCollector` walks the crate's HIR (in `targeted` or `scan`
//! mode), and for each candidate assembles a [`FunctionTarget`]: unsafe
//! call-site checkpoints with per-callee preconditions, raw-pointer/static-mut
//! synthetic checkpoints, struct invariants, and std type invariants.

use crate::analysis::Analysis;
use crate::analysis::safety_flow::root::{
    function_has_struct_invariant, function_has_trait_ensurance, hir_contains_unsafe,
};
use crate::cli::VerifyMode;
use crate::compat::FxHashMap;
use crate::def_ids::lang_api::{self, LangItem};
use crate::helpers::name::short_fn_name;
use crate::verify::checkpoint::{collect_raw_ptr_deref_info, collect_static_mut_access_info};
#[cfg(rapx_has_attr_ir)]
use rustc_attr_ir::Attribute;
#[cfg(not(rapx_has_attr_ir))]
use rustc_hir::Attribute;
use rustc_hir::{
    BodyId, FnDecl, ItemKind,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::{
    hir::nested_filter,
    mir::{Body, TerminatorKind},
    ty::{self, EarlyBinder, Instance, InstanceKind, Ty, TyCtxt, TypingEnv},
};
use rustc_span::{Span, Symbol};
use std::collections::{HashMap, HashSet, VecDeque};

use super::{
    contract::{
        ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind,
        attr::parse_rapx_attr,
    },
    path::PathExtractor,
    type_invariants::build_type_invariants_from_params,
};
use crate::helpers::fn_info::get_adt_def_id_by_adt_method;
use crate::helpers::mir_utils::{
    collect_return_block_indices, has_rapx_verify_attr, is_std_crate_def_id, is_trait_unsafe,
    resolve_impl_self_ty_def_id,
};
use crate::verify::checkpoint::{Checkpoint, CheckpointKind, collect_unsafe_callsites};

/// A list of parsed `requires` contracts.
pub(crate) type FnContracts<'tcx> = Vec<Property<'tcx>>;

/// A list of parsed struct invariants.
pub(crate) type StructInvariants<'tcx> = Vec<Property<'tcx>>;
pub(crate) type CalleeBodies<'tcx> = FxHashMap<DefId, &'tcx Body<'tcx>>;

/// Collected verification data for a single function under analysis.
///
/// `FunctionTarget` is the complete **problem statement** for one function: it
/// records every unsafe operation found in the function's MIR body, the safety
/// contracts that each operation demands, and any contracts or invariants that
/// serves as entry assumptions or structural guarantees.
///
/// # How it is built
///
/// [`VerifyTargetCollector::build_function_target`] assembles a `FunctionTarget`
/// in one pass over the MIR body:
///
/// 1. Unsafe checkpoints are collected via [`collect_unsafe_callsites`].
/// 2. Each unique callee `DefId` gets its `#[rapx::requires]` contracts parsed
///    (with fallback to bundled JSON contracts for standard-library callees).
/// 3. Raw pointer dereferences are detected and converted into synthetic
///    (pseudo-checkpoint, `[ValidPtr, Align, (Typed)]`) pairs.
/// 4. The caller's own `#[rapx::requires]` contracts become entry assumptions.
/// 5. If the function is a method on a struct, struct-level `#[rapx::invariant]`
///    and `#[rapx::requires]` annotations are collected.
///
/// # Role in the pipeline
///
/// The [`VerifyDriver`](super::driver::VerifyDriver) consumes a `FunctionTarget`
/// to route each unsafe operation to the verifier engine along reachability paths
/// extracted from the MIR CFG.  The target is the primary data carrier between
/// the *target collection* stage and the *path extraction / verification* stage.
#[derive(Clone, Debug)]
pub(crate) struct FunctionTarget<'tcx> {
    /// The function being verified.
    pub def_id: DefId,

    /// Instantiated MIR shared by path extraction, slicing, and symbolic replay.
    pub body: Option<&'tcx rustc_middle::mir::Body<'tcx>>,
    /// Unique direct generic callees instantiated in the root's parameter environment.
    pub callee_bodies: CalleeBodies<'tcx>,

    /// Owning struct when this function is an associated method (e.g.
    /// `impl MyStruct { fn foo(...) }`).  `None` for free functions.
    ///
    /// Used to associate struct invariants and to group method-level
    /// verification results under the owning struct in diagnostic output.
    pub owner_struct_def_id: Option<DefId>,

    /// All unsafe checkpoints found in this function's MIR.
    ///
    /// Each [`Checkpoint`] records its MIR location, operands, and callee when present.
    pub checkpoints: Vec<Checkpoint<'tcx>>,

    /// Safety contracts demanded by each unique unsafe callee reachable from
    /// this function, keyed by callee `DefId`.
    ///
    /// Contracts are sourced from `#[rapx::requires(...)]` annotations on the
    /// callee (inline mode) or from a bundled JSON contract database for
    /// standard-library functions.  Each value is a `Vec<Property>` — the
    /// concrete safety requirements the callee expects its caller to satisfy.
    pub callee_requires: HashMap<DefId, FnContracts<'tcx>>,

    /// Safety contracts that the **caller itself** requires as entry
    /// assumptions, parsed from `#[rapx::requires(...)]` on this function.
    ///
    /// During verification the engine prepends these properties as *facts* that
    /// are assumed to hold at function entry, constraining the backward
    /// data-dependency analysis and forward simulation.
    pub caller_requires: FnContracts<'tcx>,

    /// Struct invariants that methods of the owning struct must maintain.
    ///
    /// Collected from `#[rapx::invariant(...)]` / `#[rapx::requires(...)]`
    /// annotations on the struct definition.  Checked at constructor return
    /// blocks and at all path endpoints for non-constructor methods.
    pub struct_invariants: Vec<Property<'tcx>>,

    /// Built-in type invariants (e.g. the synthesized `NonNull`/`Init`/`Alive`
    /// slice invariant for `&[T]`/`&mut [T]` receivers and returns).
    ///
    /// These are assumed at entry (via `caller_requires`) and checked at exit
    /// when the body has a checkable unsafe operation and the value is live.
    pub type_invariants: Vec<Property<'tcx>>,

    /// Raw pointer dereference checks with their required safety properties.
    ///
    /// Each entry is a `(Checkpoint, Vec<Property>)` pair where the `Checkpoint`
    /// carries a synthetic dummy `DefId` (so the path extractor can treat
    /// dereferences uniformly with checkpoints) and the properties encode the
    /// pointer-validity requirements: always [`Allocated`](PropertyKind::Allocated),
    /// [`InBound`](PropertyKind::InBound), and [`Align`](PropertyKind::Align);
    /// additionally [`Typed`](PropertyKind::Typed) when the dereference is a read.
    pub raw_ptr_deref_checks: Vec<(Checkpoint<'tcx>, Vec<Property<'tcx>>)>,

    /// Static mut access checks with their required safety properties.
    ///
    /// Each entry is a `(Checkpoint, Vec<Property>)` pair following the same
    /// pattern as [`raw_ptr_deref_checks`](Self::raw_ptr_deref_checks).  The
    /// properties are [`Allocated`](PropertyKind::Allocated),
    /// [`InBound`](PropertyKind::InBound), [`Align`](PropertyKind::Align),
    /// and [`Init`](PropertyKind::Init)
    /// (conservatively checked for both reads and writes).
    pub static_mut_checks: Vec<(Checkpoint<'tcx>, Vec<Property<'tcx>>)>,
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
            .chain(
                self.raw_ptr_deref_checks
                    .iter()
                    .map(|(checkpoint, _)| checkpoint),
            )
            .chain(
                self.static_mut_checks
                    .iter()
                    .map(|(checkpoint, _)| checkpoint),
            )
    }

    pub(crate) fn properties_for_callsite<'a>(
        &'a self,
        checkpoint: &'a Checkpoint<'tcx>,
    ) -> &'a [Property<'tcx>] {
        let loc = checkpoint.location();
        match checkpoint.kind {
            crate::verify::checkpoint::CheckpointKind::RawPtrDeref => self
                .raw_ptr_deref_checks
                .iter()
                .find(|(candidate, _)| {
                    candidate.location() == loc
                        && candidate.statement_index == checkpoint.statement_index
                })
                .map(|(_, properties)| properties.as_slice())
                .unwrap_or(&[]),
            crate::verify::checkpoint::CheckpointKind::StaticMutAccess => self
                .static_mut_checks
                .iter()
                .find(|(candidate, _)| {
                    candidate.location() == loc && candidate.site_ordinal == checkpoint.site_ordinal
                })
                .map(|(_, properties)| properties.as_slice())
                .unwrap_or(&[]),
            crate::verify::checkpoint::CheckpointKind::UnsafeCall => checkpoint
                .callee
                .and_then(|callee| self.callee_requires.get(&callee))
                .map(Vec::as_slice)
                .unwrap_or(&[]),
            crate::verify::checkpoint::CheckpointKind::CopyNonOverlapping => &checkpoint.requires,
        }
    }
}

/// Collected verification data for a struct that owns methods marked with `#[rapx::verify]`.
pub(crate) struct StructTarget<'tcx> {
    /// Struct that owns one or more methods selected as targets to verify.
    pub def_id: DefId,
    /// Parsed `invariant` contracts attached to the struct.
    pub invariants: StructInvariants<'tcx>,
    /// Methods of this struct selected as targets to verify.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
}

/// Collected verification data for an `impl unsafe Trait for Type` block.
///
/// Covers two cases, distinguished by whether the trait has methods:
/// - marker traits (`Send`/`Sync`) carry *type-level* obligations, and
/// - unsafe traits with methods carry *method-level* `ensures` contracts.
#[derive(Clone)]
pub(crate) struct TraitEnsurance<'tcx> {
    /// The trait being implemented.
    pub def_id: DefId,
    /// The `impl ... for Type` block's DefId (carries the impl's generic bounds,
    /// e.g. `T: Send`).
    pub impl_def_id: DefId,
    /// The concrete type that implements the trait (e.g. `SomeStruct`).
    pub self_ty_def_id: Option<DefId>,
    /// The obligations to verify, keyed by whether the trait has methods.
    pub kind: TraitEnsuranceKind<'tcx>,
}

/// What a [`TraitEnsurance`] must verify.
#[derive(Clone)]
pub(crate) enum TraitEnsuranceKind<'tcx> {
    /// A marker trait (`Send`/`Sync`, no methods): type-level obligations
    /// generated from the bundled `std-trait.json` template.
    Marker(MarkerTraitKind, Vec<Property<'tcx>>),
    /// An unsafe trait with methods: `ensures` contracts grouped by method name.
    Unsafe(Vec<(String, FnContracts<'tcx>)>),
}

/// Which marker trait an `unsafe impl` is claiming safety for.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum MarkerTraitKind {
    Send,
    Sync,
}

/// Trace a call-site argument operand back to the enclosing callee's parameter
/// index (0-based), following direct `Copy`/`Move` assignment chains. Returns
/// `None` for constants, field projections, call results, or values that do not
/// trace to a parameter (those references cannot be restated on the enclosing
/// callee).
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
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return Some(cidx - 1);
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != current || !dest.projection.is_empty() {
                    continue;
                }
                let source = match rvalue {
                    rustc_middle::mir::Rvalue::Use(
                        rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p),
                        ..,
                    ) => p.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
            }
        }
    }
    None
}

/// Rewrite a contract's argument references (`PlaceBase::Arg(i)`) onto the
/// enclosing callee's parameters using the call-site argument list. This rebinds
/// a leaf callee's contract (e.g. `ptr::write`'s `ValidPtr(self, T, 1)`) to the
/// wrapper callee's arguments (e.g. `maybe_init_slot`'s `ptr`).
///
/// Returns `false` when a referenced argument cannot be traced to a parameter
/// (a constant, a field projection, a temporary, or a call result). Such a
/// contract expresses an internal invariant of the leaf callee and cannot be
/// restated as a precondition on this callee's parameters, so it is dropped.
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
            if let Some(place) = &mut atom.for_each
                && !rebind_place(place, args, body)
            {
                ok = false;
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
    place: &mut ContractPlace<'tcx>,
    args: &[rustc_middle::mir::Operand<'tcx>],
    body: &rustc_middle::mir::Body<'tcx>,
) -> bool {
    // A contract references the leaf callee's arguments either as a 0-based
    // `Arg(i)` (std JSON contracts) or as a MIR `Local(k)` (inline
    // `#[rapx::requires]`, where local 1..=arg_count are the parameters). Map
    // both onto the argument index, then trace that argument back to this
    // callee's parameter. `Local(0)`/`Return` name the return value and cannot
    // be restated as a precondition.
    let arg_idx = match place.base {
        PlaceBase::Arg(i) => Some(i),
        PlaceBase::Local(k) if k >= 1 => Some(k - 1),
        _ => return false,
    };
    match arg_idx
        .and_then(|i| args.get(i))
        .and_then(|op| call_arg_to_outer_param(op, body))
    {
        Some(outer) => {
            place.base = PlaceBase::Arg(outer);
            true
        }
        None => false,
    }
}

/// Follow an unsafe callee's call chain to find inherited safety contracts.
///
/// When an unsafe callee (e.g. B) lacks its own contracts, look into its MIR
/// body for the unsafe callees it calls (e.g. C, D).  If one of those has
/// contracts (e.g. D), inherit them.  The chain `A -> B -> C -> D` means A's
/// checkpoint on B is verified using D's contracts.
///
/// `visited` prevents infinite recursion on mutually-recursive functions.
fn resolve_chain_contracts<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    visited: &mut HashSet<DefId>,
) -> FnContracts<'tcx> {
    if !visited.insert(callee_def_id) {
        return Vec::new();
    }

    if !tcx.is_mir_available(callee_def_id) {
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
                reqs = super::contract::json::query_json_contracts(tcx, sub_def_id);
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
            #[cfg(rapx_ge_99)]
            let callee_args = callee_args.skip_binder();
            reqs.retain_mut(|req| rebind_property_to_args(req, &arg_operands, &callee_args, body));

            contracts.extend(reqs);
        }
    }

    contracts
}

/// Visitor that collects targets annotated with `#[rapx::verify]`.
pub(crate) struct VerifyTargetCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: VerifyMode,
    skip_invariant: bool,
    crate_filter: Option<String>,
    crate_filter_matched: bool,
    module_filter: Option<String>,
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
    /// Collect all verification targets across the current crate and optionally
    /// external crates (when `crate_filter` is set).
    pub(crate) fn collect_all(
        tcx: TyCtxt<'tcx>,
        mode: VerifyMode,
        skip_invariant: bool,
        crate_filter: Option<String>,
        module_filter: Option<String>,
    ) -> Self {
        let mut collector = Self::new(
            tcx,
            mode,
            skip_invariant,
            crate_filter.clone(),
            module_filter,
        );
        tcx.hir_visit_all_item_likes_in_crate(&mut collector);
        if crate_filter.is_some() {
            collector.collect_extern_crate_targets();
        }
        collector.check_module_filter_result();
        collector
    }

    /// Creates a new collector for the current type context.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        mode: VerifyMode,
        skip_invariant: bool,
        crate_filter: Option<String>,
        module_filter: Option<String>,
    ) -> Self {
        VerifyTargetCollector {
            tcx,
            mode,
            skip_invariant,
            crate_filter,
            crate_filter_matched: false,
            module_filter,
            module_filter_matched: false,
            function_targets: Vec::new(),
            struct_targets: HashMap::new(),
            trait_targets: Vec::new(),
            fn_contract_cache: HashMap::new(),
        }
    }

    /// Returns (and caches) the contracts for an unsafe callee.
    ///
    /// Contracts are resolved with the following priority:
    /// 1. Inline RAPx annotations attached to the callee.
    /// 2. If the callee is a trait method impl without its own annotations,
    ///    fall back to the trait method's `#[rapx::requires(...)]`.
    /// 3. If no annotations are found and the callee belongs to the standard
    ///    library, fall back to the bundled JSON contract database.
    ///
    /// Results are memoized in `fn_contract_cache` to avoid recomputation.
    ///
    /// `follow_chain` controls whether an otherwise-unannotated callee's
    /// contract is resolved by walking its call chain (e.g. an unsafe wrapper
    /// that calls `ptr::write`). It must be `true` when resolving the contracts
    /// a *caller* has to prove at a call site (`callee_requires`), and `false`
    /// when resolving a function's own assumed preconditions (`caller_requires`)
    /// — those must not inherit contracts from the function's internal calls.
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
                    requires = super::contract::json::query_json_contracts(self.tcx, callee_def_id);
                }

                if requires.is_empty() && follow_chain {
                    let mut visited = HashSet::new();
                    requires = resolve_chain_contracts(self.tcx, callee_def_id, &mut visited);
                    if requires.is_empty() {
                        // Safe callees, intrinsics, and verified bodies need no JSON contract.
                        let is_intrinsic =
                            crate::def_ids::intrinsic_api::is_intrinsic(self.tcx, callee_def_id);
                        let has_json_entry = is_std
                            && super::contract::json::get_std_contracts_from_json(
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
                            let path = crate::helpers::name::get_cleaned_def_path_name(
                                self.tcx,
                                callee_def_id,
                            );
                            rap_warn!("no safety contracts found for callee \"{path}\"");
                        }
                    } else {
                        let path = crate::helpers::name::get_cleaned_def_path_name(
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
                    // An empty JSON entry or verified body may have no `requires`.
                    let has_json_entry = is_std
                        && super::contract::json::get_std_contracts_from_json(
                            self.tcx,
                            callee_def_id,
                        )
                        .is_some();
                    let is_verify_target = callee_def_id
                        .as_local()
                        .is_some_and(|id| has_rapx_verify_attr(self.tcx, id));
                    if !has_json_entry && !is_verify_target {
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
            .filter(|inst| !crate::helpers::mir_utils::has_unresolved_const_args(self.tcx, def_id, inst.args))
            .and_then(|inst| {
                let mir = self.tcx.optimized_mir(def_id);
                inst.try_instantiate_mir_and_normalize_erasing_regions(
                    self.tcx,
                    rustc_middle::ty::TypingEnv::post_analysis(self.tcx, def_id),
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
                let Some(callee) = crate::helpers::mir_utils::dep_callee_resolved_def_id(
                    self.tcx, def_id, func,
                ) else {
                    continue;
                };
                if !self.tcx.is_mir_available(callee)
                    || !crate::helpers::mir_utils::has_direct_unmodeled_generic_call(self.tcx, callee)
                {
                    continue;
                }
                let Some(inst) = crate::helpers::mir_utils::resolve_callee_instance(
                    self.tcx, def_id, func,
                ) else {
                    continue;
                };
                if !matches!(inst.def, InstanceKind::Item(_)) || inst.def_id() != callee {
                    continue;
                }
                if crate::helpers::mir_utils::has_unresolved_const_args(self.tcx, def_id, inst.args) {
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
                    TypingEnv::post_analysis(self.tcx, def_id),
                    EarlyBinder::bind(self.tcx, mir),
                ) else {
                    continue;
                };
                callee_bodies.insert(callee, &*self.tcx.arena.alloc(instantiated));
            }
        }
        let mut checkpoints = collect_unsafe_callsites(self.tcx, def_id);
        for checkpoint in checkpoints
            .iter_mut()
            .filter(|checkpoint| checkpoint.kind == CheckpointKind::CopyNonOverlapping)
        {
            checkpoint.requires = checkpoint
                .callee
                .map(|callee| {
                    super::contract::json::query_json_contracts_at_path(
                        self.tcx,
                        callee,
                        "core::intrinsics::copy_nonoverlapping",
                    )
                })
                .filter(|requires| !requires.is_empty())
                .unwrap_or_else(|| vec![Property::new_atom(PropertyKind::Unknown, Vec::new())]);
        }
        let unsafe_callees: HashSet<_> = checkpoints
            .iter()
            .filter(|checkpoint| checkpoint.kind == CheckpointKind::UnsafeCall)
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

        let raw_ptr_deref_checks = build_raw_ptr_deref_checks(self.tcx, def_id);
        let static_mut_checks = build_static_mut_checks(self.tcx, def_id);

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

        // Type invariants for parameters and returns are entry facts.
        let type_invariants = build_type_invariants_from_params(self.tcx, def_id);
        caller_requires.extend(type_invariants.clone());

        FunctionTarget {
            def_id,
            body,
            callee_bodies,
            owner_struct_def_id,
            checkpoints,
            callee_requires,
            caller_requires,
            struct_invariants,
            type_invariants,
            raw_ptr_deref_checks,
            static_mut_checks,
        }
    }

    /// Build one target per monomorphized instance when `def_id` has an
    /// unmodeled generic trait call (monomorphization is the fallback for an
    /// opaque call with no summary), or a single non-generic target.
    fn build_function_targets(&mut self, def_id: DefId) -> Vec<FunctionTarget<'tcx>> {
        if !crate::helpers::mir_utils::has_unmodeled_generic_call(self.tcx, def_id) {
            return vec![self.build_function_target(def_id, None)];
        }
        let instances = crate::helpers::mir_utils::enumerate_mono_instances(
            self.tcx,
            def_id,
            crate::limit::trait_impl_limit(),
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

    /// Process MIR keys from non-local crates that match the `--crate` filter.
    ///
    /// `hir_visit_all_item_likes_in_crate` only visits the *local* crate, but
    /// in a workspace the target crate (e.g. `core`) may be compiled as a
    /// dependency of another crate (e.g. `std`).  This method iterates all
    /// crates' MIR bodies and collects targets from those matching the filter.
    fn collect_extern_crate_targets(&mut self) {
        let local_crate = rustc_hir::def_id::LOCAL_CRATE;

        for def_id in self.tcx.mir_keys(()) {
            let def_id = def_id.to_def_id();
            if def_id.krate == local_crate {
                continue; // already visited via the HIR visitor
            }
            if !self.crate_name_matches(def_id) {
                continue;
            }
            let def_kind = self.tcx.def_kind(def_id);
            if !matches!(
                def_kind,
                rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn
            ) {
                continue;
            }

            if matches!(self.mode, VerifyMode::Targeted) {
                continue;
            }

            self.crate_filter_matched = true;

            if !self.module_path_matches(def_id) {
                continue;
            }
            self.module_filter_matched = true;

            let function_targets = self.build_function_targets(def_id);
            for function_target in function_targets {
                self.push_function_target(function_target);
            }
        }
    }

    fn crate_name_matches(&self, def_id: DefId) -> bool {
        match self.crate_filter {
            None => true,
            Some(ref filter) => {
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
        let Some(ref filter) = self.module_filter else {
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
        if let Some(ref filter) = self.crate_filter
            && !self.crate_filter_matched
        {
            rap_warn!("[rapx::verify] --crate \"{filter}\" matched no targets");
        }
        if let Some(ref filter) = self.module_filter
            && !self.module_filter_matched
        {
            rap_warn!("[rapx::verify] --module \"{filter}\" matched no functions in the crate");
        }
    }
}

pub(crate) fn get_trait_method_requires<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
) -> FnContracts<'tcx> {
    let Some(assoc_item) = tcx.opt_associated_item(callee_def_id) else {
        return Vec::new();
    };
    let Some(trait_item_def_id) = assoc_item.trait_item_def_id() else {
        return Vec::new();
    };
    get_contract_from_annotation(tcx, trait_item_def_id)
}

impl<'tcx> Visitor<'tcx> for VerifyTargetCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    /// Detect `impl unsafe Trait for Type` blocks and record them as
    /// [`TraitEnsurance`] placeholders.
    ///
    /// In `targeted` mode, only `impl` blocks annotated with `#[rapx::verify]`
    /// are recorded.  In `scan` mode, all `unsafe trait` impls
    /// are recorded.
    fn visit_item(&mut self, item: &'tcx rustc_hir::Item<'tcx>) {
        if let ItemKind::Impl(rustc_hir::Impl { of_trait, .. }) = &item.kind
            && of_trait.is_some()
        {
            if matches!(self.mode, VerifyMode::Targeted)
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

    /// Visits each function body and records verification targets.
    ///
    /// In `targeted` mode, only functions annotated with `#[rapx::verify]` are collected.
    /// In `scan` mode, a HIR-level pre-filter (`contains_unsafe`
    /// and `function_has_struct_invariant`) avoids expensive MIR scanning for functions
    /// that have no unsafe content and no struct invariants.
    fn visit_fn(
        &mut self,
        _: FnKind<'tcx>,
        _: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if matches!(self.mode, VerifyMode::Targeted) && !has_rapx_verify_attr(self.tcx, id) {
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

        if !matches!(self.mode, VerifyMode::Targeted)
            && !hir_contains_unsafe(self.tcx, body_id)
            && !function_has_struct_invariant(self.tcx, def_id)
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

        match self.mode {
            VerifyMode::Targeted => {}
            VerifyMode::Scan => {
                if let Some(first) = function_targets.first()
                    && first.checkpoints.is_empty()
                    && first.raw_ptr_deref_checks.is_empty()
                    && first.static_mut_checks.is_empty()
                {
                    if !first.struct_invariants.is_empty() {
                        if self.skip_invariant {
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

/// Analysis pass that finds all verification targets.
///
/// In `targeted` mode, only functions annotated with `#[rapx::verify]` are listed.
/// In `scan` mode, all functions with unsafe callees or struct invariants are listed.
pub(crate) struct PrepareTargets<'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: VerifyMode,
    skip_invariant: bool,
    crate_filter: Option<String>,
    module_filter: Option<String>,
}

impl<'tcx> Analysis for PrepareTargets<'tcx> {
    fn run(&mut self) {
        let collector = VerifyTargetCollector::collect_all(
            self.tcx,
            self.mode,
            self.skip_invariant,
            self.crate_filter.clone(),
            self.module_filter.clone(),
        );

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
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        mode: VerifyMode,
        skip_invariant: bool,
        crate_filter: Option<String>,
        module_filter: Option<String>,
    ) -> Self {
        PrepareTargets {
            tcx,
            mode,
            skip_invariant,
            crate_filter,
            module_filter,
        }
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

        let tree = PathExtractor::new_with_body(self.tcx, target.def_id, 0, target.body)
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

fn is_rapx_named_attr(tcx: TyCtxt<'_>, attr: &Attribute, name: &str) -> bool {
    let name = Symbol::intern(name);
    crate::compat::attribute_path_matches(tcx, attr, &[Symbol::intern("rapx"), name])
        || crate::compat::attribute_path_matches(tcx, attr, &[name])
}

/// Resolve whether an `unsafe impl` is implementing the `Send`/`Sync` marker trait.
fn marker_trait_kind(tcx: TyCtxt<'_>, trait_def_id: DefId) -> Option<MarkerTraitKind> {
    if tcx.get_diagnostic_item(rustc_span::sym::Send) == Some(trait_def_id) {
        Some(MarkerTraitKind::Send)
    } else if tcx.get_diagnostic_item(rustc_span::sym::Sync) == Some(trait_def_id) {
        Some(MarkerTraitKind::Sync)
    } else {
        None
    }
}

/// Generate the type-level `ensures` obligations for a marker-trait impl from
/// the bundled `std-trait.json` template, substituting `ty:Self` with
/// the implementing type.
fn build_marker_trait_obligations<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty_def_id: Option<DefId>,
    trait_kind: MarkerTraitKind,
) -> Vec<Property<'tcx>> {
    let Some(self_ty_def_id) = self_ty_def_id else {
        return Vec::new();
    };
    let self_ty = tcx.type_of(self_ty_def_id).skip_binder();

    let trait_def_id = match trait_kind {
        MarkerTraitKind::Send => tcx.get_diagnostic_item(rustc_span::sym::Send),
        MarkerTraitKind::Sync => tcx.get_diagnostic_item(rustc_span::sym::Sync),
    };
    let Some(trait_def_id) = trait_def_id else {
        return Vec::new();
    };

    let templates = super::contract::json::query_trait_ensures(tcx, trait_def_id);
    let mut obligations = Vec::new();
    for entry in templates {
        if let Some(prop) = build_type_atom(tcx, self_ty_def_id, &entry, self_ty) {
            obligations.push(prop);
        }
    }
    obligations
}

/// Build a single type-level obligation from a `std-trait.json` entry,
/// substituting `ty:Self` with `self_ty`.  Supports the `any` disjunction and
/// falls back to named compound properties (`expand_compound`) for tags that are
/// not built-in primitives.
fn build_type_atom<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    entry: &super::contract::json::JsonProperty,
    self_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<Property<'tcx>> {
    if let Some(items) = &entry.any {
        let disjuncts: Vec<Property<'tcx>> = items
            .iter()
            .filter_map(|item| match item {
                super::contract::json::AnyItem::Single(e) => {
                    build_type_atom(tcx, def_id, e, self_ty)
                }
                super::contract::json::AnyItem::And(es) => {
                    let conjuncts: Vec<Property<'tcx>> = es
                        .iter()
                        .filter_map(|e| build_type_atom(tcx, def_id, e, self_ty))
                        .collect();
                    if conjuncts.is_empty() {
                        None
                    } else {
                        Some(Property::new_and(conjuncts))
                    }
                }
            })
            .collect();
        return if disjuncts.is_empty() {
            None
        } else {
            Some(Property::new_or(disjuncts))
        };
    }

    match entry.tag.as_str() {
        "ContainNoType" => {
            let mut args = vec![PropertyArg::Ty(self_ty)];
            args.extend(
                entry.args[1..]
                    .iter()
                    .map(|s| PropertyArg::Ident(s.strip_prefix("ty:").unwrap_or(s).to_string())),
            );
            Some(Property::new_atom(PropertyKind::ContainNoType, args))
        }
        "NoRawPtr" => Some(Property::new_atom(
            PropertyKind::NoRawPtr,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "NoInternalMut" => Some(Property::new_atom(
            PropertyKind::NoInternalMut,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "UniInternalMut" => Some(Property::new_atom(
            PropertyKind::UniInternalMut,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "AtomicUpdate" => Some(Property::new_atom(
            PropertyKind::AtomicUpdate,
            vec![PropertyArg::Ty(self_ty)],
        )),
        "RefSend" => Some(Property::new_atom(
            PropertyKind::RefSend,
            vec![PropertyArg::Ty(self_ty)],
        )),
        // Fall back to a named compound property (e.g. `TamedRawPtr` defined in
        // `std-compound-properties.rs`).  The `ty:Self` placeholder is normalized
        // to `Self` and resolved by the compound's `Ty` parameter; a `Ptr`
        // parameter not supplied by the JSON template is filled in from the
        // struct's own `Allocated`/`Owning` invariant field.
        _ => {
            let mut exprs: Vec<syn::Expr> = entry
                .args
                .iter()
                .filter_map(|s| {
                    let normalized = super::contract::json::normalize_json_contract_arg(s);
                    syn::parse_str::<syn::Expr>(&normalized).ok()
                })
                .collect();
            if exprs.len() != entry.args.len() {
                return None;
            }

            if let Some(spec) = super::contract::compound::find_compound(def_id.krate, &entry.tag) {
                for i in exprs.len()..spec.param_tys.len() {
                    if spec.param_tys.get(i).map(|s| s.as_str()) != Some("Ptr") {
                        return None;
                    }
                    let field = extract_tamed_field(tcx, def_id)?;
                    let Ok(e) = syn::parse_str::<syn::Expr>(&field) else {
                        return None;
                    };
                    exprs.push(e);
                }
            }

            match super::contract::compound::expand_compound(tcx, def_id, &entry.tag, &exprs) {
                Some(mut props) if !props.is_empty() => {
                    // A compound body expands into one property per conjunct, each
                    // tagged with the compound's origin.  Hoist that origin onto the
                    // combined node so the report shows `Name(args)` once instead of
                    // `And(Name, Name, Name)`.
                    let origin = props.first().and_then(|p| p.origin()).cloned();
                    for p in &mut props {
                        p.clear_origin();
                    }
                    let mut combined = Property::conjunction(props);
                    if let Some(o) = origin {
                        combined.set_origin(o.name, o.args, o.meaning);
                    }
                    Some(combined)
                }
                _ => None,
            }
        }
    }
}

/// The raw-pointer field name a struct declares via `#[rapx::invariant(Allocated(field))]`
/// or `#[rapx::invariant(Owning(field))]`, used to bind a `TamedRawPtr` compound's
/// `Ptr` parameter.
fn extract_tamed_field<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<String> {
    let invariants = get_struct_invariants_from_annotation(tcx, def_id, def_id);
    invariants
        .iter()
        .find(|p| {
            matches!(
                p.kind(),
                Some(PropertyKind::Allocated) | Some(PropertyKind::Owning)
            )
        })
        .and_then(|p| p.args().first())
        .and_then(|a| super::contract::place::field_name_from_arg(tcx, def_id, a))
}

fn collect_properties_from_named_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
    attr_name: &str,
) -> Vec<Property<'tcx>> {
    let mut results = Vec::new();

    for attr in attrs {
        if !is_rapx_named_attr(tcx, attr, attr_name) {
            continue;
        }

        let attr_str = crate::compat::attribute_to_string(tcx, attr);
        let parsed = match parse_rapx_attr(attr_str.as_str(), attr_name) {
            Ok(parsed) => parsed,
            Err(err) => {
                rap_error!(
                    "Failed to parse RAPx {} attr '{}': {}",
                    parse_error_label,
                    attr_str,
                    err
                );
                continue;
            }
        };

        let Some(property) = parsed else { continue };
        results.extend(
            Property::parse_list(tcx, property_def_id, property.tag.as_str(), &property.args)
                .into_iter()
                .map(move |mut p| {
                    p.apply_kind(property.kind.as_deref());
                    p
                }),
        );
    }

    results
}

/// Parses `requires` contracts from source-level RAPx annotations attached to a definition.
pub(crate) fn get_contract_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> FnContracts<'tcx> {
    // Prefer HIR-level attrs for local defs (tool attributes visible),
    // fall back to get_all_attrs for external defs.
    if let Some(local_def_id) = def_id.as_local() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let hir_attrs = tcx.hir_attrs(hir_id);
        return collect_properties_from_named_attrs(tcx, hir_attrs, def_id, "requires", "requires");
    }

    let attrs = crate::compat::get_all_attrs(tcx, def_id);
    collect_properties_from_named_attrs(tcx, attrs, def_id, "requires", "requires")
}

/// Parses struct invariants from source-level RAPx annotations attached to a struct definition.
pub(crate) fn get_struct_invariants_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    struct_def_id: DefId,
    context_def_id: DefId,
) -> StructInvariants<'tcx> {
    let Some(local_def_id) = struct_def_id.as_local() else {
        return Vec::new();
    };

    let item = tcx.hir_expect_item(local_def_id);
    if !matches!(item.kind, ItemKind::Struct(..)) {
        return Vec::new();
    }

    let mut invariants = collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, struct_def_id),
        context_def_id,
        "invariant",
        "requires",
    );
    invariants.extend(collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, struct_def_id),
        context_def_id,
        "invariant",
        "invariant",
    ));
    // A lifetime in a struct invariant (`Alive(ptr, 'a)`) names a lifetime on
    // the *struct*, so bind it here against the struct's own generics. Parsing
    // used `context_def_id` (the method), whose generics lack `'a`.
    for inv in &mut invariants {
        bind_alive_regions(tcx, struct_def_id, inv);
    }
    invariants
}

/// Resolve `Owning(self.field...)` invariants on a local returned struct to
/// field-index paths, without requiring a method `self` binding.
pub(crate) fn owning_field_paths_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    output: Ty<'tcx>,
) -> Vec<Vec<usize>> {
    let ty::Adt(adt, _) = output.kind() else {
        return Vec::new();
    };
    if !adt.did().is_local() || !adt.is_struct() {
        return Vec::new();
    }
    crate::compat::get_all_attrs(tcx, adt.did())
        .into_iter()
        .filter(|attr| is_rapx_named_attr(tcx, attr, "invariant"))
        .filter_map(|attr| {
            let text = crate::compat::attribute_to_string(tcx, attr);
            parse_rapx_attr(&text, "invariant").ok().flatten()
        })
        .filter(|property| property.tag == "Owning")
        .filter_map(|property| {
            let mut members = Vec::new();
            let mut expr = property.args.first()?;
            while let syn::Expr::Field(field) = expr {
                members.push(&field.member);
                expr = &field.base;
            }
            let syn::Expr::Path(root) = expr else { return None };
            if !root.path.is_ident("self") {
                return None;
            }
            let mut ty = output;
            let mut path = Vec::new();
            for member in members.into_iter().rev() {
                let ty::Adt(adt, args) = ty.kind() else { return None };
                let fields = &adt.non_enum_variant().fields;
                let index = match member {
                    syn::Member::Named(name) =>
                        fields.iter().position(|field| field.name.as_str() == name.to_string())?,
                    syn::Member::Unnamed(index) => index.index as usize,
                };
                let field = fields.iter().nth(index)?;
                path.push(index);
                ty = crate::helpers::mir_utils::field_ty(tcx, field, args);
            }
            Some(path)
        })
        .collect()
}

/// Bind `Alive(p, 'a)` region idents in a contract to `Region`s, resolving `'a`
/// against `def_id` (the item that declares `'a`: the struct for its
/// invariants, the function for its `requires`).
fn bind_alive_regions<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, property: &mut Property<'tcx>) {
    match property {
        Property::Atom(atom) => {
            if atom.kind == PropertyKind::Alive
                && let Some(PropertyArg::Ident(name)) = atom.args.get(1).cloned()
                && let Some(region) =
                    crate::verify::vm::region::resolve_region_name(tcx, def_id, &name)
            {
                atom.args[1] = PropertyArg::Region(region);
            }
        }
        Property::And(and) => {
            for conjunct in &mut and.conjuncts {
                bind_alive_regions(tcx, def_id, conjunct);
            }
        }
        Property::Or(or) => {
            for disjunct in &mut or.disjuncts {
                bind_alive_regions(tcx, def_id, disjunct);
            }
        }
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

pub(crate) fn get_trait_method_ensures<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> FnContracts<'tcx> {
    let trait_item_def_id = tcx
        .opt_associated_item(def_id)
        .and_then(|item| item.trait_item_def_id())
        .unwrap_or(def_id);
    if tcx.trait_of_assoc(trait_item_def_id).is_none() {
        return Vec::new();
    }
    let mut ensures = if trait_item_def_id.is_local() {
        collect_properties_from_named_attrs(
            tcx,
            crate::compat::get_all_attrs(tcx, trait_item_def_id),
            trait_item_def_id,
            "trait ensures",
            "ensures",
        )
    } else {
        Vec::new()
    };
    if ensures.is_empty() {
        ensures = super::contract::json::query_trait_method_ensures(tcx, def_id);
    }
    for property in &mut ensures {
        property.set_contract_kind(crate::verify::contract::ContractKind::Postcond);
    }
    ensures
}

pub(crate) fn get_call_ensures<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> FnContracts<'tcx> {
    if !tcx.is_foreign_item(def_id) {
        return get_trait_method_ensures(tcx, def_id);
    }
    let mut ensures = collect_properties_from_named_attrs(
        tcx,
        crate::compat::get_all_attrs(tcx, def_id),
        def_id,
        "foreign function ensures",
        "ensures",
    );
    for property in &mut ensures {
        property.set_contract_kind(crate::verify::contract::ContractKind::Postcond);
    }
    ensures
}

pub(crate) fn has_slice_offset_ensures(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    get_trait_method_ensures(tcx, def_id)
        .iter()
        .any(|property| property.kind() == Some(crate::verify::contract::PropertyKind::SliceOffset))
}

/// Build (pseudo-checkpoint, properties) pairs for every raw pointer dereference
/// in the target function.
fn build_raw_ptr_deref_checks<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<(Checkpoint<'tcx>, Vec<Property<'tcx>>)> {
    let infos = collect_raw_ptr_deref_info(tcx, def_id);
    if infos.is_empty() {
        return Vec::new();
    }

    infos
        .into_iter()
        .map(|info| {
            let target = PropertyArg::Expr(ContractExpr::Place(ContractPlace {
                base: PlaceBase::Arg(0),
                projections: vec![],
            }));
            let ty = PropertyArg::Ty(info.pointee_ty);
            let count = PropertyArg::Expr(ContractExpr::Const(1));

            let mut properties = if info.is_ptr2ref {
                vec![
                    Property::new_atom(
                        PropertyKind::Init,
                        vec![target.clone(), ty.clone(), count.clone()],
                    ),
                    Property::new_atom(PropertyKind::NonNull, vec![target.clone()]),
                    Property::new_atom(
                        PropertyKind::Allocated,
                        vec![target.clone(), ty.clone(), count.clone()],
                    ),
                    Property::new_atom(
                        PropertyKind::InBound,
                        vec![target.clone(), ty.clone(), count.clone()],
                    ),
                    Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
                    {
                        let mut p = Property::new_atom(PropertyKind::Alias, vec![target.clone()]);
                        p.set_contract_kind(crate::verify::contract::ContractKind::Hazard);
                        p
                    },
                ]
            } else {
                vec![
                    Property::new_atom(
                        PropertyKind::Allocated,
                        vec![target.clone(), ty.clone(), count.clone()],
                    ),
                    Property::new_atom(
                        PropertyKind::InBound,
                        vec![target.clone(), ty.clone(), count.clone()],
                    ),
                    Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
                ]
            };

            if info.is_read && !info.is_ptr2ref {
                properties.push(Property::new_atom(PropertyKind::Typed, vec![target, ty]));
            }

            (
                Checkpoint {
                    caller: def_id,
                    callee: None,
                    block: info.block,
                    args: vec![info.ptr_operand],
                    kind: crate::verify::checkpoint::CheckpointKind::RawPtrDeref,
                    requires: Vec::new(),
                    destination: Some(info.destination),
                    is_mut_ref: info.is_mut_ref,
                    statement_index: info.statement_index,
                    site_ordinal: 0,
                },
                properties,
            )
        })
        .collect()
}

/// Build (pseudo-checkpoint, properties) pairs for every static mut access
/// in the target function.
fn build_static_mut_checks<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<(Checkpoint<'tcx>, Vec<Property<'tcx>>)> {
    let infos = collect_static_mut_access_info(tcx, def_id);
    if infos.is_empty() {
        return Vec::new();
    }

    infos
        .into_iter()
        .map(|info| {
            let target = PropertyArg::Expr(ContractExpr::Place(ContractPlace {
                base: PlaceBase::Arg(0),
                projections: vec![],
            }));
            let ty = PropertyArg::Ty(info.ty);
            let count = PropertyArg::Expr(ContractExpr::Const(1));

            let properties = vec![
                Property::new_atom(
                    PropertyKind::Allocated,
                    vec![target.clone(), ty.clone(), count.clone()],
                ),
                Property::new_atom(
                    PropertyKind::InBound,
                    vec![target.clone(), ty.clone(), count.clone()],
                ),
                Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
                Property::new_atom(PropertyKind::Init, vec![target, ty, count]),
            ];

            (
                Checkpoint {
                    caller: def_id,
                    callee: None,
                    block: info.block,
                    args: vec![info.ptr_operand],
                    kind: crate::verify::checkpoint::CheckpointKind::StaticMutAccess,
                    requires: Vec::new(),
                    destination: None,
                    is_mut_ref: false,
                    statement_index: info.statement_index,
                    site_ordinal: info.site_ordinal,
                },
                properties,
            )
        })
        .collect()
}

fn is_drop_impl(tcx: TyCtxt<'_>, fn_did: DefId) -> bool {
    let Some(impl_id) = tcx.trait_impl_of_assoc(fn_did) else {
        return false;
    };
    let trait_did = tcx.impl_trait_id(impl_id);
    lang_api::matches(tcx, trait_did, LangItem::Drop)
}
