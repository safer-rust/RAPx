use crate::analysis::Analysis;
use crate::analysis::safetyflow_analysis::root::{
    function_has_struct_invariant, function_has_trait_ensurance, hir_contains_unsafe,
};
use crate::cli::VerifyMode;
use crate::helpers::fn_info::get_cons;
use crate::helpers::mir_scan::{collect_raw_ptr_deref_info, collect_static_mut_access_info};
use rustc_hir::{
    Attribute, BodyId, FnDecl, ItemKind,
    def_id::{DefId, LocalDefId},
    intravisit::{FnKind, Visitor},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
use syn::Expr;

use super::{
    attribute::assets_parser::*,
    attribute::attr_parser::parse_rapx_attr,
    contract::{ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind},
    helpers::{
        Callsite, collect_return_block_indices, collect_unsafe_callsites, get_owner_struct_def_id,
        has_rapx_verify_attr, is_std_crate_def_id, is_trait_unsafe, resolve_impl_self_ty_def_id,
    },
    path::PathExtractor,
};

/// A list of parsed `requires` contracts.
pub type FnContracts<'tcx> = Vec<Property<'tcx>>;

/// A list of parsed struct invariants.
pub type StructInvariants<'tcx> = Vec<Property<'tcx>>;

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
/// 1. Unsafe callsites are collected via [`collect_unsafe_callsites`].
/// 2. Each unique callee `DefId` gets its `#[rapx::requires]` contracts parsed
///    (with fallback to bundled JSON contracts for standard-library callees).
/// 3. Raw pointer dereferences are detected and converted into synthetic
///    (pseudo-callsite, `[ValidPtr, Align, (Typed)]`) pairs.
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
#[derive(Clone)]
pub struct FunctionTarget<'tcx> {
    /// The function being verified.
    pub def_id: DefId,

    /// Owning struct when this function is an associated method (e.g.
    /// `impl MyStruct { fn foo(...) }`).  `None` for free functions.
    ///
    /// Used to associate struct invariants and to group method-level
    /// verification results under the owning struct in diagnostic output.
    pub owner_struct_def_id: Option<DefId>,

    /// All call-terminator-based unsafe callsites found in this function's MIR.
    ///
    /// Each [`Callsite`] records the callee `DefId`, the source-span of the
    /// call, the basic-block location, and the MIR operands passed as arguments.
    pub callsites: Vec<Callsite<'tcx>>,

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

    /// Raw pointer dereference checks with their required safety properties.
    ///
    /// Each entry is a `(Callsite, Vec<Property>)` pair where the `Callsite`
    /// carries a synthetic dummy `DefId` (so the path extractor can treat
    /// dereferences uniformly with callsites) and the properties encode the
    /// pointer-validity requirements: always [`ValidPtr`](PropertyKind::ValidPtr)
    /// and [`Align`](PropertyKind::Align); additionally [`Typed`](PropertyKind::Typed)
    /// when the dereference is a read.
    pub raw_ptr_deref_checks: Vec<(Callsite<'tcx>, Vec<Property<'tcx>>)>,

    /// Static mut access checks with their required safety properties.
    ///
    /// Each entry is a `(Callsite, Vec<Property>)` pair following the same
    /// pattern as [`raw_ptr_deref_checks`](Self::raw_ptr_deref_checks).  The
    /// properties are [`ValidPtr`](PropertyKind::ValidPtr),
    /// [`Align`](PropertyKind::Align), and [`Init`](PropertyKind::Init)
    /// (conservatively checked for both reads and writes).
    pub static_mut_checks: Vec<(Callsite<'tcx>, Vec<Property<'tcx>>)>,
}

/// Collected verification data for a struct that owns methods marked with `#[rapx::verify]`.
pub struct StructTarget<'tcx> {
    /// Struct that owns one or more methods selected as targets to verify.
    pub def_id: DefId,
    /// Parsed `invariant` contracts attached to the struct.
    pub invariants: StructInvariants<'tcx>,
    /// Methods of this struct selected as targets to verify.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
}

/// Collected verification data for an `impl unsafe Trait for Type` block.
///
/// The trait's `#[rapx::ensures(...)]` contracts define safety obligations the
/// implementor must satisfy.  Full verification of trait impls is deferred.
pub struct TraitEnsurance<'tcx> {
    /// The unsafe trait definition.
    pub def_id: DefId,
    /// The concrete type that implements the trait (e.g. `SomeStruct`).
    pub self_ty_def_id: Option<DefId>,
    /// `ensures` contracts grouped by trait method name.
    pub ensures: Vec<(String, FnContracts<'tcx>)>,
}

/// Visitor that collects targets annotated with `#[rapx::verify]`.
pub struct VerifyTargetCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: VerifyMode,
    /// All function targets to verify collected from the current crate.
    pub function_targets: Vec<FunctionTarget<'tcx>>,
    /// All struct targets to verify collected from the current crate.
    pub struct_targets: HashMap<DefId, StructTarget<'tcx>>,
    /// All trait targets to verify collected from the current crate.
    pub trait_targets: HashMap<DefId, TraitEnsurance<'tcx>>,
    /// Cached contracts for each callee function so repeated callees are parsed once.
    fn_contract_cache: HashMap<DefId, FnContracts<'tcx>>,
}

impl<'tcx> VerifyTargetCollector<'tcx> {
    /// Creates a new collector for the current type context.
    pub fn new(tcx: TyCtxt<'tcx>, mode: VerifyMode) -> Self {
        VerifyTargetCollector {
            tcx,
            mode,
            function_targets: Vec::new(),
            struct_targets: HashMap::new(),
            trait_targets: HashMap::new(),
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
    fn get_fn_contracts(&mut self, callee_def_id: DefId) -> FnContracts<'tcx> {
        let is_std = is_std_crate_def_id(self.tcx, callee_def_id);

        let trait_requires = get_trait_method_requires(self.tcx, callee_def_id);

        self.fn_contract_cache
            .entry(callee_def_id)
            .or_insert_with(|| {
                let mut requires = get_contract_from_annotation(self.tcx, callee_def_id);

                if requires.is_empty() && !trait_requires.is_empty() {
                    requires = trait_requires.clone();
                }

                if requires.is_empty() && is_std {
                    requires = get_contract_from_entry(
                        self.tcx,
                        callee_def_id,
                        get_std_contracts_from_assets(self.tcx, callee_def_id),
                    );

                if requires.is_empty() {
                        let path = crate::helpers::name::get_cleaned_def_path_name(
                            self.tcx,
                            callee_def_id,
                        );
                        rap_warn!(
                            "no safety contracts found for std callee \"{path}\" \
                             (missing from std-contracts.json)"
                        );
                    } else {
                        let path = crate::helpers::name::get_cleaned_def_path_name(
                            self.tcx,
                            callee_def_id,
                        );
                        rap_debug!(
                            "loaded {} safety contract(s) for std callee \"{path}\" from std-contracts.json",
                            requires.len()
                        );
                    }
                }

                if requires.is_empty() {
                    requires.push(Property::new(
                        self.tcx,
                        callee_def_id,
                        "Unknown",
                        &[],
                    ));
                }

                requires
            })
            .clone()
    }

    /// Builds a function target to verify from a function definition.
    fn build_function_target(&mut self, def_id: DefId) -> FunctionTarget<'tcx> {
        let callsites = collect_unsafe_callsites(self.tcx, def_id);
        let unsafe_callees: HashSet<_> = callsites
            .iter()
            .filter_map(|callsite| callsite.callee)
            .collect();
        let callee_requires = unsafe_callees
            .iter()
            .map(|callee_def_id| (*callee_def_id, self.get_fn_contracts(*callee_def_id)))
            .collect();

        let caller_requires = self.get_fn_contracts(def_id);

        let raw_ptr_deref_checks = build_raw_ptr_deref_checks(self.tcx, def_id);
        let static_mut_checks = build_static_mut_checks(self.tcx, def_id);

        let owner_struct_def_id = get_owner_struct_def_id(self.tcx, def_id);
        let struct_invariants = owner_struct_def_id
            .map(|struct_def_id| {
                get_struct_invariants_from_annotation(self.tcx, struct_def_id, def_id)
            })
            .unwrap_or_default();

        FunctionTarget {
            def_id,
            owner_struct_def_id,
            callsites,
            callee_requires,
            caller_requires,
            struct_invariants,
            raw_ptr_deref_checks,
            static_mut_checks,
        }
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
}

fn get_trait_method_requires<'tcx>(tcx: TyCtxt<'tcx>, callee_def_id: DefId) -> FnContracts<'tcx> {
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
    /// are recorded.  In `scan` and `invless` modes, all `unsafe trait` impls
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

            let trait_ref = {
                #[cfg(rapx_rustc_ge_193)]
                {
                    self.tcx.impl_opt_trait_ref(impl_def_id)
                }
                #[cfg(not(rapx_rustc_ge_193))]
                {
                    self.tcx.impl_trait_ref(impl_def_id)
                }
            };

            if let Some(trait_ref) = trait_ref {
                let trait_def_id = trait_ref.skip_binder().def_id;
                if is_trait_unsafe(self.tcx, trait_def_id) {
                    let ensures = get_trait_contracts_from_annotation(self.tcx, trait_def_id);

                    let self_ty_def_id = resolve_impl_self_ty_def_id(&item);

                    self.trait_targets
                        .entry(trait_def_id)
                        .or_insert_with(|| TraitEnsurance {
                            def_id: trait_def_id,
                            self_ty_def_id,
                            ensures,
                        });
                }
            }
        }

        rustc_hir::intravisit::walk_item(self, item);
    }

    /// Visits each function body and records verification targets.
    ///
    /// In `targeted` mode, only functions annotated with `#[rapx::verify]` are collected.
    /// In `all` and `invariantless` modes, a HIR-level pre-filter (`contains_unsafe`
    /// and `function_has_struct_invariant`) avoids expensive MIR scanning for functions
    /// that have no unsafe content and no struct invariants.
    fn visit_fn(
        &mut self,
        _fk: FnKind<'tcx>,
        _fd: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _span: Span,
        id: LocalDefId,
    ) -> Self::Result {
        if matches!(self.mode, VerifyMode::Targeted) && !has_rapx_verify_attr(self.tcx, id) {
            return;
        }

        // HIR pre-filter: skip functions that have nothing to verify.
        // `contains_unsafe` catches functions with unsafe blocks/declarations;
        // `function_has_struct_invariant` catches methods on structs with invariants;
        // `function_has_trait_ensurance` catches methods on unsafe trait impls with contracts.
        let def_id = id.to_def_id();
        if !matches!(self.mode, VerifyMode::Targeted) {
            if !hir_contains_unsafe(self.tcx, body_id)
                && !function_has_struct_invariant(self.tcx, def_id)
                && !function_has_trait_ensurance(self.tcx, def_id)
            {
                return;
            }
        }

        let function_target = self.build_function_target(def_id);

        match self.mode {
            VerifyMode::Targeted => {}
            VerifyMode::Scan => {
                if function_target.callsites.is_empty()
                    && function_target.raw_ptr_deref_checks.is_empty()
                    && function_target.static_mut_checks.is_empty()
                    && function_target.struct_invariants.is_empty()
                {
                    let root =
                        crate::analysis::safetyflow_analysis::root::scan_mir(self.tcx, def_id);
                    if root.is_none() {
                        return;
                    }
                }
            }
            VerifyMode::Invless => {
                if function_target.callsites.is_empty()
                    && function_target.raw_ptr_deref_checks.is_empty()
                    && function_target.static_mut_checks.is_empty()
                {
                    return;
                }
            }
        }

        self.push_function_target(function_target);
    }
}

/// Analysis pass that finds all verification targets.
///
/// In `targeted` mode, only functions annotated with `#[rapx::verify]` are listed.
/// In `scan` mode, all functions with unsafe callees or struct invariants are listed.
pub struct PrepareTargets<'tcx> {
    tcx: TyCtxt<'tcx>,
    mode: VerifyMode,
}

impl<'tcx> Analysis for PrepareTargets<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Identify Targets Analysis"
    }

    fn run(&mut self) {
        let mut collector = VerifyTargetCollector::new(self.tcx, self.mode);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        // Free functions (no owning struct)
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

        // Structs with methods
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

            rap_info!("");
        }

        // Traits with impl methods
        let mut trait_ids: Vec<_> = collector.trait_targets.keys().copied().collect();
        trait_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for trait_def_id in trait_ids {
            let Some(trait_target) = collector.trait_targets.get(&trait_def_id) else {
                continue;
            };
            let trait_path = self.tcx.def_path_str(trait_target.def_id);

            rap_info!("============================================================");
            rap_info!(
                "[rapx::verify] prepare targets for unsafe trait: {}",
                trait_path
            );
            rap_info!("============================================================");

            self.log_trait_ensurance(trait_target);

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

    fn reset(&mut self) {}
}

impl<'tcx> PrepareTargets<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, mode: VerifyMode) -> Self {
        PrepareTargets { tcx, mode }
    }

    fn log_struct_invariants(&self, struct_target: &StructTarget<'tcx>) {
        if struct_target.invariants.is_empty() {
            rap_info!("  struct invariants: <none>");
        } else {
            rap_info!("  struct invariants:");
            for property in &struct_target.invariants {
                rap_info!("    - {:?}, args={:?}", property.kind, property.args);
            }
        }
    }

    fn log_trait_ensurance(&self, trait_target: &TraitEnsurance<'tcx>) {
        if let Some(self_ty) = trait_target.self_ty_def_id {
            rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
        }
        if trait_target.ensures.is_empty() {
            rap_info!("  ensures: <none>");
        } else {
            rap_info!("  ensures (implementor must satisfy):");
            for (method_name, contracts) in &trait_target.ensures {
                rap_info!("    fn {}:", method_name);
                for property in contracts {
                    rap_info!("      - {:?}, args={:?}", property.kind, property.args);
                }
            }
        }
    }

    fn log_method_target(&self, target: &FunctionTarget<'tcx>) {
        let target_path = self.tcx.def_path_str(target.def_id);
        let name = target_path.rsplit("::").next().unwrap_or(&target_path);
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

        let cons = get_cons(self.tcx, target.def_id);
        for con in &cons {
            rap_info!("      + constructor: {}", self.tcx.def_path_str(*con));
        }

        self.log_unsafe_callees_and_contracts(target);
        self.log_callsite_paths(target);
    }

    fn log_free_function_unsafe_callees(&self, target: &FunctionTarget<'tcx>) {
        self.log_unsafe_callees_and_contracts(target);
        self.log_callsite_paths(target);
    }

    fn log_unsafe_callees_and_contracts(&self, target: &FunctionTarget<'tcx>) {
        if target.callee_requires.is_empty() {
            rap_info!("      unsafe callsites: <none>");
            return;
        }

        let mut unsafe_callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        unsafe_callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));

        for unsafe_callee_def_id in unsafe_callee_ids {
            let unsafe_callee_path = self.tcx.def_path_str(unsafe_callee_def_id);
            rap_info!("      unsafe callee: {}", unsafe_callee_path,);

            if let Some(requires) = target.callee_requires.get(&unsafe_callee_def_id) {
                if requires.is_empty() {
                    rap_info!("        safety contracts: <none>");
                } else {
                    rap_info!("        safety contracts:");
                    for property in requires {
                        rap_info!("          - {:?}, args={:?}", property.kind, property.args);
                    }
                }
            }
        }
    }

    fn log_callsite_paths(&self, target: &FunctionTarget<'tcx>) {
        if target.callsites.is_empty() {
            return;
        }

        let result = PathExtractor::new(self.tcx, target.def_id, target.callsites.clone(), 0).run();
        rap_info!("      callsite paths:");
        for (display_index, callsite) in result.callsites().iter().enumerate() {
            rap_info!(
                "        #{} {} at bb{} ({} arg(s))",
                display_index,
                callsite.callee_name(self.tcx),
                callsite.block.as_usize(),
                callsite.args.len()
            );

            let mut callsite_paths: Vec<_> = result.paths_for(callsite.location()).iter().collect();
            callsite_paths.sort_by_key(|path| path.describe());

            if callsite_paths.is_empty() {
                rap_info!("          paths: <none>");
                continue;
            }

            for (path_idx, path) in callsite_paths.iter().enumerate() {
                rap_info!("          path {}: {}", path_idx, path.describe());
            }
        }
    }
}

/// Builds contracts from backup JSON entries.
///
/// Each entry stores property-expression arguments that are passed directly into
/// `Property::new`. The target information is resolved by `Property` itself
/// from those arguments.
fn get_contract_from_entry<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    contract_entries: &[PropertyEntry],
) -> FnContracts<'tcx> {
    let mut results = Vec::new();
    for entry in contract_entries {
        if entry.args.is_empty() {
            continue;
        }

        let mut exprs: Vec<Expr> = Vec::new();
        for arg_str in &entry.args {
            let normalized_arg = normalize_json_contract_arg(arg_str);
            match syn::parse_str::<Expr>(&normalized_arg) {
                Ok(expr) => exprs.push(expr),
                Err(_) => {
                    rap_error!(
                        "JSON Contract Error: Failed to parse arg '{}' as Rust Expr for tag {}",
                        arg_str,
                        entry.tag
                    );
                }
            }
        }

        if exprs.len() != entry.args.len() {
            rap_error!(
                "Parse std API args error: Failed to parse arg '{:?}'",
                entry.args
            );
            continue;
        }

        let property = Property::new(tcx, def_id, entry.tag.as_str(), &exprs);
        if matches!(property.kind, PropertyKind::Unknown) {
            rap_debug!(
                "skip unsupported std safety contract tag '{}' for callee {:?}",
                entry.tag,
                def_id
            );
            continue;
        }
        results.push(property);
    }
    results
}

/// Convert explicit JSON contract tokens into the expression syntax accepted by
/// the existing property parser.
///
/// Supported explicit tokens:
/// - `arg:N` names callee argument `N` and becomes internal `Arg_N`.
/// - `const:N` names an integer constant and becomes `N`.
/// - `ty:T` names a type parameter/type identifier and becomes `T`.
///
/// Unprefixed strings are kept unchanged for compatibility with older entries
/// such as `"0"`, `"T"`, and `"1"`.
fn normalize_json_contract_arg(arg: &str) -> String {
    let bytes = arg.as_bytes();
    let mut out = String::with_capacity(arg.len());
    let mut i = 0;

    while i < bytes.len() {
        if arg[i..].starts_with("arg:") {
            let start = i + "arg:".len();
            let end = scan_while(arg, start, |ch| ch.is_ascii_digit());
            if end > start {
                out.push_str("Arg_");
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        if arg[i..].starts_with("const:") {
            let start = i + "const:".len();
            let end = scan_while(arg, start, is_contract_token_char);
            if end > start {
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        if arg[i..].starts_with("ty:") {
            let start = i + "ty:".len();
            let end = scan_while(arg, start, is_contract_token_char);
            if end > start {
                out.push_str(&arg[start..end]);
                i = end;
                continue;
            }
        }

        let ch = arg[i..].chars().next().unwrap();
        out.push(ch);
        i += ch.len_utf8();
    }

    out
}

fn scan_while(arg: &str, mut index: usize, predicate: impl Fn(char) -> bool) -> usize {
    while index < arg.len() {
        let ch = arg[index..].chars().next().unwrap();
        if !predicate(ch) {
            break;
        }
        index += ch.len_utf8();
    }
    index
}

fn is_contract_token_char(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_' || ch == ':'
}

fn is_rapx_named_attr(attr: &Attribute, name: &str) -> bool {
    let path = attr.path();
    path.len() >= 2
        && path[path.len() - 2].as_str() == "rapx"
        && path[path.len() - 1].as_str() == name
}

/// Collects properties from `#[rapx::requires(...)]` attributes.
fn collect_properties_from_requires_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    collect_properties_from_named_attrs(tcx, attrs, property_def_id, parse_error_label, "requires")
}

/// Collects properties from `#[rapx::invariant(...)]` attributes.
fn collect_properties_from_invariant_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    collect_properties_from_named_attrs(tcx, attrs, property_def_id, parse_error_label, "invariant")
}

/// Collects properties from `#[rapx::ensures(...)]` attributes.
fn collect_properties_from_ensures_attrs<'tcx>(
    tcx: TyCtxt<'tcx>,
    attrs: impl IntoIterator<Item = &'tcx Attribute>,
    property_def_id: DefId,
    parse_error_label: &str,
) -> Vec<Property<'tcx>> {
    collect_properties_from_named_attrs(tcx, attrs, property_def_id, parse_error_label, "ensures")
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
        if !is_rapx_named_attr(attr, attr_name) {
            continue;
        }

        let attr_str = rustc_hir_pretty::attribute_to_string(&tcx, attr);
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

        results.extend(parsed.properties.into_iter().map(|property| {
            Property::new(tcx, property_def_id, property.tag.as_str(), &property.args)
        }));
    }

    results
}

/// Parses `requires` contracts from source-level RAPx annotations attached to a definition.
pub(crate) fn get_contract_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> FnContracts<'tcx> {
    #[allow(deprecated)]
    let attrs = tcx.get_all_attrs(def_id);
    collect_properties_from_requires_attrs(tcx, attrs, def_id, "requires")
}

/// Parses struct invariants from source-level RAPx annotations attached to a struct definition.
fn get_struct_invariants_from_annotation<'tcx>(
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

    let mut invariants = collect_properties_from_requires_attrs(
        tcx,
        {
            #[allow(deprecated)]
            {
                tcx.get_all_attrs(struct_def_id)
            }
        },
        context_def_id,
        "invariant",
    );
    invariants.extend(collect_properties_from_invariant_attrs(
        tcx,
        {
            #[allow(deprecated)]
            {
                tcx.get_all_attrs(struct_def_id)
            }
        },
        context_def_id,
        "invariant",
    ));
    invariants
}

/// Parses trait safety contracts from `#[rapx::ensures(...)]` on unsafe trait
/// methods, grouped by method name.
fn get_trait_contracts_from_annotation<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_def_id: DefId,
) -> Vec<(String, FnContracts<'tcx>)> {
    let Some(local_id) = trait_def_id.as_local() else {
        return Vec::new();
    };

    let item = tcx.hir_expect_item(local_id);

    let trait_items = {
        #[cfg(not(rapx_rustc_ge_198))]
        if let ItemKind::Trait(.., items) = &item.kind {
            items
        } else {
            return Vec::new();
        }
        #[cfg(rapx_rustc_ge_198)]
        if let ItemKind::Trait { items, .. } = &item.kind {
            items
        } else {
            return Vec::new();
        }
    };

    let mut ensures: Vec<(String, FnContracts<'tcx>)> = Vec::new();

    for trait_item_id in trait_items.iter() {
        let trait_item_def_id = trait_item_id.owner_id.to_def_id();
        let method_name = tcx.def_path_str(trait_item_def_id);
        #[allow(deprecated)]
        let attrs = tcx.get_all_attrs(trait_item_def_id);

        let method_ensures =
            collect_properties_from_ensures_attrs(tcx, attrs, trait_item_def_id, "trait ensures");

        if !method_ensures.is_empty() {
            ensures.push((method_name, method_ensures));
        }
    }

    ensures
}

/// Build (pseudo-callsite, properties) pairs for every raw pointer dereference
/// in the target function.
fn build_raw_ptr_deref_checks<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<(Callsite<'tcx>, Vec<Property<'tcx>>)> {
    let infos = collect_raw_ptr_deref_info(tcx, def_id);
    if infos.is_empty() {
        return Vec::new();
    }

    infos
        .into_iter()
        .map(|info| {
            let target = PropertyArg::Place(ContractPlace {
                base: PlaceBase::Arg(0),
                projections: vec![],
            });
            let ty = PropertyArg::Ty(info.pointee_ty);
            let count = PropertyArg::Expr(ContractExpr::Const(1));

            let mut properties = vec![
                Property {
                    kind: PropertyKind::ValidPtr,
                    args: vec![target.clone(), ty.clone(), count.clone()],
                },
                Property {
                    kind: PropertyKind::Align,
                    args: vec![target.clone(), ty.clone()],
                },
            ];

            if info.is_read {
                properties.push(Property {
                    kind: PropertyKind::Typed,
                    args: vec![target, ty],
                });
            }

            (
                Callsite {
                    caller: def_id,
                    callee: None,
                    block: info.block,
                    span: rustc_span::DUMMY_SP,
                    args: vec![info.ptr_operand],
                    kind: crate::helpers::mir_scan::CallsiteKind::RawPtrDeref,
                },
                properties,
            )
        })
        .collect()
}

/// Build (pseudo-callsite, properties) pairs for every static mut access
/// in the target function.
fn build_static_mut_checks<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<(Callsite<'tcx>, Vec<Property<'tcx>>)> {
    let infos = collect_static_mut_access_info(tcx, def_id);
    if infos.is_empty() {
        return Vec::new();
    }

    infos
        .into_iter()
        .map(|info| {
            let target = PropertyArg::Place(ContractPlace {
                base: PlaceBase::Arg(0),
                projections: vec![],
            });
            let ty = PropertyArg::Ty(info.ty);
            let count = PropertyArg::Expr(ContractExpr::Const(1));

            let properties = vec![
                Property {
                    kind: PropertyKind::ValidPtr,
                    args: vec![target.clone(), ty.clone(), count.clone()],
                },
                Property {
                    kind: PropertyKind::Align,
                    args: vec![target.clone(), ty.clone()],
                },
                Property {
                    kind: PropertyKind::Init,
                    args: vec![target, ty, count],
                },
            ];

            (
                Callsite {
                    caller: def_id,
                    callee: None,
                    block: info.block,
                    span: rustc_span::DUMMY_SP,
                    args: vec![info.ptr_operand],
                    kind: crate::helpers::mir_scan::CallsiteKind::StaticMutAccess,
                },
                properties,
            )
        })
        .collect()
}
