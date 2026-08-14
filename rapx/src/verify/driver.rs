//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! `VerifyDriver` prepares paths for two kinds of checks (unsafe checkpoints and
//! struct invariants) and delegates the actual backward/forward/SMT work to
//! the shared `VerifyEngine`.

use crate::analysis::Analysis;
use crate::analysis::path::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};
use crate::cli::VerifyMode;
use crate::helpers::fn_info::{FnKind, get_cons, get_mutated_fields, get_muts, get_type};
use crate::verify::contract::PropertyKind;
use crate::verify::target::get_contract_from_annotation;

use crate::compat::{FxHashMap, FxHashSet};
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;

use super::{
    contract::Property,
    display::{
        dedup_compound_props, emit_results_and_verdict, emit_verify_summary,
        fmt_contract_expanded, fmt_fn_path_with_bounds, fmt_fn_path_with_generics,
        fmt_fn_with_params,
    },
    engine::VerifyEngine,
    loop_sensitivity::{LoopSensitivityAnalyzer, RepeatStrategy},
    path_extractor::{CallGroup, PATH_LIMIT, PathExtractor},
    report::{CheckResult, PropertyCheckResult, VerificationReport},
    slicer::BackwardItem,
    target::{FunctionTarget, VerifyTargetCollector},
};

use crate::helpers::mir_utils::collect_return_block_indices;

use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

/// Orchestrates the three-stage verification pipeline (backward data-dependency
/// analysis → forward state simulation → SMT checking) for a single function
/// under analysis.
///
/// Each `VerifyDriver` instance bundles together:
///
/// 1. The **problem statement** (`target`) — which unsafe checkpoints and
///    raw-pointer dereferences exist, what safety contracts they demand, and
///    what entry assumptions (from `#[rapx::requires]`) and struct invariants
///    apply.
///
/// 2. The **reachability model** (`path_info`) — SCC-aware acyclic paths
///    from function entry to each checkpoint, produced by flattening the MIR
///    control-flow graph with bounded loop unrolling.
///
/// 3. The **verification engine** (`engine`) — a stateless pipeline shared
///    across all (checkpoint, path, property) triples.
///
/// 4. The **loop-unrolling budget** (`allow_repeat`) — caps how many extra
///    iterations a loop body may appear beyond its first occurrence, trading
///    completeness against path enumeration cost.
///
/// Verification proceeds in two phases per driver instance:
/// - [`verify_function`](Self::verify_function): checks safety properties at
///   each unsafe checkpoint (callee `#[rapx::requires]` contracts).
/// - [`verify_struct_invariants`](Self::verify_struct_invariants): checks
///   struct invariants at return-block checkpoints (constructors) or at all
///   path endpoints (non-constructor methods).
pub struct VerifyDriver<'target, 'tcx> {
    tcx: TyCtxt<'tcx>,

    target: &'target FunctionTarget<'tcx>,

    path_info: Vec<CallGroup<'tcx>>,

    engine: VerifyEngine<'tcx>,

    allow_repeat: usize,
}

impl<'target, 'tcx> VerifyDriver<'target, 'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>) -> Self {
        Self::new_with_repeat(tcx, target, 0)
    }

    pub fn new_with_repeat(
        tcx: TyCtxt<'tcx>,
        target: &'target FunctionTarget<'tcx>,
        allow_repeat: usize,
    ) -> Self {
        let all_checkpoints: Vec<_> = target.all_checkpoints().into_iter().cloned().collect();
        let path_info = PathExtractor::new(tcx, target.def_id, all_checkpoints, allow_repeat).run();
        Self {
            tcx,
            target,
            path_info,
            engine: VerifyEngine::new(tcx),
            allow_repeat,
        }
    }

    /// Return the compiler type context owned by this driver.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Return the function target managed by this driver.
    pub fn target(&self) -> &'target FunctionTarget<'tcx> {
        self.target
    }

    /// Return the per-callee call groups managed by this driver.
    pub fn path_info(&self) -> &[CallGroup<'tcx>] {
        &self.path_info
    }

    /// Run unsafe-checkpoint verification for the managed function target.
    pub fn verify_function(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);

        for view in self.iter_callsite_checks() {
            let mut view_results: Vec<PropertyCheckResult<'tcx>> = Vec::new();

            for (property_index, property) in view.properties.iter().enumerate() {
                if property.is_or() {
                    self.check_or_property(&mut report, &view, property_index, property);
                    continue;
                }
                let bulk = self.engine.check_callsite_from_tree(
                    view.tree,
                    view.checkpoint,
                    property,
                    &self.target.caller_requires,
                );
                for (path_index, (result, path_desc)) in bulk.iter().enumerate() {
                    let item = PropertyCheckResult {
                        checkpoint: view.checkpoint.location(),
                        checkpoint_index: view.checkpoint_index,
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: result.clone(),
                        diagnostics: Some(format!("vm-check: {:?}", result)),
                        path_description: path_desc.clone(),
                        callee_name: view.checkpoint.callee_name(self.tcx),
                    };
                    view_results.push(item);
                }
            }

            for item in view_results {
                report.push(item);
            }
        }

        report
    }

    fn check_or_property(
        &self,
        report: &mut VerificationReport<'tcx>,
        view: &CheckpointCheckView<'_, '_, 'tcx>,
        property_index: usize,
        or_property: &Property<'tcx>,
    ) {
        // Per-path final OR result, aggregating the AND of each group.
        let mut per_path: Vec<Option<(super::report::CheckResult, String)>> = Vec::new();

        for group in or_property.groups().iter() {
            // Per-path AND result of this group.
            let mut group_per_path: Vec<Option<(super::report::CheckResult, String)>> = Vec::new();
            for sub_prop in group.iter() {
                let bulk = self.engine.check_callsite_from_tree(
                    view.tree,
                    view.checkpoint,
                    sub_prop,
                    &self.target.caller_requires,
                );
                if group_per_path.is_empty() {
                    group_per_path.resize(bulk.len(), None);
                }
                for (path_idx, (result, path_desc)) in bulk.iter().enumerate() {
                    let slot = group_per_path[path_idx]
                        .get_or_insert_with(|| (result.clone(), path_desc.clone()));
                    slot.0 = slot.0.clone().and(result.clone());
                    if matches!(result, super::report::CheckResult::Failed | super::report::CheckResult::Unknown) {
                        slot.1 = path_desc.clone();
                    }
                }
            }

            // Fold this group's per-path AND result into the OR.
            if per_path.is_empty() {
                per_path.resize(group_per_path.len(), None);
            }
            for (path_idx, g) in group_per_path.iter().enumerate() {
                if let Some((g_result, g_desc)) = g {
                    let slot = per_path[path_idx]
                        .get_or_insert_with(|| (g_result.clone(), g_desc.clone()));
                    slot.0 = slot.0.clone().or(g_result.clone());
                    if matches!(g_result, super::report::CheckResult::Proved) {
                        slot.1 = g_desc.clone();
                    }
                }
            }
        }

        for (path_index, best) in per_path.iter().enumerate() {
            if let Some((result, path_desc)) = best {
                report.push(PropertyCheckResult {
                    checkpoint: view.checkpoint.location(),
                    checkpoint_index: view.checkpoint_index,
                    path_index,
                    property_index,
                    property: or_property.clone(),
                    result: result.clone(),
                    diagnostics: Some(path_desc.clone()),
                    path_description: path_desc.clone(),
                    callee_name: view.checkpoint.callee_name(self.tcx),
                });
            }
        }
    }

    /// Return the required properties for a concrete unsafe checkpoint.
    ///
    /// Dispatches on [`CheckpointKind`]: synthetic checkpoints (raw pointer
    /// dereference, static mut access) carry their properties in
    /// `target.raw_ptr_deref_checks` / `target.static_mut_checks`; real
    /// unsafe calls look up `target.callee_requires` by callee `DefId`.
    pub fn properties_for_callsite(
        &self,
        checkpoint: &Checkpoint<'tcx>,
    ) -> &'target [Property<'tcx>] {
        self.target.properties_for_callsite(checkpoint)
    }

    /// Iterate over checkpoints together with their shared path tree and properties.
    pub fn iter_callsite_checks(
        &self,
    ) -> impl Iterator<Item = CheckpointCheckView<'_, 'target, 'tcx>> + '_ {
        let mut checkpoint_index = 0usize;
        self.path_info.iter().flat_map(move |group| {
            group.checkpoints.iter().filter_map(move |checkpoint| {
                let properties = self.properties_for_callsite(checkpoint);
                if properties.is_empty() {
                    return None;
                }
                let view = CheckpointCheckView {
                    checkpoint_index,
                    checkpoint,
                    tree: &group.tree,
                    properties,
                };
                checkpoint_index += 1;
                Some(view)
            })
        })
    }

    /// Run struct invariant verification for the managed function target.
    ///
    /// For constructors (functions returning `Self`), paths are filtered to
    /// return blocks to avoid unwinding paths where the struct may not be
    /// fully initialised. For methods, all whole-CFG paths from
    /// `PathGraph::enumerate_paths_repeat` are used directly.
    pub fn verify_struct_invariants(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let invariants = &self.target.struct_invariants;
        if invariants.is_empty() {
            return report;
        }

        let is_constructor = get_type(self.tcx, self.target.def_id) == FnKind::Constructor;
        let caller_contracts = &self.target.caller_requires;

        let fn_sig = self.tcx.fn_sig(self.target.def_id).skip_binder();
        let output = fn_sig.output().skip_binder();
        let returns_self = is_constructor || output.is_param(0);

        let entry_facts: Vec<BackwardItem<'tcx>> = if is_constructor {
            caller_contracts
                .iter()
                .filter(|c| !matches!(c.kind(), Some(PropertyKind::Unknown)))
                .map(|c| BackwardItem::ContractFact {
                    property: c.clone(),
                })
                .collect()
        } else {
            invariants
                .iter()
                .map(|inv| BackwardItem::ContractFact {
                    property: inv.clone(),
                })
                .collect()
        };

        for (checkpoint, tree) in self.build_invariant_trees(is_constructor) {
            rap_debug!(
                "[rapx::verify] struct invariant checkpoint bb{}: {} tree node(s)",
                checkpoint.block.as_usize(),
                tree.len()
            );

            let paths = tree.to_vecs();

            for (property_index, invariant) in invariants.iter().enumerate() {
                let results = self.engine.check_invariant_from_tree(
                    self.target.def_id,
                    &tree,
                    checkpoint,
                    invariant,
                    &entry_facts,
                );

                for (path_index, (result, _path_desc)) in results.iter().enumerate() {
                    let path_description = paths
                        .get(path_index)
                        .map(|p| {
                            p.iter()
                                .map(|b| b.to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        })
                        .unwrap_or_default();
                    report.push(PropertyCheckResult {
                        checkpoint: checkpoint,
                        checkpoint_index: checkpoint.block.as_usize(),
                        path_index,
                        property_index,
                        property: invariant.clone(),
                        result: result.clone(),
                        diagnostics: Some(format!("vm-invariant: {:?}", result)),
                        path_description,
                        callee_name: format!("struct-invariant(bb{})", checkpoint.block.as_usize()),
                    });
                }
            }
        }

        if !returns_self && !is_constructor {
            let has_failed = report.results.iter().any(|r| matches!(r.result, CheckResult::Failed));
            if !has_failed {
                report.results.retain(|r| !matches!(r.result, CheckResult::Unknown));
            }
        }

        report
    }

    fn build_invariant_trees(
        &self,
        is_constructor: bool,
    ) -> FxHashMap<CheckpointLocation, PathTree> {
        let mut pg = PathGraph::new(self.tcx, self.target.def_id);
        pg.find_scc();
        let mut enumerator = PathEnumerator::new(&pg);
        let all_paths = enumerator.enumerate_paths_repeat(self.allow_repeat);

        let kind_label = if is_constructor {
            "constructor"
        } else {
            "method"
        };
        rap_debug!(
            "[rapx::verify] struct invariant ({kind_label}): {} whole-cfg path(s) for {}",
            all_paths.len(),
            self.tcx.def_path_str(self.target.def_id),
        );

        let mut trees_by_checkpoint: FxHashMap<CheckpointLocation, PathTree> = FxHashMap::default();

        if is_constructor {
            let return_blocks = collect_return_block_indices(self.tcx, self.target.def_id);
            for &return_block in &return_blocks {
                let checkpoint = CheckpointLocation {
                    caller: self.target.def_id,
                    block: return_block,
                };
                let mut tree = PathTree::new();
                let _ = all_paths.walk_prefixes(
                    return_block.as_usize(),
                    &mut |prefix: &[usize]| -> bool {
                        if tree.len() >= PATH_LIMIT {
                            return false;
                        }
                        tree.insert(prefix);
                        true
                    },
                );
                if !tree.is_empty() {
                    trees_by_checkpoint.insert(checkpoint, tree);
                }
            }
        } else {
            let mut seen_paths = FxHashSet::default();
            for path in all_paths.iter() {
                if path.is_empty() {
                    continue;
                }
                if !seen_paths.insert(path.clone()) {
                    continue;
                }
                let last_block = BasicBlock::from(*path.last().unwrap());
                let checkpoint = CheckpointLocation {
                    caller: self.target.def_id,
                    block: last_block,
                };
                trees_by_checkpoint
                    .entry(checkpoint)
                    .or_insert_with(PathTree::new)
                    .insert(path.as_slice());
            }
        }

        trees_by_checkpoint
    }
}

/// Returns whether a function returns the owning struct type (i.e. is a constructor).
/// Borrowed view of all verification inputs for one unsafe checkpoint.
pub struct CheckpointCheckView<'view, 'target, 'tcx> {
    /// Position among checkpoints that have properties to verify.
    pub checkpoint_index: usize,
    /// The concrete unsafe checkpoint in the caller MIR body.
    pub checkpoint: &'view Checkpoint<'tcx>,
    /// Per-checkpoint prefix tree of all verification paths to this checkpoint.
    pub tree: &'view PathTree,
    /// Required safety properties for the unsafe callee.
    pub properties: &'target [Property<'tcx>],
}

/// Analysis pass that runs verification and emits function-level summaries.
pub struct VerifyRun<'tcx> {
    tcx: TyCtxt<'tcx>,
    repeat_strategy: RepeatStrategy,
    mode: VerifyMode,
    skip_invariant: bool,
    crate_filter: Option<String>,
    module_filter: Option<String>,
    debug_contracts: bool,
}

impl<'tcx> VerifyRun<'tcx> {
    /// Create the default verify pass for the current compiler type context.
    pub fn new(
        tcx: TyCtxt<'tcx>,
        repeat_strategy: RepeatStrategy,
        mode: VerifyMode,
        skip_invariant: bool,
        crate_filter: Option<String>,
        module_filter: Option<String>,
        debug_contracts: bool,
    ) -> Self {
        Self {
            tcx,
            repeat_strategy,
            mode,
            skip_invariant,
            crate_filter,
            module_filter,
            debug_contracts,
        }
    }

    fn repeat_rounds_for_target(&self, target: &FunctionTarget<'tcx>) -> (usize, Vec<usize>) {
        match self.repeat_strategy {
            RepeatStrategy::Fixed(n) => (n, (0..=n).collect()),
            RepeatStrategy::Auto => {
                let plan = LoopSensitivityAnalyzer::new(self.tcx).analyze(target);
                let repeat = plan.repeat;
                (repeat, (0..=repeat).collect())
            }
        }
    }

    /// With `--skip-invariant`, generate verification sequences for each read method
    /// that chain through constructors and mutators.
    ///
    /// Produces sequences like:
    /// - `constructor → method`
    /// - `constructor → mutator → method`
    ///
    /// Each sequence propagates the constructor's `#[rapx::requires]` through
    /// the mutator chain to serve as entry assumptions for the read method.
    fn run_invless_sequences(&self, targets: &[FunctionTarget<'tcx>]) {
        for target in targets {
            let read_def_id = target.def_id;
            let cons = get_cons(self.tcx, read_def_id);
            if cons.is_empty() {
                continue;
            }
            let muts = get_muts(self.tcx, read_def_id);

            for &con_id in &cons {
                let con_target = self.build_virtual_target(target, read_def_id, con_id, &[]);
                self.verify_and_emit_sequence(read_def_id, &con_target, con_id, &[]);

                for &mut_id in &muts {
                    let con_target =
                        self.build_virtual_target(target, read_def_id, con_id, &[mut_id]);
                    self.verify_and_emit_sequence(
                        read_def_id,
                        &con_target,
                        con_id,
                        &[mut_id],
                    );
                }
            }
        }
    }

    fn build_virtual_target(
        &self,
        read_target: &FunctionTarget<'tcx>,
        read_def_id: rustc_hir::def_id::DefId,
        con_id: rustc_hir::def_id::DefId,
        mut_ids: &[rustc_hir::def_id::DefId],
    ) -> FunctionTarget<'tcx> {
        let mut accumulated_requires: Vec<Property<'tcx>> = Vec::new();

        // Start with the constructor's requires, remapped to refer to struct
        // fields (self.field) instead of constructor parameters.
        let con_contracts: Vec<Property<'tcx>> = get_contract_from_annotation(self.tcx, con_id)
            .into_iter()
            .map(|c| remap_constructor_contract(c))
            .collect();
        accumulated_requires.extend(con_contracts);

        // Remove contracts that are invalidated by mutators
        if !mut_ids.is_empty() {
            let mut mutated_fields: Vec<usize> = Vec::new();
            for &mut_id in mut_ids {
                for field_idx in get_mutated_fields(self.tcx, mut_id) {
                    if !mutated_fields.contains(&field_idx) {
                        mutated_fields.push(field_idx);
                    }
                }
            }
            if !mutated_fields.is_empty() {
                accumulated_requires.retain(|prop| {
                    let prop_fields = property_field_indices(prop);
                    !prop_fields.iter().any(|f| mutated_fields.contains(f))
                });
            }
        }

        // Also include the read method's own caller requires (which already
        // contains struct invariants merged by build_function_target).
        // This is broader than just `get_contract_from_annotation` because
        // it propagates struct-level properties even when the method has no
        // explicit `#[rapx::requires]`.
        accumulated_requires.extend(read_target.caller_requires.clone());

        FunctionTarget {
            def_id: read_def_id,
            owner_struct_def_id: read_target.owner_struct_def_id,
            checkpoints: read_target.checkpoints.clone(),
            callee_requires: read_target.callee_requires.clone(),
            caller_requires: accumulated_requires,
            struct_invariants: Vec::new(),
            raw_ptr_deref_checks: read_target.raw_ptr_deref_checks.clone(),
            static_mut_checks: read_target.static_mut_checks.clone(),
        }
    }

    fn verify_and_emit_sequence(
        &self,
        read_def_id: rustc_hir::def_id::DefId,
        con_target: &FunctionTarget<'tcx>,
        con_id: rustc_hir::def_id::DefId,
        mut_ids: &[rustc_hir::def_id::DefId],
    ) {
        let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();

        let (_, repeat_rounds) = self.repeat_rounds_for_target(con_target);
        for repeat in repeat_rounds {
            let driver = VerifyDriver::new_with_repeat(
                self.tcx, con_target, repeat,
            );
            match crate::helpers::mir_utils::catch_panic(|| driver.verify_function()) {
                Ok(report) => {
                    rap_debug!("{}", report.describe());
                    all_results.extend(report.results);
                }
                Err(msg) => {
                    rap_warn!(
                        "Skipping constructor {} (repeat {}): {msg}",
                        self.tcx.def_path_str(con_id),
                        repeat,
                    );
                    all_results.clear();
                    break;
                }
            }
        }

        let read_name = short_fn_name(self.tcx, read_def_id);
        let con_name = short_fn_name(self.tcx, con_id);
        let mut chain_parts: Vec<String> = vec![con_name];
        for &mut_id in mut_ids {
            chain_parts.push(short_fn_name(self.tcx, mut_id));
        }
        chain_parts.push(read_name);
        let chain_label = chain_parts.join(" -> ");

        rap_info!("============================================================");
        rap_info!("[rapx::verify] sequence: {chain_label}");
        rap_info!("============================================================");

        if all_results.is_empty() {
            rap_info!("  result: SOUND (no unsafe checkpoints)");
        } else {
            emit_results_and_verdict(self.tcx, &all_results);
        }
        rap_info!("");
    }
}

impl<'tcx> Analysis for VerifyRun<'tcx> {
    /// Collect verify targets, run the staged driver, and emit a compact summary.
    ///
    /// For each target, extracts paths with increasing `postfix-repeat`
    /// levels from 0 to the configured maximum, running verification at each
    /// level. Earlier rounds use fewer loop unrollings; later rounds incrementally
    /// add deeper paths.
    fn run(&mut self) {
        // Register `#[rapx::def_contract]` proc-macro definitions from the crate.
        crate::verify::contract::def::register_contract_defs(self.tcx);

        let collector = VerifyTargetCollector::collect_all(
            self.tcx,
            self.mode,
            self.skip_invariant,
            self.crate_filter.clone(),
            self.module_filter.clone(),
        );

        if self.debug_contracts {
            self.print_contracts_debug(&collector.function_targets);
            return;
        }

        for target in &collector.function_targets {
            let target_path = fmt_fn_path_with_bounds(self.tcx, target.def_id);
            let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();

            let (planned_repeat, repeat_rounds) = self.repeat_rounds_for_target(target);

            // Phase 1: unsafe checkpoint verification
            for repeat in repeat_rounds {
                let driver = VerifyDriver::new_with_repeat(
                    self.tcx, target, repeat,
                );
                match crate::helpers::mir_utils::catch_panic(|| driver.verify_function()) {
                    Ok(report) => {
                        rap_debug!("{}", report.describe());
                        all_results.extend(report.results);
                    }
                    Err(msg) => {
                        rap_warn!(
                            "Skipping function {} (repeat {}): {msg}",
                            target_path,
                            repeat,
                        );
                        all_results.clear();
                        break;
                    }
                }
            }

            // Phase 2: struct invariant verification
            if !target.struct_invariants.is_empty() && !self.skip_invariant {
                let driver = VerifyDriver::new_with_repeat(
                    self.tcx, target, planned_repeat,
                );
                let struct_report = driver.verify_struct_invariants();
                rap_debug!("{}", struct_report.describe());
                all_results.extend(struct_report.results);
            }

            if all_results.is_empty() {
                let all_callees_skipped = !target.checkpoints.is_empty()
                    && target.checkpoints.iter().all(|ckpt| {
                        ckpt.callee.map_or(false, |callee| {
                            target
                                .callee_requires
                                .get(&callee)
                                .map_or(true, |c| c.is_empty())
                        })
                    });
                if (target.checkpoints.is_empty() || all_callees_skipped)
                    && target.raw_ptr_deref_checks.is_empty()
                    && target.static_mut_checks.is_empty()
                    && target.struct_invariants.is_empty()
                {
                    rap_info!("============================================================");
                    rap_info!("[rapx::verify] function: {target_path}");
                    rap_info!("============================================================");
                    if self.skip_invariant {
                        let cons = get_cons(self.tcx, target.def_id);
                        for con in &cons {
                            rap_info!("  + constructor: {}", self.tcx.def_path_str(*con));
                        }
                    }
                    rap_info!("  --- unsafe checkpoints ---");
                    rap_info!("      <none>");
                    rap_info!("        <none>");
                    rap_info!("  result: SOUND (no unsafe checkpoints)");
                    rap_info!("");
                }
                continue;
            }

            // When --skip-invariant is set, skip standalone emission for methods that
            // have constructors — sequences will generate dedicated entries.
            if self.skip_invariant && !get_cons(self.tcx, target.def_id).is_empty() {
                continue;
            }

            emit_verify_summary(
                self.tcx,
                &target_path,
                target.def_id,
                &all_results,
                self.skip_invariant,
            );
        }

        // Emit detected unsafe trait impls (verification deferred)
        if !collector.trait_targets.is_empty() {
            let mut trait_ids: Vec<_> = collector.trait_targets.keys().copied().collect();
            trait_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));
            for trait_def_id in trait_ids {
                let Some(trait_target) = collector.trait_targets.get(&trait_def_id) else {
                    continue;
                };
                rap_info!("============================================================");
                rap_info!(
                    "[rapx::verify] unsafe trait impl: {}",
                    self.tcx.def_path_str(trait_target.def_id)
                );
                rap_info!("============================================================");
                if let Some(self_ty) = trait_target.self_ty_def_id {
                    rap_info!("  impl for: {}", self.tcx.def_path_str(self_ty));
                }
                if trait_target.ensures.is_empty() {
                    rap_info!("  ensures: <none>");
                } else {
                    rap_info!("  ensures (implementor must satisfy):");
                    for (method_name, contracts) in &trait_target.ensures {
                        rap_info!("    fn {}:", method_name);
                        for property in dedup_compound_props(contracts.iter()) {
                            rap_info!(
                                "      - {}",
                                property.display_for_report(
                                    self.tcx,
                                    trait_target.self_ty_def_id,
                                    None,
                                )
                            );
                        }
                    }
                }
                rap_info!("  verification: deferred");
                rap_info!("");
            }
        }

        // --skip-invariant: generate constructor-mutator-method sequences
        if self.skip_invariant {
            self.run_invless_sequences(&collector.function_targets);
        }
    }

}

impl<'tcx> VerifyRun<'tcx> {
    fn print_contracts_debug(&self, targets: &[FunctionTarget<'tcx>]) {
        rap_info!("{:=<1$}", "", 76);
        rap_info!("[rapx::debug-contracts] Expanded Contract Assertions");
        rap_info!("{:=<1$}", "", 76);
        rap_info!("");

        let mut struct_groups: FxHashMap<
            rustc_hir::def_id::DefId,
            Vec<&FunctionTarget<'tcx>>,
        > = FxHashMap::default();
        let mut free_targets: Vec<&FunctionTarget<'tcx>> = Vec::new();

        for target in targets {
            if let Some(sid) = target.owner_struct_def_id {
                struct_groups.entry(sid).or_default().push(target);
            } else {
                free_targets.push(target);
            }
        }

        let mut struct_ids: Vec<_> = struct_groups.keys().copied().collect();
        struct_ids.sort_by_key(|did| self.tcx.def_path_str(*did));

        for struct_def_id in struct_ids {
            let methods = &struct_groups[&struct_def_id];
            let struct_name = self.tcx.def_path_str(struct_def_id);

            // -- Struct invariants (once) --
            let inv_target = methods
                .iter()
                .find(|t| !t.struct_invariants.is_empty());
            let have_invariants = inv_target.is_some();

            if have_invariants || methods.iter().any(|t| {
                self.has_printable_contracts(t)
            }) {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("[rapx::debug-contracts] struct: {struct_name}");
                rap_info!("{:=<1$}", "", 76);
            }

            if let Some(tgt) = inv_target {
                rap_info!("  [Struct Invariants]:");
                let invariants = dedup_compound_props(tgt.struct_invariants.iter());
                let inv_count = invariants.len();
                for (ii, property) in invariants.iter().enumerate() {
                    let ibranch = if ii + 1 == inv_count { "`-" } else { "|-" };
                    let (call, meaning) = fmt_contract_expanded(
                        self.tcx,
                        property,
                        tgt.owner_struct_def_id,
                        Some(tgt.def_id),
                    );
                    self.print_contract_lines("  ", &ibranch, &call, &meaning);
                }
                rap_info!("");
            }

            // -- Each method --
            let mut printed = false;
            for (mi, target) in methods.iter().enumerate() {
                let is_last_method = mi + 1 == methods.len();
                let branch = if is_last_method { "`-" } else { "|-" };
                let cont = if is_last_method { "  " } else { "| " };
                if self.print_target_contracts(target, branch, cont) {
                    printed = true;
                }
            }
            if printed {
                rap_info!("{:=<1$}", "", 76);
                rap_info!("");
            }
        }

        // -- Free functions --
        for target in &free_targets {
            self.print_target_contracts(target, "- ", "  ");
        }
    }

    fn has_printable_contracts(&self, target: &FunctionTarget<'tcx>) -> bool {
        use crate::verify::contract::PropertyKind;
        let is_unsafe_fn = self
            .tcx
            .fn_sig(target.def_id)
            .skip_binder()
            .safety()
            == rustc_hir::Safety::Unsafe;
        let has_caller = is_unsafe_fn
            && target
                .caller_requires
                .iter()
                .any(|p| p.kind() != Some(PropertyKind::Unknown));
        if has_caller {
            return true;
        }
        target.callee_requires.values().any(|c| {
            c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown))
        })
    }

    fn print_contract_lines(&self, prefix: &str, branch: &str, call: &str, meaning: &str) {
        rap_info!("{prefix}{branch} {call}");
        let cont = if branch == "`-" { "  " } else { "| " };
        for line in meaning.lines() {
            rap_info!("{prefix}{cont} {line}");
        }
    }

    fn print_target_contracts(
        &self,
        target: &FunctionTarget<'tcx>,
        branch: &str,
        cont: &str,
    ) -> bool {
        use crate::verify::contract::PropertyKind;

        let (arg_names_typed, ret_ty) = self.resolve_arg_names_with_types(target.def_id);
        let is_unsafe_fn = self
            .tcx
            .fn_sig(target.def_id)
            .skip_binder()
            .safety()
            == rustc_hir::Safety::Unsafe;

        let target_path = fmt_fn_path_with_generics(self.tcx, target.def_id);
        let short_name = crate::helpers::name::short_fn_name(self.tcx, target.def_id);

        // Collect what to print first
        let has_caller = is_unsafe_fn
            && target
                .caller_requires
                .iter()
                .any(|p| p.kind() != Some(PropertyKind::Unknown));
        let mut callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        callee_ids.retain(|did| {
            target
                .callee_requires
                .get(did)
                .is_some_and(|c| c.iter().any(|p| p.kind() != Some(PropertyKind::Unknown)))
        });
        callee_ids.sort_by_key(|did| self.tcx.def_path_str(*did));
        let has_callees = !callee_ids.is_empty();

        if !has_caller && !has_callees {
            return false;
        }

        let fn_display = fmt_fn_with_params(&target_path, &arg_names_typed, ret_ty.as_deref());
        let header = format!("--- method: {short_name}");
        let dashes = 72usize.saturating_sub(header.len());
        rap_info!("{branch} {header} {}", "-".repeat(dashes));
        rap_info!("{cont}  {fn_display}");

        // Caller Contracts (only for unsafe functions)
        if has_caller {
            rap_info!("{cont}  [Caller Contracts]:");
            let caller_props = dedup_compound_props(
                target
                    .caller_requires
                    .iter()
                    .filter(|p| p.kind() != Some(PropertyKind::Unknown)),
            );
            for (pi, property) in caller_props.iter().enumerate() {
                let is_last = pi + 1 == caller_props.len();
                let pbranch = if is_last { "`-" } else { "|-" };
                let (call, meaning) = fmt_contract_expanded(
                    self.tcx,
                    property,
                    target.owner_struct_def_id,
                    Some(target.def_id),
                );
                self.print_contract_lines(
                    &format!("{cont}  "),
                    pbranch,
                    &call,
                    &meaning,
                );
            }
            if !has_callees {
                rap_info!("");
            }
        }

        // Callee Contracts (for each unsafe callee)
        if has_callees {
            rap_info!("{cont}  [Unsafe Callees]:");
            for (ci, &callee_id) in callee_ids.iter().enumerate() {
                let is_last_callee = ci + 1 == callee_ids.len();
                let cbranch = if is_last_callee { "`-" } else { "|-" };
                let ccont = if is_last_callee { "  " } else { "| " };
                let contracts = target.callee_requires.get(&callee_id).unwrap();
                let (callee_typed, callee_ret) =
                    self.resolve_arg_names_with_types(callee_id);
                let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                rap_info!(
                    "{cont}  {cbranch} {}",
                    fmt_fn_with_params(
                        &callee_path,
                        &callee_typed,
                        callee_ret.as_deref()
                    )
                );
                let props = dedup_compound_props(
                    contracts
                        .iter()
                        .filter(|p| p.kind() != Some(PropertyKind::Unknown)),
                );
                for (pi, property) in props.iter().enumerate() {
                    let is_last_prop = pi + 1 == props.len();
                    let pbranch = if is_last_prop { "`-" } else { "|-" };
                    let (call, meaning) = fmt_contract_expanded(
                        self.tcx,
                        property,
                        None,
                        Some(callee_id),
                    );
                    self.print_contract_lines(
                        &format!("{cont}  {ccont}"),
                        pbranch,
                        &call,
                        &meaning,
                    );
                }
            }
        }

        rap_info!("");
        true
    }

    fn resolve_arg_names_with_types(
        &self,
        def_id: rustc_hir::def_id::DefId,
    ) -> (Vec<String>, Option<String>) {
        if !self.tcx.is_mir_available(def_id) {
            return (Vec::new(), None);
        }
        let body = self.tcx.optimized_mir(def_id);
        let args: Vec<String> = body
            .local_decls
            .iter()
            .enumerate()
            .skip(1)
            .take(body.arg_count)
            .map(|(i, decl)| {
                let name = {
                    let span = decl.source_info.span;
                    self.tcx
                        .sess
                        .source_map()
                        .span_to_snippet(span)
                        .unwrap_or_else(|_| format!("_{}", i))
                };
                let ty = decl.ty.to_string();
                format!("{name}: {ty}")
            })
            .collect();
        let ret_ty = self.tcx.fn_sig(def_id).skip_binder().output().skip_binder();
        let ret_ty = if ret_ty.is_unit() {
            None
        } else {
            Some(ret_ty.to_string())
        };
        (args, ret_ty)
    }
}

use crate::helpers::name::short_fn_name;

/// Return true when two properties have the same kind.
/// Collect struct field indices referenced by a property's contract places.
///
/// Used to determine which invariants are invalidated when a mutator writes
/// to specific struct fields.
fn property_field_indices(property: &crate::verify::contract::Property<'_>) -> Vec<usize> {
    use crate::verify::contract::{ContractExpr, PropertyArg};
    let mut indices = Vec::new();
    for arg in property.args() {
        let place = match arg {
            PropertyArg::Expr(ContractExpr::Place(p)) => Some(p),
            _ => None,
        };
        if let Some(place) = place {
            for proj in &place.projections {
                match proj {
                    crate::verify::contract::ContractProjection::Field { index, .. } => {
                        let idx = *index;
                        if !indices.contains(&idx) {
                            indices.push(idx);
                        }
                    }
                    crate::verify::contract::ContractProjection::Downcast { .. } => {}
                    crate::verify::contract::ContractProjection::IterElements => {}
                }
            }
        }
    }
    indices
}

fn remap_constructor_contract<'tcx>(
    property: crate::verify::contract::Property<'tcx>,
) -> crate::verify::contract::Property<'tcx> {
    use crate::verify::contract::{
        ContractExpr, ContractPlace, ContractProjection, PlaceBase, PropertyArg,
    };

    fn remap_place_arg<'tcx>(arg: &PropertyArg<'tcx>) -> PropertyArg<'tcx> {
        let place = match arg {
            PropertyArg::Expr(ContractExpr::Place(p)) => p,
            _ => return arg.clone(),
        };
        let PlaceBase::Arg(field_idx) = place.base else {
            return arg.clone();
        };
        let projection = ContractProjection::Field {
            index: field_idx,
            ty: None,
        };
        let mut new_place = ContractPlace {
            base: PlaceBase::Arg(0),
            projections: vec![projection],
        };
        new_place
            .projections
            .extend(place.projections.iter().cloned());
        PropertyArg::Expr(ContractExpr::Place(new_place))
    }

    let new_args: Vec<PropertyArg<'tcx>> = property
        .args()
        .iter()
        .map(|arg| remap_place_arg(arg))
        .collect();

    match property {
        crate::verify::contract::Property::Leaf(mut leaf) => {
            leaf.args = new_args;
            crate::verify::contract::Property::Leaf(leaf)
        }
        crate::verify::contract::Property::Or(or) => crate::verify::contract::Property::Or(or),
    }
}
