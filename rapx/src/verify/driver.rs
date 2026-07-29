//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! `VerifyDriver` prepares paths for two kinds of checks (unsafe checkpoints and
//! struct invariants) and delegates the actual backward/forward/SMT work to
//! the shared `VerifyEngine`.

use crate::analysis::Analysis;
use crate::analysis::path_analysis::{
    PathTree,
    graph::{PathEnumerator, PathGraph},
};
use crate::cli::VerifyMode;
use crate::helpers::fn_info::{FnKind, get_cons, get_mutated_fields, get_muts, get_type};
use crate::verify::contract::PropertyKind;
use crate::verify::target::get_contract_from_annotation;

use crate::compat::{FxHashMap, FxHashSet};
use indexmap::IndexMap;
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::TyCtxt;

use super::{
    contract::Property,
    display::{
        emit_lines, emit_property_rows, emit_verify_summary, fmt_contract_expanded,
        fmt_fn_path_with_generics, fmt_fn_with_params,
    },
    engine::VerifyEngine,
    loop_sensitivity::{LoopSensitivityAnalyzer, RepeatStrategy},
    path_extractor::{CallGroup, PATH_LIMIT, PathExtractor},
    report::{PropertyCheckResult, VerificationReport, VisitDiagnostics},
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
    /// Compiler type-context handle — gateway to MIR bodies, type definitions,
    /// HIR attributes, and def-path strings used throughout the pipeline.
    tcx: TyCtxt<'tcx>,

    /// The function being verified: its identity (`def_id`), the unsafe
    /// operations inside it (`checkpoints`, `raw_ptr_deref_checks`), the
    /// contracts those operations demand (`callee_requires`), the contracts
    /// the function itself requires as entry assumptions
    /// (`caller_requires`), and any struct invariants to be enforced
    /// (`struct_invariants`).
    target: &'target FunctionTarget<'tcx>,

    /// SCC-aware path metadata for this function.
    ///
    /// Per-callee call groups with shared path trees.
    path_info: Vec<CallGroup<'tcx>>,

    /// Stateless three-stage verification pipeline: backward data-dependency
    /// analysis → forward state simulation → SMT constraint checking.
    /// Shared across all (checkpoint, path, property) triples for this target.
    engine: VerifyEngine<'tcx>,

    /// Loop-unrolling depth for SCC-aware path enumeration.
    ///
    /// Controls how many **extra** times a repeated SCC postfix segment
    /// (loop-body) is allowed to appear beyond its first occurrence.
    /// - `0` = each distinct postfix segment at most once (no loop repeats).
    /// - `1` = allow one repeat (loop body appears up to twice).
    /// - `n` = allow n repeats (loop body appears up to n+1 times).
    ///
    /// Higher values increase path coverage but risk exponential blow-up in
    /// path count.  The CLI driver iterates `repeat` from 0 to the configured
    /// maximum, accumulating results incrementally.
    allow_repeat: usize,
}

impl<'target, 'tcx> VerifyDriver<'target, 'tcx> {
    /// Build a driver for one collected function target.
    pub fn new(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>) -> Self {
        Self::new_with_repeat(tcx, target, 0)
    }

    /// Build a driver with control over SCC postfix repeat count.
    pub fn new_with_repeat(
        tcx: TyCtxt<'tcx>,
        target: &'target FunctionTarget<'tcx>,
        allow_repeat: usize,
    ) -> Self {
        let all_checkpoints: Vec<_> = target.all_checkpoints().into_iter().cloned().collect();
        let path_info = PathExtractor::new(tcx, target.def_id, all_checkpoints, allow_repeat).run();
        let engine = VerifyEngine::new(tcx);
        Self {
            tcx,
            target,
            path_info,
            engine,
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
            for (property_index, property) in view.properties.iter().enumerate() {
                if property.kind == PropertyKind::Or {
                    self.check_or_property(&mut report, &view, property_index, property);
                } else {
                    let bulk = self.engine.check_callsite_from_tree(
                        view.tree,
                        view.checkpoint,
                        property,
                        &self.target.caller_requires,
                    );
                    for (path_index, (forward, smt_check)) in bulk.iter().enumerate() {
                        let check_diagnostics =
                            format!("{}\n{}", forward.describe(), smt_check.describe());
                        report.push(PropertyCheckResult {
                            checkpoint: view.checkpoint.location(),
                            checkpoint_index: view.checkpoint_index,
                            path_index,
                            property_index,
                            property: property.clone(),
                            result: smt_check.result.clone(),
                            diagnostics: Some(VisitDiagnostics::new(
                                String::new(),
                                check_diagnostics,
                            )),
                            path_description: forward.path.describe_indices(),
                            callee_name: view.checkpoint.callee_name(self.tcx),
                        });
                    }
                }
            }
        }

        report
    }

    /// Check an `Or` property by trying each alternative group.
    /// At least one group must be fully proved on each path for the OR to hold.
    fn check_or_property(
        &self,
        report: &mut VerificationReport<'tcx>,
        view: &CheckpointCheckView<'_, '_, 'tcx>,
        property_index: usize,
        or_property: &Property<'tcx>,
    ) {
        use crate::verify::report::CheckResult;

        let num_groups = or_property.or_alternatives.len();
        let mut best_per_path: Vec<Option<(usize, super::smt_check::SmtCheckResult, String)>> =
            Vec::new();

        for (group_idx, group) in or_property.or_alternatives.iter().enumerate() {
            let mut group_proved = true;

            for sub_prop in group.iter() {
                let bulk = self.engine.check_callsite_from_tree(
                    view.tree,
                    view.checkpoint,
                    sub_prop,
                    &self.target.caller_requires,
                );
                if best_per_path.is_empty() {
                    best_per_path.resize(bulk.len(), None);
                }
                for (path_idx, (_forward, smt)) in bulk.iter().enumerate() {
                    if !matches!(smt.result, CheckResult::Proved) {
                        group_proved = false;
                    }
                    let better = match &best_per_path[path_idx] {
                        None => true,
                        Some((_, existing, _)) => {
                            matches!(smt.result, CheckResult::Proved)
                                && !matches!(existing.result, CheckResult::Proved)
                        }
                    };
                    if better {
                        let desc = format!("OR group {}/{}", group_idx + 1, num_groups,);
                        best_per_path[path_idx] = Some((group_idx, smt.clone(), desc));
                    }
                }
            }

            if group_proved {
                let desc = format!(
                    "OR group {}/{} ({} sub-properties all proved)",
                    group_idx + 1,
                    num_groups,
                    group.len(),
                );
                report.push(PropertyCheckResult {
                    checkpoint: view.checkpoint.location(),
                    checkpoint_index: view.checkpoint_index,
                    path_index: 0,
                    property_index,
                    property: or_property.clone(),
                    result: CheckResult::Proved,
                    diagnostics: Some(VisitDiagnostics::new(String::new(), desc)),
                    path_description: format!("group-{}/{}", group_idx + 1, num_groups),
                    callee_name: view.checkpoint.callee_name(self.tcx),
                });
                return;
            }
        }

        // No group was fully proved — report the best attempt per path.
        for (path_idx, best) in best_per_path.iter().enumerate() {
            if let Some((group_idx, smt, path_desc)) = best {
                report.push(PropertyCheckResult {
                    checkpoint: view.checkpoint.location(),
                    checkpoint_index: view.checkpoint_index,
                    path_index: path_idx,
                    property_index,
                    property: or_property.clone(),
                    result: smt.result.clone(),
                    diagnostics: Some(VisitDiagnostics::new(
                        String::new(),
                        format!(
                            "OR: best effort group {}/{} did not prove",
                            group_idx + 1,
                            num_groups,
                        ),
                    )),
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

        let entry_facts: Vec<BackwardItem<'tcx>> = if is_constructor {
            caller_contracts
                .iter()
                .filter(|c| !matches!(c.kind, PropertyKind::Unknown))
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

                for (path_index, check) in results.iter().enumerate() {
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
                        result: check.result.clone(),
                        diagnostics: Some(VisitDiagnostics::new(
                            check.slicing_diag.clone(),
                            check.verification_diag.clone(),
                        )),
                        path_description,
                        callee_name: format!("struct-invariant(bb{})", checkpoint.block.as_usize()),
                    });
                }
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
            let driver = VerifyDriver::new_with_repeat(self.tcx, con_target, repeat);
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

        let unproved = all_results
            .iter()
            .filter(|r| {
                if r.property.contract_kind == crate::verify::contract::ContractKind::Hazard
                    || r.property.contract_kind == crate::verify::contract::ContractKind::Option_
                {
                    return false;
                }
                !matches!(r.result, super::report::CheckResult::Proved)
            })
            .count();

        let mut groups: IndexMap<(CheckpointLocation, String), Vec<&PropertyCheckResult<'_>>> =
            IndexMap::new();
        for r in &all_results {
            groups
                .entry((r.checkpoint, r.callee_name.clone()))
                .or_default()
                .push(r);
        }

        let checkpoint_groups: Vec<_> = groups
            .iter()
            .filter(|((_, name), _)| !name.starts_with("struct-invariant"))
            .collect();

        if !checkpoint_groups.is_empty() {
            rap_info!("  --- unsafe checkpoints ---");
            for ((checkpoint, callee_name), results) in &checkpoint_groups {
                rap_info!(
                    "      unsafe checkpoint: bb{} -> {callee_name}",
                    checkpoint.block.as_usize(),
                );
                emit_property_rows(results);
            }
        }

        if all_results.is_empty() {
            rap_info!("  result: SOUND (no unsafe checkpoints)");
        } else if unproved == 0 {
            rap_info!(green, "  result: SOUND");
        } else {
            rap_warn!("  result: UNSOUND ({unproved} unproved)");
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
        let mut collector = VerifyTargetCollector::new(
            self.tcx,
            self.mode,
            self.skip_invariant,
            self.crate_filter.clone(),
            self.module_filter.clone(),
        );
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);
        collector.check_module_filter_result();

        if self.debug_contracts {
            self.print_contracts_debug(&collector.function_targets);
            return;
        }

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();

            let (planned_repeat, repeat_rounds) = self.repeat_rounds_for_target(target);

            // Phase 1: unsafe checkpoint verification
            for repeat in repeat_rounds {
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
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
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, planned_repeat);
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
                        for property in contracts {
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
        use crate::compat::FxHashSet;
        use crate::verify::contract::PropertyKind;

        rap_info!("============================================================");
        rap_info!("[rapx::debug-contracts] Expanded Contract Assertions");
        rap_info!("============================================================");
        rap_info!("");

        let mut global_seen = FxHashSet::default();
        let mut global_seen_callees = FxHashSet::default();

        for target in targets {
            let local_names = self.resolve_local_names(target.def_id);
            let (arg_names_typed, ret_ty) = self.resolve_arg_names_with_types(target.def_id);
            let has_caller = target
                .caller_requires
                .iter()
                .any(|p| p.kind != PropertyKind::Unknown);
            let has_inv = !target.struct_invariants.is_empty();

            if has_caller || has_inv {
                let mut lines: Vec<(String, String)> = Vec::new();
                let mut seen_kinds = FxHashSet::default();

                for property in &target.caller_requires {
                    if property.kind != PropertyKind::Unknown {
                        lines.push(fmt_contract_expanded(
                            self.tcx,
                            &local_names,
                            property,
                            target.owner_struct_def_id,
                        ));
                        seen_kinds.insert(property.kind.clone());
                    }
                }

                for property in &target.struct_invariants {
                    lines.push(fmt_contract_expanded(
                        self.tcx,
                        &local_names,
                        property,
                        target.owner_struct_def_id,
                    ));
                }

                self.append_callee_contracts(
                    &target,
                    &mut lines,
                    &mut seen_kinds,
                    &mut global_seen_callees,
                );

                if lines.is_empty() {
                    continue;
                }

                let target_path = fmt_fn_path_with_generics(self.tcx, target.def_id);
                rap_info!(
                    "{}",
                    fmt_fn_with_params(&target_path, &arg_names_typed, ret_ty.as_deref())
                );
                rap_info!("{:-<1$}", "", 76);
                emit_lines(&lines);
                rap_info!("{:-<1$}", "", 76);
                rap_info!("");
            } else {
                let mut callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
                callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));
                let mut first_callee = true;
                for callee_id in callee_ids {
                    if !global_seen_callees.insert(callee_id) {
                        continue;
                    }
                    let callee_names = self.resolve_local_names(callee_id);
                    let (callee_typed, callee_ret) = self.resolve_arg_names_with_types(callee_id);
                    if let Some(contracts) = target.callee_requires.get(&callee_id) {
                        let mut lines: Vec<(String, String)> = Vec::new();
                        for property in contracts {
                            if property.kind != PropertyKind::Unknown
                                && global_seen.insert(property.kind.clone())
                            {
                                lines.push(fmt_contract_expanded(
                                    self.tcx,
                                    &callee_names,
                                    property,
                                    None,
                                ));
                            }
                        }
                        if !lines.is_empty() {
                            if !first_callee {
                                rap_info!("");
                            }
                            first_callee = false;
                            let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                            rap_info!(
                                "{}",
                                fmt_fn_with_params(
                                    &callee_path,
                                    &callee_typed,
                                    callee_ret.as_deref()
                                )
                            );
                            rap_info!("{:-<1$}", "", 76);
                            emit_lines(&lines);
                            rap_info!("{:-<1$}", "", 76);
                            rap_info!("");
                        }
                    }
                }
            }
        }
    }

    fn append_callee_contracts(
        &self,
        target: &FunctionTarget<'tcx>,
        lines: &mut Vec<(String, String)>,
        seen_kinds: &mut crate::compat::FxHashSet<crate::verify::contract::PropertyKind>,
        global_seen_callees: &mut crate::compat::FxHashSet<rustc_hir::def_id::DefId>,
    ) {
        use crate::compat::FxHashSet;
        use crate::verify::contract::PropertyKind;
        let mut callee_ids: Vec<_> = target.callee_requires.keys().copied().collect();
        callee_ids.sort_by_key(|def_id| self.tcx.def_path_str(*def_id));
        for callee_id in callee_ids {
            if !global_seen_callees.insert(callee_id) {
                continue;
            }
            let callee_names = self.resolve_local_names(callee_id);
            if let Some(contracts) = target.callee_requires.get(&callee_id) {
                let mut callee_seen = FxHashSet::default();
                let mut callee_lines: Vec<(String, String)> = Vec::new();
                for property in contracts {
                    if property.kind != PropertyKind::Unknown
                        && !seen_kinds.contains(&property.kind)
                        && callee_seen.insert(property.kind.clone())
                    {
                        callee_lines.push(fmt_contract_expanded(
                            self.tcx,
                            &callee_names,
                            property,
                            None,
                        ));
                    }
                }
                if !callee_lines.is_empty() {
                    let (callee_typed, callee_ret) = self.resolve_arg_names_with_types(callee_id);
                    let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                    let header =
                        fmt_fn_with_params(&callee_path, &callee_typed, callee_ret.as_deref());
                    lines.push((format!("[{header}]"), String::new()));
                    lines.extend(callee_lines);
                }
            }
        }
    }

    fn resolve_local_names(&self, def_id: rustc_hir::def_id::DefId) -> Vec<String> {
        if !self.tcx.is_mir_available(def_id) {
            return Vec::new();
        }
        let body = self.tcx.optimized_mir(def_id);
        body.local_decls
            .iter()
            .enumerate()
            .map(|(i, decl)| {
                let span = decl.source_info.span;
                self.tcx
                    .sess
                    .source_map()
                    .span_to_snippet(span)
                    .unwrap_or_else(|_| format!("_{}", i))
            })
            .collect()
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

/// Extract the last segment of a def-path (the bare function name).
fn short_fn_name(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> String {
    let path = tcx.def_path_str(def_id);
    path.rsplit("::").next().unwrap_or(&path).to_string()
}

/// Return true when two properties have the same kind.
/// Collect struct field indices referenced by a property's contract places.
///
/// Used to determine which invariants are invalidated when a mutator writes
/// to specific struct fields.
fn property_field_indices(property: &crate::verify::contract::Property<'_>) -> Vec<usize> {
    use crate::verify::contract::{ContractExpr, PropertyArg};
    let mut indices = Vec::new();
    for arg in &property.args {
        let place = match arg {
            PropertyArg::Place(p) => Some(p),
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
            PropertyArg::Place(p) => p,
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
        match arg {
            PropertyArg::Place(_) => PropertyArg::Place(new_place),
            PropertyArg::Expr(_) => PropertyArg::Expr(ContractExpr::Place(new_place)),
            _ => unreachable!(),
        }
    }

    let new_args: Vec<PropertyArg<'tcx>> = property
        .args
        .iter()
        .map(|arg| remap_place_arg(arg))
        .collect();

    crate::verify::contract::Property {
        args: new_args,
        ..property
    }
}
