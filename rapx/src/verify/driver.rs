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
use std::panic::{AssertUnwindSafe, catch_unwind};

use super::{
    contract::Property,
    engine::VerifyEngine,
    helpers::{Checkpoint, CheckpointKind, CheckpointLocation, collect_return_block_indices},
    path_extractor::{CallGroup, PATH_LIMIT, PathExtractor},
    report::{PropertyCheckResult, VerificationReport, VisitDiagnostics},
    slicer::BackwardItem,
    target::{FunctionTarget, VerifyTargetCollector},
};

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
        let mut all_checkpoints = target.checkpoints.clone();
        for (checkpoint, _) in &target.raw_ptr_deref_checks {
            all_checkpoints.push(checkpoint.clone());
        }
        for (checkpoint, _) in &target.static_mut_checks {
            all_checkpoints.push(checkpoint.clone());
        }
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
                        diagnostics: Some(VisitDiagnostics::new(String::new(), check_diagnostics)),
                        path_description: forward.path.describe_indices(),
                        callee_name: view.checkpoint.callee_name(self.tcx),
                    });
                }
            }
        }

        report
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
        let loc = checkpoint.location();
        match checkpoint.kind {
            CheckpointKind::RawPtrDeref => {
                for (cs, props) in &self.target.raw_ptr_deref_checks {
                    if cs.location() == loc {
                        return props.as_slice();
                    }
                }
                &[]
            }
            CheckpointKind::StaticMutAccess => {
                for (cs, props) in &self.target.static_mut_checks {
                    if cs.location() == loc {
                        return props.as_slice();
                    }
                }
                &[]
            }
            CheckpointKind::UnsafeCall => {
                if let Some(callee) = checkpoint.callee {
                    self.target
                        .callee_requires
                        .get(&callee)
                        .map(Vec::as_slice)
                        .unwrap_or(&[])
                } else {
                    &[]
                }
            }
        }
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

            for (property_index, invariant) in invariants.iter().enumerate() {
                let results = self.engine.check_invariant_from_tree(
                    self.target.def_id,
                    &tree,
                    checkpoint,
                    invariant,
                    &entry_facts,
                );

                for (path_index, check) in results.iter().enumerate() {
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
                        path_description: String::new(),
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
    postfix_repeat: usize,
    mode: VerifyMode,
    crate_filter: Option<String>,
    module_filter: Option<String>,
    debug_contracts: bool,
}

impl<'tcx> VerifyRun<'tcx> {
    /// Create the default verify pass for the current compiler type context.
    pub fn new(
        tcx: TyCtxt<'tcx>,
        postfix_repeat: usize,
        mode: VerifyMode,
        crate_filter: Option<String>,
        module_filter: Option<String>,
        debug_contracts: bool,
    ) -> Self {
        Self {
            tcx,
            postfix_repeat,
            mode,
            crate_filter,
            module_filter,
            debug_contracts,
        }
    }

    /// In invless mode, generate verification sequences for each read method
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
                self.verify_and_emit_sequence(target, read_def_id, &con_target, con_id, &[], 0);

                for (mut_idx, &mut_id) in muts.iter().enumerate() {
                    let con_target =
                        self.build_virtual_target(target, read_def_id, con_id, &[mut_id]);
                    self.verify_and_emit_sequence(
                        target,
                        read_def_id,
                        &con_target,
                        con_id,
                        &[mut_id],
                        1 + mut_idx,
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

        // Start with the constructor's requires
        let con_contracts = get_contract_from_annotation(self.tcx, con_id);
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

        // Also include the read method's own requires
        let own_requires = get_contract_from_annotation(self.tcx, read_def_id);
        for req in own_requires {
            if !accumulated_requires.iter().any(|p| same_property(p, &req)) {
                accumulated_requires.push(req);
            }
        }

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
        _read_target: &FunctionTarget<'tcx>,
        read_def_id: rustc_hir::def_id::DefId,
        con_target: &FunctionTarget<'tcx>,
        con_id: rustc_hir::def_id::DefId,
        mut_ids: &[rustc_hir::def_id::DefId],
        _seq_index: usize,
    ) {
        let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();

        for repeat in 0..=self.postfix_repeat {
            let driver = VerifyDriver::new_with_repeat(self.tcx, con_target, repeat);
            let result = catch_unwind(AssertUnwindSafe(|| driver.verify_function()));
            match result {
                Ok(report) => {
                    rap_debug!("{}", report.describe());
                    all_results.extend(report.results);
                }
                Err(e) => {
                    let msg = e
                        .downcast_ref::<String>()
                        .map(|s| s.as_str())
                        .or_else(|| e.downcast_ref::<&str>().copied())
                        .unwrap_or("<rustc ICE>");
                    rap_warn!(
                        "Skipping invless constructor {} (repeat {}): {}",
                        self.tcx.def_path_str(con_id),
                        repeat,
                        msg
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
            .filter(|r| !matches!(r.result, super::report::CheckResult::Proved))
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

        if unproved == 0 && !all_results.is_empty() {
            rap_info!(green, "  result: SOUND");
        } else {
            rap_warn!("  result: UNSOUND ({unproved} unproved)");
        }
        rap_info!("");
    }
}

impl<'tcx> Analysis for VerifyRun<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Driver"
    }

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

            // Phase 1: unsafe checkpoint verification
            for repeat in 0..=self.postfix_repeat {
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let result = catch_unwind(AssertUnwindSafe(|| driver.verify_function()));
                match result {
                    Ok(report) => {
                        rap_debug!("{}", report.describe());
                        all_results.extend(report.results);
                    }
                    Err(e) => {
                        let msg = e
                            .downcast_ref::<String>()
                            .map(|s| s.as_str())
                            .or_else(|| e.downcast_ref::<&str>().copied())
                            .unwrap_or("<rustc ICE>");
                        rap_warn!(
                            "Skipping function {} (repeat {}): {}",
                            target_path,
                            repeat,
                            msg
                        );
                        all_results.clear();
                        break;
                    }
                }
            }

            // Phase 1.5: InBound loop-depth detector
            //
            // When postfix_repeat == 0, a loop body appears at most once per path,
            // which can miss off-by-one bugs that only manifest on later iterations.
            //
            // The detector tries progressively deeper unrolling and tracks the
            // set of Proved InBound properties at each level.  Three stopping criteria:
            //
            //  1. Unproven InBound found → unsound, propagate results, stop.
            //  2. State converged (same Proven set as a previous level) → stop.
            //  3. State oscillates (Proven set alternates between two states) → stop.
            const MAX_LOOP_INBOUND_UNROLL: usize = 16;

            if self.postfix_repeat == 0 && !all_results.is_empty() {
                let has_inbound = all_results
                    .iter()
                    .any(|r| matches!(r.property.kind, PropertyKind::InBound));
                let all_inbound_proven = all_results
                    .iter()
                    .filter(|r| matches!(r.property.kind, PropertyKind::InBound))
                    .all(|r| matches!(r.result, super::report::CheckResult::Proved));

                if has_inbound && all_inbound_proven {
                    // Proven-set history: each entry is a sorted vector of
                    // (checkpoint_index, property_index) for Proved InBound results.
                    let mut proven_history: Vec<Vec<(usize, usize)>> = Vec::new();

                    // Seed with the repeat=0 Proven set.
                    let seed: Vec<_> = {
                        let mut v: Vec<_> = all_results
                            .iter()
                            .filter(|r| {
                                matches!(r.property.kind, PropertyKind::InBound)
                                    && matches!(r.result, super::report::CheckResult::Proved)
                            })
                            .map(|r| (r.checkpoint_index, r.property_index))
                            .collect();
                        v.sort();
                        v
                    };
                    proven_history.push(seed);

                    for repeat in 1..=MAX_LOOP_INBOUND_UNROLL {
                        let detector_driver =
                            VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                        let result =
                            catch_unwind(AssertUnwindSafe(|| detector_driver.verify_function()));
                        match result {
                            Ok(report) => {
                                // Collect genuinely non-Proved InBound (excluding
                                // SMT precision-loss noise).
                                let current_unproven: FxHashSet<_> = report
                                    .results
                                    .iter()
                                    .filter(|r| {
                                        matches!(r.property.kind, PropertyKind::InBound)
                                            && !matches!(
                                                r.result,
                                                super::report::CheckResult::Proved
                                            )
                                            && !r.diagnostics.as_ref().is_some_and(|d| {
                                                d.forward.contains("path has precision loss")
                                                    || d.forward.contains("could not connect")
                                            })
                                    })
                                    .map(|r| (r.checkpoint_index, r.property_index))
                                    .collect();

                                // Pattern 1: violation found.
                                if !current_unproven.is_empty() {
                                    all_results.extend(report.results);
                                    break;
                                }

                                // Collect Proven InBound set for this level.
                                let mut current_proven: Vec<_> = report
                                    .results
                                    .iter()
                                    .filter(|r| {
                                        matches!(r.property.kind, PropertyKind::InBound)
                                            && matches!(
                                                r.result,
                                                super::report::CheckResult::Proved
                                            )
                                    })
                                    .map(|r| (r.checkpoint_index, r.property_index))
                                    .collect();
                                current_proven.sort();

                                // Pattern 2: same Proven set as any prior level.
                                if proven_history.contains(&current_proven) {
                                    break;
                                }

                                // Pattern 3: oscillation — alternation between two sets.
                                let len = proven_history.len();
                                if len >= 3
                                    && proven_history[len - 1] == proven_history[len - 3]
                                    && current_proven == proven_history[len - 2]
                                {
                                    break;
                                }

                                proven_history.push(current_proven);
                            }
                            Err(_) => break,
                        }
                    }
                }
            }

            // Phase 2: struct invariant verification
            if !target.struct_invariants.is_empty() && !matches!(self.mode, VerifyMode::Invless) {
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, self.postfix_repeat);
                let struct_report = driver.verify_struct_invariants();
                rap_debug!("{}", struct_report.describe());
                all_results.extend(struct_report.results);
            }

            if all_results.is_empty() {
                if target.checkpoints.is_empty()
                    && target.raw_ptr_deref_checks.is_empty()
                    && target.static_mut_checks.is_empty()
                    && target.struct_invariants.is_empty()
                {
                    rap_info!("============================================================");
                    rap_info!("[rapx::verify] function: {target_path}");
                    rap_info!("============================================================");
                    if matches!(self.mode, VerifyMode::Invless) {
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

            // In invless mode, skip standalone emission for methods that
            // have constructors — sequences will generate dedicated entries.
            if matches!(self.mode, VerifyMode::Invless)
                && !get_cons(self.tcx, target.def_id).is_empty()
            {
                continue;
            }

            emit_verify_summary(
                self.tcx,
                &target_path,
                target.def_id,
                &all_results,
                self.mode,
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
                            rap_info!("      - {:?}, args={:?}", property.kind, property.args);
                        }
                    }
                }
                rap_info!("  verification: deferred");
                rap_info!("");
            }
        }

        // Invless mode: generate constructor-mutator-method sequences
        if matches!(self.mode, VerifyMode::Invless) {
            self.run_invless_sequences(&collector.function_targets);
        }
    }

    fn reset(&mut self) {}
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
            let arg_names = self.resolve_arg_names(target.def_id);
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
                        lines.push(fmt_contract_expanded(self.tcx, &local_names, property));
                        seen_kinds.insert(property.kind.clone());
                    }
                }

                for property in &target.struct_invariants {
                    lines.push(fmt_contract_expanded(self.tcx, &local_names, property));
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
                rap_info!("{}", fmt_fn_with_params(&target_path, &arg_names_typed, ret_ty.as_deref()));
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
                                ));
                            }
                        }
                        if !lines.is_empty() {
                            if !first_callee {
                                rap_info!("");
                            }
                            first_callee = false;
                            let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                            rap_info!("{}", fmt_fn_with_params(&callee_path, &callee_typed, callee_ret.as_deref()));
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
                        callee_lines.push(fmt_contract_expanded(self.tcx, &callee_names, property));
                    }
                }
                if !callee_lines.is_empty() {
                    let (callee_typed, callee_ret) = self.resolve_arg_names_with_types(callee_id);
                    let callee_path = fmt_fn_path_with_generics(self.tcx, callee_id);
                    let header = fmt_fn_with_params(&callee_path, &callee_typed, callee_ret.as_deref());
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

    fn resolve_arg_names(&self, def_id: rustc_hir::def_id::DefId) -> Vec<String> {
        if !self.tcx.is_mir_available(def_id) {
            return Vec::new();
        }
        let body = self.tcx.optimized_mir(def_id);
        body.local_decls
            .iter()
            .enumerate()
            .skip(1)
            .take(body.arg_count)
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
        let ret_ty = body.local_decls.iter().next().map(|d| d.ty);
        let ret_ty = ret_ty.filter(|ty| !ty.is_unit()).map(|ty| ty.to_string());
        (args, ret_ty)
    }
}

fn fmt_fn_with_params(path: &str, arg_names: &[String], ret_ty: Option<&str>) -> String {
    let args = arg_names.join(", ");
    match ret_ty {
        Some(ret) => format!("fn {path}({args}) -> {ret}"),
        None if args.is_empty() => format!("fn {path}"),
        None => format!("fn {path}({args})"),
    }
}

fn fmt_fn_path_with_generics(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> String {
    let path = tcx.def_path_str(def_id);
    let generics = tcx.generics_of(def_id);
    let params: Vec<_> = generics
        .own_params
        .iter()
        .map(|p| p.name.to_string())
        .collect();
    if params.is_empty() {
        path
    } else {
        format!("{}::<{}>", path, params.join(", "))
    }
}

fn emit_lines(lines: &[(String, String)]) {
    for (tag, meaning) in lines {
        if tag.is_empty() && meaning.is_empty() {
            rap_info!("");
        } else if meaning.is_empty() {
            if let Some(header) = tag.strip_prefix("[").and_then(|s| s.strip_suffix("]")) {
                rap_info!("");
                rap_info!("{}", header);
                rap_info!("{:-<1$}", "", 76);
            } else {
                rap_info!("  // {tag}");
            }
        } else {
            rap_info!("  Safety Tag: {tag}");
            rap_info!("    Meaning:   {meaning}");
        }
    }
}

fn fmt_contract_expanded(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    property: &crate::verify::contract::Property<'_>,
) -> (String, String) {
    use crate::verify::contract::PropertyKind;
    let args: Vec<String> = property
        .args
        .iter()
        .map(|a| fmt_arg_plain(tcx, local_names, a))
        .collect();
    let tag = format!("{:?}", property.kind);
    let call = if matches!(property.kind, PropertyKind::TransmuteWithoutAlign) {
        let wrapped: Vec<String> = args.iter().map(|a| format!("[{a}]")).collect();
        format!("{tag}({})", wrapped.join(", "))
    } else if matches!(property.kind, PropertyKind::InBound)
        && matches!(
            property.args.first(),
            Some(crate::verify::contract::PropertyArg::Expr(
                crate::verify::contract::ContractExpr::IndexAccess { .. }
            ))
        )
    {
        use crate::verify::contract::{ContractExpr, PropertyArg};
        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args.first()
        {
            let mut s = fmt_expr_plain(tcx, local_names, slice);
            s = s.strip_prefix("&mut ").unwrap_or(&s).to_string();
            s = s.strip_prefix("&").unwrap_or(&s).to_string();
            let i = fmt_expr_plain(tcx, local_names, index);
            format!("{tag}({s}, {i})")
        } else {
            unreachable!()
        }
    } else {
        if matches!(property.kind, PropertyKind::Alive) && args.len() >= 2 {
            format!("{tag}({}, '{})", args[0], args[1])
        } else {
            format!("{tag}({})", args.join(", "))
        }
    };
    let call = if matches!(property.kind, PropertyKind::ValidNum)
        && let Some(crate::verify::contract::PropertyArg::Predicates(preds)) = property.args.first()
    {
        format!("{tag}({})", fmt_valid_num_call(tcx, local_names, preds))
    } else {
        call
    };
    let meaning = match property.kind {
        PropertyKind::NonNull => format!(
            "{} as usize != 0",
            args.first().map(|s| s.as_str()).unwrap_or("_")
        ),
        PropertyKind::Align => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            format!("({ptr} as usize) % align_of::<{ty}>() == 0")
        }
        PropertyKind::InBound => {
            use crate::verify::contract::{ContractExpr, PropertyArg};
            let placeholder = format!("InBound({})", args.join(", "));
            match property.args.first() {
                Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) => {
                    let mut s = fmt_expr_plain(tcx, local_names, slice);
                    s = s.strip_prefix("&mut ").unwrap_or(&s).to_string();
                    s = s.strip_prefix("&").unwrap_or(&s).to_string();
                    let i = fmt_expr_plain(tcx, local_names, index);
                    format!("0 <= {i} < {s}.len()")
                }
                Some(PropertyArg::Place(place)) => {
                    let ptr = fmt_place_plain(place, local_names);
                    let ty = property
                        .args
                        .get(1)
                        .and_then(|a| match a {
                            PropertyArg::Ty(ty) => Some(ty.to_string()),
                            _ => None,
                        })
                        .unwrap_or_else(|| "?".to_string());
                    let cnt = property
                        .args
                        .get(2)
                        .map(|a| fmt_arg_plain(tcx, local_names, a))
                        .unwrap_or_else(|| "?".to_string());
                    format!("same_alloc([{ptr}, {ptr} + sizeof({ty})*{cnt}])")
                }
                _ => placeholder,
            }
        }
        PropertyKind::ValidPtr => {
            use crate::verify::contract::PropertyArg;
            let ptr = property
                .args
                .first()
                .map(|a| fmt_arg_plain(tcx, local_names, a))
                .unwrap_or_else(|| "?".to_string());
            let ty = property
                .args
                .get(1)
                .and_then(|a| match a {
                    PropertyArg::Ty(ty) => Some(ty.to_string()),
                    _ => None,
                })
                .unwrap_or_else(|| "?".to_string());
            let cnt = property
                .args
                .get(2)
                .map(|a| fmt_arg_plain(tcx, local_names, a))
                .unwrap_or_else(|| "?".to_string());
            format!("same_alloc([{ptr}, {ptr} + sizeof({ty})*{cnt}])")
        }
        PropertyKind::Init => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            let cnt = args.get(2).map(|s| s.as_str()).unwrap_or("count");
            let line1 = format!("{cnt} element(s) of type {ty} at {p} are initialized");
            let line2 = format!(
                "                     forall i in 0..{cnt}: *({p} + i*sizeof({ty})) |= type_invariant({ty})"
            );
            format!("{line1}\n{line2}")
        }
        PropertyKind::Typed => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let ty = args.get(1).map(|s| s.as_str()).unwrap_or("T");
            format!("*{ptr} holds TypeInvariant({ty})")
        }
        PropertyKind::Alive => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            if let Some(lt) = args.get(1) {
                format!("lifetime({ptr}) anchored to lifetime('{lt})")
            } else {
                format!("lifetime(return) anchored to {ptr}")
            }
        }
        PropertyKind::Alias => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{ptr} has exclusive access (no conflicting mutable aliases)")
        }
        PropertyKind::Allocated => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            let suffix = if args.len() >= 3 {
                format!(", {}, {}", args[1], args[2])
            } else {
                String::new()
            };
            format!("{ptr} points to live heap/stack allocation{suffix}")
        }
        PropertyKind::NonOverlap => {
            let joined = args.join(", ");
            format!("[{joined}] are pairwise disjoint memory ranges")
        }
        PropertyKind::ValidNum => args.join(" && "),
        PropertyKind::ValidTransmute => {
            let src = args.first().map(|s| s.as_str()).unwrap_or("Src");
            let dst = args.get(1).map(|s| s.as_str()).unwrap_or("Dst");
            format!("bytes_of({dst}) within bytes_of({src})")
        }
        PropertyKind::TransmuteWithoutAlign => {
            let src = args.first().map(|s| s.as_str()).unwrap_or("T");
            let dst = args.get(1).map(|s| s.as_str()).unwrap_or("U");
            let line1 = format!(
                "[{src}] as [{dst}]: every size_of({dst})-byte contiguous chunk of [{src}] is a valid bit-pattern of {dst} (type_invariant satisfied, alignment not required)"
            );
            let line2 = format!(
                "                     forall w subset bytes([{src}]), |w| == |{dst}|: reinterpret_as_{dst}(w) |= type_invariant({dst}) \\ align_of({dst})",
            );
            format!("{line1}\n{line2}")
        }
        PropertyKind::Deref => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("same_alloc({ptr}) and 0 <= byte_offset({ptr}) < alloc_len({ptr})")
        }
        PropertyKind::Ptr2Ref => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("can soundly convert {ptr} to &/&mut reference")
        }
        PropertyKind::Owning => {
            let ptr = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{ptr} has unique ownership, no other write-capable alias")
        }
        PropertyKind::ValidSlice => {
            let s = args.first().map(|s| s.as_str()).unwrap_or("slice");
            format!("{s} points to valid slice with non-null aligned data")
        }
        PropertyKind::Layout => {
            let l = args.first().map(|s| s.as_str()).unwrap_or("layout");
            format!("{l} matches prior allocation size and alignment")
        }
        PropertyKind::Size => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("sizeof(type_pointed_by({p})) > 0")
        }
        PropertyKind::NonSize => "Size(T, !=0)".to_string(),
        PropertyKind::NoPadding => {
            let t = args.first().map(|s| s.as_str()).unwrap_or("T");
            format!("{t} has no padding bytes between fields")
        }
        PropertyKind::Unwrap => {
            let x = args.first().map(|s| s.as_str()).unwrap_or("x");
            format!("{x} is in expected variant / not None / not Err")
        }
        PropertyKind::ValidString => {
            let v = args.first().map(|s| s.as_str()).unwrap_or("v");
            format!("{v} is valid UTF-8")
        }
        PropertyKind::ValidCStr => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} is a null-terminated valid UTF-8 byte sequence")
        }
        PropertyKind::Pinned => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} will not be moved")
        }
        PropertyKind::NonVolatile => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} does not reference volatile memory")
        }
        PropertyKind::Opened => {
            let f = args.first().map(|s| s.as_str()).unwrap_or("fd");
            format!("{f} is a valid open file descriptor")
        }
        PropertyKind::Trait => {
            let t = args.first().map(|s| s.as_str()).unwrap_or("T");
            format!("{t} upholds its unsafe trait contract")
        }
        PropertyKind::Nullable => {
            let p = args.first().map(|s| s.as_str()).unwrap_or("ptr");
            format!("{p} may be null")
        }
        PropertyKind::Unreachable => "not Reachable()".to_string(),
        PropertyKind::Unknown => "(unresolved contract)".to_string(),
    };
    (call, meaning)
}

fn fmt_arg_plain(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    arg: &crate::verify::contract::PropertyArg<'_>,
) -> String {
    match arg {
        crate::verify::contract::PropertyArg::Place(place) => fmt_place_plain(place, local_names),
        crate::verify::contract::PropertyArg::Ty(ty) => format!("{}", ty),
        crate::verify::contract::PropertyArg::Expr(expr) => fmt_expr_plain(tcx, local_names, expr),
        crate::verify::contract::PropertyArg::Predicates(preds) => {
            let p: Vec<_> = preds
                .iter()
                .map(|p| fmt_pred_plain(tcx, local_names, p))
                .collect();
            p.join(" && ")
        }
        crate::verify::contract::PropertyArg::Ident(id) => id.clone(),
    }
}

fn fmt_place_plain(
    place: &crate::verify::contract::ContractPlace<'_>,
    local_names: &[String],
) -> String {
    let mut base = match place.base {
        crate::verify::contract::PlaceBase::Return => "return".to_string(),
        crate::verify::contract::PlaceBase::Arg(i) => format!("arg:{}", i),
        crate::verify::contract::PlaceBase::Local(l) => local_names
            .get(l)
            .cloned()
            .unwrap_or_else(|| format!("local_{}", l)),
    };
    base = base.strip_prefix("&mut ").unwrap_or(&base).to_string();
    base = base.strip_prefix("&").unwrap_or(&base).to_string();
    if place.projections.is_empty() {
        base
    } else {
        let proj: Vec<String> = place
            .projections
            .iter()
            .map(|p| match p {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    index.to_string()
                }
            })
            .collect();
        format!("{}.{}", base, proj.join("."))
    }
}

fn fmt_expr_plain(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    expr: &crate::verify::contract::ContractExpr<'_>,
) -> String {
    use crate::verify::contract::ContractExpr;
    match expr {
        ContractExpr::Place(place) => fmt_place_plain(place, local_names),
        ContractExpr::Const(c) => format!("{}", c),
        ContractExpr::ConstParam { name, .. } => name.clone(),
        ContractExpr::SizeOf(ty) => format!("size_of::<{}>()", ty),
        ContractExpr::AlignOf(ty) => format!("align_of::<{}>()", ty),
        ContractExpr::Len(inner) => {
            let inner_str = fmt_expr_plain(tcx, local_names, inner);
            if matches!(inner.as_ref(), ContractExpr::Place(_)) {
                format!("{}.len()", inner_str)
            } else {
                format!("len({})", inner_str)
            }
        }
        ContractExpr::IndexAccess { slice, index } => {
            format!(
                "index_access({}, {})",
                fmt_expr_plain(tcx, local_names, slice),
                fmt_expr_plain(tcx, local_names, index)
            )
        }
        ContractExpr::Binary { op, lhs, rhs } => {
            let op_str = match op {
                crate::verify::contract::NumericOp::Add => "+",
                crate::verify::contract::NumericOp::Sub => "-",
                crate::verify::contract::NumericOp::Mul => "*",
                crate::verify::contract::NumericOp::Div => "/",
                crate::verify::contract::NumericOp::Rem => "%",
                crate::verify::contract::NumericOp::BitAnd => "&",
                crate::verify::contract::NumericOp::BitOr => "|",
                crate::verify::contract::NumericOp::BitXor => "^",
            };
            format!(
                "{} {} {}",
                fmt_expr_plain(tcx, local_names, lhs),
                op_str,
                fmt_expr_plain(tcx, local_names, rhs)
            )
        }
        ContractExpr::Unary { op, expr: inner } => {
            let op_str = match op {
                crate::verify::contract::NumericUnaryOp::Not => "!",
                crate::verify::contract::NumericUnaryOp::Neg => "-",
            };
            format!("{}{}", op_str, fmt_expr_plain(tcx, local_names, inner))
        }
        ContractExpr::Unknown => "<?>".to_string(),
    }
}

fn fmt_valid_num_pred(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    pred: &crate::verify::contract::NumericPredicate<'_>,
) -> String {
    use crate::verify::contract::ContractExpr;
    if matches!(pred.op, crate::verify::contract::RelOp::Ne)
        && matches!(pred.rhs, ContractExpr::Const(0))
    {
        return fmt_expr_plain(tcx, local_names, &pred.lhs);
    }
    fmt_pred_plain(tcx, local_names, pred)
}

fn fmt_valid_num_call(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    preds: &[crate::verify::contract::NumericPredicate<'_>],
) -> String {
    use crate::verify::contract::RelOp;

    if preds.len() == 2 {
        let (lower, upper) = (&preds[0], &preds[1]);
        let lower_l = fmt_expr_plain(tcx, local_names, &lower.lhs);
        let lower_val = fmt_expr_plain(tcx, local_names, &lower.rhs);
        let upper_val = fmt_expr_plain(tcx, local_names, &upper.lhs);
        let upper_r = fmt_expr_plain(tcx, local_names, &upper.rhs);
        if lower_val == upper_val {
            let lo = match lower.op {
                RelOp::Gt | RelOp::Le => lower_l,
                _ => {
                    return preds
                        .iter()
                        .map(|p| fmt_valid_num_pred(tcx, local_names, p))
                        .collect::<Vec<_>>()
                        .join(", ");
                }
            };
            let lb = if matches!(lower.op, RelOp::Ge | RelOp::Le) {
                "["
            } else {
                "("
            };
            let ub = if matches!(upper.op, RelOp::Le | RelOp::Ge) {
                "]"
            } else {
                ")"
            };
            let hi = match upper.op {
                RelOp::Le | RelOp::Lt => upper_r,
                _ => {
                    return preds
                        .iter()
                        .map(|p| fmt_valid_num_pred(tcx, local_names, p))
                        .collect::<Vec<_>>()
                        .join(", ");
                }
            };
            return format!("{upper_val}, \"{lb}{lo}, {hi}{ub}\"");
        }
    }

    preds
        .iter()
        .map(|p| fmt_valid_num_pred(tcx, local_names, p))
        .collect::<Vec<_>>()
        .join(", ")
}

fn fmt_pred_plain(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    local_names: &[String],
    pred: &crate::verify::contract::NumericPredicate<'_>,
) -> String {
    let op = match pred.op {
        crate::verify::contract::RelOp::Eq => "==",
        crate::verify::contract::RelOp::Ne => "!=",
        crate::verify::contract::RelOp::Lt => "<",
        crate::verify::contract::RelOp::Le => "<=",
        crate::verify::contract::RelOp::Gt => ">",
        crate::verify::contract::RelOp::Ge => ">=",
    };
    format!(
        "{} {} {}",
        fmt_expr_plain(tcx, local_names, &pred.lhs),
        op,
        fmt_expr_plain(tcx, local_names, &pred.rhs)
    )
}

fn emit_verify_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    target_path: &str,
    def_id: rustc_hir::def_id::DefId,
    all_results: &[PropertyCheckResult<'tcx>],
    mode: VerifyMode,
) {
    let unproved = all_results
        .iter()
        .filter(|r| !matches!(r.result, super::report::CheckResult::Proved))
        .count();

    rap_info!("============================================================");
    rap_info!("[rapx::verify] function: {target_path}");
    rap_info!("============================================================");

    if matches!(mode, VerifyMode::Invless) {
        let cons = get_cons(tcx, def_id);
        for con in &cons {
            rap_info!("  + constructor: {}", tcx.def_path_str(*con));
        }
    }

    // Group results by (checkpoint, callee_name)
    let mut groups: IndexMap<(CheckpointLocation, String), Vec<&PropertyCheckResult<'_>>> =
        IndexMap::new();
    for r in all_results {
        groups
            .entry((r.checkpoint, r.callee_name.clone()))
            .or_default()
            .push(r);
    }

    // Separate into checkpoint groups and struct-invariant groups
    let checkpoint_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| !name.starts_with("struct-invariant"))
        .collect();
    let invariant_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| name.starts_with("struct-invariant"))
        .collect();

    // Print unsafe checkpoint results
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

    // Print struct invariant results
    if !invariant_groups.is_empty() {
        rap_info!("  --- struct invariants ---");
        for ((checkpoint, _), results) in &invariant_groups {
            rap_info!("      checkpoint bb{}:", checkpoint.block.as_usize(),);
            emit_property_rows(results);
        }
    }

    if unproved == 0 {
        rap_info!(green, "  result: SOUND");
    } else {
        rap_warn!("  result: UNSOUND ({unproved} unproved)");
    }

    rap_info!("");
}

fn emit_property_rows(results: &[&PropertyCheckResult<'_>]) {
    let mut path_groups: FxHashMap<&str, Vec<_>> = FxHashMap::default();
    for r in results.iter() {
        path_groups
            .entry(r.path_description.as_str())
            .or_default()
            .push(r);
    }
    for (path_desc, props) in &path_groups {
        rap_info!("        path {path_desc}:");
        for r in props.iter() {
            let line = format!("          {:?} | {:?}", r.property.kind, r.result);
            if matches!(r.result, super::report::CheckResult::Proved) {
                rap_info!(green, "{line}");
            } else {
                rap_warn!("{line}");
            }
        }
    }
}

/// Analysis pass that dumps backward and forward visitor diagnostics.
pub struct VerifyVisitDump<'tcx> {
    tcx: TyCtxt<'tcx>,
    postfix_repeat: usize,
    mode: VerifyMode,
}

/// Extract the last segment of a def-path (the bare function name).
fn short_fn_name(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> String {
    let path = tcx.def_path_str(def_id);
    path.rsplit("::").next().unwrap_or(&path).to_string()
}

/// Return true when two properties have the same kind.
fn same_property(
    a: &crate::verify::contract::Property<'_>,
    b: &crate::verify::contract::Property<'_>,
) -> bool {
    matches!(
        (&a.kind, &b.kind),
        (PropertyKind::Align, PropertyKind::Align)
            | (PropertyKind::InBound, PropertyKind::InBound)
            | (PropertyKind::Init, PropertyKind::Init)
            | (PropertyKind::NonNull, PropertyKind::NonNull)
            | (PropertyKind::ValidPtr, PropertyKind::ValidPtr)
    )
}

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
                let crate::verify::contract::ContractProjection::Field { index, .. } = proj;
                let idx = *index;
                if !indices.contains(&idx) {
                    indices.push(idx);
                }
            }
        }
    }
    indices
}

impl<'tcx> VerifyVisitDump<'tcx> {
    /// Create a diagnostic dump pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>, postfix_repeat: usize, mode: VerifyMode) -> Self {
        Self {
            tcx,
            postfix_repeat,
            mode,
        }
    }
}

impl<'tcx> Analysis for VerifyVisitDump<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Visitor Diagnostic Dump"
    }

    /// Collect verify targets and print the current staged visitor output.
    fn run(&mut self) {
        rap_debug!("======== #[rapx::verify] visitor diagnostics ========");
        let mut collector = VerifyTargetCollector::new(self.tcx, self.mode, None, None);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_debug!(
                "[rapx::verify::diagnostics] target: {} (DefId: {:?})",
                target_path,
                target.def_id
            );

            for repeat in 0..=self.postfix_repeat {
                if self.postfix_repeat > 0 {
                    rap_debug!(
                        "[rapx::verify::diagnostics] round {}/{}: postfix-repeat={}",
                        repeat,
                        self.postfix_repeat,
                        repeat
                    );
                }
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let result = catch_unwind(AssertUnwindSafe(|| driver.verify_function()));
                match result {
                    Ok(report) => {
                        rap_debug!("{}", report.describe());
                    }
                    Err(_) => {
                        rap_debug!(
                            "[rapx::verify::diagnostics] function {} skipped due to ICE",
                            self.tcx.def_path_str(target.def_id)
                        );
                    }
                }
            }
        }

        rap_debug!("=======================================");
    }

    fn reset(&mut self) {}
}
