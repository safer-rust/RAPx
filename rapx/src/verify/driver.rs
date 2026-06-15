//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! `VerifyDriver` prepares paths for two kinds of checks (unsafe callsites and
//! struct invariants) and delegates the actual backward/forward/SMT work to
//! the shared `VerifyEngine`.

use crate::analysis::Analysis;
use crate::analysis::path_analysis::graph::PathGraph;
use crate::cli::VerifyMode;

use indexmap::IndexMap;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::BasicBlock;
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    contract::Property,
    engine::VerifyEngine,
    helpers::{Callsite, CallsiteLocation, collect_return_block_indices},
    path::{FunctionPaths, PATH_LIMIT, Path, PathExtractor, PathStart, PathStep},
    report::{PropertyCheckResult, VerificationReport, VisitDiagnostics},
    target::{FunctionTarget, VerifyTargetCollector},
};

/// Orchestrates verification inputs for one function target.
pub struct VerifyDriver<'target, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: &'target FunctionTarget<'tcx>,
    path_info: FunctionPaths<'tcx>,
    properties_to_verify: FxHashMap<super::helpers::CallsiteLocation, &'target [Property<'tcx>]>,
    engine: VerifyEngine<'tcx>,
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
        let path_info =
            PathExtractor::new(tcx, target.def_id, target.callsites.clone(), allow_repeat).run();
        let properties_to_verify = Self::build_properties_to_verify(target);
        let engine = VerifyEngine::new(tcx);
        Self {
            tcx,
            target,
            path_info,
            properties_to_verify,
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

    /// Return the SCC-aware path metadata managed by this driver.
    pub fn path_info(&self) -> &FunctionPaths<'tcx> {
        &self.path_info
    }

    /// Run unsafe-callsite verification for the managed function target.
    pub fn verify_function(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);

        for view in self.iter_callsite_checks() {
            for (path_index, path) in view.paths.iter().enumerate() {
                for (property_index, property) in view.properties.iter().enumerate() {
                    let (forward, smt_check) =
                        self.engine.check_callsite(view.callsite, path, property);
                    let check_diagnostics =
                        format!("{}\n{}", forward.describe(), smt_check.describe());
                    report.push(PropertyCheckResult {
                        callsite: view.callsite.location(),
                        callsite_index: view.callsite_index,
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: smt_check.result,
                        diagnostics: Some(VisitDiagnostics::new(String::new(), check_diagnostics)),
                        path_description: path.describe_indices(),
                        callee_name: view.callsite.callee_name(self.tcx),
                    });
                }
            }
        }

        report
    }

    /// Return the required properties for a concrete unsafe callsite.
    pub fn properties_for_callsite(&self, callsite: &Callsite<'tcx>) -> &'target [Property<'tcx>] {
        self.properties_to_verify
            .get(&callsite.location())
            .copied()
            .unwrap_or(&[])
    }

    /// Iterate over callsites together with their paths and properties to verify.
    pub fn iter_callsite_checks(
        &self,
    ) -> impl Iterator<Item = CallsiteCheckView<'_, 'target, 'tcx>> + '_ {
        self.path_info
            .callsites()
            .iter()
            .filter_map(move |callsite| {
                let paths = self.path_info.paths_for(callsite.location());
                let properties = self.properties_for_callsite(callsite);
                if properties.is_empty() {
                    return None;
                }
                Some((callsite, paths, properties))
            })
            .enumerate()
            .map(
                move |(callsite_index, (callsite, paths, properties))| CallsiteCheckView {
                    callsite_index,
                    callsite,
                    paths,
                    properties,
                },
            )
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

        let is_constructor = self
            .target
            .owner_struct_def_id
            .map(|sid| returns_self(self.tcx, self.target.def_id, sid))
            .unwrap_or(false);

        for (checkpoint, paths) in self.build_invariant_paths(is_constructor) {
            rap_debug!(
                "[rapx::verify] struct invariant checkpoint bb{}: {} reachable path(s)",
                checkpoint.block.as_usize(),
                paths.len()
            );

            for (path_index, path) in paths.iter().enumerate() {
                for (property_index, property) in invariants.iter().enumerate() {
                    rap_debug!(
                        "[rapx::verify] struct invariant path {} check: kind={:?}",
                        path_index,
                        property.kind
                    );

                    let (backward, forward, smt_check) = self.engine.check_invariant(
                        self.target.def_id,
                        checkpoint,
                        path,
                        property,
                        invariants,
                        is_constructor,
                    );
                    let check_diagnostics =
                        format!("{}\n{}", forward.describe(), smt_check.describe());

                    report.push(PropertyCheckResult {
                        callsite: checkpoint,
                        callsite_index: checkpoint.block.as_usize(),
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: smt_check.result,
                        diagnostics: Some(VisitDiagnostics::new(
                            backward.describe_for_checkpoint(self.tcx, checkpoint, path_index),
                            check_diagnostics,
                        )),
                        path_description: path.describe_indices(),
                        callee_name: format!("struct-invariant(bb{})", checkpoint.block.as_usize()),
                    });
                }
            }
        }

        report
    }

    fn build_invariant_paths(
        &self,
        is_constructor: bool,
    ) -> FxHashMap<CallsiteLocation, Vec<Path>> {
        let mut pg = PathGraph::new(self.tcx, self.target.def_id);
        pg.find_scc();
        let all_paths = pg.enumerate_paths_repeat(self.allow_repeat);

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

        let mut paths_by_checkpoint: FxHashMap<CallsiteLocation, Vec<Path>> = FxHashMap::default();
        let mut seen_paths = FxHashSet::default();

        if is_constructor {
            let return_blocks = collect_return_block_indices(self.tcx, self.target.def_id);
            for &return_block in &return_blocks {
                let checkpoint = CallsiteLocation {
                    caller: self.target.def_id,
                    block: return_block,
                };
                let mut paths = Vec::new();
                let mut seen_prefixes = FxHashSet::default();
                for (_idx, path) in all_paths.iter().enumerate() {
                    if paths.len() >= PATH_LIMIT {
                        break;
                    }
                    let Some(pos) = path.iter().position(|&b| b == return_block.as_usize()) else {
                        continue;
                    };
                    let prefix: Vec<usize> = path[..=pos].to_vec();
                    if !seen_prefixes.insert(prefix.clone()) {
                        continue;
                    }
                    if !pg.is_path_reachable(&prefix) {
                        continue;
                    }
                    paths.push(Path {
                        target: checkpoint,
                        start: PathStart::FunctionEntry,
                        steps: prefix
                            .into_iter()
                            .map(|b| PathStep::Block(BasicBlock::from(b)))
                            .chain(std::iter::once(PathStep::Callsite(checkpoint)))
                            .collect(),
                    });
                }
                if !paths.is_empty() {
                    paths_by_checkpoint.insert(checkpoint, paths);
                }
            }
        } else {
            for path in all_paths.iter() {
                if path.is_empty() || !pg.is_path_reachable(path) {
                    continue;
                }
                if !seen_paths.insert(path.clone()) {
                    continue;
                }
                let last_block = BasicBlock::from(*path.last().unwrap());
                let checkpoint = CallsiteLocation {
                    caller: self.target.def_id,
                    block: last_block,
                };
                paths_by_checkpoint
                    .entry(checkpoint)
                    .or_default()
                    .push(Path {
                        target: checkpoint,
                        start: PathStart::FunctionEntry,
                        steps: path
                            .iter()
                            .map(|&b| PathStep::Block(BasicBlock::from(b)))
                            .chain(std::iter::once(PathStep::Callsite(checkpoint)))
                            .collect(),
                    });
            }
        }

        paths_by_checkpoint
    }

    /// Build the per-callsite property view from the target's callee requirements.
    fn build_properties_to_verify(
        target: &'target FunctionTarget<'tcx>,
    ) -> FxHashMap<super::helpers::CallsiteLocation, &'target [Property<'tcx>]> {
        target
            .callsites
            .iter()
            .map(|callsite| {
                let properties = target
                    .callee_requires
                    .get(&callsite.callee)
                    .map(Vec::as_slice)
                    .unwrap_or(&[]);
                (callsite.location(), properties)
            })
            .collect()
    }
}

/// Returns whether a function returns the owning struct type (i.e. is a constructor).
fn returns_self(
    tcx: TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
    struct_def_id: rustc_hir::def_id::DefId,
) -> bool {
    let output = tcx.fn_sig(def_id).skip_binder().output().skip_binder();
    match output.kind() {
        TyKind::Adt(adt_def, _) => adt_def.did() == struct_def_id,
        _ => false,
    }
}

/// Borrowed view of all verification inputs for one unsafe callsite.
pub struct CallsiteCheckView<'view, 'target, 'tcx> {
    /// Position among callsites that have properties to verify.
    pub callsite_index: usize,
    /// The concrete unsafe callsite in the caller MIR body.
    pub callsite: &'view Callsite<'tcx>,
    /// SCC-aware paths that can reach this callsite.
    pub paths: &'view [Path],
    /// Required safety properties for the unsafe callee.
    pub properties: &'target [Property<'tcx>],
}

/// Analysis pass that runs verification and emits function-level summaries.
pub struct VerifyRun<'tcx> {
    tcx: TyCtxt<'tcx>,
    allow_pathseg_repeat: usize,
    mode: VerifyMode,
}

impl<'tcx> VerifyRun<'tcx> {
    /// Create the default verify pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>, allow_pathseg_repeat: usize, mode: VerifyMode) -> Self {
        Self {
            tcx,
            allow_pathseg_repeat,
            mode,
        }
    }
}

impl<'tcx> Analysis for VerifyRun<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Driver"
    }

    /// Collect verify targets, run the staged driver, and emit a compact summary.
    ///
    /// For each target, extracts paths with increasing `allow-pathseg-repeat`
    /// levels from 0 to the configured maximum, running verification at each
    /// level. Earlier rounds use fewer loop unrollings; later rounds incrementally
    /// add deeper paths.
    fn run(&mut self) {
        let mut collector = VerifyTargetCollector::new(self.tcx, self.mode);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            let mut all_results: Vec<PropertyCheckResult<'_>> = Vec::new();

            // Phase 1: unsafe callsite verification
            for repeat in 0..=self.allow_pathseg_repeat {
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let report = driver.verify_function();
                all_results.extend(report.results);
            }

            // Phase 2: struct invariant verification
            if !target.struct_invariants.is_empty()
                && !matches!(self.mode, VerifyMode::Invariantless)
            {
                let driver =
                    VerifyDriver::new_with_repeat(self.tcx, target, self.allow_pathseg_repeat);
                let struct_report = driver.verify_struct_invariants();
                all_results.extend(struct_report.results);
            }

            if all_results.is_empty() {
                continue;
            }

            emit_verify_summary(&target_path, &all_results);
        }
    }

    fn reset(&mut self) {}
}

fn emit_verify_summary(target_path: &str, all_results: &[PropertyCheckResult<'_>]) {
    let unproved = all_results
        .iter()
        .filter(|r| !matches!(r.result, super::report::CheckResult::Proved))
        .count();

    rap_info!("============================================================");
    rap_info!("[rapx::verify] function: {target_path}");
    rap_info!("============================================================");

    // Group results by (callsite, callee_name)
    let mut groups: IndexMap<(CallsiteLocation, String), Vec<&PropertyCheckResult<'_>>> =
        IndexMap::new();
    for r in all_results {
        groups
            .entry((r.callsite, r.callee_name.clone()))
            .or_default()
            .push(r);
    }

    // Separate into callsite groups and struct-invariant groups
    let callsite_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| !name.starts_with("struct-invariant"))
        .collect();
    let invariant_groups: Vec<_> = groups
        .iter()
        .filter(|((_, name), _)| name.starts_with("struct-invariant"))
        .collect();

    // Print unsafe callsite results
    if !callsite_groups.is_empty() {
        rap_info!("  --- unsafe callsites ---");
        for ((callsite, callee_name), results) in &callsite_groups {
            rap_info!(
                "      unsafe callsite: bb{} -> {callee_name}",
                callsite.block.as_usize(),
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
        rap_info!("  result: SOUND");
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
            rap_info!("          {:?} | {:?}", r.property.kind, r.result);
        }
    }
}

/// Analysis pass that dumps backward and forward visitor diagnostics.
pub struct VerifyVisitDump<'tcx> {
    tcx: TyCtxt<'tcx>,
    allow_pathseg_repeat: usize,
    mode: VerifyMode,
}

impl<'tcx> VerifyVisitDump<'tcx> {
    /// Create a diagnostic dump pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>, allow_pathseg_repeat: usize, mode: VerifyMode) -> Self {
        Self {
            tcx,
            allow_pathseg_repeat,
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
        let mut collector = VerifyTargetCollector::new(self.tcx, self.mode);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_debug!(
                "[rapx::verify::diagnostics] target: {} (DefId: {:?})",
                target_path,
                target.def_id
            );

            for repeat in 0..=self.allow_pathseg_repeat {
                if self.allow_pathseg_repeat > 0 {
                    rap_debug!(
                        "[rapx::verify::diagnostics] round {}/{}: allow-pathseg-repeat={}",
                        repeat,
                        self.allow_pathseg_repeat,
                        repeat
                    );
                }
                let driver = VerifyDriver::new_with_repeat(self.tcx, target, repeat);
                let report = driver.verify_function();
                rap_debug!("{}", report.describe());
            }
        }

        rap_debug!("=======================================");
    }

    fn reset(&mut self) {}
}
