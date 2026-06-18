//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! `VerifyDriver` prepares paths for two kinds of checks (unsafe callsites and
//! struct invariants) and delegates the actual backward/forward/SMT work to
//! the shared `VerifyEngine`.

use crate::analysis::Analysis;
use crate::analysis::path_analysis::graph::{PathEnumerator, PathGraph};
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
        let mut all_callsites = target.callsites.clone();
        for (callsite, _) in &target.raw_ptr_deref_checks {
            all_callsites.push(callsite.clone());
        }
        let path_info = PathExtractor::new(tcx, target.def_id, all_callsites, allow_repeat).run();
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
        let tree = self.path_info.path_tree();

        for view in self.iter_callsite_checks() {
            let target_block = view.callsite.block.as_usize();
            for (property_index, property) in view.properties.iter().enumerate() {
                let bulk = self.engine.check_callsite_from_tree(
                    tree,
                    target_block,
                    view.callsite,
                    property,
                    &self.target.caller_requires,
                );
                for (path_index, (forward, smt_check)) in bulk.iter().enumerate() {
                    let check_diagnostics =
                        format!("{}\n{}", forward.describe(), smt_check.describe());
                    report.push(PropertyCheckResult {
                        callsite: view.callsite.location(),
                        callsite_index: view.callsite_index,
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: smt_check.result.clone(),
                        diagnostics: Some(VisitDiagnostics::new(String::new(), check_diagnostics)),
                        path_description: forward.path.describe_indices(),
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

        let is_constructor = get_type(self.tcx, self.target.def_id) == FnKind::Constructor;
        let caller_contracts = &self.target.caller_requires;

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
                        caller_contracts,
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
                let _ = all_paths.walk_prefixes(
                    return_block.as_usize(),
                    &mut |prefix: &[usize]| -> bool {
                        if paths.len() >= PATH_LIMIT {
                            return false;
                        }
                        paths.push(Path {
                            target: checkpoint,
                            start: PathStart::FunctionEntry,
                            steps: prefix
                                .iter()
                                .map(|&b| PathStep::Block(BasicBlock::from(b)))
                                .chain(std::iter::once(PathStep::Callsite(checkpoint)))
                                .collect(),
                        });
                        true
                    },
                );
                if !paths.is_empty() {
                    paths_by_checkpoint.insert(checkpoint, paths);
                }
            }
        } else {
            for path in all_paths.iter() {
                if path.is_empty() {
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
        use super::helpers::CallsiteLocation;
        let mut map: FxHashMap<CallsiteLocation, &'target [Property<'tcx>]> = target
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
            .collect();

        for (callsite, properties) in &target.raw_ptr_deref_checks {
            let props: &'target [Property<'tcx>] = properties;
            map.entry(callsite.location())
                .and_modify(|existing| {
                    // If both raw ptr deref and regular callsite exist at same
                    // location (different blocks won't collide), merge properties.
                    // Since they're slices, we can't trivially merge; just replace
                    // with the new one for now (raw ptr takes priority).
                    *existing = props;
                })
                .or_insert(props);
        }

        map
    }
}

/// Returns whether a function returns the owning struct type (i.e. is a constructor).
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
            callsites: read_target.callsites.clone(),
            callee_requires: read_target.callee_requires.clone(),
            caller_requires: accumulated_requires,
            struct_invariants: Vec::new(),
            raw_ptr_deref_checks: read_target.raw_ptr_deref_checks.clone(),
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

        for repeat in 0..=self.allow_pathseg_repeat {
            let driver = VerifyDriver::new_with_repeat(self.tcx, con_target, repeat);
            let report = driver.verify_function();
            rap_debug!("{}", report.describe());
            all_results.extend(report.results);
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

        let mut groups: IndexMap<(CallsiteLocation, String), Vec<&PropertyCheckResult<'_>>> =
            IndexMap::new();
        for r in &all_results {
            groups
                .entry((r.callsite, r.callee_name.clone()))
                .or_default()
                .push(r);
        }

        let callsite_groups: Vec<_> = groups
            .iter()
            .filter(|((_, name), _)| !name.starts_with("struct-invariant"))
            .collect();

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

        if unproved == 0 && !all_results.is_empty() {
            rap_info!("  result: SOUND");
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
                rap_debug!("{}", report.describe());
                all_results.extend(report.results);
            }

            // Phase 2: struct invariant verification
            if !target.struct_invariants.is_empty() && !matches!(self.mode, VerifyMode::Invless) {
                let driver =
                    VerifyDriver::new_with_repeat(self.tcx, target, self.allow_pathseg_repeat);
                let struct_report = driver.verify_struct_invariants();
                rap_debug!("{}", struct_report.describe());
                all_results.extend(struct_report.results);
            }

            if all_results.is_empty() {
                if target.callsites.is_empty()
                    && target.raw_ptr_deref_checks.is_empty()
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
                    rap_info!("  --- unsafe callsites ---");
                    rap_info!("      <none>");
                    rap_info!("        Unknown | Unproved");
                    rap_warn!("  result: UNSOUND (no safety contracts found)");
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

        // Invless mode: generate constructor-mutator-method sequences
        if matches!(self.mode, VerifyMode::Invless) {
            self.run_invless_sequences(&collector.function_targets);
        }
    }

    fn reset(&mut self) {}
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
