//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into SCC-aware path metadata.
//! This module keeps those pieces together for one function target and exposes
//! callsite-level views for later backward visits, forward visits, and SMT stages.

use crate::analysis::Analysis;

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;

use super::{
    backward_visit::BackwardVisitor,
    contract::Property,
    fact_check::FactChecker,
    forward_visit::ForwardVisitor,
    helpers::Callsite,
    path::{FunctionPaths, Path, PathExtractor},
    report::{PropertyCheckResult, VerificationReport, VisitDiagnostics},
    target::{FunctionTarget, VerifyTargetCollector},
};

/// Orchestrates verification inputs for one function target.
pub struct VerifyDriver<'target, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: &'target FunctionTarget<'tcx>,
    path_info: FunctionPaths<'tcx>,
    properties_to_verify: FxHashMap<super::helpers::CallsiteLocation, &'target [Property<'tcx>]>,
}

impl<'target, 'tcx> VerifyDriver<'target, 'tcx> {
    /// Build a driver for one collected function target.
    pub fn new(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>) -> Self {
        let path_info = PathExtractor::new(tcx, target.def_id, target.callsites.clone()).run();
        let properties_to_verify = Self::build_properties_to_verify(target);
        Self {
            tcx,
            target,
            path_info,
            properties_to_verify,
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

    /// Run the current staged verifier pipeline for the managed function target.
    ///
    /// This method is the main driver entry for later verification stages.  It
    /// currently walks `(callsite, path, property)` items and records an
    /// `Unknown` result for each one. Backward visiting, forward visiting, and
    /// SMT checking can replace the placeholder result inside this loop without
    /// changing the surrounding control flow.
    pub fn verify_function(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let backward_visitor = BackwardVisitor::new(self.tcx);
        let forward_visitor = ForwardVisitor::new(self.tcx);
        let fact_checker = FactChecker::new(self.tcx);

        for view in self.iter_callsite_checks() {
            for (path_index, path) in view.paths.iter().enumerate() {
                for (property_index, property) in view.properties.iter().enumerate() {
                    let backward = backward_visitor.visit(view.callsite, path, property);
                    let forward = forward_visitor.visit(&backward);
                    let fact_check = fact_checker.check(view.callsite, property, &forward);
                    report.push(PropertyCheckResult {
                        callsite: view.callsite.location(),
                        callsite_index: view.callsite_index,
                        path_index,
                        property_index,
                        property: property.clone(),
                        result: fact_check.result.clone(),
                        diagnostics: Some(VisitDiagnostics::new(
                            backward.describe(self.tcx, view.callsite, path_index),
                            format!("{}\n{}", forward.describe(), fact_check.describe()),
                        )),
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

/// Analysis pass that dumps backward and forward visitor diagnostics.
pub struct VerifyVisitDump<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> VerifyVisitDump<'tcx> {
    /// Create a diagnostic dump pass for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }
}

impl<'tcx> Analysis for VerifyVisitDump<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Visitor Diagnostic Dump"
    }

    /// Collect verify targets and print the current staged visitor output.
    fn run(&mut self) {
        rap_info!("======== #[rapx::verify] visitor diagnostics ========");
        let mut collector = VerifyTargetCollector::new(self.tcx);
        self.tcx.hir_visit_all_item_likes_in_crate(&mut collector);

        for target in &collector.function_targets {
            let target_path = self.tcx.def_path_str(target.def_id);
            rap_info!(
                "[rapx::verify::dump-visits] target: {} (DefId: {:?})",
                target_path,
                target.def_id
            );
            let driver = VerifyDriver::new(self.tcx, target);
            let report = driver.verify_function();
            rap_info!("{}", report.describe());
        }

        rap_info!("=======================================");
    }

    fn reset(&mut self) {}
}
