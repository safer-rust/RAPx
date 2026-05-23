//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns selected functions and their callee requirements.
//! The path extractor upgrades a function CFG into loop-aware path metadata.
//! This module keeps those pieces together for one function target and exposes
//! callsite-level views for later evidence, replay, and SMT stages.

use rustc_data_structures::fx::FxHashMap;
use rustc_middle::ty::TyCtxt;

use super::{
    contract::Property,
    evidence::EvidenceReducer,
    helpers::Callsite,
    path::{Path, PathExtractor, PathMetaInfo},
    report::{CheckResult, PropertyCheckResult, VerificationReport},
    target::FunctionTarget,
};

/// Orchestrates verification inputs for one function target.
pub struct VerifyDriver<'target, 'tcx> {
    tcx: TyCtxt<'tcx>,
    target: &'target FunctionTarget<'tcx>,
    path_info: PathMetaInfo<'tcx>,
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

    /// Return the loop-aware path metadata managed by this driver.
    pub fn path_info(&self) -> &PathMetaInfo<'tcx> {
        &self.path_info
    }

    /// Run the current staged verifier pipeline for the managed function target.
    ///
    /// This method is the main driver entry for later verification stages.  It
    /// currently walks `(callsite, path, property)` items and records an
    /// `Unknown` result for each one.  Evidence reduction, abstract replay, and
    /// SMT checking can replace the placeholder result inside this loop without
    /// changing the surrounding control flow.
    pub fn verify_function(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let reducer = EvidenceReducer::new(self.tcx);

        for view in self.iter_callsite_checks() {
            for (path_index, path) in view.paths.iter().enumerate() {
                for property in view.properties {
                    let _evidence = reducer.reduce(view.callsite, path, property);
                    report.push(PropertyCheckResult {
                        callsite: view.callsite.location(),
                        path_index,
                        property: property.clone(),
                        result: CheckResult::Unknown,
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
        self.path_info.callsites().iter().map(move |callsite| {
            let paths = self.path_info.paths_for(callsite.location());
            let properties = self.properties_for_callsite(callsite);
            CallsiteCheckView {
                callsite,
                paths,
                properties,
            }
        })
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
    /// The concrete unsafe callsite in the caller MIR body.
    pub callsite: &'view Callsite<'tcx>,
    /// Loop-aware paths that can reach this callsite.
    pub paths: &'view [Path],
    /// Required safety properties for the unsafe callee.
    pub properties: &'target [Property<'tcx>],
}
