//! Driver utilities for the staged verifier pipeline.
//!
//! The target collector owns the list of functions and their required callee
//! contracts.  The path extractor owns loop-aware paths to concrete unsafe
//! callsites.  This module connects those pieces without introducing another
//! storage model for obligations.

use rustc_middle::ty::TyCtxt;

use super::{
    contract::Property,
    helpers::{Callsite, collect_unsafe_callsites},
    path::{Path, PathExtractor, PathResult},
    target::FunctionTarget,
};

/// Entry point for building callsite-level verification inputs.
pub struct VerifyDriver<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> VerifyDriver<'tcx> {
    /// Create a verifier driver over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Collect concrete unsafe callsites from a function target.
    pub fn collect_callsites(&self, target: &FunctionTarget<'tcx>) -> Vec<Callsite<'tcx>> {
        collect_unsafe_callsites(self.tcx, target.def_id)
    }

    /// Extract loop-aware paths for the given target and callsites.
    pub fn extract_paths(
        &self,
        target: &FunctionTarget<'tcx>,
        callsites: Vec<Callsite<'tcx>>,
    ) -> PathResult<'tcx> {
        PathExtractor::new(self.tcx, target.def_id, callsites).run()
    }

    /// Collect callsites and extract paths for one function target.
    pub fn build_path_result(&self, target: &FunctionTarget<'tcx>) -> PathResult<'tcx> {
        let callsites = self.collect_callsites(target);
        self.extract_paths(target, callsites)
    }

    /// Return the required properties for a concrete unsafe callsite.
    pub fn requires_for_callsite<'a>(
        &self,
        target: &'a FunctionTarget<'tcx>,
        callsite: &Callsite<'tcx>,
    ) -> &'a [Property<'tcx>] {
        target
            .callee_requires
            .get(&callsite.callee)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Iterate over callsites together with their paths and required properties.
    pub fn iter_callsite_checks<'a>(
        &'a self,
        target: &'a FunctionTarget<'tcx>,
        path_result: &'a PathResult<'tcx>,
    ) -> impl Iterator<Item = CallsiteCheckView<'a, 'tcx>> + 'a {
        path_result.callsites().iter().map(move |callsite| {
            let paths = path_result.paths_for(callsite.location());
            let requires = self.requires_for_callsite(target, callsite);
            CallsiteCheckView {
                callsite,
                paths,
                requires,
            }
        })
    }
}

/// Borrowed view of all verification inputs for one unsafe callsite.
pub struct CallsiteCheckView<'a, 'tcx> {
    /// The concrete unsafe callsite in the caller MIR body.
    pub callsite: &'a Callsite<'tcx>,
    /// Loop-aware paths that can reach this callsite.
    pub paths: &'a [Path],
    /// Required safety properties for the unsafe callee.
    pub requires: &'a [Property<'tcx>],
}
