/// NOTE: This analysis module is currently under development and is highly unstable.
/// The #[allow(unused)] attribute is applied to suppress excessive lint warnings.
/// Once the analysis stabilizes, this marker should be removed.
pub mod scan;

use crate::analysis::Analysis;
use rustc_middle::ty::TyCtxt;

/// Verify Analysis - entry point for verify-related analyses
pub struct VerifyAnalysis<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Analysis for VerifyAnalysis<'tcx> {
    fn name(&self) -> &'static str {
        "Verify Analysis"
    }

    fn run(&mut self) {}

    fn reset(&mut self) {}
}

impl<'tcx> VerifyAnalysis<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        VerifyAnalysis { tcx }
    }
}
