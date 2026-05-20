//! Diagnostics and summaries for the staged verifier pipeline.
//!
//! The driver and later checking stages report their per-path property results
//! through the types in this module.  Keeping these types here leaves the driver
//! focused on orchestration.

use rustc_hir::def_id::DefId;

use super::{contract::Property, helpers::CallsiteLocation};

/// Verification status for one required property on one path.
#[derive(Clone, Debug)]
pub enum CheckResult {
    /// The property has been proved for this path.
    Proved,
    /// The verifier found a possible violation for this path.
    Failed,
    /// The verifier has not implemented or completed the proof for this path.
    Unknown,
}

/// Result for one required property along one path to a callsite.
#[derive(Clone, Debug)]
pub struct PropertyCheckResult<'tcx> {
    /// Unsafe callsite being checked.
    pub callsite: CallsiteLocation,
    /// Index of the path in the callsite path set.
    pub path_index: usize,
    /// Required property checked on this path.
    pub property: Property<'tcx>,
    /// Current verification status.
    pub result: CheckResult,
}

/// Verification report for one function target.
#[derive(Clone, Debug)]
pub struct VerificationReport<'tcx> {
    /// Function that was verified.
    pub function: DefId,
    /// Per-path property results emitted by the verifier.
    pub results: Vec<PropertyCheckResult<'tcx>>,
}

impl<'tcx> VerificationReport<'tcx> {
    /// Create an empty report for a function target.
    pub fn new(function: DefId) -> Self {
        Self {
            function,
            results: Vec::new(),
        }
    }

    /// Add one path/property check result to this report.
    pub fn push(&mut self, result: PropertyCheckResult<'tcx>) {
        self.results.push(result);
    }

    /// Return the number of check results in this report.
    pub fn len(&self) -> usize {
        self.results.len()
    }

    /// Return true when this report contains no check results.
    pub fn is_empty(&self) -> bool {
        self.results.is_empty()
    }
}
