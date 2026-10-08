//! Diagnostics and summaries for the staged verifier pipeline.
//!
//! The driver and later checking stages report their per-path property results
//! through the types in this module.  Keeping these types here leaves the driver
//! focused on orchestration.

use rustc_hir::def_id::DefId;

use super::contract::Property;
use crate::helpers::mir_scan::CheckpointLocation;

/// Why a [`CheckResult::Unknown`] could not be discharged.
///
/// Carried by the `Unknown` variant so the report can distinguish a solver
/// timeout (the common case under the fixed per-query budget) from a structural
/// "no rule for this shape" gap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum UnknownReason {
    /// The SMT solver returned `unknown` — with the fixed per-query timeout
    /// this is effectively a timeout on a query it could not decide in time.
    SmtTimeout,
    /// The checker has no rule for this shape (unsupported property, unannotated
    /// callee, unresolvable operand, undecidable generic, …).
    Unimplemented,
}

impl UnknownReason {
    /// Merge two reasons, keeping the more diagnostic one.
    fn merge(self, other: UnknownReason) -> UnknownReason {
        match (self, other) {
            (UnknownReason::SmtTimeout, _) | (_, UnknownReason::SmtTimeout) => {
                UnknownReason::SmtTimeout
            }
            _ => UnknownReason::Unimplemented,
        }
    }
}

/// Verification status for one required property on one path.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum CheckResult {
    /// Proved by a *sound structural rule* (a fast-path that needs no solver
    /// query): ZST guards, zero-element access, tracked invariants/flags,
    /// type-level transparency, provenance-origin classification.  These are
    /// the rules that must be audited for soundness.
    ProvedByRule,
    /// Proved by an *SMT query*: the solver showed the negation is unsatisfiable
    /// (numeric bounds, byte-range coverage, alignment modulo/linear checks).
    ProvedBySmt,
    /// The verifier found a possible violation for this path.
    Failed,
    /// The verifier has not implemented or completed the proof for this path;
    /// the reason is carried in the payload.
    Unknown(UnknownReason),
}

impl CheckResult {
    /// Whether this result counts as "proved" (by rule or by SMT).
    pub(crate) fn is_proved(&self) -> bool {
        matches!(self, CheckResult::ProvedByRule | CheckResult::ProvedBySmt)
    }

    /// The user-facing label for this result.  `ProvedByRule` and `ProvedBySmt`
    /// both report as `"Proved"` — the rule/SMT distinction is an internal
    /// audit signal, not part of the report.  An `Unknown` result is suffixed
    /// with its reason when it is not the generic unimplemented case.
    pub(crate) fn label(&self) -> &'static str {
        match self {
            CheckResult::ProvedByRule | CheckResult::ProvedBySmt => "Proved",
            CheckResult::Failed => "Failed",
            CheckResult::Unknown(UnknownReason::SmtTimeout) => "Unknown (timeout)",
            CheckResult::Unknown(UnknownReason::Unimplemented) => "Unknown",
        }
    }

    /// AND-combine two results: any `Failed` → `Failed`; any `Unknown` →
    /// `Unknown`; only all-proved → proved (`Rule` when every conjunct was a
    /// rule, otherwise `Smt`).
    pub(crate) fn and(self, other: CheckResult) -> CheckResult {
        match (self, other) {
            (CheckResult::Failed, _) | (_, CheckResult::Failed) => CheckResult::Failed,
            (CheckResult::Unknown(a), CheckResult::Unknown(b)) => {
                CheckResult::Unknown(a.merge(b))
            }
            (CheckResult::Unknown(a), _) | (_, CheckResult::Unknown(a)) => CheckResult::Unknown(a),
            (CheckResult::ProvedByRule, CheckResult::ProvedByRule) => CheckResult::ProvedByRule,
            _ => CheckResult::ProvedBySmt,
        }
    }

    /// OR-combine two results: any proved → proved (a `Rule` proof dominates);
    /// all `Failed` → `Failed`; otherwise `Unknown`.
    pub(crate) fn or(self, other: CheckResult) -> CheckResult {
        match (self, other) {
            (CheckResult::ProvedByRule, _) | (_, CheckResult::ProvedByRule) => {
                CheckResult::ProvedByRule
            }
            (CheckResult::ProvedBySmt, _) | (_, CheckResult::ProvedBySmt) => {
                CheckResult::ProvedBySmt
            }
            (CheckResult::Failed, CheckResult::Failed) => CheckResult::Failed,
            (CheckResult::Unknown(a), CheckResult::Unknown(b)) => {
                CheckResult::Unknown(a.merge(b))
            }
            (CheckResult::Unknown(a), _) | (_, CheckResult::Unknown(a)) => CheckResult::Unknown(a),
        }
    }
}

/// Result for one required property along one path to a checkpoint.
#[derive(Clone, Debug)]
pub(crate) struct PropertyCheckResult<'tcx> {
    /// Unsafe checkpoint being checked.
    pub checkpoint: CheckpointLocation,
    /// Index of the checkpoint in the function-level checkpoint list.
    pub checkpoint_index: usize,
    /// Index of the path in the checkpoint path set.
    pub path_index: usize,
    /// Index of the property in the checkpoint-level property list.
    pub property_index: usize,
    /// Required property checked on this path.
    pub property: Property<'tcx>,
    /// Current verification status.
    pub result: CheckResult,
    /// Optional path-local diagnostic message generated by the verifier.
    pub diagnostics: Option<String>,
    /// Human-readable path description.
    pub path_description: String,
    /// Callee name for this checkpoint.
    pub callee_name: String,
}

/// Verification report for one function target.
#[derive(Clone, Debug)]
pub(crate) struct VerificationReport<'tcx> {
    /// Function that was verified.
    pub function: DefId,
    /// Per-path property results emitted by the verifier.
    pub results: Vec<PropertyCheckResult<'tcx>>,
}

impl<'tcx> VerificationReport<'tcx> {
    /// Create an empty report for a function target.
    pub(crate) fn new(function: DefId) -> Self {
        Self {
            function,
            results: Vec::new(),
        }
    }

    /// Add one path/property check result to this report.
    pub(crate) fn push(&mut self, result: PropertyCheckResult<'tcx>) {
        self.results.push(result);
    }

    /// Render the whole report as a readable multi-line diagnostic.
    pub(crate) fn describe(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "[rapx::verify::diagnostics] function {:?}: {} check item(s)\n",
            self.function,
            self.results.len()
        ));

        for (index, result) in self.results.iter().enumerate() {
            out.push_str(&format!(
                "  check #{index}: checkpoint #{}, bb{}, path #{}, property #{} {:?}, result {}\n",
                result.checkpoint_index,
                result.checkpoint.block.as_usize(),
                result.path_index,
                result.property_index,
                result.property.kind(),
                result.result.label()
            ));

            if let Some(diagnostics) = &result.diagnostics {
                out.push_str(diagnostics);
                if !diagnostics.ends_with('\n') {
                    out.push('\n');
                }
            }
        }

        out
    }
}
