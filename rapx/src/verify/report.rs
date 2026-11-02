//! Diagnostics and summaries for the staged verifier pipeline.
//!
//! The driver and later checking stages report their per-path property results
//! through the types in this module.  Keeping these types here leaves the driver
//! focused on orchestration.

use rustc_hir::def_id::DefId;

use super::contract::Property;
use crate::verify::checkpoint::CheckpointLocation;

pub(crate) const PATH_LIMIT_DESCRIPTION: &str = "[not enumerated: path limit reached]";

/// Why a [`CheckResult::Unknown`] could not be discharged.
///
/// Carried by the `Unknown` variant so the report can identify incomplete proofs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UnknownReason {
    SmtUnknown(String),
    /// The inline recursion limit was reached, so the callee's body was not
    /// executed and the memory state is incomplete.
    InlineDepthExceeded,
    UnsupportedMir(Vec<String>),
    UnsupportedEffect(Vec<String>),
    MissingMir(Vec<String>),
    OpaqueControlFlow(Vec<String>),
    IncompleteInlineBranch,
    UnmodeledIntrinsic(String),
    CallbackMayInvalidate,
    UnresolvedUnsafeCall,
    MissingContract(String),
    UnsupportedProperty,
    /// A checker cannot resolve a value or supported property shape.
    Unimplemented,
    Multiple(Vec<UnknownReason>),
}

impl UnknownReason {
    pub(crate) fn categories(&self, out: &mut Vec<&'static str>) {
        match self {
            Self::SmtUnknown(reason) if reason == "timeout" => out.push("smt_timeout"),
            Self::SmtUnknown(_) => out.push("smt_unknown"),
            Self::InlineDepthExceeded => out.push("inline_depth"),
            Self::UnsupportedMir(_) => out.push("unsupported_mir"),
            Self::UnsupportedEffect(_) => out.push("unsupported_effect"),
            Self::MissingMir(_) => out.push("missing_mir"),
            Self::OpaqueControlFlow(_) => out.push("opaque_control_flow"),
            Self::IncompleteInlineBranch => out.push("incomplete_inline_branch"),
            Self::UnmodeledIntrinsic(_) => out.push("unmodeled_intrinsic"),
            Self::CallbackMayInvalidate => out.push("callback_invalidation"),
            Self::UnresolvedUnsafeCall => out.push("unresolved_unsafe_call"),
            Self::MissingContract(_) => out.push("missing_contract"),
            Self::UnsupportedProperty => out.push("unsupported_property"),
            Self::Unimplemented => out.push("unresolved_value"),
            Self::Multiple(reasons) => {
                for reason in reasons {
                    reason.categories(out);
                }
            }
        }
    }

    pub(crate) fn from_solver(solver: &z3::Solver<'_>) -> Self {
        Self::SmtUnknown(
            solver
                .get_reason_unknown()
                .unwrap_or_else(|| "reason unavailable".to_string()),
        )
    }

    fn description(&self) -> String {
        match self {
            Self::SmtUnknown(reason) if reason == "timeout" => "timeout".to_string(),
            Self::SmtUnknown(reason) => format!("SMT: {reason}"),
            Self::InlineDepthExceeded => "inline depth".to_string(),
            Self::UnsupportedMir(_) => "unsupported MIR".to_string(),
            Self::UnsupportedEffect(_) => "unsupported call effect".to_string(),
            Self::MissingMir(_) => "MIR unavailable".to_string(),
            Self::OpaqueControlFlow(_) => "opaque call controls branch".to_string(),
            Self::IncompleteInlineBranch => "incomplete inline branch".to_string(),
            Self::UnmodeledIntrinsic(_) => "unmodeled intrinsic".to_string(),
            Self::CallbackMayInvalidate => "callback may invalidate allocation".to_string(),
            Self::UnresolvedUnsafeCall => "unresolved unsafe call".to_string(),
            Self::MissingContract(callee) => format!("missing safety contract: {callee}"),
            Self::UnsupportedProperty => "unsupported property".to_string(),
            Self::Unimplemented => "unresolved value or unsupported shape".to_string(),
            Self::Multiple(reasons) => reasons
                .iter()
                .map(Self::description)
                .collect::<Vec<_>>()
                .join("; "),
        }
    }

    pub(crate) fn unsupported_details(&self, out: &mut Vec<String>) {
        match self {
            Self::UnsupportedMir(details) => out.extend(details.iter().cloned()),
            Self::UnsupportedEffect(details) => out.extend(details.iter().cloned()),
            Self::MissingMir(callees) => {
                out.extend(
                    callees
                        .iter()
                        .map(|callee| format!("MIR unavailable: {callee}")),
                );
            }
            Self::OpaqueControlFlow(details) => out.extend(details.iter().cloned()),
            Self::UnmodeledIntrinsic(name) => out.push(format!("intrinsic: {name}")),
            Self::MissingContract(callee) => out.push(format!("missing contract: {callee}")),
            Self::Multiple(reasons) => {
                for reason in reasons {
                    reason.unsupported_details(out);
                }
            }
            _ => {}
        }
    }

    pub(crate) fn merge(self, other: UnknownReason) -> UnknownReason {
        let mut reasons = match self {
            Self::Multiple(reasons) => reasons,
            reason => vec![reason],
        };
        let others = match other {
            Self::Multiple(reasons) => reasons,
            reason => vec![reason],
        };
        for reason in others {
            if !reasons.contains(&reason) {
                reasons.push(reason);
            }
        }
        if reasons.len() == 1 {
            reasons.pop().unwrap()
        } else {
            Self::Multiple(reasons)
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

/// Soundness of a group of required checks. The order defines conjunction:
/// a failure wins over an incomplete proof, which wins over a proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Soundness {
    Sound,
    Unknown,
    Failed,
}

impl Soundness {
    pub(crate) fn join(self, other: Self) -> Self {
        self.max(other)
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Sound => "SOUND",
            Self::Unknown => "UNKNOWN",
            Self::Failed => "FAILED",
        }
    }
}

impl CheckResult {
    pub(crate) fn soundness(&self) -> Soundness {
        match self {
            Self::ProvedByRule | Self::ProvedBySmt => Soundness::Sound,
            Self::Unknown(_) => Soundness::Unknown,
            Self::Failed => Soundness::Failed,
        }
    }

    /// Whether this result counts as "proved" (by rule or by SMT).
    pub(crate) fn is_proved(&self) -> bool {
        matches!(self, CheckResult::ProvedByRule | CheckResult::ProvedBySmt)
    }

    /// The user-facing label for this result.
    pub(crate) fn label(&self) -> String {
        match self {
            CheckResult::ProvedByRule | CheckResult::ProvedBySmt => "Proved".to_string(),
            CheckResult::Failed => "Failed".to_string(),
            CheckResult::Unknown(reason) => format!("Unknown ({})", reason.description()),
        }
    }

    /// AND-combine two results: any `Failed` → `Failed`; any `Unknown` →
    /// `Unknown`; only all-proved → proved (`Rule` when every conjunct was a
    /// rule, otherwise `Smt`).
    pub(crate) fn and(self, other: CheckResult) -> CheckResult {
        match self.soundness().join(other.soundness()) {
            Soundness::Failed => CheckResult::Failed,
            Soundness::Unknown => match (self, other) {
                (CheckResult::Unknown(a), CheckResult::Unknown(b)) => {
                    CheckResult::Unknown(a.merge(b))
                }
                (CheckResult::Unknown(a), _) | (_, CheckResult::Unknown(a)) => {
                    CheckResult::Unknown(a)
                }
                _ => unreachable!(),
            },
            Soundness::Sound => match (self, other) {
                (CheckResult::ProvedByRule, CheckResult::ProvedByRule) => CheckResult::ProvedByRule,
                _ => CheckResult::ProvedBySmt,
            },
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
            (CheckResult::Unknown(a), CheckResult::Unknown(b)) => CheckResult::Unknown(a.merge(b)),
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

#[cfg(test)]
mod tests {
    use super::{CheckResult, Soundness, UnknownReason};

    #[test]
    fn soundness_join_uses_failed_unknown_sound_priority() {
        assert_eq!(Soundness::Sound.join(Soundness::Sound), Soundness::Sound);
        assert_eq!(
            Soundness::Sound.join(Soundness::Unknown),
            Soundness::Unknown
        );
        assert_eq!(
            Soundness::Unknown.join(Soundness::Failed),
            Soundness::Failed
        );
        assert_eq!(
            Soundness::Failed.join(Soundness::Unknown),
            Soundness::Failed
        );
    }

    #[test]
    fn unknown_labels_preserve_solver_reason_and_multiple_causes() {
        let timeout = CheckResult::Unknown(UnknownReason::SmtUnknown("timeout".into()));
        assert_eq!(timeout.label(), "Unknown (timeout)");

        let combined = UnknownReason::UnsupportedMir(Vec::new())
            .merge(UnknownReason::SmtUnknown("incomplete".into()));
        assert_eq!(
            CheckResult::Unknown(combined).label(),
            "Unknown (unsupported MIR; SMT: incomplete)"
        );
    }
}
