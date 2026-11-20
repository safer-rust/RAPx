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
            Self::UnresolvedUnsafeCall => out.push("unresolved_unsafe_call"),
            Self::MissingContract(_) => out.push("missing_contract"),
            Self::UnsupportedProperty => out.push("unsupported_property"),
            Self::Unimplemented => out.push("unimplemented"),
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

    /// OR-combine two results: any proved → proved (a `Rule` proof dominates).
    /// Separate counterexamples for the disjuncts do not prove their OR false.
    pub(crate) fn or(self, other: CheckResult) -> CheckResult {
        match (self, other) {
            (CheckResult::ProvedByRule, _) | (_, CheckResult::ProvedByRule) => {
                CheckResult::ProvedByRule
            }
            (CheckResult::ProvedBySmt, _) | (_, CheckResult::ProvedBySmt) => {
                CheckResult::ProvedBySmt
            }
            (CheckResult::Failed, CheckResult::Failed) => {
                // Separate counterexamples do not establish a common witness.
                CheckResult::Unknown(UnknownReason::UnsupportedProperty)
            }
            (CheckResult::Unknown(a), CheckResult::Unknown(b)) => CheckResult::Unknown(a.merge(b)),
            (CheckResult::Unknown(a), _) | (_, CheckResult::Unknown(a)) => CheckResult::Unknown(a),
        }
    }

    pub(crate) fn disjunction(results: impl IntoIterator<Item = CheckResult>) -> CheckResult {
        let mut results = results.into_iter();
        let Some(first) = results.next() else {
            return CheckResult::Failed;
        };
        results.fold(first, CheckResult::or)
    }

    /// A false guard is independent of the symbolic program state. When all
    /// other disjuncts except one are false guards, that disjunct's witness is
    /// also a witness against the whole OR.
    pub(crate) fn disjunction_with_guards(
        results: impl IntoIterator<Item = (CheckResult, bool)>,
    ) -> CheckResult {
        let results: Vec<_> = results.into_iter().collect();
        if !results.is_empty()
            && results
                .iter()
                .all(|(result, _)| matches!(result, CheckResult::Failed))
            && results.iter().filter(|(_, guard)| *guard).count() + 1 >= results.len()
        {
            return CheckResult::Failed;
        }
        Self::disjunction(results.into_iter().map(|(result, _)| result))
    }
}

/// Result for one property on a path to a checkpoint or function exit.
#[derive(Clone, Debug)]
pub(crate) struct PropertyCheckResult<'tcx> {
    /// MIR block containing the checked operation or exit.
    pub checkpoint: CheckpointLocation,
    /// Distinguishes checks sharing a MIR block; exit checks use the block index.
    pub checkpoint_index: usize,
    /// Property checked on this path, or a synthetic Unknown obligation.
    pub property: Property<'tcx>,
    /// Current verification status.
    pub result: CheckResult,
    /// Human-readable path or path-limit marker.
    pub path_desc: String,
    /// Callee name or synthetic obligation label.
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
                "  check #{index}: checkpoint #{}, bb{}, path {}, property {:?}, callee {}, result {:?}\n",
                result.checkpoint_index,
                result.checkpoint.block.as_usize(),
                result.path_desc,
                result.property.kind(),
                result.callee_name,
                result.result,
            ));
        }

        out
    }
}
