//! Diagnostics and summaries for the staged verifier pipeline.
//!
//! The driver and later checking stages report their per-path property results
//! through the types in this module.  Keeping these types here leaves the driver
//! focused on orchestration.

use super::contract::Property;
use crate::verify::checkpoint::CheckpointLocation;

pub(crate) const PATH_LIMIT_DESCRIPTION: &str = "[not enumerated: path limit reached]";

/// Why a [`CheckResult::Unknown`] could not be discharged.
///
/// Carried by the `Unknown` variant so the report can identify incomplete proofs.
///
/// # Agent Rules
/// Do not add new variants or fields without human approval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum UnknownReason {
    /// The SMT solver could not decide the query and returned this reason.
    SmtUnknown(String),

    /// A callee's MIR body was unavailable.
    MissingMir(Vec<String>),
    /// The VM could not model one or more MIR operations.
    UnsupportedMir(Vec<String>),
    /// The VM could not model one or more call effects.
    UnsupportedEffect(Vec<String>),
    /// An intrinsic result was left opaque because its effect was not modeled.
    UnmodeledIntrinsic(String),

    /// An inlined callee stopped at the depth limit or an incomplete branch.
    IncompleteInline,
    /// An opaque value influenced a control-flow decision.
    OpaqueControlFlow(Vec<String>),
    /// An unsafe call's callee could not be resolved.
    UnresolvedUnsafeCall,

    /// A required safety contract was not found for this callee.
    MissingContract(String),
    /// The checker cannot prove this property with its supported rules.
    UnsupportedProperty,
    /// A checker could not resolve a value or handle this property shape.
    Unimplemented,

    /// Several independent reasons contributed to the unknown result.
    Multiple(Vec<UnknownReason>),
}

impl UnknownReason {
    pub(crate) fn categories(&self, out: &mut Vec<&'static str>) {
        match self {
            Self::SmtUnknown(reason) if reason == "timeout" => out.push("smt_timeout"),
            Self::SmtUnknown(_) => out.push("smt_unknown"),
            Self::MissingMir(_) => out.push("missing_mir"),
            Self::UnsupportedMir(_) => out.push("unsupported_mir"),
            Self::UnsupportedEffect(_) => out.push("unsupported_effect"),
            Self::UnmodeledIntrinsic(_) => out.push("unmodeled_intrinsic"),
            Self::IncompleteInline => out.push("incomplete_inline"),
            Self::OpaqueControlFlow(_) => out.push("opaque_control_flow"),
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
        Self::SmtUnknown(solver.get_reason_unknown().unwrap_or_else(|| "reason unavailable".to_string()))
    }

    fn description(&self) -> String {
        match self {
            Self::SmtUnknown(reason) if reason == "timeout" => "timeout".to_string(),
            Self::SmtUnknown(reason) => format!("SMT: {reason}"),
            Self::MissingMir(_) => "MIR unavailable".to_string(),
            Self::UnsupportedMir(_) => "unsupported MIR".to_string(),
            Self::UnsupportedEffect(_) => "unsupported call effect".to_string(),
            Self::UnmodeledIntrinsic(_) => "unmodeled intrinsic".to_string(),
            Self::IncompleteInline => "incomplete inline".to_string(),
            Self::OpaqueControlFlow(_) => "opaque call controls branch".to_string(),
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
    /// Proved by a sound structural rule without an SMT query.
    ProvedByRule,
    /// Proved by an SMT query showing the negation is unsatisfiable.
    ProvedBySmt,
    /// The verifier found a possible violation for this path.
    Failed,
    /// The proof is incomplete; the payload records why.
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

    /// A false guard is independent of the symbolic program state. When all
    /// other disjuncts except one are false guards, that disjunct's witness is
    /// also a witness against the whole OR.
    pub(crate) fn disjunction_with_guards(
        results: impl IntoIterator<Item = (CheckResult, bool)>,
    ) -> CheckResult {
        let results: Vec<_> = results.into_iter().collect();
        if !results.is_empty()
            && results.iter().all(|(result, _)| matches!(result, CheckResult::Failed))
            && results.iter().filter(|(_, guard)| *guard).count() + 1 >= results.len()
        {
            return CheckResult::Failed;
        }
        results.into_iter().map(|(result, _)| result).reduce(CheckResult::or).unwrap_or(CheckResult::Failed)
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
