//! User-facing labels and diagnostic details for verification results.

use crate::verify::report::{CheckResult, Soundness, UnknownReason};

impl UnknownReason {
    pub(super) fn categories(&self, out: &mut Vec<&'static str>) {
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
            Self::Multiple(reasons) => reasons.iter().map(Self::description).collect::<Vec<_>>().join("; "),
        }
    }

    pub(super) fn unsupported_details(&self, out: &mut Vec<String>) {
        match self {
            Self::UnsupportedMir(details) | Self::UnsupportedEffect(details) | Self::OpaqueControlFlow(details) => out.extend(details.iter().cloned()),
            Self::MissingMir(callees) => out.extend(callees.iter().map(|callee| format!("MIR unavailable: {callee}"))),
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
}

impl Soundness {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Sound => "SOUND",
            Self::Unknown => "UNKNOWN",
            Self::Failed => "FAILED",
        }
    }
}

impl CheckResult {
    /// The user-facing label for this result.
    pub(super) fn label(&self) -> String {
        match self {
            Self::ProvedByRule | Self::ProvedBySmt => "Proved".to_string(),
            Self::Failed => "Failed".to_string(),
            Self::Unknown(reason) => format!("Unknown ({})", reason.description()),
        }
    }
}
