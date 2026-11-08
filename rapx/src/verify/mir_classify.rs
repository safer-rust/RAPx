//! MIR forms that need no dedicated state transfer rule in RAPx's verifier.
//! Other supported forms are handled directly in each dispatcher's match arms.

use rustc_middle::mir::{StatementKind, TerminatorKind};

/// Statements with no state or relevance effect for RAPx's verifier.
pub(crate) fn is_noop_statement(kind: &StatementKind<'_>) -> bool {
    matches!(
        kind,
        StatementKind::FakeRead(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Coverage(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::ConstEvalCounter
                | StatementKind::Nop
                | StatementKind::BackwardIncompatibleDropHint { .. }
    )
}

/// Terminators whose branch or exit is handled by the path, without a state transfer here.
pub(crate) fn is_control_only_terminator(kind: &TerminatorKind<'_>) -> bool {
    matches!(
        kind,
        TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
    )
}
