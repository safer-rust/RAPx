//! SMT lowering for the `ValidNum` safety property.
//!
//! `ValidNum` carries one or more numeric predicates, for example:
//!
//! ```text
//! ValidNum(i < len)
//! ValidNum(size_of(T) * len <= isize::MAX)
//! ```
//!
//! This module only rebinds callee-side contract expressions to the concrete
//! checkpoint arguments and converts them to common SMT predicates.  The shared
//! backend discharges the query by checking whether the negated predicate is
//! satisfiable under the forward path facts.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, verifier::ForwardVisitResult, helpers::Checkpoint};

/// Check `ValidNum` by lowering all predicates to a common predicate obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(smt_predicates) = checker.property_numeric_smt_predicates(checkpoint, property) else {
        return SmtCheckResult::unknown("ValidNum predicate could not be lowered to SMT");
    };

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Predicate {
            predicates: smt_predicates,
        },
    )
}
