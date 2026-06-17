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
//! callsite arguments and converts them to common SMT predicates.  The shared
//! backend discharges the query by checking whether the negated predicate is
//! satisfiable under the forward path facts.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `ValidNum` by lowering all predicates to a common predicate obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(predicates) = checker.property_numeric_predicates(callsite, property) else {
        return SmtCheckResult::unknown("ValidNum predicates could not be resolved");
    };
    let smt_predicates = predicates
        .iter()
        .map(|predicate| checker.numeric_predicate_to_smt_predicate(callsite.caller, predicate))
        .collect::<Option<Vec<_>>>();
    let Some(smt_predicates) = smt_predicates else {
        return SmtCheckResult::unknown("ValidNum predicate could not be lowered to SMT");
    };

    checker.prove_obligation(
        callsite,
        forward,
        SmtObligation::Predicate {
            predicates: smt_predicates,
        },
    )
}
