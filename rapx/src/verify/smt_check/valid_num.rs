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
use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};

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

    if checker.validnum_is_slice_size_invariant(checkpoint, property, forward) {
        return SmtCheckResult::proved(
            "ValidNum proved: slice-size language invariant size_of(T) * slice.len() <= isize::MAX",
        );
    }

    // `align_of::<T>()` is always >= 1 for any type.  When a ValidNum predicate
    // is a single `x != 0` and `x` resolves to the align_of call argument at the
    // callsite (e.g. `ptr::align_offset(ptr, align_of::<U>())` requiring `a != 0`),
    // the constraint holds trivially.  The SMT model cannot prove this because
    // `align_of` is a symbolic constant, so we short-circuit here.
    if checker.validnum_is_align_nonzero(checkpoint, property, forward) {
        return SmtCheckResult::proved(
            "ValidNum proved: align_of::<T>() >= 1 for every T",
        );
    }

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Predicate {
            predicates: smt_predicates,
        },
    )
}
