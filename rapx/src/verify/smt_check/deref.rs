//! SMT lowering for the `Deref` safety property.
//!
//! `Deref(p, T, n)` is the range-level part of pointer validity:
//!
//! ```text
//! Deref(p, T, n) = Allocated(p, T, n, *) && InBound(p, T, n)
//! ```
//!
//! The star in `Allocated` represents the current allocation object/provenance
//! abstraction.  This module keeps `Deref` as a composite SP and delegates the
//! object and bounds checks to their existing lowerings.

use super::{allocated, common::SmtCheckResult, in_bound};
use crate::verify::{
    contract::Property, helpers::Checkpoint, report::CheckResult, verifier::ForwardVisitResult,
};

/// Check `Deref` by proving both allocation and bounds obligations.
pub(crate) fn check<'tcx>(
    checker: &super::common::SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let allocated = allocated::check(checker, checkpoint, property, forward);
    let in_bound = in_bound::check(checker, checkpoint, property, forward);

    match (&allocated.result, &in_bound.result) {
        (CheckResult::Proved, CheckResult::Proved) => {
            SmtCheckResult::proved("Deref proved: target range is allocated and in bounds")
        }
        (CheckResult::Failed, _) | (_, CheckResult::Failed) => SmtCheckResult {
            result: CheckResult::Failed,
            query: None,
            notes: vec![String::from(
                "Deref failed: Allocated and InBound must both hold",
            )],
        },
        _ => SmtCheckResult::unknown("Deref unknown: Allocated or InBound is not proved"),
    }
    .with_note(format!(
        "primitive Allocated via SMT: {:?}",
        allocated.result
    ))
    .with_note(format!("primitive InBound via SMT: {:?}", in_bound.result))
}
