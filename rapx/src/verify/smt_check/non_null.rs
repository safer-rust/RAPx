//! SMT lowering for the `NonNull` safety property.
//!
//! This module reduces:
//!
//! ```text
//! NonNull(p)
//! ```
//!
//! to the common SMT obligation:
//!
//! ```text
//! NonZero { place: p }
//! ```
//!
//! The common model asserts path-local facts such as reference-derived pointers
//! and `as_ptr` results as non-zero assumptions, then asks whether the target can
//! still be zero.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `NonNull` by lowering it to `SmtObligation::NonZero`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("NonNull target could not be resolved");
    };

    let obligation = SmtObligation::NonZero { place: target };
    checker.prove_obligation(callsite, forward, obligation)
}
