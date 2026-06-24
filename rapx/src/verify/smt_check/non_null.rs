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
use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};

/// Check `NonNull` by lowering it to `SmtObligation::NonZero`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("NonNull target could not be resolved");
    };

    let obligation = SmtObligation::NonZero { place: target };
    checker.prove_obligation(checkpoint, forward, obligation)
}
