//! SMT lowering for the `Init` safety property.
//!
//! This first version proves only a local one-element write pattern:
//!
//! ```text
//! ptr.write(value)
//! require Init(ptr, T, 1)
//! ```
//!
//! Forward visit records `ptr.write` as a `KnownInit` fact.  The common SMT
//! backend then checks whether the Init target has the same address as a known
//! initialized pointer.  Range initialization across loops still needs a loop
//! summary and is intentionally left as `Unknown`.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `Init` by lowering it to a common initialized-memory obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("Init target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("Init type could not be resolved");
    };
    let Some(elements) = checker.property_len_const(property) else {
        return SmtCheckResult::unknown(
            "Init currently requires a constant element-count argument",
        );
    };

    checker.prove_obligation(
        callsite,
        forward,
        SmtObligation::Initialized {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements,
        },
    )
}
