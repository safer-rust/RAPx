//! SMT lowering for the `Allocated` safety property.
//!
//! `Allocated(p, T, n)` means the whole `n`-element range starting at `p`
//! belongs to a single live allocation object.  The lowering is intentionally
//! object-sensitive: adjacent stack locals do not form one larger allocation
//! even when their addresses happen to be close.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `Allocated` by lowering it to a common allocation obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("Allocated target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("Allocated type could not be resolved");
    };
    let Some(elements_expr) = checker.property_len_expr(callsite, property) else {
        return SmtCheckResult::unknown("Allocated element-count argument could not be resolved");
    };
    let Some(elements) = checker.contract_expr_to_smt_term(callsite.caller, &elements_expr) else {
        return SmtCheckResult::unknown(
            "Allocated element-count argument could not be lowered to SMT",
        );
    };

    checker.prove_obligation(
        callsite,
        forward,
        SmtObligation::Allocated {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements,
        },
    )
}
