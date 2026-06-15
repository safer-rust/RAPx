//! SMT lowering for the `InBound` safety property.
//!
//! The current implementation handles the common slice pattern:
//!
//! ```text
//! ptr = slice.as_ptr()
//! current = ptr.add(index)
//! guard: index < slice.len()
//! property: InBound(current, T, n)
//! ```
//!
//! The module only lowers the property to `SmtObligation::InBounds`.  The
//! common SMT model is responsible for matching `as_ptr`, `ptr.add`, `len`, and
//! branch facts from the forward visit result.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{
    contract::{ContractExpr, Property},
    forward_visit::ForwardVisitResult,
    helpers::Callsite,
};

/// Check `InBound` by lowering it to a common bounds obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let Some((_, elem_size)) = checker.type_layout(callsite.caller, required_ty) else {
        return SmtCheckResult::unknown(format!(
            "InBound layout unavailable for {:?}",
            required_ty
        ));
    };
    let Some(access_count_expr) = checker.property_len_expr(callsite, property) else {
        return SmtCheckResult::unknown("InBound length argument could not be resolved");
    };
    let ContractExpr::Const(access_count) = access_count_expr else {
        return SmtCheckResult::unknown(
            "InBound currently requires a constant element-count argument",
        );
    };
    let Some(access_count) = u64::try_from(access_count).ok() else {
        return SmtCheckResult::unknown("InBound element-count argument is too large");
    };

    checker.prove_obligation(
        callsite,
        forward,
        SmtObligation::InBounds {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elem_size,
            access_count,
        },
    )
}
