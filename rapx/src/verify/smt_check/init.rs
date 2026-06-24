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

use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};

/// Check `Init` by lowering it to a common initialized-memory obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("Init target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(checkpoint, property) else {
        return SmtCheckResult::unknown("Init type could not be resolved");
    };
    let Some(elements_expr) = checker.property_len_expr(checkpoint, property) else {
        return SmtCheckResult::unknown("Init element-count argument could not be resolved");
    };
    let Some(elements_term) = checker.contract_expr_to_smt_term(checkpoint.caller, &elements_expr)
    else {
        return SmtCheckResult::unknown("Init element-count argument could not be lowered to SMT");
    };

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Initialized {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements: elements_term,
        },
    )
}

/// Check `Init` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target_direct(property) else {
        return SmtCheckResult::unknown("Init target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty_direct(property) else {
        return SmtCheckResult::unknown("Init type could not be resolved");
    };
    let Some(elements_expr) = checker.property_len_expr_direct(property) else {
        return SmtCheckResult::unknown("Init element-count argument could not be resolved");
    };
    let Some(elements) = checker.contract_expr_to_smt_term(caller, &elements_expr) else {
        return SmtCheckResult::unknown("Init element-count argument could not be lowered to SMT");
    };

    checker.prove_obligation_for_checkpoint(
        caller,
        forward,
        SmtObligation::Initialized {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements,
        },
    )
}
