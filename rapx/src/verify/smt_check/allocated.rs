//! SMT lowering for the `Allocated` safety property.
//!
//! `Allocated(p, T, n)` means the whole `n`-element range starting at `p`
//! belongs to a single live allocation object.  The lowering is intentionally
//! object-sensitive: adjacent stack locals do not form one larger allocation
//! even when their addresses happen to be close.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};

/// Check `Allocated` by lowering it to a common allocation obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("Allocated target could not be resolved");
    };
    if checker.property_required_ty(checkpoint, property).is_none()
        && checker.property_len_expr(checkpoint, property).is_none()
    {
        if checker.is_len_carrying_place_for_caller(checkpoint.caller, &target) {
            return SmtCheckResult::proved(
                "allocation proved: safe slice/reference target carries one live allocation object",
            );
        }
        return SmtCheckResult::unknown(
            "Allocated target has no type/count arguments and is not a supported slice/reference",
        );
    }
    let Some(required_ty) = checker.property_required_ty(checkpoint, property) else {
        return SmtCheckResult::unknown("Allocated type could not be resolved");
    };
    let Some(elements_expr) = checker.property_len_expr(checkpoint, property) else {
        return SmtCheckResult::unknown("Allocated element-count argument could not be resolved");
    };
    let Some(elements) = checker.contract_expr_to_smt_term(checkpoint.caller, &elements_expr)
    else {
        return SmtCheckResult::unknown(
            "Allocated element-count argument could not be lowered to SMT",
        );
    };

    if let Some(reason) = super::provenance::vec_from_raw_parts_roundtrip(checker, checkpoint) {
        return SmtCheckResult::proved(format!("Allocated proved: {reason}"));
    }

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Allocated {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements,
        },
    )
}

/// Check `Allocated` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target_direct(property) else {
        return SmtCheckResult::unknown("Allocated target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty_direct(property) else {
        return SmtCheckResult::unknown("Allocated type could not be resolved");
    };
    let Some(elements_expr) = checker.property_len_expr_direct(property) else {
        return SmtCheckResult::unknown("Allocated element-count argument could not be resolved");
    };
    let Some(elements) = checker.contract_expr_to_smt_term(caller, &elements_expr) else {
        return SmtCheckResult::unknown(
            "Allocated element-count argument could not be lowered to SMT",
        );
    };
    checker.prove_obligation_for_checkpoint(
        caller,
        forward,
        SmtObligation::Allocated {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements,
        },
    )
}
