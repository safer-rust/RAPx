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

use super::common::{SmtCheckResult, SmtChecker, SmtObligation, SmtTerm};
use crate::verify::{
    contract::Property, helpers::Checkpoint, primitive::PrimitiveCall, verifier::ForwardVisitResult,
};

/// Check `InBound` by lowering it to a common bounds obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if let Some(predicates) =
        checker.property_index_access_in_bound_predicates(checkpoint, property)
    {
        return checker.prove_obligation(
            checkpoint,
            forward,
            SmtObligation::Predicate { predicates },
        );
    }

    let Some(target) = checker.property_target(checkpoint, property) else {
        rap_debug!("  [SMT InBound] target could not be resolved");
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(checkpoint, property) else {
        rap_debug!("  [SMT InBound] type could not be resolved");
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let Some((_, elem_size)) = checker.type_layout(checkpoint.caller, required_ty) else {
        rap_debug!("  [SMT InBound] layout unavailable for {:?}", required_ty);
        return SmtCheckResult::unknown(format!(
            "InBound layout unavailable for {:?}",
            required_ty
        ));
    };
    let Some(access_count_expr) = checker.property_len_expr(checkpoint, property) else {
        rap_debug!("  [SMT InBound] length argument could not be resolved");
        return SmtCheckResult::unknown("InBound length argument could not be resolved");
    };
    let Some(access_count) =
        checker.contract_expr_to_smt_term(checkpoint.caller, &access_count_expr)
    else {
        rap_debug!(
            "  [SMT InBound] length expression could not be lowered: {:?}",
            access_count_expr
        );
        return SmtCheckResult::unknown("InBound length argument could not be lowered to SMT");
    };

    if let Some(obligation) =
        pointer_arithmetic_obligation(checker, checkpoint, required_ty, access_count.clone())
    {
        return checker.prove_obligation(checkpoint, forward, obligation);
    }

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::InBounds {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elem_size,
            access_count,
        },
    )
}

fn pointer_arithmetic_obligation<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    required_ty: rustc_middle::ty::Ty<'tcx>,
    count: SmtTerm,
) -> Option<SmtObligation> {
    let callee_name = checker.tcx.def_path_str(checkpoint.callee?);
    let primitive = PrimitiveCall::classify(&callee_name)?;
    if !primitive.is_pointer_arithmetic() {
        return None;
    }

    let base = checker.callsite_arg_place(checkpoint, 0)?;
    let zero = SmtTerm::Const(0);
    let negative_count = SmtTerm::Sub(Box::new(zero.clone()), Box::new(count.clone()));
    let (lower_delta, upper_delta) = if primitive.is_pointer_sub_like() {
        (negative_count, zero)
    } else if primitive.is_signed_pointer_arithmetic() {
        (count.clone(), count)
    } else {
        (zero, count)
    };

    Some(SmtObligation::PointerRangeInBounds {
        place: base,
        ty_name: format!("{required_ty:?}"),
        lower_delta,
        upper_delta,
    })
}

/// Check `InBound` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target_direct(property) else {
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty_direct(property) else {
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let Some((_, elem_size)) = checker.type_layout(caller, required_ty) else {
        return SmtCheckResult::unknown(format!(
            "InBound layout unavailable for {:?}",
            required_ty
        ));
    };
    let Some(access_count_expr) = checker.property_len_expr_direct(property) else {
        return SmtCheckResult::unknown("InBound length argument could not be resolved");
    };
    let Some(access_count) = checker.contract_expr_to_smt_term(caller, &access_count_expr) else {
        return SmtCheckResult::unknown("InBound length argument could not be lowered to SMT");
    };

    checker.prove_obligation_for_checkpoint(
        caller,
        forward,
        SmtObligation::InBounds {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elem_size,
            access_count,
        },
    )
}
