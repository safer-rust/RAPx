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
    contract::{ContractExpr, Property, PropertyArg},
    helpers::Checkpoint,
    primitive::PrimitiveCall,
    verifier::ForwardVisitResult,
};

/// Check `InBound` by lowering it to a common bounds obligation.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    // An `InBound(index_access(slice, indices))` over an array that a preceding
    // `get_disjoint`-style validator has checked is discharged by that trusted
    // summary.  Checked up front because the array-index contract does not
    // always rebind to a resolvable place at the call site.
    if property
        .args
        .iter()
        .any(|arg| matches!(arg, PropertyArg::Expr(ContractExpr::IndexAccess { .. })))
        && checker.checkpoint_uses_validated_array(checkpoint, forward)
    {
        return SmtCheckResult::proved(
            "InBound proved: indices validated in-bounds by a preceding disjoint check",
        );
    }

    if let Some(predicates) =
        checker.property_index_access_in_bound_predicates(checkpoint, property)
    {
        return checker.prove_obligation(
            checkpoint,
            forward,
            SmtObligation::Predicate { predicates },
            property.null_guard.as_ref(),
        );
    }

    let Some(target) = checker.property_target(Some(checkpoint), property) else {
        rap_debug!("  [SMT InBound] target could not be resolved");
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker
        .property_required_ty(Some(checkpoint), property)
        .or_else(|| checker.infer_pointee_ty(checkpoint.caller, &target))
    else {
        rap_debug!("  [SMT InBound] type could not be resolved");
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let elem_size = checker
        .type_layout(checkpoint.caller, required_ty)
        .map(|(_, s)| s)
        .unwrap_or(0);
    let access_count = checker
        .property_len_expr(Some(checkpoint), property)
        .and_then(|expr| checker.contract_expr_to_smt_term(checkpoint.caller, &expr, None))
        .unwrap_or(SmtTerm::Const(1));

    if let Some(obligation) =
        pointer_arithmetic_obligation(checker, checkpoint, required_ty, access_count.clone())
    {
        return checker.prove_obligation(
            checkpoint,
            forward,
            obligation,
            property.null_guard.as_ref(),
        );
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
        property.null_guard.as_ref(),
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
    let Some(target) = checker.property_target(None, property) else {
        return SmtCheckResult::unknown("InBound target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(None, property) else {
        return SmtCheckResult::unknown("InBound type could not be resolved");
    };
    let elem_size = checker
        .type_layout(caller, required_ty)
        .map(|(_, s)| s)
        .unwrap_or(0);
    let Some(access_count_expr) = checker.property_len_expr(None, property) else {
        return SmtCheckResult::unknown("InBound length argument could not be resolved");
    };
    let Some(access_count) = checker.contract_expr_to_smt_term(caller, &access_count_expr, None)
    else {
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
