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

use super::common::{SmtCheckResult, SmtChecker, SmtObligation, SmtTerm};

use crate::verify::{contract::Property, helpers::Checkpoint, verifier::ForwardVisitResult};
use rustc_middle::ty::{Ty, TyKind};

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

    // Detect the pattern `MaybeUninit<[E; N]>::assume_init()` following a
    // covering `for i in 0..N { base.add(i).write(v) }` loop.  When the
    // array length is a const generic and a write to every index `0..N` is
    // on the forward path, the whole array is initialized.
    if checker.maybeuninit_covering_init(checkpoint, &target, required_ty, forward) {
        return SmtCheckResult::proved(format!(
            "Init proved: MaybeUninit<[{required_ty:?}; N]> fully initialized by covering loop"
        ));
    }

    let Some(elements_expr) = checker.property_len_expr(checkpoint, property) else {
        return SmtCheckResult::unknown("Init element-count argument could not be resolved");
    };
    let Some(elements_term) = checker.contract_expr_to_smt_term(checkpoint.caller, &elements_expr)
    else {
        return SmtCheckResult::unknown("Init element-count argument could not be lowered to SMT");
    };

    let elem_size = compute_elem_size(checker, checkpoint.caller, required_ty);

    checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Initialized {
            place: target,
            ty_name: format!("{required_ty:?}"),
            elements: elements_term,
            elem_size,
            array_elem_size: array_elem_size(checker, checkpoint.caller, required_ty),
            array_len_term: array_len_term(checker, required_ty),
        },
    )
}

fn compute_elem_size<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    ty: Ty<'tcx>,
) -> Option<u64> {
    if let Some((_, size)) = checker.type_layout(caller, ty) {
        return Some(size);
    }
    None
}

fn array_elem_size<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    ty: Ty<'tcx>,
) -> Option<u64> {
    if let TyKind::Array(elem, _) = ty.kind() {
        checker.type_layout(caller, *elem).map(|(_, s)| s)
    } else {
        None
    }
}

fn array_len_term<'tcx>(checker: &SmtChecker<'tcx>, ty: Ty<'tcx>) -> Option<SmtTerm> {
    use rustc_middle::ty::ConstKind;
    if let TyKind::Array(_, len) = ty.kind() {
        if let Some(val) = len.try_to_target_usize(checker.tcx) {
            return Some(SmtTerm::Const(val));
        }
        if let ConstKind::Param(param) = len.kind() {
            return Some(SmtTerm::ConstParam(param.name.to_string()));
        }
        Some(SmtTerm::ConstParam(format!("Ty(usize, {len})")))
    } else {
        None
    }
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
            elem_size: compute_elem_size(checker, caller, required_ty),
            array_elem_size: array_elem_size(checker, caller, required_ty),
            array_len_term: array_len_term(checker, required_ty),
        },
    )
}
