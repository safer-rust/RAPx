//! SMT lowering for the `Align` safety property.
//!
//! This module reduces:
//!
//! ```text
//! Align(p, T)
//! ```
//!
//! to the common SMT obligation:
//!
//! ```text
//! Aligned { place: p, align: align_of(T) }
//! ```
//!
//! The common model then proves the obligation by asking whether the path facts
//! plus the negated alignment goal are satisfiable.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, forward_visit::ForwardVisitResult, helpers::Callsite};

/// Check `Align` by lowering it to `SmtObligation::Aligned`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(callsite, property) else {
        return SmtCheckResult::unknown("SMT Align target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("SMT Align type could not be resolved");
    };
    let Some(required_align) = checker.required_alignment(callsite.caller, required_ty) else {
        return SmtCheckResult::unknown(format!(
            "SMT Align layout unavailable for {:?}",
            required_ty
        ));
    };

    let obligation = SmtObligation::Aligned {
        place: target,
        align: required_align,
        ty_name: format!("{required_ty:?}"),
    };
    checker.prove_obligation(callsite, forward, obligation)
}

/// Check `Align` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target_direct(property) else {
        return SmtCheckResult::unknown("SMT Align target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty_direct(property) else {
        return SmtCheckResult::unknown("SMT Align type could not be resolved");
    };
    let Some(required_align) = checker.required_alignment(caller, required_ty) else {
        return SmtCheckResult::unknown(format!(
            "SMT Align layout unavailable for {:?}",
            required_ty
        ));
    };

    let obligation = SmtObligation::Aligned {
        place: target,
        align: required_align,
        ty_name: format!("{required_ty:?}"),
    };
    checker.prove_obligation_for_checkpoint(caller, forward, obligation)
}
