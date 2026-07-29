//! SMT lowering for the `Align` safety property.
//!
//! Reduces `Align(p, T)` to `SmtObligation::Aligned { place: p, align: align_of(T) }`.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{contract::Property, verifier::ForwardVisitResult};
use crate::helpers::mir_scan::Checkpoint;

fn resolve<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    opt_checkpoint: Option<&Checkpoint<'tcx>>,
) -> Option<(crate::verify::def_use::PlaceKey, u64, String)> {
    let target = checker.property_target(opt_checkpoint, property)?;
    let required_ty = checker.property_required_ty(opt_checkpoint, property)?;
    let align = checker
        .required_alignment(caller, required_ty)
        .or_else(|| checker.type_layout(caller, required_ty).map(|(a, _)| a))
        .unwrap_or(0);
    Some((target, align, format!("{required_ty:?}")))
}

pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if checkpoint.is_ref {
        return SmtCheckResult::proved("Align trivially holds for ref-derived pointer");
    }
    if let Some(reason) =
        super::field_invariant::discharge_from_contract_fact_with_checkpoint(
            property, forward, checkpoint,
        )
    {
        return SmtCheckResult::proved(format!("Align proved: {reason}"));
    }
    let Some((target, align, ty_name)) =
        resolve(checker, checkpoint.caller, property, Some(checkpoint))
    else {
        return SmtCheckResult::unknown("SMT Align target/type could not be resolved");
    };
    let obligation = SmtObligation::Aligned { place: target, align, ty_name };
    checker.prove_obligation(checkpoint, forward, obligation, property.null_guard.as_ref())
}

pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if let Some(reason) = super::field_invariant::discharge_from_contract_fact(property, forward) {
        return SmtCheckResult::proved(format!("Align proved: {reason}"));
    }
    let Some((target, align, ty_name)) = resolve(checker, caller, property, None) else {
        return SmtCheckResult::unknown("SMT Align target/type could not be resolved");
    };
    let obligation = SmtObligation::Aligned { place: target, align, ty_name };
    checker.prove_obligation_for_checkpoint(caller, forward, obligation)
}
