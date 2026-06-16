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
use std::collections::HashSet;

use crate::verify::{
    contract::Property,
    def_use::{PlaceBaseKey, PlaceKey},
    forward_visit::{AbstractValue, ForwardVisitResult},
    helpers::Callsite,
};

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
    let Some(elements_expr) = checker.property_len_expr(callsite, property) else {
        return SmtCheckResult::unknown("Init element-count argument could not be resolved");
    };
    let Some(elements_term) = checker.contract_expr_to_smt_term(callsite.caller, &elements_expr)
    else {
        return SmtCheckResult::unknown("Init element-count argument could not be lowered to SMT");
    };
    let Some(elements) = smt_term_const_u64(&elements_term, forward) else {
        return SmtCheckResult::unknown(
            "Init currently requires a constant element-count after callsite binding",
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
    let elements = checker.property_len_const(property).unwrap_or(0);

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

fn smt_term_const_u64<'tcx>(term: &SmtTerm, forward: &ForwardVisitResult<'tcx>) -> Option<u64> {
    match term {
        SmtTerm::Const(value) => Some(*value),
        SmtTerm::Place(place) => const_place_value(place, forward, &mut HashSet::new()),
        _ => None,
    }
}

fn const_place_value<'tcx>(
    place: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
    seen: &mut HashSet<PlaceKey>,
) -> Option<u64> {
    if !seen.insert(place.clone()) {
        return None;
    }
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    let value = forward
        .values
        .get(&rustc_middle::mir::Local::from_usize(local))?;
    const_value(value, forward, seen)
}

fn const_value<'tcx>(
    value: &AbstractValue<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    seen: &mut HashSet<PlaceKey>,
) -> Option<u64> {
    match value {
        AbstractValue::ConstInt(value) => u64::try_from(*value).ok(),
        AbstractValue::Place(place) => const_place_value(place, forward, seen),
        AbstractValue::Cast(inner, _) => const_value(inner, forward, seen),
        _ => None,
    }
}
