//! SMT lowering for the `Owning` safety property.
//!
//! `Owning(p)` means the caller has unique ownership of the memory pointed to
//! by `p`.  This is required by `Box::from_raw` and similar ownership-transfer
//! APIs to ensure the pointer was obtained from a known ownership source
//! (`Box::into_raw`, `Box::leak`, `alloc::alloc`) and no conflicting aliases
//! remain.
//!
//! The check is performed by examining the forward facts for:
//! 1. A `KnownAllocated` fact that traces to an ownership-producing operation.
//! 2. Absence of aliasing conflicts (checked separately by the `Alias` hazard).
//!
//! Since the `Alias` hazard is checked independently in the contracts, this
//! module focuses on proving the provenance / ownership aspect.

use std::collections::HashSet;

use rustc_middle::mir::Local;

use super::common::{SmtCheckResult, SmtChecker, place_label};
use crate::verify::{
    contract::Property,
    helpers::Checkpoint,
    verifier::{AbstractValue, ForwardVisitResult, StateFact},
};

pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("Owning target could not be resolved");
    };

    let target_label = place_label(&target);

    let owning_facts: Vec<&StateFact<'tcx>> = forward
        .facts
        .iter()
        .filter(|fact| matches!(fact, StateFact::KnownAllocated { .. }))
        .collect();

    for fact in &owning_facts {
        let StateFact::KnownAllocated {
            place,
            object: _,
            ty_name,
            elements: _,
            reason,
        } = fact
        else {
            continue;
        };

        if !is_ownership_source(reason) {
            continue;
        }

        if !places_refer_to_same(place, &target, forward) {
            continue;
        }

        return SmtCheckResult::proved(format!(
            "Owning proved: {target_label} traces to ownership source ({reason}) for {ty_name}",
        ));
    }

    SmtCheckResult::unknown(format!(
        "Owning: {target_label} does not trace to a known ownership source on this path",
    ))
}

fn is_ownership_source(reason: &str) -> bool {
    let lower = reason.to_lowercase();
    lower.contains("box")
        || lower.contains("ownership")
        || lower.contains("alloc::")
        || lower.contains("into_raw")
}

fn places_refer_to_same(
    a: &crate::verify::def_use::PlaceKey,
    b: &crate::verify::def_use::PlaceKey,
    forward: &ForwardVisitResult,
) -> bool {
    if a == b {
        return true;
    }
    let a_local = resolve_root_local(a, forward);
    let b_local = resolve_root_local(b, forward);
    a_local.is_some() && a_local == b_local
}

fn resolve_root_local(
    place: &crate::verify::def_use::PlaceKey,
    forward: &ForwardVisitResult,
) -> Option<Local> {
    let mut current = place.clone();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(current.clone()) {
            break;
        }
        let Some(local) = current.local() else {
            return None;
        };
        let value = forward.values.get(&local)?;
        let next = match value {
            AbstractValue::Place(next) | AbstractValue::Ref(next) | AbstractValue::RawPtr(next) => {
                next.clone()
            }
            AbstractValue::Cast(inner, _) => match inner.as_ref() {
                AbstractValue::Place(next)
                | AbstractValue::Ref(next)
                | AbstractValue::RawPtr(next) => next.clone(),
                _ => break,
            },
            _ => break,
        };
        current = next;
    }
    current.local()
}
