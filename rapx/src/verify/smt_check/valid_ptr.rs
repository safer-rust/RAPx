//! SMT lowering for the composite `ValidPtr` safety property.
//!
//! `ValidPtr(p, T, n)` is not a primitive SMT obligation.  The verifier reduces
//! it to the pointer-validity formula used by the staged SMT checker:
//!
//! ```text
//! ValidPtr(p, T, n) =
//!   Size(T, 0) || (!Size(T, 0) && Deref(p, T, n))
//!
//! Deref(p, T, n) =
//!   Allocated(p, T, n, *) && InBound(p, T, n)
//! ```
//!
//! Zero-sized types do not require an allocated dereferenceable range.  For
//! non-ZSTs, `ValidPtr` delegates to the `Deref` composite checker.

use super::{
    common::{SmtCheckResult, SmtChecker, TypeSizeClass},
    deref,
};
use crate::verify::{
    contract::{Property, PropertyKind},
    helpers::Checkpoint,
    report::CheckResult,
    verifier::ForwardVisitResult,
};

/// Check `ValidPtr` using `Size(T,0) || (!Size(T,0) && Deref(p,T,n))`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(required_ty) = checker.property_required_ty(checkpoint, property) else {
        return SmtCheckResult::unknown("ValidPtr type could not be resolved");
    };

    match checker.type_size_class(checkpoint.caller, required_ty) {
        TypeSizeClass::Zero => {
            SmtCheckResult::proved(format!("ValidPtr proved by Size({required_ty:?}, 0)"))
        }
        TypeSizeClass::NonZero => {
            let deref_property = primitive_property(property, PropertyKind::Deref);
            let deref = deref::check(checker, checkpoint, &deref_property, forward);
            match &deref.result {
                CheckResult::Proved => {
                    SmtCheckResult::proved("ValidPtr proved: non-ZST target satisfies Deref")
                }
                CheckResult::Failed => SmtCheckResult {
                    result: CheckResult::Failed,
                    query: None,
                    notes: vec![String::from(
                        "ValidPtr failed: non-ZST target does not satisfy Deref",
                    )],
                },
                CheckResult::Unknown => {
                    if let Some(reason) = super::provenance::pedigree_proof(
                        checker, checkpoint, property, forward, true,
                    ) {
                        SmtCheckResult::proved(format!("ValidPtr proved: {reason}"))
                    } else if let Some(reason) =
                        field_invariant_reason(checker, checkpoint, property, forward, required_ty)
                    {
                        SmtCheckResult::proved(format!("ValidPtr proved: {reason}"))
                    } else {
                        SmtCheckResult::unknown("ValidPtr unknown: non-ZST Deref is not proved")
                    }
                }
            }
            .with_note(format!("primitive Deref via SMT: {:?}", deref.result))
        }
        TypeSizeClass::Unknown => {
            let deref_property = primitive_property(property, PropertyKind::Deref);
            let deref = deref::check(checker, checkpoint, &deref_property, forward);
            match &deref.result {
                CheckResult::Proved => SmtCheckResult::proved(
                    "ValidPtr proved: Deref holds, so the formula holds for zero and non-zero sizes",
                ),
                CheckResult::Failed | CheckResult::Unknown => SmtCheckResult::unknown(
                    "ValidPtr unknown: type size is unresolved and Deref is not proved",
                ),
            }
            .with_note("type size: Unknown")
            .with_note(format!("primitive Deref via SMT: {:?}", deref.result))
        }
    }
}

/// Reuse the original arguments while checking one primitive component.
fn primitive_property<'tcx>(property: &Property<'tcx>, kind: PropertyKind) -> Property<'tcx> {
    Property {
        null_guard: None,
        contract_kind: property.contract_kind.clone(),
        kind,
        args: property.args.clone(),
    }
}

/// Try to discharge `ValidPtr` from a struct field invariant covering the
/// dereferenced pointer (same field path, type, and element count).
fn field_invariant_reason<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    required_ty: rustc_middle::ty::Ty<'tcx>,
) -> Option<String> {
    let target = checker.property_target(checkpoint, property)?;
    let required_elements = checker
        .property_len_expr(checkpoint, property)
        .and_then(|expr| match expr {
            crate::verify::contract::ContractExpr::Const(value) => u64::try_from(value).ok(),
            _ => None,
        });
    super::field_invariant::discharge_from_field_invariant(
        checker.tcx,
        checkpoint.caller,
        &target,
        forward,
        PropertyKind::ValidPtr,
        Some(required_ty),
        required_elements,
    )
}
