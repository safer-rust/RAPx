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
    forward_visit::ForwardVisitResult,
    helpers::Callsite,
    report::CheckResult,
};

/// Check `ValidPtr` using `Size(T,0) || (!Size(T,0) && Deref(p,T,n))`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(required_ty) = checker.property_required_ty(callsite, property) else {
        return SmtCheckResult::unknown("ValidPtr type could not be resolved");
    };

    match checker.type_size_class(callsite.caller, required_ty) {
        TypeSizeClass::Zero => {
            SmtCheckResult::proved(format!("ValidPtr proved by Size({required_ty:?}, 0)"))
        }
        TypeSizeClass::NonZero => {
            let deref_property = primitive_property(property, PropertyKind::Deref);
            let deref = deref::check(checker, callsite, &deref_property, forward);
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
                    SmtCheckResult::unknown("ValidPtr unknown: non-ZST Deref is not proved")
                }
            }
            .with_note(format!("primitive Deref via SMT: {:?}", deref.result))
        }
        TypeSizeClass::Unknown => {
            let deref_property = primitive_property(property, PropertyKind::Deref);
            let deref = deref::check(checker, callsite, &deref_property, forward);
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
        kind,
        args: property.args.clone(),
    }
}
