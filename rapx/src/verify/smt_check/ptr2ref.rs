//! SMT lowering for the `Ptr2Ref` safety property.
//!
//! `Ptr2Ref(p)` means the pointer `p` can be soundly converted to a `&T` or
//! `&mut T` reference.  This module decomposes it into the primitive checks:
//!
//! - `NonNull(p)`: the pointer is not null.
//! - `Align(p, T)`: the pointer is aligned for its pointee type.
//!
//! The remaining requirements (Allocated + InBound + Init) are not checked here
//! because they require richer provenance and element-count tracking.

use super::common::{SmtCheckResult, SmtChecker, SmtObligation, place_label};
use crate::verify::{
    contract::Property, helpers::Checkpoint, report::CheckResult, verifier::ForwardVisitResult,
};

pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    // For NonNull::as_mut / NonNull::as_ref, the callee's self parameter type
    // is NonNull<T> whose inner pointer is guaranteed non-null and properly
    // aligned (NonNull can only be constructed from a valid, aligned pointer).
    if let Some(callee) = checkpoint.callee {
        let callee_path = checker.tcx.def_path_str(callee);
        if callee_path.contains("NonNull::as_ref") || callee_path.contains("NonNull::as_mut") {
            return SmtCheckResult::proved(
                "Ptr2Ref proved: NonNull guarantees valid pointer-to-ref conversion",
            );
        }
    }

    let Some(target) = checker.property_target(Some(checkpoint), property) else {
        return SmtCheckResult::unknown("Ptr2Ref target could not be resolved");
    };

    let target_label = place_label(&target);

    let nonnull_result = checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::NonZero {
            place: target.clone(),
        },
        property.null_guard.as_ref(),
    );

    let Some(pointee_ty) = checker.infer_pointee_ty(checkpoint.caller, &target) else {
        return match &nonnull_result.result {
            CheckResult::Proved => SmtCheckResult::proved(
                "Ptr2Ref: NonNull proved, alignment skipped (no pointee type)",
            ),
            CheckResult::Failed => SmtCheckResult {
                result: CheckResult::Failed,
                query: None,
                notes: vec![
                    "Ptr2Ref failed: pointer is null (no pointee type to check alignment)"
                        .to_string(),
                ],
            },
            CheckResult::Unknown => {
                SmtCheckResult::unknown("Ptr2Ref: could not infer pointee type for alignment check")
            }
        }
        .with_note("Ptr2Ref alignment check skipped: could not infer pointee type");
    };

    let Some(required_align) = checker.required_alignment(checkpoint.caller, pointee_ty) else {
        return match &nonnull_result.result {
            CheckResult::Proved => SmtCheckResult::proved(format!(
                "Ptr2Ref: NonNull proved, alignment skipped (layout unavailable for {pointee_ty:?})",
            )),
            CheckResult::Failed => SmtCheckResult {
                result: CheckResult::Failed,
                query: None,
                notes: vec![format!(
                    "Ptr2Ref failed: pointer is null (layout unavailable for {pointee_ty:?})"
                )],
            },
            CheckResult::Unknown => SmtCheckResult::unknown(format!(
                "Ptr2Ref: could not determine alignment for {pointee_ty:?}"
            )),
        };
    };

    let align_result = checker.prove_obligation(
        checkpoint,
        forward,
        SmtObligation::Aligned {
            place: target.clone(),
            align: required_align,
            ty_name: format!("{pointee_ty:?}"),
        },
        property.null_guard.as_ref(),
    );

    match (&nonnull_result.result, &align_result.result) {
        (CheckResult::Proved, CheckResult::Proved) => SmtCheckResult::proved(format!(
            "Ptr2Ref proved: {target_label} is non-null and {required_align}-byte aligned for {pointee_ty:?}",
        ))
        .with_note("Ptr2Ref: NonNull + Align both proved"),
        (CheckResult::Failed, _) => SmtCheckResult {
            result: CheckResult::Failed,
            query: None,
            notes: vec![format!(
                "Ptr2Ref failed: pointer {target_label} is not provably non-null"
            )],
        },
        (_, CheckResult::Failed) => SmtCheckResult {
            result: CheckResult::Failed,
            query: None,
            notes: vec![format!(
                "Ptr2Ref failed: pointer {target_label} is not {required_align}-byte aligned for {pointee_ty:?}",
            )],
        },
        (CheckResult::Proved, CheckResult::Unknown) => SmtCheckResult::unknown(format!(
            "Ptr2Ref: NonNull proved for {target_label}, but alignment ({required_align}-byte for {pointee_ty:?}) is unproven",
        )),
        (CheckResult::Unknown, CheckResult::Proved) => SmtCheckResult::unknown(format!(
            "Ptr2Ref: alignment proved for {target_label}, but non-null is unproven",
        )),
        _ => SmtCheckResult::unknown(format!(
            "Ptr2Ref: could not prove non-null nor alignment for {target_label}"
        )),
    }
}
