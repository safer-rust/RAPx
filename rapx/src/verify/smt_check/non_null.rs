//! SMT lowering for the `NonNull` safety property.
//!
//! This module reduces:
//!
//! ```text
//! NonNull(p)
//! ```
//!
//! to the common SMT obligation:
//!
//! ```text
//! NonZero { place: p }
//! ```
//!
//! The common model asserts path-local facts such as reference-derived pointers
//! and `as_ptr` results as non-zero assumptions, then asks whether the target can
//! still be zero.

use rustc_middle::ty::{TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{
    contract::{ContractPlace, PlaceBase, Property, PropertyArg},
    helpers::Checkpoint,
    verifier::ForwardVisitResult,
};

fn is_nonnull_param_ty(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    let peeled = ty.peel_refs();
    if let TyKind::Adt(def, _) = peeled.kind() {
        let path = tcx.def_path_str(def.did());
        if path.contains("ptr::non_null::NonNull") {
            return true;
        }
    }
    false
}

/// Check `NonNull` by lowering it to `SmtObligation::NonZero`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if checkpoint.is_ref {
        return SmtCheckResult::proved("NonNull trivially holds for ref-derived pointer");
    }

    // If the target maps to a callee parameter whose type is NonNull<T>,
    // the pointer is guaranteed non-null by construction.
    if let Some(callee) = checkpoint.callee {
        if let Some(PropertyArg::Place(ContractPlace {
            base: PlaceBase::Arg(arg_index),
            ..
        })) = property.args.first()
        {
            let tcx = checker.tcx;
            let fn_sig = tcx.fn_sig(callee).skip_binder();
            let input_tys = fn_sig.inputs().skip_binder();
            if let Some(param_ty) = input_tys.get(*arg_index) {
                if is_nonnull_param_ty(tcx, *param_ty) {
                    return SmtCheckResult::proved(
                        "NonNull trivially holds: callee parameter type is NonNull<T>",
                    );
                }
            }
        }
    }

    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("NonNull target could not be resolved");
    };

    let obligation = SmtObligation::NonZero { place: target };
    let result = checker.prove_obligation(checkpoint, forward, obligation);
    if result.result == crate::verify::report::CheckResult::Unknown {
        if let Some(reason) =
            super::provenance::pedigree_proof(checker, checkpoint, property, forward, false)
        {
            return SmtCheckResult::proved(format!("NonNull proved: {reason}"));
        }
    }
    result
}

/// Check `NonNull` at a return checkpoint for struct invariant verification.
pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target_direct(property) else {
        return SmtCheckResult::unknown("SMT NonNull target could not be resolved");
    };
    let obligation = SmtObligation::NonZero { place: target };
    checker.prove_obligation_for_checkpoint(caller, forward, obligation)
}
