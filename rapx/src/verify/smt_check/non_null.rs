//! SMT lowering for the `NonNull` safety property.
//!
//! Reduces `NonNull(p)` to `SmtObligation::NonZero { place: p }`.

use rustc_middle::ty::{TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker, SmtObligation};
use crate::verify::{
    contract::{ContractPlace, PlaceBase, Property, PropertyArg},
    verifier::ForwardVisitResult,
};

use crate::helpers::mir_scan::Checkpoint;

fn is_nonnull_param_ty(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    let peeled = ty.peel_refs();
    if let TyKind::Adt(def, _) = peeled.kind() {
        return tcx.def_path_str(def.did()).contains("ptr::non_null::NonNull");
    }
    false
}

fn resolve_target<'tcx>(
    checker: &SmtChecker<'tcx>,
    opt_checkpoint: Option<&Checkpoint<'tcx>>,
    property: &Property<'tcx>,
) -> Option<crate::verify::def_use::PlaceKey> {
    checker.property_target(opt_checkpoint, property)
}

pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    if checkpoint.is_ref {
        return SmtCheckResult::proved("NonNull trivially holds for ref-derived pointer");
    }
    if let Some(callee) = checkpoint.callee {
        if let Some(PropertyArg::Place(ContractPlace { base: PlaceBase::Arg(ix), .. })) =
            property.args.first()
        {
            let fn_sig = checker.tcx.fn_sig(callee).skip_binder();
            if let Some(param_ty) = fn_sig.inputs().skip_binder().get(*ix) {
                if is_nonnull_param_ty(checker.tcx, *param_ty) {
                    return SmtCheckResult::proved(
                        "NonNull trivially holds: callee parameter type is NonNull<T>",
                    );
                }
            }
        }
    }
    let Some(target) = resolve_target(checker, Some(checkpoint), property) else {
        return SmtCheckResult::unknown("NonNull target could not be resolved");
    };
    let obligation = SmtObligation::NonZero { place: target };
    checker
        .prove_obligation(checkpoint, forward, obligation, property.null_guard.as_ref())
        .or_try(|| {
            super::provenance::pedigree_proof(checker, checkpoint, property, forward, false)
                .map(|reason| SmtCheckResult::proved(format!("NonNull proved: {reason}")))
                .unwrap_or(SmtCheckResult::unknown("NonNull: pedigree proof inconclusive"))
        })
}

pub(crate) fn check_for_checkpoint<'tcx>(
    checker: &SmtChecker<'tcx>,
    caller: rustc_hir::def_id::DefId,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = resolve_target(checker, None, property) else {
        return SmtCheckResult::unknown("SMT NonNull target could not be resolved");
    };
    let obligation = SmtObligation::NonZero { place: target };
    checker.prove_obligation_for_checkpoint(caller, forward, obligation)
}
