//! Checking for the `TransmuteWithoutAlign` safety property.
//!
//! `TransmuteWithoutAlign([T], [U])` requires that `[T]` and `[U]` have a
//! compatible size relationship so that a sequence of `T` values can be
//! reinterpreted as a sequence of `U` values after alignment is accounted for.
//!
//! Unlike `ValidTransmute`, this does NOT check that `dst` is composed entirely
//! of `src`. It only checks the size ratio: `sizeof(U) % sizeof(T) == 0`
//! or `sizeof(T) % sizeof(U) == 0`. This allows reinterprets like `[u8]` to
//! `[u16]` where 2 * sizeof(u8) == sizeof(u16). Alignment is the caller's
//! responsibility (e.g., handled by `slice::align_to`'s own logic).

use rustc_middle::ty::{Ty, TyCtxt};

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{
    contract::{Property, PropertyArg},
    helpers::Checkpoint,
    verifier::ForwardVisitResult,
};

/// Check `TransmuteWithoutAlign(src, dst)`.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let tys: Vec<Ty<'tcx>> = property
        .args
        .iter()
        .filter_map(|arg| match arg {
            PropertyArg::Ty(ty) => Some(checker.instantiate_callsite_ty(checkpoint, *ty)),
            _ => None,
        })
        .collect();
    let [src, dst] = tys.as_slice() else {
        return SmtCheckResult::unknown("TransmuteWithoutAlign expects two type arguments");
    };

    let (src_bytes, dst_bytes) = match (
        size_of(checker.tcx, checkpoint.caller, *src),
        size_of(checker.tcx, checkpoint.caller, *dst),
    ) {
        (Some(s), Some(d)) => (s, d),
        _ => return SmtCheckResult::unknown("TransmuteWithoutAlign: unsized types"),
    };

    if src_bytes == 0 || dst_bytes == 0 {
        return SmtCheckResult::proved("TransmuteWithoutAlign: ZST trivially compatible");
    }

    if src_bytes % dst_bytes == 0 || dst_bytes % src_bytes == 0 {
        SmtCheckResult::proved(format!(
            "TransmuteWithoutAlign proved: sizeof(T)={src_bytes} sizeof(U)={dst_bytes} compatible"
        ))
    } else {
        SmtCheckResult::unknown(format!(
            "TransmuteWithoutAlign: incompatible sizes sizeof(T)={src_bytes} sizeof(U)={dst_bytes}"
        ))
    }
}

fn size_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_span::def_id::DefId, ty: Ty<'tcx>) -> Option<u64> {
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    let input = rustc_middle::ty::PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    match tcx.layout_of(input) {
        Ok(layout) => Some(layout.size.bytes()),
        Err(_) => None,
    }
}
