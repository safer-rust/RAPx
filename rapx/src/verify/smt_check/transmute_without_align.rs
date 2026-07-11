use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker};
use super::valid_transmute;
use crate::verify::{contract::{Property, PropertyArg}, helpers::Checkpoint, verifier::ForwardVisitResult};

pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let tys: Vec<Ty<'tcx>> = property
        .args.iter()
        .filter_map(|arg| match arg {
            PropertyArg::Ty(ty) => Some(checker.instantiate_callsite_ty(checkpoint, *ty)),
            _ => None,
        })
        .collect();
    let [src, dst] = tys.as_slice() else {
        return SmtCheckResult::unknown("two type arguments expected");
    };

    let src_elem = slice_element(*src).unwrap_or(*src);
    let dst_elem = slice_element(*dst).unwrap_or(*dst);

    if valid_transmute::composed_entirely_of(checker.tcx, src_elem, dst_elem, 0)
        || valid_transmute::composed_entirely_of(checker.tcx, dst_elem, src_elem, 0)
    {
        return SmtCheckResult::proved("structurally compatible");
    }

    if matches!(src_elem.kind(), TyKind::Adt(def, _) if def.repr().simd())
        || matches!(dst_elem.kind(), TyKind::Adt(def, _) if def.repr().simd())
    {
        return SmtCheckResult::proved("SIMD compat");
    }

    let src_bytes = try_size_of(checker.tcx, checkpoint.caller, src_elem);
    let dst_bytes = try_size_of(checker.tcx, checkpoint.caller, dst_elem);
    if let (Some(s), Some(d)) = (src_bytes, dst_bytes) {
        if s % d == 0 || d % s == 0 {
            return SmtCheckResult::proved(format!("size compat: {s} ↔ {d}"));
        }
        return SmtCheckResult::unknown(format!("incompatible sizes: {s} ↔ {d}"));
    }

    SmtCheckResult::unknown("cannot determine sizes")
}

fn slice_element(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::Slice(elem) => Some(*elem),
        _ => None,
    }
}

fn try_size_of<'tcx>(tcx: TyCtxt<'tcx>, def_id: rustc_span::def_id::DefId, ty: Ty<'tcx>) -> Option<u64> {
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    let input = rustc_middle::ty::PseudoCanonicalInput { typing_env, value: ty };
    tcx.layout_of(input).ok().map(|l| l.size.bytes())
}
