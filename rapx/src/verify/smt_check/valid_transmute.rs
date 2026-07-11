//! Checking for the `ValidTransmute` safety property.
//!
//! `ValidTransmute(src, dst)` requires that reinterpreting a region of `src`
//! values as `dst` is valid, i.e. every bit pattern produced by valid `src`
//! values is a valid `dst`.  A general decision procedure for transmutability
//! is out of scope; this module proves the common *sound* sufficient case used
//! by `slice::align_to`/`as_simd`-style reinterprets: `dst` is composed
//! entirely of `src` (arrays, `repr(simd)`/`repr(transparent)` wrappers, and
//! tuples/structs whose leaves are all `src`).  Under that shape any sequence
//! of valid `src` values is a valid `dst`, so the transmute never introduces an
//! invalid bit pattern.

use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{
    contract::{Property, PropertyArg},
    helpers::Checkpoint,
    verifier::ForwardVisitResult,
};

/// Check `ValidTransmute(src, dst)`.
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
        return SmtCheckResult::unknown("ValidTransmute expects two type arguments");
    };

    if composed_entirely_of(checker.tcx, *dst, *src, 0) {
        SmtCheckResult::proved(format!(
            "ValidTransmute proved: {dst:?} is composed entirely of {src:?}"
        ))
    } else {
        SmtCheckResult::unknown(format!(
            "ValidTransmute unknown: cannot show {dst:?} accepts every bit pattern of {src:?}"
        ))
    }
}

/// True when every leaf of `ty` is `elem`, so any sequence of valid `elem`
/// values forms a valid `ty` (arrays, SIMD/transparent wrappers, and
/// aggregates whose fields all reduce to `elem`).
pub(crate) fn composed_entirely_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    elem: Ty<'tcx>,
    depth: usize,
) -> bool {
    if depth > 16 {
        return false;
    }
    if ty == elem {
        return true;
    }
    match ty.kind() {
        TyKind::Array(inner, _) => composed_entirely_of(tcx, *inner, elem, depth + 1),
        TyKind::Tuple(elems) => elems
            .iter()
            .all(|inner| composed_entirely_of(tcx, inner, elem, depth + 1)),
        TyKind::Adt(def, args)
            if def.is_struct() && (def.repr().simd() || def.repr().transparent()) =>
        {
            def.all_fields().all(|field| {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = field.ty(tcx, args);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = field.ty(tcx, args).skip_norm_wip();
                composed_entirely_of(tcx, field_ty, elem, depth + 1)
            })
        }
        _ => false,
    }
}
