use rustc_abi::{BackendRepr, Scalar};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker};
use super::valid_transmute;
use crate::verify::{
    contract::{Property, PropertyArg},
    helpers::Checkpoint,
    verifier::ForwardVisitResult,
};

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

    if all_bit_patterns_valid(checker.tcx, dst_elem, 0) {
        return SmtCheckResult::proved(
            "dst_type accepts all bit patterns, any byte-window is a valid dst value",
        );
    }

    let src_bytes = try_size_of(checker.tcx, checkpoint.caller, src_elem);
    let dst_bytes = try_size_of(checker.tcx, checkpoint.caller, dst_elem);
    if src_bytes.is_some() && dst_bytes.is_some() {
        return SmtCheckResult::unknown(format!(
            "cannot prove type_invariant of {dst_elem:?} for every {}-byte window \
             (|{src_elem:?}|={}, |{dst_elem:?}|={})",
            dst_bytes.unwrap(),
            src_bytes.unwrap(),
            dst_bytes.unwrap(),
        ));
    }

    SmtCheckResult::unknown("cannot determine element sizes")
}

fn slice_element(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::Slice(elem) => Some(*elem),
        _ => None,
    }
}

fn try_size_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
    ty: Ty<'tcx>,
) -> Option<u64> {
    let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, def_id);
    let input = rustc_middle::ty::PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    tcx.layout_of(input).ok().map(|l| l.size.bytes())
}

fn all_bit_patterns_valid<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: usize) -> bool {
    if depth > 16 {
        return false;
    }
    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Str
        | TyKind::Ref(..)
        | TyKind::FnPtr(..)
        | TyKind::Never
        | TyKind::Foreign(..) => false,

        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => true,

        TyKind::RawPtr(..) => true,

        TyKind::Array(elem, _) => all_bit_patterns_valid(tcx, *elem, depth + 1),

        TyKind::Slice(elem) => all_bit_patterns_valid(tcx, *elem, depth + 1),

        TyKind::Tuple(elems) => elems
            .iter()
            .all(|e| all_bit_patterns_valid(tcx, e, depth + 1)),

        TyKind::Adt(def, args) => {
            if def.is_union() {
                return false;
            }
            if def.is_struct() {
                if !def.all_fields().all(|field| {
                    #[cfg(not(rapx_rustc_ge_198))]
                    let field_ty = field.ty(tcx, args);
                    #[cfg(rapx_rustc_ge_198)]
                    let field_ty = field.ty(tcx, args).skip_norm_wip();
                    all_bit_patterns_valid(tcx, field_ty, depth + 1)
                }) {
                    return false;
                }
                !has_non_trivial_valid_range(tcx, ty)
            } else {
                false
            }
        }

        TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_) => false,

        _ => false,
    }
}

fn has_non_trivial_valid_range<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
    let input = rustc_middle::ty::PseudoCanonicalInput {
        typing_env,
        value: ty,
    };
    let Ok(layout) = tcx.layout_of(input) else {
        return true;
    };
    check_backend_repr(tcx, &layout.backend_repr)
}

fn check_backend_repr<'tcx>(tcx: TyCtxt<'tcx>, repr: &BackendRepr) -> bool {
    match repr {
        BackendRepr::Scalar(scalar) => scalar_has_constrained_range(tcx, scalar),
        #[cfg(not(rapx_rustc_ge_199))]
        BackendRepr::ScalarPair(a, b) => {
            scalar_has_constrained_range(tcx, a) || scalar_has_constrained_range(tcx, b)
        }
        #[cfg(rapx_rustc_ge_199)]
        BackendRepr::ScalarPair { a, b, .. } => {
            scalar_has_constrained_range(tcx, a) || scalar_has_constrained_range(tcx, b)
        }
        #[cfg(not(rapx_rustc_ge_199))]
        BackendRepr::SimdVector { element, .. } => scalar_has_constrained_range(tcx, element),
        #[cfg(rapx_rustc_ge_199)]
        BackendRepr::SimdScalableVector { element, .. }
        | BackendRepr::SimdVector { element, .. } => scalar_has_constrained_range(tcx, element),
        _ => false,
    }
}

fn scalar_has_constrained_range<'tcx>(tcx: TyCtxt<'tcx>, scalar: &Scalar) -> bool {
    let valid_range = scalar.valid_range(&tcx);
    let max = scalar.size(&tcx).unsigned_int_max();
    valid_range.start != 0 || valid_range.end != max
}
