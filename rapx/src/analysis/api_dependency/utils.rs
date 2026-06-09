#![allow(warnings, unused)]
use super::fuzzable;
use rustc_hir::LangItem;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, FnSig, GenericArgsRef, Ty, TyCtxt, TyKind};
use rustc_span::sym;

pub fn is_def_id_public(fn_def_id: impl Into<DefId>, tcx: TyCtxt<'_>) -> bool {
    let fn_def_id: DefId = fn_def_id.into();
    let local_id = fn_def_id.expect_local();
    rap_trace!(
        "vis: {:?} (path: {}) => {:?}",
        fn_def_id,
        tcx.def_path_str(fn_def_id),
        tcx.effective_visibilities(()).effective_vis(local_id)
    );

    tcx.effective_visibilities(()).is_directly_public(local_id)
        || tcx.effective_visibilities(()).is_exported(local_id)
}

pub fn is_fuzzable_ty<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    rap_trace!("check fuzzable ty: {}.", ty);
    let is_fuzzable = fuzzable::is_fuzzable_ty(ty, tcx, 0);
    rap_trace!("is_fuzzable({}) = {}.", ty, is_fuzzable);
    is_fuzzable
}

pub fn is_fuzzable_api<'tcx>(fn_did: DefId, args: GenericArgsRef<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let fn_sig = fn_sig_with_generic_args(fn_did, args, tcx);
    fn_sig
        .inputs()
        .iter()
        .copied()
        .all(|ty| is_fuzzable_ty(ty, tcx))
}

pub fn fn_sig_with_generic_args<'tcx>(
    fn_did: DefId,
    args: &[ty::GenericArg<'tcx>],
    tcx: TyCtxt<'tcx>,
) -> FnSig<'tcx> {
    let early_fn_sig = tcx.fn_sig(fn_did);
    let binder_fn_sig = early_fn_sig.instantiate(tcx, args);
    tcx.liberate_late_bound_regions(fn_did, binder_fn_sig)
}

pub fn fn_requires_monomorphization<'tcx>(fn_did: DefId, tcx: TyCtxt<'_>) -> bool {
    tcx.generics_of(fn_did).requires_monomorphization(tcx)
}

pub fn is_ty_eq<'tcx>(ty1: Ty<'tcx>, ty2: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    let ty1 = tcx.erase_and_anonymize_regions(ty1);
    let ty2 = tcx.erase_and_anonymize_regions(ty2);
    return ty1 == ty2;
}

pub fn ty_complexity<'tcx>(ty: Ty<'tcx>) -> usize {
    match ty.kind() {
        // Reference, Array, Slice
        TyKind::Ref(_, inner_ty, _) | TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => {
            ty_complexity(*inner_ty) + 1
        }

        // Tuple
        TyKind::Tuple(tys) => tys.iter().fold(0, |ans, ty| ans.max(ty_complexity(ty))) + 1,

        // ADT
        TyKind::Adt(_, args) => {
            args.iter().fold(0, |ans, arg| {
                if let Some(ty) = arg.as_type() {
                    ans.max(ty_complexity(ty))
                } else {
                    ans
                }
            }) + 1
        }

        // the depth of other primitive type default to 1
        _ => 1,
    }
}

pub fn is_ty_unstable<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    ty == tcx.types.f16
}
