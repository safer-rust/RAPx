use rustc_hir::LangItem;
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::sym;

pub fn std_vec<'tcx>(element_ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
    let vec_def_id = tcx
        .get_diagnostic_item(sym::Vec)
        .expect("Vec should be defined in std");
    let alloc_def_id = tcx
        .lang_items()
        .global_alloc_ty()
        .expect("Global should be defined in std");
    let alloc_ty = tcx.type_of(alloc_def_id).skip_binder();
    let args = tcx.mk_args(&[
        ty::GenericArg::from(element_ty),
        ty::GenericArg::from(alloc_ty),
    ]);
    Ty::new_adt(tcx, tcx.adt_def(vec_def_id), args)
}
