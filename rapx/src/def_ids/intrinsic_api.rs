//! Identity of compiler intrinsics by `DefId`.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;

pub(crate) fn intrinsic_name(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<Symbol> {
    tcx.intrinsic(callee?).map(|intrinsic| intrinsic.name)
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}
