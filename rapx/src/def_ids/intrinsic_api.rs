//! Identity of compiler intrinsics by `DefId` or lowered MIR variant.

use rustc_hir::def_id::DefId;
#[cfg(rapx_intrinsic_enum)]
use rustc_middle::ty::Intrinsic;
use rustc_middle::{mir::NonDivergingIntrinsic, ty::TyCtxt};
use rustc_span::Symbol;

pub(crate) fn intrinsic_name(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<Symbol> {
    let intrinsic = tcx.intrinsic(callee?)?;
    #[cfg(rapx_intrinsic_enum)]
    let name = match intrinsic.name {
        Intrinsic::Rustc(name) | Intrinsic::Backend { llvm: name } => name,
    };
    #[cfg(not(rapx_intrinsic_enum))]
    let name = intrinsic.name;
    Some(name)
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}

/// Canonical contract path for an intrinsic lowered to a MIR statement.
pub(crate) fn lowered_mir_path(intrinsic: &NonDivergingIntrinsic<'_>) -> &'static str {
    match intrinsic {
        NonDivergingIntrinsic::Assume(_) => "core::intrinsics::assume",
        NonDivergingIntrinsic::CopyNonOverlapping(_) => "core::intrinsics::copy_nonoverlapping",
    }
}

/// Diagnostic `DefId` available for a lowered MIR intrinsic, if any.
pub(crate) fn lowered_mir_def_id(
    tcx: TyCtxt<'_>,
    intrinsic: &NonDivergingIntrinsic<'_>,
) -> Option<DefId> {
    match intrinsic {
        NonDivergingIntrinsic::Assume(_) => None,
        NonDivergingIntrinsic::CopyNonOverlapping(_) => {
            tcx.get_diagnostic_item(rustc_span::sym::ptr_copy_nonoverlapping)
        }
    }
}
