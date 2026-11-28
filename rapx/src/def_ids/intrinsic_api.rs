//! Identity of compiler intrinsics by `DefId` or lowered MIR variant.

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::NonDivergingIntrinsic, ty::TyCtxt};
use rustc_span::Symbol;

pub(crate) fn intrinsic_name(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<Symbol> {
    crate::compat::intrinsic_symbol(tcx, callee)
}

pub fn is_intrinsic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.intrinsic(callee).is_some()
}

/// Identify atomic intrinsics that write memory; loads and fences are excluded.
pub(crate) fn is_atomic_update(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    intrinsic_name(tcx, Some(callee)).is_some_and(|name| {
        name.as_str().strip_prefix("atomic_").is_some_and(|op| {
            ["store", "xchg", "cxchg", "xadd", "xsub", "and", "or", "xor", "nand", "min", "max", "umin", "umax"]
                .iter().any(|prefix| op.starts_with(prefix))
        })
    })
}

/// Whether this is the pointer `copy` or `copy_nonoverlapping` intrinsic.
pub(crate) fn is_ptr_copy(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    intrinsic_name(tcx, Some(callee))
        .is_some_and(|name| matches!(name.as_str(), "copy" | "copy_nonoverlapping"))
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
