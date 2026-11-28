//! VM rules for pointer-preserving calls and owner lifetimes.

use crate::compat::MirTerminatorExt as _;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use crate::analysis::dataflow::pointer_flow::{is_nonnull_view, return_source_arg};
use crate::util::mir_utils;

/// Whether MIR shows a read-only pointer view of the first argument.
pub(crate) fn is_benign_origin_use(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| is_read_only_return(tcx, did) || is_read_only_nonnull_view(tcx, did))
}

/// A `NonNull` view that leaves its input allocation unchanged.
pub(crate) fn is_read_only_nonnull_view(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    is_nonnull_view(tcx, callee) && single_block_without_effects(tcx.optimized_mir(callee))
}

/// A pointer result from a single, side-effect-free MIR block is safe to use
/// while tracking an existing pointer origin.
pub(crate) fn is_read_only_return(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if return_source_arg(tcx, callee) != Some(0) {
        return false;
    }
    let inputs = tcx.fn_sig(callee).skip_binder().inputs().skip_binder();
    if !inputs
        .first()
        .is_some_and(|ty| mir_utils::pointee_ty(*ty).is_some())
    {
        return false;
    }
    single_block_without_effects(tcx.optimized_mir(callee))
}

/// A consumed owner remains allocated when a side-effect-free MIR body
/// returns its pointer without running a destructor.
pub(crate) fn returns_undropped_arg(tcx: TyCtxt<'_>, callee: DefId, arg: usize) -> bool {
    return_source_arg(tcx, callee) == Some(arg)
        && single_block_without_effects(tcx.optimized_mir(callee))
}

/// A single return block with no writes through a dereferenced place.
pub(crate) fn single_block_without_effects(body: &Body<'_>) -> bool {
    let [block] = &body.basic_blocks[..] else {
        return false;
    };
    matches!(block.rapx_terminator().kind, TerminatorKind::Return)
        && block.statements.iter().all(|stmt| match &stmt.kind {
            StatementKind::Assign(assign) => !assign
                .0
                .projection
                .iter()
                .any(|p| matches!(p, rustc_middle::mir::ProjectionElem::Deref)),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                true
            }
            _ => false,
        })
}
