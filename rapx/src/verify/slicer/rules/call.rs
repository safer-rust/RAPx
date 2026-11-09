//! Call-terminator visiting logic.
//!
//! When the backward visitor encounters a call terminator, it delegates to this
//! module, which consults the dependency summaries to decide
//! which arguments flow through to the destination and whether the call may
//! modify relevant state.

use crate::compat::Spanned;
use crate::helpers::mir_utils;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Operand, Place},
    ty::{TyCtxt, TyKind},
};

use crate::analysis::dataflow::types::DataflowGraph;

use crate::helpers::def_use::{RelevantPlaces, call_args_uses_at};
use crate::verify::call_summary;

use super::super::types::RelevantItem;

/// Visit a call terminator using a dependency summary.
#[allow(clippy::too_many_arguments)]
pub(crate) fn visit<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    block: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    flow: &DataflowGraph,
    body: &Body<'tcx>,
    relevant: &mut RelevantPlaces,
    items: &mut Vec<RelevantItem<'tcx>>,
) {
    let mut defs = RelevantPlaces::new();
    defs.insert_mir_place(destination);

    let tpos = body.basic_blocks[block].statements.len();
    let mut arg_uses = RelevantPlaces::new();
    for &edge_idx in &flow.node(destination.local).in_edges {
        let edge = &flow.edges[edge_idx];
        if edge.block == block.as_usize() && edge.statement_index == tpos {
            arg_uses.insert_local(edge.src);
        }
    }

    let summary = call_summary::dependency_summary(tcx, def_id, func, destination.local, args, body);

    if call_summary::effects::is_unmodeled_intrinsic(
        tcx,
        mir_utils::dep_callee_def_id(func),
    ) {
        items.push(RelevantItem::Terminator { def_id, block, global_block: None, switch_succ: None });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    if defs.intersects(relevant) {
        items.push(RelevantItem::Terminator { def_id, block, global_block: None, switch_succ: None });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    // A call returning a pointer/reference (e.g. `get_unchecked`, `as_ptr`,
    // `Box::new`'s `NonNull` destination) carries the callee's provenance even
    // when its destination is not *value*-relevant.  Keep it so the forward VM
    // applies the call's effect (and thus the provenance/alloc) instead of
    // relying on the backward `propagate_pass` re-application.  Deliberately
    // *not* applied to write calls (e.g. `MaybeUninit::write`), whose write
    // effect is tracked separately below via `write_args`.
    let dest_is_ptr = matches!(
        body.local_decls[destination.local].ty.kind(),
        TyKind::RawPtr(..) | TyKind::Ref(..)
    );
    if dest_is_ptr && summary.write_args.is_empty() {
        items.push(RelevantItem::Terminator { def_id, block, global_block: None, switch_succ: None });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    let summarized_write = !summary.write_args.is_empty();
    if summarized_write || arg_uses.intersects(relevant) {
        items.push(RelevantItem::Terminator { def_id, block, global_block: None, switch_succ: None });
        relevant.extend(call_args_uses_at(args, &summary.write_inputs));
    }

}
