//! Call-terminator visiting logic.
//!
//! When the backward visitor encounters a call terminator, it delegates to this
//! module, which consults the dependency summaries to decide
//! which arguments flow through to the destination and whether the call may
//! modify relevant state.

use crate::helpers::mir_utils;
use crate::compat::Spanned;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Operand, Place};
use rustc_middle::ty::{TyCtxt, TyKind};

use crate::analysis::dataflow::types::DataflowGraph;

use crate::verify::call_summary;
use crate::helpers::def_use::{call_args_uses_at, PlaceKey, RelevantPlaces};

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

    // If the contract requires the length of a place (via `Len(place)`),
    // and this call is a `slice::len()` whose argument traces to the
    // same origin, add the destination to relevance so the length term
    // is available for the contract obligation.
    if !relevant.need_len.is_empty() {
        let callee = mir_utils::dep_callee_def_id(func);
        if crate::def_ids::other_api::is_len(callee)
            && let Some(first) = args.first() {
                let arg_place = mir_utils::operand_place(&first.node);
                if let Some(arg_key) = arg_place {
                    let matches = relevant.need_len.contains(&arg_key)
                        || relevant.need_len.iter().any(|nl| {
                            crate::helpers::def_use::trace_place_origin(flow, nl)
                                == crate::helpers::def_use::trace_place_origin(flow, &arg_key)
                        });
                    if matches {
                        let dest_key = PlaceKey::from_mir_place(destination);
                        if relevant.places.insert(dest_key.clone()) {
                            relevant.just_added.insert(dest_key.clone());
                        }
                        if let Some(local) = dest_key.local() {
                            relevant.locals.insert(local);
                        }
                        items.push(RelevantItem::Terminator { def_id, block, global_block: None, switch_succ: None });
                    }
                }
            }
    }
}
