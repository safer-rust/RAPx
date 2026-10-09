//! Call-terminator visiting logic.
//!
//! When the backward visitor encounters a call terminator, it delegates to this
//! module, which consults the interprocedural dependency summaries to decide
//! which arguments flow through to the destination and whether the call may
//! modify relevant state.

use crate::helpers::mir_utils;
use crate::compat::{FxHashMap, Spanned};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Operand, Place};
use rustc_middle::ty::{TyCtxt, TyKind};

use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{
    call_summary,
    def_use::{PlaceKey, RelevantPlaces, call_args_uses_at, operand_uses},
};

use super::types::RelevantItem;

/// Visit a call terminator using an interprocedural dependency summary.
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

    let summary = call_summary::dependency_summary(tcx, func, args.len(), &call_context_from_args(args));

    if defs.intersects(relevant) {
        if summary.unsupported {
            items.push(RelevantItem::UnknownCall);
        }
        items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    // A call returning a pointer/reference (e.g. `get_unchecked`, `as_ptr`,
    // `Box::new`'s `NonNull` destination) carries the callee's provenance even
    // when its destination is not *value*-relevant.  Keep it so the forward VM
    // applies the call's effect (and thus the provenance/alloc) instead of
    // relying on the backward `propagate_pass` re-application.  Deliberately
    // *not* applied to must-write calls (e.g. `MaybeUninit::write`), whose
    // write effect is tracked separately below via `must_write_args`.
    let dest_is_ptr = matches!(
        body.local_decls[destination.local].ty.kind(),
        TyKind::RawPtr(..) | TyKind::Ref(..)
    );
    if dest_is_ptr && summary.must_write_args.is_empty() {
        if summary.unsupported {
            items.push(RelevantItem::UnknownCall);
        }
        items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    let relevant_written_arg = summary.must_write_args.iter().any(|index| {
        args.get(*index)
            .is_some_and(|arg| operand_uses(&arg.node).intersects(relevant))
    });
    let summarized_write = !summary.must_write_args.is_empty();
    if relevant_written_arg
        || summarized_write
        || (summary.unsupported && arg_uses.intersects(relevant))
    {
        if summary.unsupported {
            items.push(RelevantItem::UnknownCall);
        }
        items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
        relevant.extend(call_args_uses_at(args, &summary.must_write_args));
    }

    // If the contract requires the length of a place (via `Len(place)`),
    // and this call is a `slice::len()` whose argument traces to the
    // same origin, add the destination to relevance so the length term
    // is available for the contract obligation.
    if !relevant.need_len.is_empty() {
        let callee = mir_utils::dep_callee_def_id(func);
        if crate::verify::api_classify::is_len(callee) {
            if let Some(first) = args.first() {
                let arg_place = mir_utils::operand_place(&first.node);
                if let Some(arg_key) = arg_place {
                    let matches = relevant.need_len.contains(&arg_key)
                        || relevant.need_len.iter().any(|nl| {
                            crate::verify::def_use::trace_place_origin(flow, nl)
                                == crate::verify::def_use::trace_place_origin(flow, &arg_key)
                        });
                    if matches {
                        let dest_key = PlaceKey::from_mir_place(destination);
                        if relevant.places.insert(dest_key.clone()) {
                            relevant.just_added.insert(dest_key.clone());
                        }
                        if let Some(local) = dest_key.local() {
                            relevant.locals.insert(local);
                        }
                        items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                    }
                }
            }
        }
    }
}

/// Build a concrete `CallContext` from the call's literal arguments so the
/// backward slicer prunes callee paths the same way the forward VM does. Only
/// constant integer arguments are carried; symbolic arguments are absent.
fn call_context_from_args(args: &[Spanned<Operand<'_>>]) -> call_summary::CallContext {
    let mut concrete = FxHashMap::default();
    for (i, arg) in args.iter().enumerate() {
        if let Some(v) = mir_utils::operand_const_u64(&arg.node) {
            concrete.insert(i, v as i128);
        }
    }
    call_summary::CallContext { concrete }
}
