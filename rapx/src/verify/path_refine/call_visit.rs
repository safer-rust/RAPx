//! Call-terminator visiting logic.
//!
//! When the backward visitor encounters a call terminator, it delegates to this
//! module, which consults the interprocedural dependency summaries to decide
//! which arguments flow through to the destination and whether the call may
//! modify relevant state.

use crate::compat::Spanned;
use rustc_middle::mir::{BasicBlock, Body, Operand, Place};
use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{
    call_summary,
    def_use::{RelevantPlaces, call_args_uses_at, operand_uses},
};

use super::types::{BackwardItem, ForgetReason, KeepReason};

/// Visit a call terminator using an interprocedural dependency summary.
pub(crate) fn visit<'tcx>(
    tcx: TyCtxt<'tcx>,
    block: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    flow: &DataflowGraph,
    body: &Body<'tcx>,
    relevant: &mut RelevantPlaces,
    items: &mut Vec<BackwardItem<'tcx>>,
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

    let summary = call_summary::dependency_summary(tcx, func, args.len());

    if defs.intersects(relevant) {
        if summary.unsupported {
            items.push(BackwardItem::Forget {
                reason: ForgetReason::UnknownCall,
            });
        }
        items.push(BackwardItem::Terminator {
            block,
            kind: if summary.unsupported {
                KeepReason::UnknownEffect
            } else {
                KeepReason::PointerFlow
            },
        });
        relevant.remove_all(&defs);
        relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
        return;
    }

    let relevant_written_arg = summary.may_write_args.iter().any(|index| {
        args.get(*index)
            .is_some_and(|arg| operand_uses(&arg.node).intersects(relevant))
    });
    let summarized_write = !summary.may_write_args.is_empty();
    if relevant_written_arg
        || summarized_write
        || (summary.unsupported && arg_uses.intersects(relevant))
    {
        if summary.unsupported {
            items.push(BackwardItem::Forget {
                reason: ForgetReason::UnknownCall,
            });
        }
        items.push(BackwardItem::Terminator {
            block,
            kind: if summary.unsupported {
                KeepReason::UnknownEffect
            } else {
                KeepReason::PointerFlow
            },
        });
        relevant.extend(call_args_uses_at(args, &summary.may_write_args));
    }
}
