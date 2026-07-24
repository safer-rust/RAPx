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
    def_use::{PlaceKey, RelevantPlaces, call_args_uses_at, operand_uses},
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

    let forget_reason = || {
        if call_summary::call_args_preserve_layout(
            args.iter().map(|arg| arg.node.ty(&body.local_decls, tcx)),
        ) {
            ForgetReason::OpaqueContentCall
        } else {
            ForgetReason::UnknownCall
        }
    };

    if defs.intersects(relevant) {
        if summary.unsupported {
            items.push(BackwardItem::Forget {
                reason: forget_reason(),
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
                reason: forget_reason(),
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

    // If the contract requires the length of a place (via `Len(place)`),
    // and this call is a `slice::len()` whose argument traces to the
    // same origin, add the destination to relevance so the length term
    // is available for the contract obligation.
    if !relevant.need_len.is_empty() {
        let name = call_summary::call_name(tcx, func);
        if name.ends_with("::len") || name.contains("::len(") {
            if let Some(first) = args.first() {
                let arg_place = match &first.node {
                    Operand::Copy(p) | Operand::Move(p) => Some(PlaceKey::from_mir_place(p)),
                    _ => None,
                };
                if let Some(arg_key) = arg_place {
                    let matches = relevant.need_len.contains(&arg_key)
                        || relevant
                            .need_len
                            .iter()
                            .any(|nl| same_origin_via_body(body, nl, &arg_key));
                    if matches {
                        let dest_key = PlaceKey::from_mir_place(destination);
                        if relevant.places.insert(dest_key.clone()) {
                            relevant.just_added.insert(dest_key.clone());
                        }
                        if let Some(local) = dest_key.local() {
                            relevant.locals.insert(local);
                        }
                        items.push(BackwardItem::Terminator {
                            block,
                            kind: KeepReason::PointerFlow,
                        });
                    }
                }
            }
        }
    }
}

fn same_origin_via_body(body: &rustc_middle::mir::Body<'_>, a: &PlaceKey, b: &PlaceKey) -> bool {
    if a == b {
        return true;
    }
    let origin = |p: &PlaceKey| -> Option<PlaceKey> {
        let local = p.local()?;
        for (_, data) in body.basic_blocks.iter_enumerated() {
            for stmt in &data.statements {
                if let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind {
                    if assign.0.local == local {
                        if let rustc_middle::mir::Rvalue::Use(
                            rustc_middle::mir::Operand::Copy(src)
                            | rustc_middle::mir::Operand::Move(src),
                            ..,
                        ) = &assign.1
                        {
                            return Some(PlaceKey::from_mir_place(src));
                        }
                        break;
                    }
                }
            }
        }
        None
    };
    let ao = origin(a).unwrap_or_else(|| a.clone());
    let bo = origin(b).unwrap_or_else(|| b.clone());
    ao == bo
}
