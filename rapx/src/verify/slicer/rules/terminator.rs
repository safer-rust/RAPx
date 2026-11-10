//! Backward relevance rules for MIR terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Operand, Place, TerminatorKind};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::compat::Spanned;
use crate::helpers::def_use::{RelevantPlaces, call_args_uses_at, terminator_use_def};
use crate::helpers::mir_utils;

use super::super::types::RelevantItem;
use super::super::visitor::BackwardSlicer;
use super::call;

impl<'tcx> BackwardSlicer<'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn visit_call_terminator(
        &self,
        def_id: DefId,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
    ) {
        if keep_invalidations {
            // Keep calls that can change an allocation's lifetime or consume
            // a raw ownership share, together with their argument sources.
            let is_state_change = mir_utils::dep_callee_def_id(func).is_some_and(|c| {
                crate::verify::api_classify::is_manually_drop_drop(Some(c))
                    || crate::verify::api_classify::is_std_drop(Some(c))
                    || crate::verify::contract::json::query_json_contracts(self.tcx, c)
                        .iter()
                        .any(|property| {
                            property.kind()
                                == Some(crate::verify::contract::PropertyKind::RefCountShare)
                        })
            });
            if is_state_change {
                items.push(RelevantItem::Terminator {
                    global_block: None,
                    def_id,
                    block,
                    switch_succ: None,
                });
                relevant.extend(call_args_uses_at(args, &[0]));
                return;
            }
        }

        // `Owning` traces an owner's construction chain: keep a call whose
        // destination is a `needs_drop` value even when that local is not
        // itself relevant, so its field provenance survives.
        if keep_owner {
            let dest_ty = body.local_decls[destination.local].ty;
            if super::may_need_drop(self.tcx, def_id, dest_ty) {
                let use_def = terminator_use_def(terminator);
                items.push(RelevantItem::Terminator {
                    global_block: None,
                    def_id,
                    block,
                    switch_succ: None,
                });
                relevant.remove_all(&use_def.defs);
                relevant.extend(use_def.uses);
                return;
            }
        }
        call::visit(
            self.tcx,
            def_id,
            block,
            func,
            args,
            destination,
            flow,
            body,
            relevant,
            items,
        );
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn visit_non_call_terminator<'tcx>(
    def_id: DefId,
    block: BasicBlock,
    terminator: &rustc_middle::mir::Terminator<'tcx>,
    relevant: &mut RelevantPlaces,
    items: &mut Vec<RelevantItem<'tcx>>,
    keep_invalidations: bool,
    successor: Option<BasicBlock>,
) {
    if keep_invalidations && matches!(terminator.kind, TerminatorKind::Drop { .. }) {
        items.push(RelevantItem::Terminator {
            global_block: None,
            def_id,
            block,
            switch_succ: None,
        });
        return;
    }

    let use_def = terminator_use_def(terminator);
    let path_successor = match terminator.kind {
        TerminatorKind::SwitchInt { .. } => Some(successor),
        TerminatorKind::Assert { .. } => Some(None),
        _ => None,
    };
    if let Some(switch_succ) = path_successor {
        items.push(RelevantItem::Terminator {
            global_block: None,
            def_id,
            block,
            switch_succ,
        });
        relevant.extend(use_def.uses);
        return;
    }

    if use_def.defs.intersects(relevant) {
        items.push(RelevantItem::Terminator {
            global_block: None,
            def_id,
            block,
            switch_succ: None,
        });
        relevant.remove_all(&use_def.defs);
        relevant.extend(use_def.uses);
        return;
    }

    if use_def.uses.intersects(relevant) {
        items.push(RelevantItem::Terminator {
            global_block: None,
            def_id,
            block,
            switch_succ: None,
        });
    }
}
