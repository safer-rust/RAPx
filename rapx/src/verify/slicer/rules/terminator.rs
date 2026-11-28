//! Backward relevance rules for MIR terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Operand, Place, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::types::DataflowGraph;
use crate::compat::Spanned;
use crate::def_ids::other_api;
use crate::util::def_use::{RelevantPlaces, call_args_uses_at, terminator_use_def};
use crate::util::mir_utils::dep_callee_def_id;

use super::super::RelevantItem;
use super::super::BackwardSlicer;
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
    ) {
        if call_changes_memory_state(self.tcx, func) {
            // Keep calls that can change an allocation's lifetime or consume
            // a raw ownership share, together with their argument sources.
            items.push(RelevantItem::Terminator {
                global_block: None,
                def_id,
                block,
                switch_succ: None,
            });
            relevant.extend(call_args_uses_at(args, &[0]));
            return;
        }

        // `Owning` traces an owner's construction chain: keep a call whose
        // destination is a `needs_drop` value even when that local is not
        // itself relevant, so its field provenance survives.
        if super::may_need_drop(self.tcx, def_id, body.local_decls[destination.local].ty) {
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
    successor: Option<BasicBlock>,
) {
    if matches!(terminator.kind, TerminatorKind::Drop { .. }) {
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

fn call_changes_memory_state(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    dep_callee_def_id(func).is_some_and(|callee| {
        other_api::is_drop_fn(tcx, callee)
            || other_api::shared_owner_raw_arg(tcx, callee).is_some()
    })
}
