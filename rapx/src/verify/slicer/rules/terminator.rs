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
            // A manual drop (`std::mem::drop` / `ManuallyDrop::drop`) also frees
            // the pointee's heap: keep the call and its argument's construction
            // chain so `Allocated`/`Owning` can see the freed allocation and
            // detect a later use / second drop.
            let is_drop_call = mir_utils::dep_callee_def_id(func).is_some_and(|c| {
                crate::verify::api_classify::is_manually_drop_drop(Some(c))
                    || crate::verify::api_classify::is_std_drop(Some(c))
            });
            if is_drop_call {
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
            let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, def_id);
            if dest_ty.needs_drop(self.tcx, typing_env) {
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
