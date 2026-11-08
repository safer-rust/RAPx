//! Direct MIR dispatch for backward slicing rules.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, Body, Local, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Statement, StatementKind,
    Terminator, TerminatorKind,
};

use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::{RelevantPlaces, operand_uses};
use crate::verify::mir_classify;

use super::super::types::RelevantItem;
use super::super::visitor::BackwardSlicer;
use super::{statement, terminator};

pub(super) struct StatementContext<'a, 'tcx> {
    pub slicer: &'a BackwardSlicer<'tcx>,
    pub def_id: DefId,
    pub block: BasicBlock,
    pub statement_index: usize,
    pub statement: &'tcx Statement<'tcx>,
    pub body: &'tcx Body<'tcx>,
    pub flow: &'a DataflowGraph,
    pub relevant: &'a mut RelevantPlaces,
    pub items: &'a mut Vec<RelevantItem<'tcx>>,
    pub keep_invalidations: bool,
    pub keep_owner: bool,
}

pub(super) struct TerminatorContext<'a, 'tcx> {
    pub slicer: &'a BackwardSlicer<'tcx>,
    pub def_id: DefId,
    pub block: BasicBlock,
    pub terminator: &'a Terminator<'tcx>,
    pub flow: &'a DataflowGraph,
    pub body: &'a Body<'tcx>,
    pub relevant: &'a mut RelevantPlaces,
    pub items: &'a mut Vec<RelevantItem<'tcx>>,
    pub keep_invalidations: bool,
    pub keep_owner: bool,
    pub successor: Option<BasicBlock>,
}

pub(super) fn apply_statement(ctx: &mut StatementContext<'_, '_>) {
    let name = match &ctx.statement.kind {
        StatementKind::Assign(assign) => {
            let (place, rvalue) = &**assign;
            ctx.slicer.visit_assign_statement(
                ctx.def_id,
                ctx.block,
                ctx.statement_index,
                place,
                rvalue,
                ctx.body,
                ctx.flow,
                ctx.relevant,
                ctx.items,
                ctx.keep_owner,
            );
            "Assign"
        }
        StatementKind::SetDiscriminant { place, variant_index } => {
            ctx.items.push(RelevantItem::Statement {
                global_block: None,
                def_id: ctx.def_id,
                block: ctx.block,
                statement_index: ctx.statement_index,
            });
            if !place.projection.is_empty() {
                ctx.relevant.insert_mir_place(place);
            }
            if (place.projection.is_empty()
                || (place.projection.len() == 1
                    && matches!(place.projection[0].kind(), ProjectionElem::Deref)))
                && let rustc_middle::ty::TyKind::Adt(adt, _) =
                    place.ty(ctx.body, ctx.slicer.tcx).ty.kind()
                && adt.is_enum()
                && !adt.variants()[*variant_index].fields.is_empty()
            {
                ctx.relevant.enum_payload_writes.insert((
                    ctx.def_id,
                    place.local,
                    variant_index.as_usize(),
                ));
            }
            "SetDiscriminant"
        }
        StatementKind::StorageDead(local) => {
            statement::visit_storage_dead(
                ctx.def_id,
                ctx.block,
                ctx.statement_index,
                *local,
                ctx.flow,
                ctx.relevant,
                ctx.items,
                ctx.keep_invalidations,
            );
            "StorageDead"
        }
        StatementKind::StorageLive(..) => {
            if ctx.keep_invalidations {
                ctx.items.push(RelevantItem::Statement {
                    global_block: None,
                    def_id: ctx.def_id,
                    block: ctx.block,
                    statement_index: ctx.statement_index,
                });
            }
            "StorageLive"
        }
        StatementKind::Intrinsic(intrinsic)
            if let NonDivergingIntrinsic::Assume(operand) = &**intrinsic =>
        {
            ctx.items.push(RelevantItem::Statement {
                global_block: None,
                def_id: ctx.def_id,
                block: ctx.block,
                statement_index: ctx.statement_index,
            });
            if let Operand::Copy(place) | Operand::Move(place) = operand {
                ctx.relevant.insert_mir_place(place);
            }
            "Assume"
        }
        StatementKind::Intrinsic(intrinsic)
            if let NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic =>
        {
            ctx.items.push(RelevantItem::Statement {
                global_block: None,
                def_id: ctx.def_id,
                block: ctx.block,
                statement_index: ctx.statement_index,
            });
            ctx.relevant.extend(operand_uses(&copy.src));
            ctx.relevant.extend(operand_uses(&copy.dst));
            ctx.relevant.extend(operand_uses(&copy.count));
            "CopyNonOverlapping"
        }
        kind if mir_classify::is_noop_statement(kind) => "NoOp",
        _ => {
            ctx.items.push(RelevantItem::Statement {
                global_block: None,
                def_id: ctx.def_id,
                block: ctx.block,
                statement_index: ctx.statement_index,
            });
            "Unsupported"
        }
    };
    log::trace!("slicer statement rule: {name}");
}

pub(super) fn apply_terminator(ctx: &mut TerminatorContext<'_, '_>) {
    let name = match &ctx.terminator.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            ctx.slicer.visit_call_terminator(
                ctx.def_id,
                ctx.block,
                ctx.terminator,
                func,
                args,
                destination,
                ctx.flow,
                ctx.body,
                ctx.relevant,
                ctx.items,
                ctx.keep_invalidations,
                ctx.keep_owner,
            );
            "Call"
        }
        TerminatorKind::TailCall { func, args, .. } => {
            let destination = Place::from(Local::from_usize(0));
            ctx.slicer.visit_call_terminator(
                ctx.def_id,
                ctx.block,
                ctx.terminator,
                func,
                args,
                &destination,
                ctx.flow,
                ctx.body,
                ctx.relevant,
                ctx.items,
                ctx.keep_invalidations,
                ctx.keep_owner,
            );
            "TailCall"
        }
        TerminatorKind::SwitchInt { .. } => {
            visit_non_call(ctx);
            "SwitchInt"
        }
        TerminatorKind::Assert { .. } => {
            visit_non_call(ctx);
            "Assert"
        }
        TerminatorKind::Drop { .. } => {
            visit_non_call(ctx);
            "Drop"
        }
        kind if mir_classify::is_control_only_terminator(kind) => {
            visit_non_call(ctx);
            "ControlOnly"
        }
        _ => {
            ctx.items.push(RelevantItem::Terminator {
                global_block: None,
                def_id: ctx.def_id,
                block: ctx.block,
                switch_succ: None,
            });
            "Unsupported"
        }
    };
    log::trace!("slicer terminator rule: {name}");
}

fn visit_non_call(ctx: &mut TerminatorContext<'_, '_>) {
    terminator::visit_non_call_terminator(
        ctx.def_id,
        ctx.block,
        ctx.terminator,
        ctx.relevant,
        ctx.items,
        ctx.keep_invalidations,
        ctx.successor,
    );
}
