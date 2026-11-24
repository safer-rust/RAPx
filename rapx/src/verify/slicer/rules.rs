//! Backward relevance rules for MIR statements and terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Statement, Terminator};
use rustc_middle::ty::{Ty, TyCtxt, TypeFlags, TypeVisitableExt, TypingEnv};

use super::RelevantItem;
use super::BackwardSlicer;
use crate::analysis::dataflow::types::DataflowGraph;
use crate::util::def_use::RelevantPlaces;

mod call;
mod dispatch;
mod statement;
mod terminator;

fn may_need_drop<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    // Generic consts and placeholders can make rustc's `needs_drop` query fail.
    ty.has_type_flags(TypeFlags::HAS_CT_PARAM)
        || ty.has_non_region_placeholders()
        || ty.has_escaping_bound_vars()
        || ty.needs_drop(tcx, TypingEnv::post_analysis(tcx, def_id))
}

impl<'tcx> BackwardSlicer<'tcx> {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_statement(
        &self,
        def_id: DefId,
        block: BasicBlock,
        stmt_index: usize,
        statement: &'tcx Statement<'tcx>,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
    ) {
        dispatch::apply_statement(&mut dispatch::StatementContext {
            slicer: self,
            def_id,
            block,
            stmt_index,
            statement,
            body,
            flow,
            relevant,
            items,
        });
    }

    #[allow(clippy::too_many_arguments)]
    pub(in crate::verify::slicer) fn visit_terminator(
        &self,
        def_id: DefId,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        successor: Option<BasicBlock>,
    ) {
        dispatch::apply_terminator(&mut dispatch::TerminatorContext {
            slicer: self,
            def_id,
            block,
            terminator,
            flow,
            body,
            relevant,
            items,
            successor,
        });
    }
}
