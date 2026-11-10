//! Backward relevance rules for MIR statements and terminators.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Body, Statement, Terminator};
use rustc_middle::ty::{Ty, TyCtxt, TypeFlags, TypeVisitableExt, TypingEnv};

use super::types::RelevantItem;
use super::visitor::BackwardSlicer;
use crate::analysis::dataflow::types::DataflowGraph;
use crate::helpers::def_use::RelevantPlaces;

mod call;
mod dispatch;
mod statement;
mod terminator;

fn may_need_drop<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, ty: Ty<'tcx>) -> bool {
    // A local with an unresolved const argument may own resources. Querying
    // `needs_drop` can enter rustc's solver with that const absent from the
    // current body's param-env (e.g. `Result<[&mut T; N], E>` in a callee).
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
        statement_index: usize,
        statement: &'tcx Statement<'tcx>,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
        keep_owner: bool,
    ) {
        dispatch::apply_statement(&mut dispatch::StatementContext {
            slicer: self,
            def_id,
            block,
            statement_index,
            statement,
            body,
            flow,
            relevant,
            items,
            keep_invalidations,
            keep_owner,
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
        keep_invalidations: bool,
        keep_owner: bool,
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
            keep_invalidations,
            keep_owner,
            successor,
        });
    }
}
