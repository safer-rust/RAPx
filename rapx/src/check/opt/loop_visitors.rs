use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::TypeckResults;
use rustc_span::Span;

pub struct LoopFinder<'tcx> {
    pub typeck_results: &'tcx TypeckResults<'tcx>,
    pub record: Vec<(Span, Vec<Span>)>,
    pub target_def_id: rustc_span::def_id::DefId,
}

pub struct PushFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: Vec<Span>,
    target_def_id: rustc_span::def_id::DefId,
}

impl<'tcx> PushFinder<'tcx> {
    pub fn new(
        typeck_results: &'tcx TypeckResults<'tcx>,
        target_def_id: rustc_span::def_id::DefId,
    ) -> PushFinder<'tcx> {
        PushFinder {
            typeck_results,
            record: Vec::new(),
            target_def_id,
        }
    }

    pub fn into_record(self) -> Vec<Span> {
        self.record
    }
}

impl<'tcx> LoopFinder<'tcx> {
    pub fn new(
        typeck_results: &'tcx TypeckResults<'tcx>,
        target_def_id: rustc_span::def_id::DefId,
    ) -> LoopFinder<'tcx> {
        LoopFinder {
            typeck_results,
            record: Vec::new(),
            target_def_id,
        }
    }

    pub fn into_record(self) -> Vec<(Span, Vec<Span>)> {
        self.record
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for PushFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            if def_id == self.target_def_id {
                self.record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for LoopFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::Loop(block, ..) = ex.kind {
            let mut push_finder = PushFinder::new(self.typeck_results, self.target_def_id);
            intravisit::walk_block(&mut push_finder, block);
            if push_finder.record.len() == 1 {
                self.record.push((ex.span, push_finder.into_record()));
            }
        }
        intravisit::walk_expr(self, ex);
    }
}
