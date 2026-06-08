use once_cell::sync::OnceCell;

use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TypeckResults;
use rustc_span::Span;

use crate::analysis::core::dataflow::Graph;
use crate::analysis::utils::def_path::DefPath;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_first_line, span_to_line_number,
    span_to_source_code, span_to_trimmed_span,
};
use annotate_snippets::{Level, Renderer, Snippet};

use super::super::super::LEVEL;
use super::super::super::NO_STD;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    vec_push: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                vec_push: DefPath::new("alloc::vec::Vec::push", tcx),
            }
        } else {
            Self {
                vec_push: DefPath::new("std::vec::Vec::push", tcx),
            }
        }
    }
}

pub struct LoopFinder<'tcx> {
    pub typeck_results: &'tcx TypeckResults<'tcx>,
    pub record: Vec<(Span, Vec<Span>)>,
}

pub struct PushFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: Vec<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for PushFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let target_def_id = (&DEFPATHS.get().unwrap()).vec_push.last_def_id();
            if def_id == target_def_id {
                self.record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for LoopFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::Loop(block, ..) = ex.kind {
            let mut push_finder = PushFinder {
                typeck_results: self.typeck_results,
                record: Vec::new(),
            };
            intravisit::walk_block(&mut push_finder, block);
            // if !push_finder.record.is_empty() {
            //     self.record.push((ex.span, push_finder.record));
            // }
            if push_finder.record.len() == 1 {
                // we only use simple cases
                self.record.push((ex.span, push_finder.record));
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

use crate::check::opt::OptCheck;

pub struct BoundsLoopPushCheck {
    pub record: Vec<(Span, Vec<Span>)>,
}

impl OptCheck for BoundsLoopPushCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            let def_id = graph.def_id;
            let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
            let typeck_results = tcx.typeck(def_id.as_local().unwrap());
            let mut loop_finder = LoopFinder {
                typeck_results,
                record: Vec::new(),
            };
            intravisit::walk_body(&mut loop_finder, body);
            self.record = loop_finder.record;
        }
    }

    fn report(&self, _: &Graph) {
        for (loop_span, push_record) in self.record.iter() {
            report_loop_push_bug(*loop_span, push_record);
        }
    }

    fn cnt(&self) -> usize {
        self.record.iter().map(|(_, spans)| spans.len()).sum()
    }
}

fn report_loop_push_bug(loop_span: Span, push_record: &Vec<Span>) {
    let code_source = span_to_source_code(loop_span);
    let filename = span_to_filename(loop_span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(loop_span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Info
                .span(relative_pos_range(
                    loop_span,
                    span_to_trimmed_span(span_to_first_line(loop_span)),
                ))
                .label("A loop operation."),
        );
    for push_span in push_record {
        snippet = snippet.annotation(
            Level::Error
                .span(relative_pos_range(loop_span, *push_span))
                .label("Push happens here."),
        );
    }
    let message = Level::Warning
        .title("Unnecessary bounds checkings detected")
        .snippet(snippet);
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
