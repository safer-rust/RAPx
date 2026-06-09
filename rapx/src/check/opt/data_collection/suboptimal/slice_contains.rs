use annotate_snippets::{Level, Renderer, Snippet};

use once_cell::sync::OnceCell;

use crate::{
    analysis::{dataflow::Graph, utils::def_path::DefPath},
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::Span;

struct DefPaths {
    slice_contains: DefPath,
}

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            slice_contains: DefPath::new("slice::contains", tcx),
        }
    }
}

struct ContainsFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: Vec<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for ContainsFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let target_def_id = (&DEFPATHS.get().unwrap()).slice_contains.last_def_id();
            if def_id == target_def_id {
                self.record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct SliceContainsCheck {
    record: Vec<Span>,
}

impl OptCheck for SliceContainsCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut contains_finder = ContainsFinder {
            typeck_results,
            record: Vec::new(),
        };
        intravisit::walk_body(&mut contains_finder, body);
        self.record = contains_finder.record;
    }

    fn report(&self, graph: &Graph) {
        for contains_span in self.record.iter() {
            report_slice_contains_bug(graph, *contains_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_slice_contains_bug(graph: &Graph, contains_span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, contains_span))
                .label("Slice contains happens here."),
        );
    let message = Level::Warning
        .title("Improper data collection detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use Set instead of Slice."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
