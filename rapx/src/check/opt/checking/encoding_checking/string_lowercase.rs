use annotate_snippets::{Level, Renderer, Snippet};

use once_cell::sync::OnceCell;

use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TypeckResults;
use rustc_span::Span;

use crate::analysis::core::dataflow::Graph;
use crate::analysis::utils::def_path::DefPath;
use crate::check::opt::OptCheck;

use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};

struct DefPaths {
    string_to_lowercase: DefPath,
}

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            string_to_lowercase: DefPath::new("str::to_lowercase", tcx),
        }
    }
}

struct LowercaseFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    record: Vec<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for LowercaseFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let target_def_id = (&DEFPATHS.get().unwrap()).string_to_lowercase.last_def_id();
            if def_id == target_def_id {
                self.record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct StringLowercaseCheck {
    record: Vec<Span>,
}

impl OptCheck for StringLowercaseCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut contains_finder = LowercaseFinder {
            typeck_results,
            record: Vec::new(),
        };
        intravisit::walk_body(&mut contains_finder, body);
        self.record = contains_finder.record;
    }

    fn report(&self, graph: &Graph) {
        for contains_span in self.record.iter() {
            report_string_ascii_bug(graph, *contains_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_string_ascii_bug(graph: &Graph, contains_span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, contains_span))
                .label("Checked here."),
        );
    let message = Level::Warning
        .title("Unnecessary encoding checkings detected.")
        .snippet(snippet)
        .footer(Level::Help.title("Use to_ascii_lowercase instead."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
