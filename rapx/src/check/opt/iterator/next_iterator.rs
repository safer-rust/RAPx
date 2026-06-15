use once_cell::sync::OnceCell;

use rustc_hir::{Expr, ExprKind, intravisit};
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::TypeckResults;
use rustc_span::Span;

use crate::analysis::dataflow::Graph;
use crate::check::opt::OptCheck;
use crate::helpers::def_path::DefPath;
use crate::utils::log::{
    relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code,
};
use annotate_snippets::{Level, Renderer, Snippet};

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    iter_next: DefPath,
    iter_chain: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            iter_next: DefPath::new("std::iter::Iterator::next", tcx),
            iter_chain: DefPath::new("std::iter::Iterator::chain", tcx),
        }
    }
}

struct NextFinder<'tcx> {
    typeck_results: &'tcx TypeckResults<'tcx>,
    next_record: Vec<Span>,
    chain_record: Vec<Span>,
}

impl<'tcx> intravisit::Visitor<'tcx> for NextFinder<'tcx> {
    fn visit_expr(&mut self, ex: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(.., span) = ex.kind {
            let def_id = self
                .typeck_results
                .type_dependent_def_id(ex.hir_id)
                .unwrap();
            let next_def_id = (&DEFPATHS.get().unwrap()).iter_next.last_def_id();
            let chain_def_id = (&DEFPATHS.get().unwrap()).iter_chain.last_def_id();
            if def_id == next_def_id {
                self.next_record.push(span);
            }
            if def_id == chain_def_id {
                self.chain_record.push(span);
            }
        }
        intravisit::walk_expr(self, ex);
    }
}

pub struct NextIteratorCheck {
    next_record: Vec<Span>,
    chain_record: Vec<Span>,
    pub valid: bool,
}

impl OptCheck for NextIteratorCheck {
    fn new() -> Self {
        Self {
            next_record: Vec::new(),
            chain_record: Vec::new(),
            valid: false,
        }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let mut next_chain_finder = NextFinder {
            typeck_results,
            next_record: Vec::new(),
            chain_record: Vec::new(),
        };
        intravisit::walk_body(&mut next_chain_finder, body);
        if next_chain_finder.chain_record.is_empty() || next_chain_finder.next_record.is_empty() {
            self.valid = false;
        } else {
            self.valid = true;
            self.next_record = next_chain_finder.next_record;
            self.chain_record = next_chain_finder.chain_record;
        }
    }

    fn report(&self, graph: &Graph) {
        report_next_iterator_bug(&self.next_record, &self.chain_record, graph.span);
    }

    fn cnt(&self) -> usize {
        self.next_record.len()
    }
}

fn report_next_iterator_bug(next_record: &Vec<Span>, chain_record: &Vec<Span>, graph_span: Span) {
    let code_source = span_to_source_code(graph_span);
    let filename = span_to_filename(graph_span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph_span))
        .origin(&filename)
        .fold(true);
    for next_span in next_record {
        snippet = snippet.annotation(Level::Error.span(relative_pos_range(graph_span, *next_span)))
    }
    for chain_span in chain_record {
        snippet = snippet.annotation(Level::Error.span(relative_pos_range(graph_span, *chain_span)))
    }
    let message = Level::Warning
        .title("Inefficient iterators detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use chunk iterators."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
