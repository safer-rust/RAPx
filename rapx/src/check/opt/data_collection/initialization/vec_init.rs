use annotate_snippets::{Level, Renderer, Snippet};

use once_cell::sync::OnceCell;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};

struct DefPaths {
    vec_from_elem: DefPath,
}

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            vec_from_elem: DefPath::new("std::vec::from_elem", tcx),
        }
    }

    fn has_id(&self, def_id: DefId) -> bool {
        def_id == self.vec_from_elem.last_def_id()
    }
}

pub struct VecInitCheck {
    record: Vec<Span>,
}

impl OptCheck for VecInitCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if def_paths.has_id(*def_id) {
                        self.record.push(node.span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_vec_init(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_vec_init(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Initialization happens here"),
        );
    let message = Level::Warning
        .title("Unnecessary data collection initialization detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use unsafe APIs to skip initialization."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
