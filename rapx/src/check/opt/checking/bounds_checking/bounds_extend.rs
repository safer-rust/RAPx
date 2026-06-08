use once_cell::sync::OnceCell;

use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};

use super::super::super::LEVEL;
use super::super::super::NO_STD;
use crate::check::opt::OptCheck;
static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    vec_extend_from_slice: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        let no_std = NO_STD.lock().unwrap();
        if *no_std {
            Self {
                vec_extend_from_slice: DefPath::new("alloc::vec::Vec::extend_from_slice", &tcx),
            }
        } else {
            Self {
                vec_extend_from_slice: DefPath::new("std::vec::Vec::extend_from_slice", &tcx),
            }
        }
    }
}

pub struct BoundsExtendCheck {
    pub record: Vec<Span>,
}

fn is_extend_from_slice(node: &GraphNode) -> bool {
    let def_paths = DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.vec_extend_from_slice.last_def_id() {
                return true;
            }
        }
    }
    false
}

impl OptCheck for BoundsExtendCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let level = LEVEL.lock().unwrap();
        if *level <= 1 {
            return;
        }
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if is_extend_from_slice(node) {
                self.record.push(node.span);
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_extend_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_extend_bug(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Checked here."),
        );
    let message = Level::Warning
        .title("Unnecessary bound checkings detected")
        .snippet(snippet)
        .footer(Level::Help.title("Manipulate memory directly."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
