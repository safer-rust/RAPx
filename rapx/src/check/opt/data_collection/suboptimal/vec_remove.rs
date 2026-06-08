use annotate_snippets::{Level, Renderer, Snippet};

use once_cell::sync::OnceCell;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

struct DefPaths {
    vec_remove: DefPath,
    vec_insert: DefPath,
}

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

impl DefPaths {
    fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            vec_remove: DefPath::new("std::vec::Vec::remove", tcx),
            vec_insert: DefPath::new("std::vec::Vec::insert", tcx),
        }
    }
}

pub struct VecRemoveCheck {
    record: Vec<Span>,
}

fn is_vec_insert_or_remove(node: &GraphNode) -> bool {
    let def_paths = DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.vec_remove.last_def_id()
                || *def_id == def_paths.vec_insert.last_def_id()
            {
                return true;
            }
        }
    }
    false
}

fn is_0_usize(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Const(desc, _) = op {
            if desc.eq("0_usize") {
                return true;
            }
        }
    }
    false
}

impl OptCheck for VecRemoveCheck {
    fn new() -> Self {
        Self { record: vec![] }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if is_vec_insert_or_remove(node) {
                let index_edge = &graph.edges[node.in_edges[1]];
                let index_node = &graph.nodes[index_edge.src];
                if is_0_usize(index_node) {
                    self.record.push(node.span);
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_vec_remove_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_vec_remove_bug(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Vec increasement / decreasement happens here."),
        );
    let message = Level::Warning
        .title("Improper data collection detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use VecQueue instead of Vec."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
