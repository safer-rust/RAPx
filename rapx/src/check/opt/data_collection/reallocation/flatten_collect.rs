use once_cell::sync::OnceCell;

use rustc_middle::ty::TyCtxt;

use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    check::opt::OptCheck,
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};
use rustc_span::Span;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    flat_map: DefPath,
    flatten: DefPath,
    collect: DefPath,
}

impl DefPaths {
    fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            flat_map: DefPath::new("std::iter::Iterator::flat_map", tcx),
            flatten: DefPath::new("std::iter::Iterator::flatten", tcx),
            collect: DefPath::new("std::iter::Iterator::collect", tcx),
        }
    }
}

pub struct FlattenCollectCheck {
    record: Vec<Span>,
}

fn is_flatten_node(node: &GraphNode) -> bool {
    let def_paths = &DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.flat_map.last_def_id()
                || *def_id == def_paths.flatten.last_def_id()
            {
                return true;
            }
        }
    }
    false
}

fn is_collect_node(node: &GraphNode) -> bool {
    let def_paths = &DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.collect.last_def_id() {
                return true;
            }
        }
    }
    false
}

impl OptCheck for FlattenCollectCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if is_flatten_node(node) {
                for edge_idx in node.out_edges.iter() {
                    let dst_idx = graph.edges[*edge_idx].dst;
                    let dst_node = &graph.nodes[dst_idx];
                    if is_collect_node(dst_node) {
                        self.record.push(dst_node.span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_flatten_collect(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_flatten_collect(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(span);
    let snippet: Snippet<'_> = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Flatten then collect."),
        );

    let message = Level::Error
        .title("Data collection inefficiency detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use extend manually."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
