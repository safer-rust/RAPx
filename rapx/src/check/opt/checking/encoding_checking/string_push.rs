use std::collections::HashSet;

use once_cell::sync::OnceCell;

use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use super::value_is_from_const;
use crate::{
    analysis::{
        core::dataflow::*,
        utils::def_path::DefPath,
    },
    utils::log::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use annotate_snippets::{Level, Renderer, Snippet};

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    string_new: DefPath,
    string_push: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            string_new: DefPath::new("std::string::String::new", tcx),
            string_push: DefPath::new("std::string::String::push", tcx),
        }
    }
}

use crate::check::opt::OptCheck;

pub struct StringPushCheck {
    record: Vec<Span>,
}

fn extract_value_if_is_string_push(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let def_paths = DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.string_push.last_def_id() {
                let push_value_idx = graph.edges[node.in_edges[1]].src; //the secod parameter
                return Some(push_value_idx);
            }
        }
    }
    None
}

fn find_upside_string_new(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut string_new_node_idx = None;
    let def_paths = DEFPATHS.get().unwrap();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.string_new.last_def_id() {
                    string_new_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        node_idx,
        Direction::Upside,
        &mut node_operator,
        &mut Graph::always_true_edge_validator,
        false,
        &mut seen,
    );
    string_new_node_idx
}

impl OptCheck for StringPushCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if let Some(pushed_value_idx) = extract_value_if_is_string_push(graph, node) {
                if find_upside_string_new(graph, node_idx).is_some() {
                    if !value_is_from_const(graph, pushed_value_idx) {
                        self.record.clear(); // Warning: Not rigorous, push of other string may cause clear
                        return;
                    }
                    self.record.push(node.span);
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        if !self.record.is_empty() {
            report_string_push_bug(graph, &self.record);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_string_push_bug(graph: &Graph, spans: &Vec<Span>) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(graph.span);
    let mut snippet = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true);
    for span in spans.iter() {
        snippet = snippet.annotation(
            Level::Error
                .span(relative_pos_range(graph.span, *span))
                .label("Checked here."),
        )
    }
    let message = Level::Warning
        .title("Unnecessary encoding checkings detected")
        .snippet(snippet)
        .footer(Level::Help.title("Use unsafe APIs instead."));
    let renderer = Renderer::styled();
    println!("{}", renderer.render(message));
}
