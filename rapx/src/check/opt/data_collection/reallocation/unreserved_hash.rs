use std::collections::HashSet;

use crate::{
    analysis::dataflow::*,
    check::opt::OptCheck,
    utils::span::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use rustc_middle::{mir::Local, ty::TyCtxt};

use annotate_snippets::{Level, Renderer, Snippet};
use rustc_span::Span;

crate::def_paths! {
    hashset_insert: "std::collections::HashSet::insert",
    hashmap_insert: "std::collections::HashMap::insert",
    hashset_new: "std::collections::HashSet::new",
    hashmap_new: "std::collections::HashMap::new",
    entry: "std::collections::HashMap::entry",
}


pub struct UnreservedHashCheck {
    record: Vec<(Span, Span)>,
}

fn is_hash_new_node(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            let def_paths = &DEFPATHS.get().unwrap();
            if *def_id == def_paths.hashmap_new.last_def_id()
                || *def_id == def_paths.hashset_new.last_def_id()
            {
                return true;
            }
        }
    }
    false
}

fn find_downside_hash_insert_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut hash_insert_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.hashmap_insert.last_def_id()
                    || *def_id == def_paths.hashset_insert.last_def_id()
                    || *def_id == def_paths.entry.last_def_id()
                {
                    hash_insert_node_idx = Some(idx);
                    return DFSStatus::Stop;
                }
            }
        }
        DFSStatus::Continue
    };
    let mut seen = HashSet::new();
    graph.dfs(
        node_idx,
        Direction::Downside,
        &mut node_operator,
        &mut Graph::equivalent_edge_validator,
        false,
        &mut seen,
    );
    hash_insert_node_idx
}

impl OptCheck for UnreservedHashCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for (node_idx, node) in graph.nodes.iter_enumerated() {
            if is_hash_new_node(node) {
                if let Some(insert_idx) = find_downside_hash_insert_node(graph, node_idx) {
                    let insert_node = &graph.nodes[insert_idx];
                    self.record.push((node.span, insert_node.span));
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for (hash_span, insert_span) in self.record.iter() {
            report_unreserved_hash_bug(graph, *hash_span, *insert_span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_unreserved_hash_bug(graph: &Graph, hash_span: Span, insert_span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(hash_span);
    let snippet: Snippet<'_> = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, hash_span))
                .label("Space unreserved."),
        )
        .annotation(
            Level::Info
                .span(relative_pos_range(graph.span, insert_span))
                .label("Insertion happens here."),
        );
    let message = Level::Warning
        .title("Improper data collection detected")
        .snippet(snippet)
        .footer(Level::Help.title("Reserve enough space."));
    let renderer = Renderer::styled();
    rap_warn!("{}", renderer.render(message));
}
