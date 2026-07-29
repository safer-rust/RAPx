use std::collections::HashSet;

use crate::{
    analysis::dataflow::*,
    check::opt::OptCheck,
    utils::span::{relative_pos_range, span_to_filename, span_to_line_number, span_to_source_code},
};
use rustc_hir::intravisit;
use rustc_middle::mir::Local;
use rustc_middle::ty::TyCtxt;

use annotate_snippets::{Level, Renderer, Snippet};
use rustc_span::Span;

use super::super::super::loop_visitors::LoopFinder;
use super::super::super::LEVEL;

crate::def_paths! {
    vec_new: "std::vec::Vec::new",
    vec_push: "std::vec::Vec::push",
    vec_with_capacity: "std::vec::Vec::with_capacity",
    vec_reserve: "std::vec::Vec::reserve",
}


pub struct UnreservedVecCheck {
    record: Vec<Span>,
}

fn is_vec_new_node(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            let def_paths = &DEFPATHS.get().unwrap();
            if *def_id == def_paths.vec_new.last_def_id() {
                return true;
            }
        }
    }
    false
}

fn is_vec_push_node(node: &GraphNode) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            let def_paths = &DEFPATHS.get().unwrap();
            if *def_id == def_paths.vec_push.last_def_id() {
                return true;
            }
        }
    }
    false
}

fn find_upside_reservation(graph: &Graph, node_idx: Local) -> Option<Local> {
    let mut reservation_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_with_capacity.last_def_id()
                    || *def_id == def_paths.vec_reserve.last_def_id()
                {
                    reservation_node_idx = Some(idx);
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
        &mut Graph::equivalent_edge_validator,
        false,
        &mut seen,
    );
    reservation_node_idx
}

impl OptCheck for UnreservedVecCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let def_paths = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let level = LEVEL.lock().unwrap();
        if *level == 2 {
            for (node_idx, node) in graph.nodes.iter_enumerated() {
                if is_vec_new_node(node) {
                    self.record.push(node.span);
                }
                if is_vec_push_node(node) {
                    if let None = find_upside_reservation(graph, node_idx) {
                        self.record.push(node.span);
                    }
                }
            }
        }

        let def_id = graph.def_id;
        let body = tcx.hir_body_owned_by(def_id.as_local().unwrap());
        let typeck_results = tcx.typeck(def_id.as_local().unwrap());
        let target_def_id = def_paths.vec_push.last_def_id();
        let mut loop_finder = LoopFinder::new(typeck_results, target_def_id);
        intravisit::walk_body(&mut loop_finder, body);
        for (_, push_record) in loop_finder.into_record() {
            for push_span in push_record {
                if let Some((node_idx, _)) = graph.query_node_by_span(push_span, false) {
                    if let None = find_upside_reservation(graph, node_idx) {
                        self.record.push(push_span);
                    }
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_unreserved_vec_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}

fn report_unreserved_vec_bug(graph: &Graph, span: Span) {
    let code_source = span_to_source_code(graph.span);
    let filename = span_to_filename(span);
    let snippet: Snippet<'_> = Snippet::source(&code_source)
        .line_start(span_to_line_number(graph.span))
        .origin(&filename)
        .fold(true)
        .annotation(
            Level::Error
                .span(relative_pos_range(graph.span, span))
                .label("Space unreserved."),
        );
    let message = Level::Warning
        .title("Improper data collection detected")
        .snippet(snippet)
        .footer(Level::Help.title("Reserve enough space."));
    let renderer = Renderer::styled();
    rap_warn!("{}", renderer.render(message));
}
