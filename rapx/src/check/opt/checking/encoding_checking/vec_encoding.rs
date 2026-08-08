use crate::analysis::dataflow::*;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use super::{report_encoding_bug, value_is_from_const};

crate::def_paths! {
    string_from_utf8: "std::string::String::from_utf8",
    string_from_utf8_lossy: "std::string::String::from_utf8_lossy",
    vec_new: "std::vec::Vec::new",
    vec_with_capacity: "std::vec::Vec::with_capacity",
    vec_push: "std::vec::Vec::push",
}

use crate::check::opt::OptCheck;

pub struct VecEncodingCheck {
    record: Vec<Span>,
}

fn extract_vec_if_is_string_from(graph: &Graph, node: &GraphNode) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.string_from_utf8.last_def_id()
                || *def_id == def_paths.string_from_utf8_lossy.last_def_id()
            {
                let in_edge = &graph.edges[node.in_edges[0]];
                return Some(in_edge.src);
            }
        }
    }
    None
}

fn find_upside_vec_new_node(graph: &Graph, node_idx: Local) -> Option<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    graph.find_first_node(
        node_idx,
        Direction::Upside,
        &mut |graph: &Graph, idx: Local| {
            let node = &graph.nodes[idx];
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == def_paths.vec_new.last_def_id()
                        || *def_id == def_paths.vec_with_capacity.last_def_id()
                    {
                        return true;
                    }
                }
            }
            false
        },
        &mut Graph::always_true_edge_validator,
    )
}

fn find_downside_push_node(graph: &Graph, node_idx: Local) -> Vec<Local> {
    let def_paths = &DEFPATHS.get().unwrap();
    graph.find_all_nodes(
        node_idx,
        Direction::Downside,
        &mut |graph: &Graph, idx: Local| {
            let node = &graph.nodes[idx];
            for op in node.ops.iter() {
                if let NodeOp::Call(def_id) = op {
                    if *def_id == def_paths.vec_push.last_def_id() {
                        return true;
                    }
                }
            }
            false
        },
        &mut Graph::always_true_edge_validator,
    )
}

impl OptCheck for VecEncodingCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        for node in graph.nodes.iter() {
            if let Some(vec_node_idx) = extract_vec_if_is_string_from(graph, node) {
                if let Some(vec_new_idx) = find_upside_vec_new_node(graph, vec_node_idx) {
                    let vec_push_indice = find_downside_push_node(graph, vec_new_idx);
                    for vec_push_idx in vec_push_indice {
                        let pushed_value_edge = &graph.edges[graph.nodes[vec_push_idx].in_edges[1]]; // The second parameter
                        let pushed_value_idx = pushed_value_edge.src;
                        if !value_is_from_const(graph, pushed_value_idx) {
                            self.record.clear();
                            return;
                        }
                    }
                    self.record.push(node.span);
                }
            }
        }
    }

    fn report(&self, graph: &Graph) {
        for span in self.record.iter() {
            report_encoding_bug(graph, *span);
        }
    }

    fn cnt(&self) -> usize {
        self.record.len()
    }
}
