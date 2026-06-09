use std::collections::HashSet;

use crate::analysis::{dataflow::*, utils::def_path::DefPath};
use once_cell::sync::OnceCell;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use super::{report_encoding_bug, value_is_from_const};

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    string_from_utf8: DefPath,
    string_from_utf8_lossy: DefPath,
    vec_new: DefPath,
    vec_with_capacity: DefPath,
    vec_push: DefPath,
}

impl DefPaths {
    // only supports push operation (can't support direct assignment)
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            string_from_utf8: DefPath::new("std::string::String::from_utf8", tcx),
            string_from_utf8_lossy: DefPath::new("std::string::String::from_utf8_lossy", tcx),
            vec_new: DefPath::new("std::vec::Vec::new", tcx),
            vec_with_capacity: DefPath::new("std::vec::Vec::with_capacity", tcx),
            vec_push: DefPath::new("std::vec::Vec::push", tcx),
        }
    }
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
    let mut vec_new_node_idx = None;
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: may traverse all upside nodes and the new result will overwrite on the previous result
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_new.last_def_id()
                    || *def_id == def_paths.vec_with_capacity.last_def_id()
                {
                    vec_new_node_idx = Some(idx);
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
    vec_new_node_idx
}

// todo: we can find downside index node too

fn find_downside_push_node(graph: &Graph, node_idx: Local) -> Vec<Local> {
    let mut push_node_idxs: Vec<Local> = Vec::new();
    let def_paths = &DEFPATHS.get().unwrap();
    // Warning: traverse all downside nodes
    let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
        let node = &graph.nodes[idx];
        for op in node.ops.iter() {
            if let NodeOp::Call(def_id) = op {
                if *def_id == def_paths.vec_push.last_def_id() {
                    push_node_idxs.push(idx);
                    break;
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
        &mut Graph::always_true_edge_validator,
        true,
        &mut seen,
    );
    push_node_idxs
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
