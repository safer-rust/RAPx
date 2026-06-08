use std::collections::HashSet;

use once_cell::sync::OnceCell;

use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use super::{report_encoding_bug, value_is_from_const};
use crate::analysis::{
    core::dataflow::*,
    utils::def_path::DefPath,
};
use crate::check::opt::OptCheck;

static DEFPATHS: OnceCell<DefPaths> = OnceCell::new();

struct DefPaths {
    str_from_utf8: DefPath,
}

impl DefPaths {
    pub fn new(tcx: &TyCtxt<'_>) -> Self {
        Self {
            str_from_utf8: DefPath::new("std::str::from_utf8", &tcx),
        }
    }
}

pub struct ArrayEncodingCheck {
    record: Vec<Span>,
}

fn extract_ancestor_set_if_is_str_from(
    graph: &Graph,
    node_idx: Local,
    node: &GraphNode,
) -> Option<HashSet<Local>> {
    let def_paths = DEFPATHS.get().unwrap();
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op {
            if *def_id == def_paths.str_from_utf8.last_def_id() {
                return Some(graph.collect_ancestor_locals(node_idx, false));
            }
        }
    }
    None
}

fn is_valid_index_edge(graph: &Graph, edge: &GraphEdge) -> bool {
    if let EdgeOp::Index = edge.op {
        // must be Index edge
        let dst_node = &graph.nodes[edge.dst];
        if dst_node.in_edges.len() > 2 {
            // must be the left value
            let rvalue_edge_idx = dst_node.in_edges[2];
            let rvalue_idx = graph.edges[rvalue_edge_idx].src;
            if value_is_from_const(graph, rvalue_idx) {
                return true;
            }
        }
    }
    false
}

impl OptCheck for ArrayEncodingCheck {
    fn new() -> Self {
        Self { record: Vec::new() }
    }

    fn check(&mut self, graph: &Graph, tcx: &TyCtxt) {
        let _ = &DEFPATHS.get_or_init(|| DefPaths::new(tcx));
        let common_ancestor = graph
            .edges
            .iter()
            .filter_map(|edge| {
                // 另外这里index必须是左值，且右值必须来自const
                if is_valid_index_edge(graph, edge) {
                    Some(graph.collect_ancestor_locals(edge.src, true))
                } else {
                    None
                }
            })
            .reduce(|set1, set2| set1.into_iter().filter(|k| set2.contains(k)).collect());

        if let Some(common_ancestor) = common_ancestor {
            for (node_idx, node) in graph.nodes.iter_enumerated() {
                if let Some(str_from_ancestor_set) =
                    extract_ancestor_set_if_is_str_from(graph, node_idx, node)
                {
                    if !common_ancestor
                        .intersection(&str_from_ancestor_set)
                        .next()
                        .is_some()
                    {
                        self.record.clear();
                        return;
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
