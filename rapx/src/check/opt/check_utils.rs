use rustc_hir::def_id::DefId;

use crate::analysis::dataflow::{GraphNode, NodeOp};

/// Returns true if the node represents a call to one of the given DefIds.
pub fn node_matches_call(node: &GraphNode, def_ids: &[DefId]) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op
            && def_ids.contains(def_id) {
                return true;
            }
    }
    false
}

/// Returns true if the node represents a call matching any of the given DefIds.
pub fn node_matches_any_call(node: &GraphNode, pred: impl Fn(DefId) -> bool) -> bool {
    for op in node.ops.iter() {
        if let NodeOp::Call(def_id) = op
            && pred(*def_id) {
                return true;
            }
    }
    false
}
