use super::super::visit::FnVisitor;
use super::ApiDependencyGraph;
use super::Config;
use super::dep_edge::DepEdge;
use super::dep_node::DepNode;
use super::transform::TransformKind;
use super::ty_wrapper::TyWrapper;
use super::utils;
use crate::analysis::utils::def_path::path_str_def_id;
use crate::rap_debug;
use crate::rap_trace;
use crate::utils::fs::rap_create_file;
use petgraph::Direction;
use petgraph::visit::EdgeRef;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashSet;

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn eligible_nodes_with(&self, tys: &[Ty<'tcx>]) -> Vec<DepNode<'tcx>> {
        let check_ty = |ty: Ty<'tcx>| {
            tys.iter()
                .any(|avail_ty| utils::is_ty_eq(*avail_ty, ty, self.tcx))
        };

        self.graph
            .node_indices()
            .filter_map(|index| match self.graph[index] {
                DepNode::Api(fn_did, args)
                    if self
                        .graph
                        .neighbors_directed(index, Direction::Incoming)
                        .all(|neighbor| {
                            let ty = self.graph[neighbor].expect_ty().ty();
                            utils::is_fuzzable_ty(ty, self.tcx) || check_ty(ty)
                        }) =>
                {
                    Some(self.graph[index])
                }
                DepNode::Ty(ty)
                    if self
                        .graph
                        .neighbors_directed(index, Direction::Incoming)
                        .any(|neighbor| {
                            if let Some(ty) = self.graph[neighbor].as_ty() {
                                check_ty(ty.ty())
                            } else {
                                false
                            }
                        }) =>
                {
                    Some(self.graph[index])
                }
                _ => None,
            })
            .collect()
    }

    pub fn eligible_transforms_to(&self, ty: Ty<'tcx>) -> Vec<(TyWrapper<'tcx>, TransformKind)> {
        let mut set = HashSet::new();
        if let Some(node) = self.get_index(DepNode::Ty(ty.into())) {
            for edge in self.graph.edges_directed(node, Direction::Incoming) {
                if let Some(kind) = edge.weight().as_transform_kind() {
                    let source_ty = self.graph[edge.source()].expect_ty();
                    set.insert((source_ty, kind));
                }
            }
        }
        set.into_iter().collect()
    }
}
