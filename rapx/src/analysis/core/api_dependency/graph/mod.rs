pub mod avail;
pub mod dep_edge;
pub mod dep_node;
mod dump;
mod resolve;
mod std_tys;
pub mod transform;
mod ty_wrapper;

use super::Config;
use super::utils;
use super::visit::{self, FnVisitor};
use crate::analysis::core::api_dependency::is_fuzzable_ty;
use crate::analysis::utils::def_path::path_str_def_id;
use crate::rap_debug;
use crate::rap_trace;
use crate::utils::fs::rap_create_file;
use bit_set::BitSet;
pub use dep_edge::DepEdge;
pub use dep_node::DepNode;
use petgraph::Direction;
use petgraph::Graph;
use petgraph::dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::Binder;
use rustc_middle::ty::{self, Ty, TyCtxt};
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::hash::Hash;
use std::io::Write;
use std::path::Path;
pub use transform::TransformKind;
pub use ty_wrapper::TyWrapper;

type InnerGraph<'tcx> = Graph<DepNode<'tcx>, DepEdge>;

#[derive(Clone)]
pub struct ApiDependencyGraph<'tcx> {
    graph: InnerGraph<'tcx>,
    node_indices: HashMap<DepNode<'tcx>, NodeIndex>,
    ty_nodes: Vec<NodeIndex>,
    api_nodes: Vec<NodeIndex>,
    tcx: TyCtxt<'tcx>,
}

#[derive(Copy, Clone, Debug)]
pub struct Statistics {
    pub num_api: usize,
    pub num_generic_api: usize,
    pub type_count: usize,
    pub edge_cnt: usize,
}

impl Statistics {
    pub fn info(&self) {
        rap_info!(
            "API Graph contains {} API nodes, {} generic API nodes, {} type nodes, {} edges",
            self.num_api,
            self.num_generic_api,
            self.type_count,
            self.edge_cnt
        );
    }
}

impl<'tcx> ApiDependencyGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> ApiDependencyGraph<'tcx> {
        ApiDependencyGraph {
            graph: Graph::new(),
            node_indices: HashMap::new(),
            ty_nodes: Vec::new(),
            api_nodes: Vec::new(),
            tcx,
        }
    }

    pub fn num_api(&self) -> usize {
        self.api_nodes.len()
    }

    pub fn num_ty(&self) -> usize {
        self.ty_nodes.len()
    }

    pub fn api_node_at(&self, idx: usize) -> DepNode<'tcx> {
        let index = self.api_nodes[idx];
        self.graph[index]
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn build(&mut self, config: &Config) {
        let tcx = self.tcx();
        let mut visitor = FnVisitor::new(config.visit_config, tcx);

        // 1. collect APIs
        tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

        // 2. add non generic APIs
        visitor.non_generic_apis().iter().for_each(|&fn_did| {
            self.add_identity_api(fn_did);
        });

        // 3. resolve generic API to monomorphic API
        if config.resolve_generic {
            self.resolve_generic_api(
                visitor.non_generic_apis(),
                visitor.generic_apis(),
                config.max_generic_search_iteration,
            );
        } else {
            self.update_transform_edges();
        }
    }

    pub fn inner_graph(&self) -> &InnerGraph<'tcx> {
        &self.graph
    }

    pub fn statistics(&self) -> Statistics {
        let mut num_api = 0;
        let mut num_generic_api = 0;
        let mut ty_cnt = 0;
        let mut edge_cnt = 0;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                DepNode::Api(did, ..) => {
                    num_api += 1;
                    if utils::fn_requires_monomorphization(did, self.tcx) {
                        num_generic_api += 1;
                    }
                }
                DepNode::Ty(_) => ty_cnt += 1,
            }
        }

        for edge in self.graph.edge_indices() {
            edge_cnt += 1;
        }

        Statistics {
            num_api,
            num_generic_api,
            type_count: ty_cnt,
            edge_cnt,
        }
    }

    pub fn is_node_exist(&self, node: &DepNode<'tcx>) -> bool {
        self.node_indices.contains_key(&node)
    }

    pub fn get_or_create_index(&mut self, node: DepNode<'tcx>) -> NodeIndex {
        if let Some(node_index) = self.node_indices.get(&node) {
            *node_index
        } else {
            let node_index = self.graph.add_node(node.clone());
            self.node_indices.insert(node.clone(), node_index);
            match node {
                DepNode::Api(..) => {
                    self.api_nodes.push(node_index);
                }
                DepNode::Ty(_) => {
                    self.ty_nodes.push(node_index);
                }
                _ => {}
            }
            node_index
        }
    }

    pub fn get_node_from_index(&self, index: NodeIndex) -> DepNode<'tcx> {
        self.graph[index]
    }

    pub fn get_index_by_ty(&self, ty: Ty<'tcx>) -> Option<NodeIndex> {
        let ty_wrapper = TyWrapper::from(ty);
        self.get_index(DepNode::Ty(ty_wrapper))
    }

    pub fn get_index(&self, node: DepNode<'tcx>) -> Option<NodeIndex> {
        self.node_indices.get(&node).map(|index| *index)
    }

    pub fn add_edge(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        self.graph.add_edge(src, dst, edge);
    }

    pub fn add_edge_once(&mut self, src: NodeIndex, dst: NodeIndex, edge: DepEdge) {
        if !self.graph.contains_edge(src, dst) {
            self.graph.add_edge(src, dst, edge);
        }
    }

    pub fn add_identity_api(&mut self, fn_did: DefId) -> bool {
        let args = ty::GenericArgs::identity_for_item(self.tcx, fn_did);

        if !self.add_api(fn_did, args) {
            return false;
        }

        self.get_or_create_index(DepNode::api(fn_did, args));

        true
    }

    /// return true if the api is added successfully, false if it already exists.
    pub fn add_api(&mut self, fn_did: DefId, args: &[ty::GenericArg<'tcx>]) -> bool {
        let node = DepNode::api(fn_did, self.tcx.mk_args(args));
        if self.is_node_exist(&node) {
            return false;
        }
        let api_node = self.get_or_create_index(node);

        rap_trace!("[ApiDependencyGraph] add fn: {:?} args: {:?}", fn_did, args);

        let fn_sig = utils::fn_sig_with_generic_args(fn_did, args, self.tcx);

        // add inputs/output to graph, and compute constraints based on subtyping
        for (no, input_ty) in fn_sig.inputs().iter().enumerate() {
            let input_node = self.get_or_create_index(DepNode::ty(*input_ty));
            self.add_edge(input_node, api_node, DepEdge::arg(no));
        }

        let output_ty = fn_sig.output();
        let output_node = self.get_or_create_index(DepNode::ty(output_ty));
        self.add_edge(api_node, output_node, DepEdge::ret());

        true
    }

    /// return all transform kind for `ty` that we intersted in.
    pub fn all_transforms(&self, ty: Ty<'tcx>) -> Vec<TransformKind> {
        let mut tfs = Vec::new();
        if let Some(index) = self.get_index(DepNode::Ty(ty.into())) {
            for edge in self.graph.edges_directed(index, Direction::Outgoing) {
                if let DepEdge::Transform(kind) = edge.weight() {
                    tfs.push(*kind);
                }
            }
        }
        tfs
    }

    pub fn is_start_node_index(&self, index: NodeIndex) -> bool {
        match self.graph[index] {
            DepNode::Api(..) => self
                .graph
                .neighbors_directed(index, Direction::Incoming)
                .next()
                .is_none(),
            DepNode::Ty(ty) => utils::is_fuzzable_ty(ty.into(), self.tcx),
        }
    }

    pub fn depth_map(&self) -> HashMap<DepNode<'tcx>, usize> {
        let mut map = HashMap::new();
        let mut visited = BitSet::with_capacity(self.graph.node_count());

        // initialize worklist with start node (indegree is zero)
        let mut worklist = VecDeque::from_iter(self.graph.node_indices().filter(|index| {
            let cond = self.is_start_node_index(*index);
            if cond {
                visited.insert(index.index());
                map.insert(self.get_node_from_index(*index), 0);
            }
            cond
        }));

        rap_trace!("[depth_map] initial worklist = {:?}", worklist);

        const LARGE_ENOUGH: usize = 0xffffffff;

        // initialize queue with fuzzable type
        while let Some(current) = worklist.pop_front() {
            let node = self.get_node_from_index(current);

            if !map.contains_key(&node) {
                // depth: Ty = min(prev_ty), Api = sum(arg_ty) + 1
                let depth = match node {
                    DepNode::Ty(_) => self
                        .graph
                        .neighbors_directed(current, Direction::Incoming)
                        .map(|prev| {
                            let prev_node = &self.get_node_from_index(prev);
                            map.get(prev_node).copied().unwrap_or(LARGE_ENOUGH)
                        })
                        .min()
                        .unwrap_or(0),
                    DepNode::Api(..) => {
                        self.graph
                            .neighbors_directed(current, Direction::Incoming)
                            .map(|prev| {
                                let prev_node = &self.get_node_from_index(prev);
                                map.get(prev_node).copied().unwrap_or(LARGE_ENOUGH)
                            })
                            .sum::<usize>()
                            + 1
                    }
                };
                map.insert(node, depth);
            }

            for next in self.graph.neighbors(current) {
                let is_reachable = match self.graph[next] {
                    DepNode::Ty(_) => true,
                    DepNode::Api(..) => self
                        .graph
                        .neighbors_directed(next, petgraph::Direction::Incoming)
                        .all(|nbor| visited.contains(nbor.index())),
                };

                if is_reachable && visited.insert(next.index()) {
                    rap_trace!("[depth_map] add {:?} to worklist", next);
                    worklist.push_back(next);
                }
            }
        }

        map
    }

    pub fn traverse_covered_api_with(
        &self,
        f_cover: &mut impl FnMut(DefId),
        f_total: &mut impl FnMut(DefId),
    ) {
        let mut visited = BitSet::with_capacity(self.graph.node_count());

        for index in self.graph.node_indices() {
            if let DepNode::Api(did, _) = self.graph[index] {
                f_total(did);
            }
        }

        // initialize worklist with start node (indegree is zero)
        let mut worklist = VecDeque::from_iter(self.graph.node_indices().filter(|index| {
            if self.is_start_node_index(*index) {
                visited.insert(index.index());
                true
            } else {
                false
            }
        }));

        rap_trace!("[estimate_coverage] initial worklist = {:?}", worklist);

        // initialize queue with fuzzable type
        while let Some(index) = worklist.pop_front() {
            if let DepNode::Api(did, args) = self.graph[index] {
                f_cover(did);
            }

            for next in self.graph.neighbors(index) {
                let is_reachable = match self.graph[next] {
                    DepNode::Ty(_) => true,
                    DepNode::Api(..) => self
                        .graph
                        .neighbors_directed(next, petgraph::Direction::Incoming)
                        .all(|nbor| visited.contains(nbor.index())),
                };
                if is_reachable && visited.insert(next.index()) {
                    rap_trace!("[traverse_covered_api] add {:?} to worklist", next);
                    worklist.push_back(next);
                }
            }
        }
    }

    fn recache(&mut self) {
        self.node_indices.clear();
        self.ty_nodes.clear();
        self.api_nodes.clear();
        for idx in self.graph.node_indices() {
            let node = &self.graph[idx];
            self.node_indices.insert(node.clone(), idx);
            match node {
                DepNode::Api(..) => self.api_nodes.push(idx),
                DepNode::Ty(..) => self.ty_nodes.push(idx),
                _ => {}
            }
        }
    }

    pub fn uncovered_api(&self) -> Vec<DefId> {
        let mut covered = HashSet::new();
        let mut total = HashSet::new();
        self.traverse_covered_api_with(
            &mut |did| {
                covered.insert(did);
            },
            &mut |did| {
                total.insert(did);
            },
        );
        total.difference(&covered).copied().collect()
    }

    /// `estimate_coverage` treat each API as the distinct API.
    /// For example, if `foo<T>`, `foo<U>` are covered, this API return (2, 2).
    pub fn estimate_coverage(&self) -> (usize, usize) {
        let mut num_total = 0;
        let mut num_estimate = 0;
        self.traverse_covered_api_with(
            &mut |did| {
                num_estimate += 1;
            },
            &mut |did| {
                num_total += 1;
            },
        );
        (num_estimate, num_total)
    }

    /// `estimate_coverage_distinct` treat mono API as the original generic API.
    /// For example, if `foo<T>`, `foo<U>` are covered, this API return (1, 1).
    pub fn estimate_coverage_distinct(&self) -> (usize, usize) {
        let mut total = HashSet::new();
        let mut estimate = HashSet::new();
        self.traverse_covered_api_with(
            &mut |did| {
                estimate.insert(did);
            },
            &mut |did| {
                total.insert(did);
            },
        );
        (estimate.len(), total.len())
    }

    pub fn dump_apis<P: AsRef<Path>>(&self, path: P) {
        let tcx = self.tcx;
        let mut file = rap_create_file(path, "can not create api file");

        self.graph
            .node_indices()
            .for_each(|index| match self.graph[index] {
                DepNode::Api(did, args) => {
                    writeln!(
                        file,
                        "API,\t{},\tis_fuzzable = {}",
                        tcx.def_path_str_with_args(did, args),
                        utils::is_fuzzable_api(did, args, tcx)
                    )
                    .expect("fail when writing data to api file");
                }
                DepNode::Ty(ty) => {
                    let ty = ty.ty();
                    writeln!(
                        file,
                        "TYPE,\t{},\tis_fuzzable = {}",
                        ty,
                        is_fuzzable_ty(ty, tcx)
                    )
                    .expect("fail when writing data to api file");
                }
            });
    }
}
