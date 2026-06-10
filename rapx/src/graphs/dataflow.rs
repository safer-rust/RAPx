use std::cell::Cell;
use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_span::{DUMMY_SP, Span};

pub type EdgeIdx = usize;
pub type GraphNodes = IndexVec<Local, DataflowNode>;
pub type GraphEdges = IndexVec<EdgeIdx, DataflowEdge>;

#[derive(Clone, Debug)]
pub enum NodeOp {
    Nop,
    Err,
    Const(String, String),
    Use,
    Repeat,
    Ref,
    ThreadLocalRef,
    AddressOf,
    Len,
    Cast,
    BinaryOp,
    CheckedBinaryOp,
    NullaryOp,
    UnaryOp,
    Discriminant,
    Aggregate(AggKind),
    ShallowInitBox,
    CopyForDeref,
    RawPtr,
    Call(DefId),
    CallOperand,
}

#[derive(Clone, Debug)]
pub enum EdgeOp {
    Nop,
    Move,
    Copy,
    Const,
    Immut,
    Mut,
    Deref,
    Field(usize),
    Downcast(String),
    Index,
    ConstIndex,
    SubSlice,
}

#[derive(Clone, Copy, Debug)]
pub enum AggKind {
    Array,
    Tuple,
    Adt(DefId),
    Closure(DefId),
    Coroutine(DefId),
    RawPtr,
}

#[derive(Clone, Debug)]
pub struct DataflowEdge {
    pub src: Local,
    pub dst: Local,
    pub op: EdgeOp,
    pub seq: usize,
    pub block: usize,
    pub statement_index: usize,
}

#[derive(Clone, Debug)]
pub struct DataflowNode {
    pub ops: Vec<NodeOp>,
    pub span: Span,
    pub seq: usize,
    pub out_edges: Vec<EdgeIdx>,
    pub in_edges: Vec<EdgeIdx>,
}

impl DataflowNode {
    pub fn new() -> Self {
        Self {
            ops: vec![NodeOp::Nop],
            span: DUMMY_SP,
            seq: 0,
            out_edges: vec![],
            in_edges: vec![],
        }
    }
}

#[derive(Clone)]
pub struct DataflowGraph {
    pub def_id: DefId,
    pub span: Span,
    pub argc: usize,
    pub nodes: GraphNodes,
    pub edges: GraphEdges,
    pub n_locals: usize,
    pub closures: HashSet<DefId>,
    pub block: usize,
    pub statement_index: usize,
}

impl DataflowGraph {
    pub fn new(def_id: DefId, span: Span, argc: usize, n_locals: usize) -> Self {
        Self {
            def_id,
            span,
            argc,
            nodes: GraphNodes::from_elem_n(DataflowNode::new(), n_locals),
            edges: GraphEdges::new(),
            n_locals,
            closures: HashSet::new(),
            block: 0,
            statement_index: 0,
        }
    }

    pub fn node(&self, local: Local) -> &DataflowNode {
        &self.nodes[local]
    }

    pub fn node_mut(&mut self, local: Local) -> &mut DataflowNode {
        &mut self.nodes[local]
    }

    pub fn edge(&self, idx: EdgeIdx) -> &DataflowEdge {
        &self.edges[idx]
    }

    pub fn is_marker(&self, idx: Local) -> bool {
        idx >= Local::from_usize(self.n_locals)
    }

    pub fn add_node_edge(&mut self, src: Local, dst: Local, op: EdgeOp) -> EdgeIdx {
        let seq = self.nodes[dst].seq;
        let edge_idx = self.edges.push(DataflowEdge {
            src,
            dst,
            op,
            seq,
            block: self.block,
            statement_index: self.statement_index,
        });
        self.nodes[dst].in_edges.push(edge_idx);
        self.nodes[src].out_edges.push(edge_idx);
        edge_idx
    }

    pub fn add_const_edge(
        &mut self,
        src_desc: String,
        src_ty: String,
        dst: Local,
        op: EdgeOp,
    ) -> EdgeIdx {
        let seq = self.nodes[dst].seq;
        let mut const_node = DataflowNode::new();
        const_node.ops[0] = NodeOp::Const(src_desc, src_ty);
        let src = self.nodes.push(const_node);
        let edge_idx = self.edges.push(DataflowEdge {
            src,
            dst,
            op,
            seq,
            block: self.block,
            statement_index: self.statement_index,
        });
        self.nodes[dst].in_edges.push(edge_idx);
        edge_idx
    }

    pub fn get_upside_idx(&self, node_idx: Local, order: usize) -> Option<Local> {
        if let Some(edge_idx) = self.nodes[node_idx].in_edges.get(order) {
            Some(self.edges[*edge_idx].src)
        } else {
            None
        }
    }

    pub fn get_downside_idx(&self, node_idx: Local, order: usize) -> Option<Local> {
        if let Some(edge_idx) = self.nodes[node_idx].out_edges.get(order) {
            Some(self.edges[*edge_idx].dst)
        } else {
            None
        }
    }

    pub fn is_connected(&self, idx_1: Local, idx_2: Local) -> bool {
        let target = idx_2;
        let find = Cell::new(false);
        let mut node_operator = |_: &DataflowGraph, idx: Local| -> DFSStatus {
            find.set(idx == target);
            if find.get() {
                DFSStatus::Stop
            } else {
                DFSStatus::Continue
            }
        };
        let mut seen = HashSet::new();
        self.dfs(
            idx_1,
            Direction::Downside,
            &mut node_operator,
            &mut Self::always_true_edge_validator,
            false,
            &mut seen,
        );
        seen.clear();
        if !find.get() {
            self.dfs(
                idx_1,
                Direction::Upside,
                &mut node_operator,
                &mut Self::always_true_edge_validator,
                false,
                &mut seen,
            );
        }
        find.get()
    }

    pub fn param_return_deps(&self) -> IndexVec<Local, bool> {
        let _0 = Local::from_usize(0);
        let deps = (0..self.argc + 1)
            .map(|i| {
                let _i = Local::from_usize(i);
                self.is_connected(_i, _0)
            })
            .collect();
        deps
    }

    pub fn dfs<F, G>(
        &self,
        now: Local,
        direction: Direction,
        node_operator: &mut F,
        edge_validator: &mut G,
        traverse_all: bool,
        seen: &mut HashSet<Local>,
    ) -> (DFSStatus, bool)
    where
        F: FnMut(&DataflowGraph, Local) -> DFSStatus,
        G: FnMut(&DataflowGraph, EdgeIdx) -> DFSStatus,
    {
        if seen.contains(&now) {
            return (DFSStatus::Stop, false);
        }
        seen.insert(now);
        macro_rules! traverse {
            ($edges: ident, $field: ident) => {
                for edge_idx in self.nodes[now].$edges.iter() {
                    let edge = &self.edges[*edge_idx];
                    if matches!(edge_validator(self, *edge_idx), DFSStatus::Continue) {
                        let (dfs_status, result) = self.dfs(
                            edge.$field,
                            direction,
                            node_operator,
                            edge_validator,
                            traverse_all,
                            seen,
                        );
                        if matches!(dfs_status, DFSStatus::Stop) && result && !traverse_all {
                            return (DFSStatus::Stop, true);
                        }
                    }
                }
            };
        }
        if matches!(node_operator(self, now), DFSStatus::Continue) {
            match direction {
                Direction::Upside => {
                    traverse!(in_edges, src);
                }
                Direction::Downside => {
                    traverse!(out_edges, dst);
                }
                Direction::Both => {
                    traverse!(in_edges, src);
                    traverse!(out_edges, dst);
                }
            };
            (DFSStatus::Continue, false)
        } else {
            (DFSStatus::Stop, true)
        }
    }

    pub fn equivalent_edge_validator(graph: &DataflowGraph, idx: EdgeIdx) -> DFSStatus {
        match graph.edges[idx].op {
            EdgeOp::Copy | EdgeOp::Move | EdgeOp::Mut | EdgeOp::Immut | EdgeOp::Deref => {
                DFSStatus::Continue
            }
            EdgeOp::Nop
            | EdgeOp::Const
            | EdgeOp::Downcast(_)
            | EdgeOp::Field(_)
            | EdgeOp::Index
            | EdgeOp::ConstIndex
            | EdgeOp::SubSlice => DFSStatus::Stop,
        }
    }

    pub fn always_true_edge_validator(_: &DataflowGraph, _: EdgeIdx) -> DFSStatus {
        DFSStatus::Continue
    }

    pub fn collect_equivalent_locals(&self, local: Local, strict: bool) -> HashSet<Local> {
        let mut set = HashSet::new();
        let root = Cell::new(local);
        let reduce_func = if strict {
            DFSStatus::and
        } else {
            DFSStatus::or
        };
        let mut find_root_operator = |graph: &DataflowGraph, idx: Local| -> DFSStatus {
            let node = &graph.nodes[idx];
            node.ops
                .iter()
                .map(|op| match op {
                    NodeOp::Nop | NodeOp::Use | NodeOp::Ref => {
                        root.set(idx);
                        DFSStatus::Continue
                    }
                    NodeOp::Call(_) => {
                        root.set(idx);
                        DFSStatus::Stop
                    }
                    _ => DFSStatus::Stop,
                })
                .reduce(reduce_func)
                .unwrap()
        };
        let mut find_equivalent_operator = |graph: &DataflowGraph, idx: Local| -> DFSStatus {
            let node = &graph.nodes[idx];
            if set.contains(&idx) {
                return DFSStatus::Stop;
            }
            node.ops
                .iter()
                .map(|op| match op {
                    NodeOp::Nop | NodeOp::Use | NodeOp::Ref => {
                        set.insert(idx);
                        DFSStatus::Continue
                    }
                    NodeOp::Call(_) => {
                        if idx == root.get() {
                            set.insert(idx);
                            DFSStatus::Continue
                        } else {
                            DFSStatus::Stop
                        }
                    }
                    _ => DFSStatus::Stop,
                })
                .reduce(reduce_func)
                .unwrap()
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Upside,
            &mut find_root_operator,
            &mut Self::equivalent_edge_validator,
            true,
            &mut seen,
        );
        seen.clear();
        self.dfs(
            root.get(),
            Direction::Downside,
            &mut find_equivalent_operator,
            &mut Self::equivalent_edge_validator,
            true,
            &mut seen,
        );
        set
    }

    pub fn collect_ancestor_locals(&self, local: Local, self_included: bool) -> HashSet<Local> {
        let mut ret = HashSet::new();
        let mut node_operator = |_: &DataflowGraph, idx: Local| -> DFSStatus {
            ret.insert(idx);
            DFSStatus::Continue
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Upside,
            &mut node_operator,
            &mut DataflowGraph::always_true_edge_validator,
            true,
            &mut seen,
        );
        if !self_included {
            ret.remove(&local);
        }
        ret
    }

    pub fn collect_descending_locals(&self, local: Local, self_included: bool) -> HashSet<Local> {
        let mut ret = HashSet::new();
        let mut node_operator = |_: &DataflowGraph, idx: Local| -> DFSStatus {
            ret.insert(idx);
            DFSStatus::Continue
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Downside,
            &mut node_operator,
            &mut DataflowGraph::always_true_edge_validator,
            true,
            &mut seen,
        );
        if !self_included {
            ret.remove(&local);
        }
        ret
    }

    pub fn get_field_sequence(&self, local: Local) -> Option<(Local, Vec<usize>)> {
        let mut fields = vec![];
        let var = Cell::new(local);
        let mut node_operator = |graph: &DataflowGraph, idx: Local| -> DFSStatus {
            if graph.is_marker(idx) {
                DFSStatus::Continue
            } else {
                var.set(idx);
                DFSStatus::Stop
            }
        };
        let mut edge_validator = |graph: &DataflowGraph, idx: EdgeIdx| -> DFSStatus {
            if let EdgeOp::Field(field) = graph.edges[idx].op {
                fields.insert(0, field);
                DFSStatus::Continue
            } else {
                DFSStatus::Stop
            }
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Upside,
            &mut node_operator,
            &mut edge_validator,
            false,
            &mut seen,
        );
        if fields.is_empty() {
            None
        } else {
            Some((var.get(), fields))
        }
    }
}

#[derive(Clone, Copy)]
pub enum Direction {
    Upside,
    Downside,
    Both,
}

pub enum DFSStatus {
    Continue,
    Stop,
}

impl DFSStatus {
    pub fn and(s1: DFSStatus, s2: DFSStatus) -> DFSStatus {
        if matches!(s1, DFSStatus::Stop) || matches!(s2, DFSStatus::Stop) {
            DFSStatus::Stop
        } else {
            DFSStatus::Continue
        }
    }

    pub fn or(s1: DFSStatus, s2: DFSStatus) -> DFSStatus {
        if matches!(s1, DFSStatus::Continue) || matches!(s2, DFSStatus::Continue) {
            DFSStatus::Continue
        } else {
            DFSStatus::Stop
        }
    }
}
