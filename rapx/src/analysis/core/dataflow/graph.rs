use std::cell::Cell;
use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{
        AggregateKind, BorrowKind, Const, Local, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::TyKind,
};
use rustc_span::{DUMMY_SP, Span};

use crate::{analysis::core::dataflow::*, utils::log::relative_pos_range};

impl GraphNode {
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
pub struct Graph {
    pub def_id: DefId,
    pub span: Span,
    pub argc: usize,
    pub nodes: GraphNodes, //constsis of locals in mir and newly created markers
    pub edges: GraphEdges,
    pub n_locals: usize,
    pub closures: HashSet<DefId>,
}

impl From<Graph> for DataFlowGraph {
    fn from(graph: Graph) -> Self {
        let param_ret_deps = graph.param_return_deps();
        DataFlowGraph {
            nodes: graph.nodes,
            edges: graph.edges,
            param_ret_deps: param_ret_deps,
        }
    }
}

impl Graph {
    pub fn new(def_id: DefId, span: Span, argc: usize, n_locals: usize) -> Self {
        Self {
            def_id,
            span,
            argc,
            nodes: GraphNodes::from_elem_n(GraphNode::new(), n_locals),
            edges: GraphEdges::new(),
            n_locals,
            closures: HashSet::new(),
        }
    }

    // add an edge into an existing node
    pub fn add_node_edge(&mut self, src: Local, dst: Local, op: EdgeOp) -> EdgeIdx {
        let seq = self.nodes[dst].seq;
        let edge_idx = self.edges.push(GraphEdge { src, dst, op, seq });
        self.nodes[dst].in_edges.push(edge_idx);
        self.nodes[src].out_edges.push(edge_idx);
        edge_idx
    }

    // add an edge into an existing node with const value as src
    pub fn add_const_edge(
        &mut self,
        src_desc: String,
        src_ty: String,
        dst: Local,
        op: EdgeOp,
    ) -> EdgeIdx {
        let seq = self.nodes[dst].seq;
        let mut const_node = GraphNode::new();
        const_node.ops[0] = NodeOp::Const(src_desc, src_ty);
        let src = self.nodes.push(const_node);
        let edge_idx = self.edges.push(GraphEdge { src, dst, op, seq });
        self.nodes[dst].in_edges.push(edge_idx);
        edge_idx
    }

    pub fn add_operand(&mut self, operand: &Operand, dst: Local) {
        match operand {
            Operand::Copy(place) => {
                let src = self.parse_place(place);
                self.add_node_edge(src, dst, EdgeOp::Copy);
            }
            Operand::Move(place) => {
                let src = self.parse_place(place);
                self.add_node_edge(src, dst, EdgeOp::Move);
            }
            Operand::Constant(boxed_const_op) => {
                let src_desc = boxed_const_op.const_.to_string();
                let src_ty = match boxed_const_op.const_ {
                    Const::Val(_, ty) => ty.to_string(),
                    Const::Unevaluated(_, ty) => ty.to_string(),
                    Const::Ty(ty, _) => ty.to_string(),
                };
                self.add_const_edge(src_desc, src_ty, dst, EdgeOp::Const);
            }
        }
    }

    pub fn parse_place(&mut self, place: &Place) -> Local {
        fn parse_one_step(graph: &mut Graph, src: Local, place_elem: PlaceElem) -> Local {
            let dst = graph.nodes.push(GraphNode::new());
            match place_elem {
                PlaceElem::Deref => {
                    graph.add_node_edge(src, dst, EdgeOp::Deref);
                }
                PlaceElem::Field(field_idx, _) => {
                    graph.add_node_edge(src, dst, EdgeOp::Field(field_idx.as_usize()));
                }
                PlaceElem::Downcast(symbol, _) => {
                    graph.add_node_edge(src, dst, EdgeOp::Downcast(symbol.unwrap().to_string()));
                }
                PlaceElem::Index(idx) => {
                    graph.add_node_edge(src, dst, EdgeOp::Index);
                    graph.add_node_edge(idx, dst, EdgeOp::Nop);
                }
                PlaceElem::ConstantIndex { .. } => {
                    graph.add_node_edge(src, dst, EdgeOp::ConstIndex);
                }
                PlaceElem::Subslice { .. } => {
                    graph.add_node_edge(src, dst, EdgeOp::SubSlice);
                }
                _ => {
                    println!("{:?}", place_elem);
                    todo!()
                }
            }
            dst
        }
        let mut ret = place.local;
        for place_elem in place.projection {
            // if there are projections, then add marker nodes
            ret = parse_one_step(self, ret, place_elem);
        }
        ret
    }

    pub fn add_statm_to_graph(&mut self, statement: &Statement) {
        if let StatementKind::Assign(boxed_statm) = &statement.kind {
            let place = boxed_statm.0;
            let dst = self.parse_place(&place);
            self.nodes[dst].span = statement.source_info.span;
            let rvalue = &boxed_statm.1;
            let seq = self.nodes[dst].seq;
            if seq == self.nodes[dst].ops.len() {
                //warning: we do not check whether seq > len
                self.nodes[dst].ops.push(NodeOp::Nop);
            }
            match rvalue {
                Rvalue::Use(op) => {
                    self.add_operand(op, dst);
                    self.nodes[dst].ops[seq] = NodeOp::Use;
                }
                Rvalue::Repeat(op, _) => {
                    self.add_operand(op, dst);
                    self.nodes[dst].ops[seq] = NodeOp::Repeat;
                }
                Rvalue::Ref(_, borrow_kind, place) => {
                    let op = match borrow_kind {
                        BorrowKind::Shared => EdgeOp::Immut,
                        BorrowKind::Mut { .. } => EdgeOp::Mut,
                        BorrowKind::Fake(_) => EdgeOp::Nop, // todo
                    };
                    let src = self.parse_place(place);
                    self.add_node_edge(src, dst, op);
                    self.nodes[dst].ops[seq] = NodeOp::Ref;
                }
                Rvalue::Cast(_cast_kind, operand, _) => {
                    self.add_operand(operand, dst);
                    self.nodes[dst].ops[seq] = NodeOp::Cast;
                }
                Rvalue::BinaryOp(_, operands) => {
                    self.add_operand(&operands.0, dst);
                    self.add_operand(&operands.1, dst);
                    self.nodes[dst].ops[seq] = NodeOp::CheckedBinaryOp;
                }
                Rvalue::Aggregate(boxed_kind, operands) => {
                    for operand in operands.iter() {
                        self.add_operand(operand, dst);
                    }
                    match **boxed_kind {
                        AggregateKind::Array(_) => {
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::Array)
                        }
                        AggregateKind::Tuple => {
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::Tuple)
                        }
                        AggregateKind::Adt(def_id, ..) => {
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::Adt(def_id))
                        }
                        AggregateKind::Closure(def_id, ..) => {
                            self.closures.insert(def_id);
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::Closure(def_id))
                        }
                        AggregateKind::Coroutine(def_id, ..) => {
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::Coroutine(def_id))
                        }
                        AggregateKind::RawPtr(_, _mutability) => {
                            self.nodes[dst].ops[seq] = NodeOp::Aggregate(AggKind::RawPtr)
                            // We temporarily have not taken mutability into account
                        }
                        _ => {
                            println!("{:?}", boxed_kind);
                            todo!()
                        }
                    }
                }
                Rvalue::UnaryOp(_, operand) => {
                    self.add_operand(operand, dst);
                    self.nodes[dst].ops[seq] = NodeOp::UnaryOp;
                }
                Rvalue::NullaryOp(..) => {
                    self.nodes[dst].ops[seq] = NodeOp::NullaryOp;
                }
                Rvalue::ThreadLocalRef(_) => {
                    //todo!()
                }
                Rvalue::Discriminant(place) => {
                    let src = self.parse_place(place);
                    self.add_node_edge(src, dst, EdgeOp::Nop);
                    self.nodes[dst].ops[seq] = NodeOp::Discriminant;
                }
                Rvalue::ShallowInitBox(operand, _) => {
                    self.add_operand(operand, dst);
                    self.nodes[dst].ops[seq] = NodeOp::ShallowInitBox;
                }
                Rvalue::CopyForDeref(place) => {
                    let src = self.parse_place(place);
                    self.add_node_edge(src, dst, EdgeOp::Nop);
                    self.nodes[dst].ops[seq] = NodeOp::CopyForDeref;
                }
                Rvalue::RawPtr(_, place) => {
                    let src = self.parse_place(place);
                    self.add_node_edge(src, dst, EdgeOp::Nop); // Mutability?
                    self.nodes[dst].ops[seq] = NodeOp::RawPtr;
                }
                _ => todo!(),
            };
            self.nodes[dst].seq = seq + 1;
        }
    }

    pub fn add_terminator_to_graph(&mut self, terminator: &Terminator) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            let dst = destination.local;
            let seq = self.nodes[dst].seq;
            if seq == self.nodes[dst].ops.len() {
                self.nodes[dst].ops.push(NodeOp::Nop);
            }
            match func {
                Operand::Constant(boxed_cnst) => {
                    if let Const::Val(_, ty) = boxed_cnst.const_ {
                        if let TyKind::FnDef(def_id, _) = ty.kind() {
                            for op in args.iter() {
                                //rustc version related
                                self.add_operand(&op.node, dst);
                            }
                            self.nodes[dst].ops[seq] = NodeOp::Call(*def_id);
                        }
                    }
                }
                Operand::Move(_) => {
                    self.add_operand(func, dst); //the func is a place
                    for op in args.iter() {
                        //rustc version related
                        self.add_operand(&op.node, dst);
                    }
                    self.nodes[dst].ops[seq] = NodeOp::CallOperand;
                }
                _ => {
                    println!("{:?}", func);
                    todo!();
                }
            }
            self.nodes[dst].span = terminator.source_info.span;
            self.nodes[dst].seq = seq + 1;
        }
    }

    // Because a node(local) may have multiple ops, we need to decide whether to strictly collect equivalent locals or not
    // For the former, all the ops should meet the equivalent condition.
    // For the later, if only one op meets the condition, we still take it into consideration.
    pub fn collect_equivalent_locals(&self, local: Local, strict: bool) -> HashSet<Local> {
        let mut set = HashSet::new();
        let root = Cell::new(local);
        let reduce_func = if strict {
            DFSStatus::and
        } else {
            DFSStatus::or
        };
        let mut find_root_operator = |graph: &Graph, idx: Local| -> DFSStatus {
            let node = &graph.nodes[idx];
            node.ops
                .iter()
                .map(|op| {
                    match op {
                        NodeOp::Nop | NodeOp::Use | NodeOp::Ref => {
                            //Nop means an orphan node or a parameter
                            root.set(idx);
                            DFSStatus::Continue
                        }
                        NodeOp::Call(_) => {
                            //We are moving towards upside. Thus we can record the call node and stop dfs.
                            //We stop because the return value does not equal to parameters
                            root.set(idx);
                            DFSStatus::Stop
                        }
                        _ => DFSStatus::Stop,
                    }
                })
                .reduce(reduce_func)
                .unwrap()
        };
        let mut find_equivalent_operator = |graph: &Graph, idx: Local| -> DFSStatus {
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
                            // We are moving towards downside. Thus we stop dfs right now.
                            DFSStatus::Stop
                        }
                    }
                    _ => DFSStatus::Stop,
                })
                .reduce(reduce_func)
                .unwrap()
        };
        // Algorithm: dfs along upside to find the root node, and then dfs along downside to collect equivalent locals
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
        let mut node_operator = |_: &Graph, idx: Local| -> DFSStatus {
            ret.insert(idx);
            DFSStatus::Continue
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Upside,
            &mut node_operator,
            &mut Graph::always_true_edge_validator,
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
        let mut node_operator = |_: &Graph, idx: Local| -> DFSStatus {
            ret.insert(idx);
            DFSStatus::Continue
        };
        let mut seen = HashSet::new();
        self.dfs(
            local,
            Direction::Downside,
            &mut node_operator,
            &mut Graph::always_true_edge_validator,
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
        let mut node_operator = |graph: &Graph, idx: Local| -> DFSStatus {
            if graph.is_marker(idx) {
                DFSStatus::Continue
            } else {
                var.set(idx);
                DFSStatus::Stop
            }
        };
        let mut edge_validator = |graph: &Graph, idx: EdgeIdx| -> DFSStatus {
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

    pub fn is_connected(&self, idx_1: Local, idx_2: Local) -> bool {
        let target = idx_2;
        let find = Cell::new(false);
        let mut node_operator = |_: &Graph, idx: Local| -> DFSStatus {
            find.set(idx == target);
            if find.get() {
                DFSStatus::Stop
            } else {
                // if not found, move on
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

    // Whether there exists dataflow between each parameter and the return value
    pub fn param_return_deps(&self) -> IndexVec<Local, bool> {
        let _0 = Local::from_usize(0);
        let deps = (0..self.argc + 1) //the length is argc + 1, because _0 depends on _0 itself.
            .map(|i| {
                let _i = Local::from_usize(i);
                self.is_connected(_i, _0)
            })
            .collect();
        deps
    }

    // This function uses precedence traversal.
    // The node operator and edge validator decide how far the traversal can reach.
    // `traverse_all` decides if a branch finds the target successfully, whether the traversal will continue or not.
    // For example, if you need to instantly stop the traversal once finding a certain node, then set `traverse_all` to false.
    // If you want to traverse all the reachable nodes which are decided by the operator and validator, then set `traverse_all` to true.
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
        F: FnMut(&Graph, Local) -> DFSStatus,
        G: FnMut(&Graph, EdgeIdx) -> DFSStatus,
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

    // if strict is set to false, we return the first node that wraps the target span and at least one end overlaps
    pub fn query_node_by_span(&self, span: Span, strict: bool) -> Option<(Local, &GraphNode)> {
        for (node_idx, node) in self.nodes.iter_enumerated() {
            if strict {
                if node.span == span {
                    return Some((node_idx, node));
                }
            } else {
                if !relative_pos_range(node.span, span).eq(0..0)
                    && (node.span.lo() == span.lo() || node.span.hi() == span.hi())
                {
                    return Some((node_idx, node));
                }
            }
        }
        None
    }

    pub fn is_marker(&self, idx: Local) -> bool {
        idx >= Local::from_usize(self.n_locals)
    }
}

impl Graph {
    pub fn equivalent_edge_validator(graph: &Graph, idx: EdgeIdx) -> DFSStatus {
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

    pub fn always_true_edge_validator(_: &Graph, _: EdgeIdx) -> DFSStatus {
        DFSStatus::Continue
    }
}

#[derive(Clone, Copy)]
pub enum Direction {
    Upside,
    Downside,
    Both,
}

pub enum DFSStatus {
    Continue, // true
    Stop,     // false
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
