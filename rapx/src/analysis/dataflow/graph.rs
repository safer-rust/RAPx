use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        AggregateKind, BorrowKind, Const, Local, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;

use super::types::*;

/// Build a `DataflowGraph` for a single function identified by `def_id`.
pub fn build_dataflow_graph(tcx: TyCtxt<'_>, def_id: DefId) -> DataflowGraph {
    let body = tcx.optimized_mir(def_id);
    build_dataflow_graph_from_body(def_id, body)
}

/// Build a `DataflowGraph` from a pre-existing MIR body (e.g. after SSA transformation).
pub fn build_dataflow_graph_from_body(
    def_id: DefId,
    body: &rustc_middle::mir::Body<'_>,
) -> DataflowGraph {
    let mut graph = DataflowGraph::new(def_id, body.span, body.arg_count, body.local_decls.len());
    for (block_idx, bb) in body.basic_blocks.iter().enumerate() {
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            graph.add_statm_to_graph(&stmt, block_idx, stmt_idx);
        }
        if let Some(terminator) = &bb.terminator {
            let stmt_idx = bb.statements.len();
            graph.add_terminator_to_graph(&terminator, block_idx, stmt_idx);
        }
    }
    graph
}

impl DataflowGraph {
    pub fn add_operand(&mut self, operand: &Operand, dst: Local, block: usize, stmt_idx: usize) {
        match operand {
            Operand::Copy(place) => {
                let src = self.parse_place(place, block, stmt_idx);
                self.add_node_edge(src, dst, EdgeOp::Copy, block, stmt_idx);
            }
            Operand::Move(place) => {
                let src = self.parse_place(place, block, stmt_idx);
                self.add_node_edge(src, dst, EdgeOp::Move, block, stmt_idx);
            }
            Operand::Constant(boxed_const_op) => {
                let src_desc = boxed_const_op.const_.to_string();
                let src_ty = match boxed_const_op.const_ {
                    Const::Val(_, ty) => ty.to_string(),
                    Const::Unevaluated(_, ty) => ty.to_string(),
                    Const::Ty(ty, _) => ty.to_string(),
                };
                self.add_const_edge(src_desc, src_ty, dst, EdgeOp::Const, block, stmt_idx);
            }
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => {}
        }
    }

    pub fn parse_place(&mut self, place: &Place, block: usize, stmt_idx: usize) -> Local {
        fn parse_one_step(
            graph: &mut DataflowGraph,
            src: Local,
            place_elem: PlaceElem,
            block: usize,
            stmt_idx: usize,
        ) -> Local {
            let dst = graph.nodes.push(DataflowNode::new());
            match place_elem {
                PlaceElem::Deref => {
                    graph.add_node_edge(src, dst, EdgeOp::Deref, block, stmt_idx);
                }
                PlaceElem::Field(field_idx, _) => {
                    graph.add_node_edge(src, dst, EdgeOp::Field(field_idx.as_usize()), block, stmt_idx);
                }
                PlaceElem::Downcast(symbol, _) => {
                    graph.add_node_edge(src, dst, EdgeOp::Downcast(symbol.unwrap().to_string()), block, stmt_idx);
                }
                PlaceElem::Index(idx) => {
                    graph.add_node_edge(src, dst, EdgeOp::Index, block, stmt_idx);
                    graph.add_node_edge(idx, dst, EdgeOp::Nop, block, stmt_idx);
                }
                PlaceElem::ConstantIndex { .. } => {
                    graph.add_node_edge(src, dst, EdgeOp::ConstIndex, block, stmt_idx);
                }
                PlaceElem::Subslice { .. } => {
                    graph.add_node_edge(src, dst, EdgeOp::SubSlice, block, stmt_idx);
                }
                _ => {
                    rap_debug!("{:?}", place_elem);
                    todo!()
                }
            }
            dst
        }
        let mut ret = place.local;
        for place_elem in place.projection {
            ret = parse_one_step(self, ret, place_elem, block, stmt_idx);
        }
        ret
    }

    pub fn add_statm_to_graph(&mut self, statement: &Statement, block: usize, stmt_idx: usize) {
        if let StatementKind::Assign(boxed_statm) = &statement.kind {
            let place = boxed_statm.0;
            let dst = self.parse_place(&place, block, stmt_idx);
            self.nodes[dst].span = statement.source_info.span;
            let rvalue = &boxed_statm.1;
            let seq = self.nodes[dst].seq;
            if seq == self.nodes[dst].ops.len() {
                self.nodes[dst].ops.push(NodeOp::Nop);
            }
            match rvalue {
                Rvalue::Use(op, ..) => {
                    self.add_operand(op, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::Use;
                }
                Rvalue::Repeat(op, _) => {
                    self.add_operand(op, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::Repeat;
                }
                Rvalue::Ref(_, borrow_kind, place) => {
                    let op = match borrow_kind {
                        BorrowKind::Shared => EdgeOp::Immut,
                        BorrowKind::Mut { .. } => EdgeOp::Mut,
                        BorrowKind::Fake(_) => EdgeOp::Nop,
                    };
                    let src = self.parse_place(place, block, stmt_idx);
                    self.add_node_edge(src, dst, op, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::Ref;
                }
                Rvalue::Cast(_cast_kind, operand, _) => {
                    self.add_operand(operand, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::Cast;
                }
                Rvalue::BinaryOp(_, operands) => {
                    self.add_operand(&operands.0, dst, block, stmt_idx);
                    self.add_operand(&operands.1, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::CheckedBinaryOp;
                }
                Rvalue::Aggregate(boxed_kind, operands) => {
                    for operand in operands.iter() {
                        self.add_operand(operand, dst, block, stmt_idx);
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
                        }
                        _ => {
                            rap_debug!("{:?}", boxed_kind);
                            todo!()
                        }
                    }
                }
                Rvalue::UnaryOp(_, operand) => {
                    self.add_operand(operand, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::UnaryOp;
                }
                #[cfg(all(rapx_rustc_ge_193, not(rapx_rustc_ge_196)))]
                Rvalue::NullaryOp(_) => {
                    self.nodes[dst].ops[seq] = NodeOp::NullaryOp;
                }
                #[cfg(all(not(rapx_rustc_ge_193), not(rapx_rustc_ge_196)))]
                Rvalue::NullaryOp(_, _) => {
                    self.nodes[dst].ops[seq] = NodeOp::NullaryOp;
                }
                Rvalue::ThreadLocalRef(_) => {}
                Rvalue::Discriminant(place) => {
                    let src = self.parse_place(place, block, stmt_idx);
                    self.add_node_edge(src, dst, EdgeOp::Nop, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::Discriminant;
                }
                #[cfg(not(rapx_rustc_ge_196))]
                Rvalue::ShallowInitBox(operand, _) => {
                    self.add_operand(operand, dst, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::ShallowInitBox;
                }
                Rvalue::CopyForDeref(place) => {
                    let src = self.parse_place(place, block, stmt_idx);
                    self.add_node_edge(src, dst, EdgeOp::Nop, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::CopyForDeref;
                }
                Rvalue::RawPtr(_, place) => {
                    let src = self.parse_place(place, block, stmt_idx);
                    self.add_node_edge(src, dst, EdgeOp::Nop, block, stmt_idx);
                    self.nodes[dst].ops[seq] = NodeOp::RawPtr;
                }
                _ => todo!(),
            };
            self.nodes[dst].seq = seq + 1;
        }
    }

    pub fn add_terminator_to_graph(
        &mut self,
        terminator: &Terminator,
        block: usize,
        stmt_idx: usize,
    ) {
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
                                self.add_operand(&op.node, dst, block, stmt_idx);
                            }
                            self.nodes[dst].ops[seq] = NodeOp::Call(*def_id);
                        }
                    }
                }
                Operand::Move(_) => {
                    self.add_operand(func, dst, block, stmt_idx);
                    for op in args.iter() {
                        self.add_operand(&op.node, dst, block, stmt_idx);
                    }
                    self.nodes[dst].ops[seq] = NodeOp::CallOperand;
                }
                _ => {
                    rap_debug!("{:?}", func);
                    todo!();
                }
            }
            self.nodes[dst].span = terminator.source_info.span;
            self.nodes[dst].seq = seq + 1;
        }
    }

    pub fn query_node_by_span(&self, span: Span, strict: bool) -> Option<(Local, &DataflowNode)> {
        for (node_idx, node) in self.nodes.iter_enumerated() {
            if strict {
                if node.span == span {
                    return Some((node_idx, node));
                }
            } else {
                if !crate::utils::span::relative_pos_range(node.span, span).eq(0..0)
                    && (node.span.lo() == span.lo() || node.span.hi() == span.hi())
                {
                    return Some((node_idx, node));
                }
            }
        }
        None
    }
}
