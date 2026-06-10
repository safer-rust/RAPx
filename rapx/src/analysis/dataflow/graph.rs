use rustc_middle::{
    mir::{
        AggregateKind, BorrowKind, Const, Local, Operand, Place, PlaceElem, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use crate::graphs::dataflow::*;

/// Build a `DataflowGraph` for a single function identified by `def_id`.
pub fn build_dataflow_graph(tcx: TyCtxt<'_>, def_id: DefId) -> DataflowGraph {
    let body = tcx.optimized_mir(def_id);
    let mut graph =
        DataflowGraph::new(def_id, body.span, body.arg_count, body.local_decls.len());
    for (block_idx, bb) in body.basic_blocks.iter().enumerate() {
        graph.block = block_idx;
        for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
            graph.statement_index = stmt_idx;
            graph.add_statm_to_graph(&stmt);
        }
        if let Some(terminator) = &bb.terminator {
            graph.statement_index = bb.statements.len();
            graph.add_terminator_to_graph(&terminator);
        }
    }
    graph
}

impl DataflowGraph {
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
        fn parse_one_step(graph: &mut DataflowGraph, src: Local, place_elem: PlaceElem) -> Local {
            let dst = graph.nodes.push(DataflowNode::new());
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
                        BorrowKind::Fake(_) => EdgeOp::Nop,
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
                Rvalue::NullaryOp(_) => {
                    self.nodes[dst].ops[seq] = NodeOp::NullaryOp;
                }
                Rvalue::ThreadLocalRef(_) => {}
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
                    self.add_node_edge(src, dst, EdgeOp::Nop);
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
                                self.add_operand(&op.node, dst);
                            }
                            self.nodes[dst].ops[seq] = NodeOp::Call(*def_id);
                        }
                    }
                }
                Operand::Move(_) => {
                    self.add_operand(func, dst);
                    for op in args.iter() {
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

    pub fn query_node_by_span(&self, span: Span, strict: bool) -> Option<(Local, &DataflowNode)> {
        for (node_idx, node) in self.nodes.iter_enumerated() {
            if strict {
                if node.span == span {
                    return Some((node_idx, node));
                }
            } else {
                if !crate::utils::log::relative_pos_range(node.span, span).eq(0..0)
                    && (node.span.lo() == span.lo() || node.span.hi() == span.hi())
                {
                    return Some((node_idx, node));
                }
            }
        }
        None
    }
}
