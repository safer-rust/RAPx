
use crate::analysis::range_analysis::domain::domain::*;
use crate::analysis::range_analysis::{Range, RangeType};

use crate::analysis::range_analysis::domain::symbolic_expr::*;
use crate::compat::Spanned;
use rustc_abi::FieldIdx;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::*,
    ty::{self},
};

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
};

use super::ConstraintGraph;

impl<'tcx, T> ConstraintGraph<'tcx, T>
where
    T: IntervalArithmetic + ConstConvert + Debug,
{
    fn register_op(&mut self, op: BasicOpKind<'tcx, T>, sink: &'tcx Place<'tcx>) -> usize {
        let idx = self.oprs.len();
        self.oprs.push(op);
        self.defmap.insert(sink, idx);
        idx
    }

    pub fn add_varnode(&mut self, v: &'tcx Place<'tcx>) -> &mut VarNode<'tcx, T> {
        let local_decls = &self.body.local_decls;

        let node = VarNode::new(v);
        let node_ref: &mut VarNode<'tcx, T> = self
            .vars
            .entry(v)
            .or_insert(node);
        self.usemap.entry(v).or_insert(HashSet::new());

        let ty = local_decls[v.local].ty;
        let place_ty = v.ty(local_decls, self.tcx);

        if v.projection.is_empty() || self.defmap.contains_key(v) {
            return node_ref;
        }

        if !v.projection.is_empty() {
            let matches: Vec<(_, _)> = self
                .defmap
                .iter()
                .filter(|(p, _)| p.local == v.local && p.projection.is_empty())
                .map(|(p, def_op)| (*p, *def_op))
                .collect();

            for (base_place, def_op) in matches {
                let mut v_op = self.oprs[def_op].clone();
                v_op.set_sink(v);

                for source in v_op.get_sources() {
                    self.usemap
                        .entry(source)
                        .or_insert(HashSet::new())
                        .insert(self.oprs.len());
                }

                self.oprs.push(v_op);
                self.defmap.insert(v, self.oprs.len() - 1);
            }
        }

        node_ref
    }

    pub fn use_add_varnode_sym(
        &mut self,
        v: &'tcx Place<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
    ) -> &mut VarNode<'tcx, T> {
        if !self.vars.contains_key(v) {
            let place_ctx: Vec<&Place<'tcx>> = self.vars.keys().map(|p| *p).collect();
            let node = VarNode::new_symb(v, SymbExpr::from_rvalue(rvalue, place_ctx.clone()));
            rap_debug!("use node:{:?}", node);

            self.vars.insert(v, node);
            self.usemap.entry(v).or_insert(HashSet::new());

            if !(v.projection.is_empty() || self.defmap.contains_key(v)) {
                let matches: Vec<_> = self
                    .defmap
                    .iter()
                    .filter(|(p, _)| p.local == v.local && p.projection.is_empty())
                    .map(|(p, &def_op)| (*p, def_op))
                    .collect();

                for (base_place, def_op) in matches {
                    let mut v_op = self.oprs[def_op].clone();
                    v_op.set_sink(v);

                    for source in v_op.get_sources() {
                        self.usemap
                            .entry(source)
                            .or_insert(HashSet::new())
                            .insert(self.oprs.len());
                    }

                    self.oprs.push(v_op);
                    self.defmap.insert(v, self.oprs.len() - 1);
                }
            }
        }

        self.vars.get_mut(v).unwrap()
    }

    pub fn def_add_varnode_sym(
        &mut self,
        v: &'tcx Place<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
    ) -> &mut VarNode<'tcx, T> {
        let place_ctx: Vec<&Place<'tcx>> = self.vars.keys().map(|p| *p).collect();

        let local_decls = &self.body.local_decls;
        let node = VarNode::new_symb(v, SymbExpr::from_rvalue(rvalue, place_ctx.clone()));
        rap_debug!("def node:{:?}", node);
        let node_ref: &mut VarNode<'tcx, T> = self
            .vars
            .entry(v)
            .and_modify(|old| *old = node.clone())
            .or_insert(node);
        self.usemap.entry(v).or_insert(HashSet::new());

        let ty = local_decls[v.local].ty;
        let place_ty = v.ty(local_decls, self.tcx);

        if v.projection.is_empty() || self.defmap.contains_key(v) {
            return node_ref;
        }

        if !v.projection.is_empty() {
            let matches: Vec<(_, _)> = self
                .defmap
                .iter()
                .filter(|(p, _)| p.local == v.local && p.projection.is_empty())
                .map(|(p, &def_op)| (*p, def_op))
                .collect();

            for (base_place, def_op) in matches {
                let mut v_op = self.oprs[def_op].clone();
                v_op.set_sink(v);

                for source in v_op.get_sources() {
                    self.usemap
                        .entry(source)
                        .or_insert(HashSet::new())
                        .insert(self.oprs.len());
                }

                self.oprs.push(v_op);
                self.defmap.insert(v, self.oprs.len() - 1);
            }
        }
        node_ref
    }

    pub fn resolve_all_symexpr(&mut self) {
        let lookup_context = self.vars.clone();
        let mut nodes: Vec<&mut VarNode<'tcx, T>> = self.vars.values_mut().collect();
        nodes.sort_by(|a, b| a.v.local.as_usize().cmp(&b.v.local.as_usize()));
        for node in nodes {
            if let IntervalType::Basic(basic) = &mut node.interval {
                rap_debug!("======{}=====", node.v.local.as_usize());
                rap_debug!("Before resolve: lower_expr: {}\n", basic.lower);
                basic.lower.resolve_lower_bound(&lookup_context);
                basic.lower.simplify();
                rap_debug!("After resolve: lower_expr: {}\n", basic.lower);
                rap_debug!("Before resolve: upper_expr: {}\n", basic.upper);
                basic.upper.resolve_upper_bound(&lookup_context);
                basic.upper.simplify();

                rap_debug!("After resolve: upper_expr: {}\n", basic.upper);
            }
        }
    }

    pub fn postprocess_defmap(&mut self) {
        for place in self.vars.keys() {
            if !place.projection.is_empty() {
                if let Some((&base_place, &base_value)) = self
                    .defmap
                    .iter()
                    .find(|(p, _)| p.local == place.local && p.projection.is_empty())
                {
                    self.defmap.insert(place, base_value);
                } else {
                    rap_trace!("postprocess_defmap: No base place found for {:?}", place);
                }
            }
        }
    }

    pub fn build_graph(&mut self, body: &'tcx Body<'tcx>) {
        self.build_value_maps(body);
        for block in body.basic_blocks.indices() {
            let block_data: &BasicBlockData<'tcx> = &body[block];
            for statement in block_data.statements.iter() {
                self.build_operations(statement, block, body);
            }
            self.build_terminator(block, block_data.terminator.as_ref().unwrap());
        }
        self.resolve_all_symexpr();
        self.print_vars();
        self.print_defmap();
        self.print_usemap();
        self.print_symbexpr();
    }

    pub fn build_value_maps(&mut self, body: &'tcx Body<'tcx>) {
        for bb in body.basic_blocks.indices() {
            let block_data = &body[bb];
            if let Some(terminator) = &block_data.terminator {
                match &terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        if targets.iter().count() == 1 {
                            self.build_value_branch_map(body, discr, targets, bb, block_data);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn trace_operand_origin(
        &self,
        body: &'tcx Body<'tcx>,
        mut current_block: BasicBlock,
        target_place: Place<'tcx>,
        original: &'tcx Operand<'tcx>,
    ) -> &'tcx Operand<'tcx> {
        let mut visited = HashSet::new();
        let target_local = target_place.local;
        while visited.insert(current_block) {
            let data = &body.basic_blocks[current_block];
            for stmt in data.statements.iter().rev() {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (lhs, rvalue) = &**assign;
                    if lhs.local == target_local {
                        return match rvalue {
                            Rvalue::Use(op, ..) => op,
                            _ => original,
                        };
                    }
                }
            }
            let preds = &body.basic_blocks.predecessors()[current_block];
            if preds.len() == 1 {
                current_block = preds[0];
            } else {
                break;
            }
        }
        original
    }

    pub fn build_value_branch_map(
        &mut self,
        body: &'tcx Body<'tcx>,
        discr: &'tcx Operand<'tcx>,
        targets: &'tcx SwitchTargets,
        switch_block: BasicBlock,
        block_data: &'tcx BasicBlockData<'tcx>,
    ) {
        if let Operand::Copy(place) | Operand::Move(place) = discr {
            if let Some((op1, op2, cmp_op)) = self.extract_condition(place, block_data) {
                rap_debug!(
                    "extract_condition op1:{:?} op2:{:?} cmp_op:{:?}\n",
                    op1,
                    op2,
                    cmp_op
                );
                let op1 = if let Some(p1) = op1.place() {
                    self.trace_operand_origin(body, switch_block, p1, op1)
                } else {
                    op1
                };

                let op2 = if let Some(p2) = op2.place() {
                    self.trace_operand_origin(body, switch_block, p2, op2)
                } else {
                    op2
                };
                rap_debug!(
                    "build_value_branch_map op1:{:?} op2:{:?} cmp_op:{:?}\n",
                    op1,
                    op2,
                    cmp_op
                );
                let const_op1 = op1.constant();
                let const_op2 = op2.constant();
                match (const_op1, const_op2) {
                    (Some(_), Some(_)) => {}
                    (Some(c), None) | (None, Some(c)) => {
                        let const_in_left: bool;
                        let variable;
                        if const_op1.is_some() {
                            const_in_left = true;
                            variable = match op2 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        } else {
                            const_in_left = false;
                            variable = match op1 {
                                Operand::Copy(p) | Operand::Move(p) => p,
                                _ => panic!("Expected a place"),
                            };
                        }
                        self.add_varnode(variable);
                        rap_trace!("add_vbm_varnode{:?}\n", variable.clone());

                        let value = T::from_const(&c.const_).unwrap();
                        let const_range =
                            Range::new(value.clone(), value.clone(), RangeType::Unknown);
                        rap_trace!("cmp_op {:?}\n", cmp_op);
                        rap_trace!("const_in_left {:?}\n", const_in_left);
                        let mut true_range =
                            self.apply_comparison(value.clone(), cmp_op, true, const_in_left);
                        let mut false_range =
                            self.apply_comparison(value.clone(), cmp_op, false, const_in_left);
                        true_range.set_regular();
                        false_range.set_regular();
                        let target_vec = targets.all_targets();

                        let vbm = ValueBranchMap::new(
                            variable,
                            &target_vec[0],
                            &target_vec[1],
                            IntervalType::Basic(BasicInterval::new(false_range)),
                            IntervalType::Basic(BasicInterval::new(true_range)),
                        );
                        self.values_branchmap.insert(variable, vbm);
                    }
                    (None, None) => {
                        let CR = Range::new(T::min_value(), T::max_value(), RangeType::Unknown);

                        let p1 = match op1 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let p2 = match op2 {
                            Operand::Copy(p) | Operand::Move(p) => p,
                            _ => panic!("Expected a place"),
                        };
                        let target_vec = targets.all_targets();
                        self.add_varnode(&p1);
                        rap_trace!("add_vbm_varnode{:?}\n", p1.clone());

                        self.add_varnode(&p2);
                        rap_trace!("add_vbm_varnode{:?}\n", p2.clone());
                        let flipped_cmp_op = match Self::flipped_binop(cmp_op) {
                            Some(op) => op,
                            None => {
                                rap_debug!(
                                    "build_value_branch_map: unsupported binop {:?}, skipping\n",
                                    cmp_op
                                );
                                return;
                            }
                        };
                        let reversed_cmp_op = match Self::reverse_binop(cmp_op) {
                            Some(op) => op,
                            None => {
                                rap_debug!(
                                    "build_value_branch_map: unsupported binop {:?}, skipping\n",
                                    cmp_op
                                );
                                return;
                            }
                        };
                        let reversed_flippedd_cmp_op = match Self::flipped_binop(reversed_cmp_op) {
                            Some(op) => op,
                            None => {
                                rap_debug!(
                                    "build_value_branch_map: unsupported binop {:?}, skipping\n",
                                    reversed_cmp_op
                                );
                                return;
                            }
                        };
                        let STOp1 = IntervalType::Symb(SymbInterval::new(CR.clone(), p2, cmp_op));
                        let SFOp1 =
                            IntervalType::Symb(SymbInterval::new(CR.clone(), p2, flipped_cmp_op));
                        let STOp2 =
                            IntervalType::Symb(SymbInterval::new(CR.clone(), p1, reversed_cmp_op));
                        let SFOp2 = IntervalType::Symb(SymbInterval::new(
                            CR.clone(),
                            p1,
                            reversed_flippedd_cmp_op,
                        ));
                        rap_trace!("SFOp1{:?}\n", SFOp1);
                        rap_trace!("SFOp2{:?}\n", SFOp2);
                        rap_trace!("STOp1{:?}\n", STOp1);
                        rap_trace!("STOp2{:?}\n", STOp2);
                        let vbm_1 =
                            ValueBranchMap::new(p1, &target_vec[0], &target_vec[1], SFOp1, STOp1);
                        let vbm_2 =
                            ValueBranchMap::new(p2, &target_vec[0], &target_vec[1], SFOp2, STOp2);
                        self.values_branchmap.insert(&p1, vbm_1);
                        self.values_branchmap.insert(&p2, vbm_2);
                        self.switchbbs.insert(switch_block, (*p1, *p2));
                    }
                }
            };
        }
    }

    pub fn flipped_binop(op: BinOp) -> Option<BinOp> {
        use BinOp::*;
        Some(match op {
            Eq => Eq,
            Ne => Ne,
            Lt => Ge,
            Le => Gt,
            Gt => Le,
            Ge => Lt,
            Add => Add,
            Mul => Mul,
            BitXor => BitXor,
            BitAnd => BitAnd,
            BitOr => BitOr,
            _ => {
                return None;
            }
        })
    }

    fn reverse_binop(op: BinOp) -> Option<BinOp> {
        use BinOp::*;
        Some(match op {
            Eq => Eq,
            Ne => Ne,
            Lt => Gt,
            Le => Ge,
            Gt => Lt,
            Ge => Le,
            Add => Add,
            Mul => Mul,
            BitXor => BitXor,
            BitAnd => BitAnd,
            BitOr => BitOr,
            _ => {
                return None;
            }
        })
    }

    fn extract_condition(
        &mut self,
        place: &'tcx Place<'tcx>,
        switch_block: &'tcx BasicBlockData<'tcx>,
    ) -> Option<(&'tcx Operand<'tcx>, &'tcx Operand<'tcx>, BinOp)> {
        for stmt in &switch_block.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (lhs, rvalue) = &**assign;
                if let Rvalue::BinaryOp(bin_op, pair) = rvalue {
                    let (op1, op2) = &**pair;
                    if lhs == place {
                        let return_op1: &Operand<'tcx> = &op1;
                        let return_op2: &Operand<'tcx> = &op2;

                        return Some((return_op1, return_op2, *bin_op));
                    }
                }
            }
        }
        None
    }

    fn apply_comparison<U: IntervalArithmetic>(
        &self,
        constant: U,
        cmp_op: BinOp,
        is_true_branch: bool,
        const_in_left: bool,
    ) -> Range<U> {
        match cmp_op {
            BinOp::Lt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant.sub(U::one()), RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Le => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant.add(U::one()), U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Gt => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant.add(U::one()), U::max_value(), RangeType::Unknown)
                }
            }

            BinOp::Ge => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value().sub(U::one()), RangeType::Unknown)
                }
            }

            BinOp::Eq => {
                if is_true_branch ^ const_in_left {
                    Range::new(U::min_value(), constant, RangeType::Unknown)
                } else {
                    Range::new(constant, U::max_value(), RangeType::Unknown)
                }
            }

            _ => Range::new(constant.clone(), constant.clone(), RangeType::Empty),
        }
    }

    pub fn build_symbolic_intersect_map(&mut self) {
        for i in 0..self.oprs.len() {
            if let BasicOpKind::Essa(essaop) = &self.oprs[i] {
                if let IntervalType::Symb(symbi) = essaop.get_intersect() {
                    let v = symbi.get_bound();
                    self.symbmap.entry(v).or_insert_with(HashSet::new).insert(i);
                    rap_trace!("symbmap insert {:?} {:?}\n", v, essaop);
                }
            }
        }
    }

    pub fn build_use_map(
        &mut self,
        component: &HashSet<&'tcx Place<'tcx>>,
    ) -> HashMap<&'tcx Place<'tcx>, HashSet<usize>> {
        // Builds use map
        let mut comp_use_map = HashMap::new();
        for &place in component {
            if let Some(uses) = self.usemap.get(place) {
                for op in uses.iter() {
                    let sink = self.oprs[*op].get_sink();
                    if component.contains(&sink) {
                        comp_use_map
                            .entry(place)
                            .or_insert_with(HashSet::new)
                            .insert(*op);
                    }
                }
            }
        }

        self.print_compusemap(component, &comp_use_map);
        comp_use_map
    }

    pub fn build_terminator(&mut self, block: BasicBlock, terminator: &'tcx Terminator<'tcx>) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target: _,
                unwind: _,
                fn_span: _,
                call_source,
            } => {
                rap_trace!(
                    "TerminatorKind::Call in block {:?} with function {:?} destination {:?} args {:?}\n",
                    block,
                    func,
                    destination,
                    args
                );
                // Handle the call operation
                self.add_call_op(destination, args, terminator, func, block);
            }
            TerminatorKind::Return => {}
            TerminatorKind::Goto { target } => {
                rap_trace!(
                    "TerminatorKind::Goto in block {:?} targeting block {:?}\n",
                    block,
                    target
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                rap_trace!(
                    "TerminatorKind::SwitchInt in block {:?} with discr {:?} and targets {:?}\n",
                    block,
                    discr,
                    targets
                );
            }
            _ => {
                rap_trace!(
                    "Unsupported terminator kind in block {:?}: {:?}",
                    block,
                    terminator.kind
                );
            }
        }
    }

    pub fn build_operations(
        &mut self,
        inst: &'tcx Statement<'tcx>,
        block: BasicBlock,
        body: &'tcx Body<'tcx>,
    ) {
        match &inst.kind {
            StatementKind::Assign(assign) => {
                let (sink, rvalue) = &**assign;
                match rvalue {
                    Rvalue::BinaryOp(op, pair) => {
                        let (op1, op2) = &**pair;
                        match op {
                            BinOp::Add
                            | BinOp::Sub
                            | BinOp::Mul
                            | BinOp::Div
                            | BinOp::Rem
                            | BinOp::AddUnchecked => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }
                            BinOp::AddWithOverflow => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }
                            BinOp::SubUnchecked => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }
                            BinOp::SubWithOverflow => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }
                            BinOp::MulUnchecked => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }
                            BinOp::MulWithOverflow => {
                                self.add_binary_op(sink, inst, rvalue, op1, op2, *op);
                            }

                            _ => {}
                        }
                    }
                    Rvalue::UnaryOp(unop, operand) => {
                        self.add_unary_op(sink, inst, rvalue, operand, *unop);
                    }
                    Rvalue::Aggregate(kind, operends) => match **kind {
                        AggregateKind::Adt(def_id, _, _, _, _) => match def_id {
                            _ if def_id == self.essa => {
                                self.add_essa_op(sink, inst, rvalue, operends, block)
                            }
                            _ if def_id == self.ssa => {
                                self.add_ssa_op(sink, inst, rvalue, operends)
                            }
                            _ => match self.unique_adt_handler(def_id) {
                                1 => {
                                    self.add_aggregate_op(sink, inst, rvalue, operends, 1);
                                }
                                _ => {
                                    rap_trace!(
                                        "AggregateKind::Adt with def_id {:?} in statement {:?} is not handled specially.\n",
                                        def_id,
                                        inst
                                    );
                                }
                            },
                        },
                        _ => {}
                    },
                    Rvalue::Use(operend, ..) => {
                        self.add_use_op(sink, inst, rvalue, operend);
                    }
                    Rvalue::Ref(_, borrowkind, place) => {
                        self.add_ref_op(sink, inst, rvalue, place, *borrowkind);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn unique_adt_handler(&mut self, def_id: DefId) -> usize {
        let adt_path = self.tcx.def_path_str(def_id);
        rap_trace!("adt_path: {:?}\n", adt_path);
        if self.unique_adt_path.contains_key(&adt_path) {
            rap_trace!(
                "unique_adt_handler for def_id: {:?} -> {}\n",
                def_id,
                adt_path
            );
            return *self.unique_adt_path.get(&adt_path).unwrap();
        }
        0
    }
    /// Adds a function call operation to the graph.

    fn add_call_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        args: &'tcx Box<[Spanned<Operand<'tcx>>]>,
        terminator: &'tcx Terminator<'tcx>,
        func: &'tcx Operand<'tcx>,
        block: BasicBlock,
    ) {
        rap_trace!("add_call_op for sink: {:?} {:?}\n", sink, terminator);
        let sink_node = self.add_varnode(&sink);

        // Convert Operand arguments to Place arguments.
        // An Operand can be a Constant or a moved/copied Place.
        // We only care about Places for our analysis.
        let mut path = String::new();
        let mut func_def_id = None;
        if let Operand::Constant(c_box) = func {
            let const_operand = &**c_box;
            let fn_ty = const_operand.ty();
            if let ty::TyKind::FnDef(def_id, _substs) = fn_ty.kind() {
                // Found the DefId for a direct function call!
                rap_debug!("fn_ty: {:?}\n", fn_ty);
                if def_id.krate != LOCAL_CRATE {
                    path = self.tcx.def_path_str(*def_id);

                    rap_debug!("called external/no-MIR fn: {:?} -> {}", def_id, path);
                }
                func_def_id = Some(def_id);
            }
        }

        if let Some(def_id) = func_def_id {
            rap_trace!(
                "TerminatorKind::Call in block {:?} with DefId {:?}\n",
                block,
                def_id
            );
            // You can now use the def_id
        } else {
            rap_trace!(
                "TerminatorKind::Call in block {:?} is an indirect call (e.g., function pointer)\n",
                block
            );
            // This handles cases where the call is not a direct one,
            // such as calling a function pointer stored in a variable.
        }
        let mut constant_count = 0 as usize;
        let arg_count = args.len();
        let mut arg_operands: Vec<Operand<'tcx>> = Vec::new();
        let mut places = Vec::new();
        for op in args.iter() {
            match &op.node {
                Operand::Copy(place) | Operand::Move(place) => {
                    arg_operands.push(op.node.clone());
                    places.push(place);
                    self.add_varnode(place);
                    self.usemap
                        .entry(place)
                        .or_default()
                        .insert(self.oprs.len());
                }

                Operand::Constant(_) => {
                    // If it's not a Place, we can still add it as an operand.
                    // This is useful for constants or other non-place operands.
                    arg_operands.push(op.node.clone());
                    constant_count += 1;
                }
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            }
        }
        {
            let bi = BasicInterval::default();

            let call_op = CallOp::new(
                IntervalType::Basic(bi),
                &sink,
                terminator, // Pass the allocated dummy statement
                arg_operands,
                *func_def_id.unwrap(), // Use the DefId if available
                path,
                places,
            );
            rap_debug!("call_op: {:?}\n", call_op);
            let bop_index = self.oprs.len();

            // Insert the operation into the graph.
            self.oprs.push(BasicOpKind::Call(call_op));

            // Insert this definition in defmap
            self.defmap.insert(&sink, bop_index);
            if constant_count == arg_count {
                rap_trace!("all args are constants\n");
                self.const_func_place.insert(&sink, bop_index);
            }
        }
    }

    fn add_ssa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,

        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
    ) {
        rap_trace!("ssa_op{:?}\n", inst);

        let sink_node: &mut VarNode<'_, T> = self.def_add_varnode_sym(sink, rvalue);
        rap_trace!("addsink_in_ssa_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::default();
        let mut phiop = PhiOp::new(IntervalType::Basic(BI), sink, inst);
        let bop_index = self.oprs.len();
        for i in 0..operands.len() {
            let source = match &operands[FieldIdx::from_usize(i)] {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.use_add_varnode_sym(place, rvalue);
                    Some(place)
                }
                _ => None,
            };
            if let Some(source) = source {
                self.use_add_varnode_sym(source, rvalue);
                phiop.add_source(source);
                rap_trace!("addvar_in_ssa_op{:?}\n", source);
                self.usemap.entry(source).or_default().insert(bop_index);
            }
        }
        // Insert the operation in the graph.

        self.oprs.push(BasicOpKind::Phi(phiop));

        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }

    fn add_use_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        op: &'tcx Operand<'tcx>,
    ) {
        rap_trace!("use_op{:?}\n", inst);

        let BI: BasicInterval<T> = BasicInterval::default();
        let source: Option<&'tcx Place<'tcx>> = None;

        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                if sink.local == RETURN_PLACE && sink.projection.is_empty() {
                    self.rerurn_places.insert(place);

                    let sink_node = self.def_add_varnode_sym(sink, rvalue);

                    rap_debug!("add_return_place{:?}\n", place);
                } else {
                    self.use_add_varnode_sym(place, rvalue);
                    rap_trace!("addvar_in_use_op{:?}\n", place);
                    let sink_node = self.def_add_varnode_sym(sink, rvalue);
                    let useop = UseOp::new(IntervalType::Basic(BI), sink, inst, Some(place), None);
                    // Insert the operation in the graph.
                    let bop_index = self.oprs.len();

                    self.oprs.push(BasicOpKind::Use(useop));
                    // Insert this definition in defmap
                    self.usemap.entry(place).or_default().insert(bop_index);

                    self.defmap.insert(sink, bop_index);
                }
            }
            Operand::Constant(constant) => {
                rap_trace!("add_constant_op{:?}\n", inst);
                let Some(c) = op.constant() else {
                    rap_trace!("add_constant_op: constant is None\n");
                    return;
                };
                let useop = UseOp::new(IntervalType::Basic(BI), sink, inst, None, Some(c.const_));
                // Insert the operation in the graph.
                let bop_index = self.oprs.len();

                self.oprs.push(BasicOpKind::Use(useop));
                // Insert this definition in defmap

                self.defmap.insert(sink, bop_index);
                let sink_node = self.def_add_varnode_sym(sink, rvalue);

                if let Some(value) = T::from_const(&c.const_) {
                    sink_node.set_range(Range::new(
                        value.clone(),
                        value.clone(),
                        RangeType::Regular,
                    ));
                    rap_trace!("set_const {:?} value: {:?}\n", sink_node, value);
                } else {
                    sink_node.set_range(Range::bottom());
                };
            }
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => {}
        }
    }

    fn add_essa_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
        block: BasicBlock,
    ) {
        let sink_node = self.def_add_varnode_sym(sink, rvalue);


        let loc_1: usize = 0;
        let loc_2: usize = 1;
        let source1 = match &operands[FieldIdx::from_usize(loc_1)] {
            Operand::Copy(place) | Operand::Move(place) => {
                self.use_add_varnode_sym(place, rvalue);
                Some(place)
            }
            _ => None,
        };
        let op = &operands[FieldIdx::from_usize(loc_2)];
        let bop_index = self.oprs.len();
        let BI: IntervalType<'_, T>;
        rap_trace!("essa_op operand1 {:?}\n", source1.unwrap());
        if let Operand::Constant(c) = op {
            let vbm = self.values_branchmap.get(source1.unwrap()).unwrap();
            if block == *vbm.get_bb_true() {
                rap_trace!("essa_op true branch{:?}\n", block);
                BI = vbm.get_itv_t();
            } else {
                rap_trace!("essa_op false branch{:?}\n", block);
                BI = vbm.get_itv_f();
            }
            self.usemap
                .entry(source1.unwrap())
                .or_default()
                .insert(bop_index);

            let essaop = EssaOp::new(BI, sink, inst, source1.unwrap(), false);
            rap_trace!(
                "addvar_in_essa_op {:?} from const {:?}\n",
                essaop,
                source1.unwrap()
            );

            // Insert the operation in the graph.

            self.oprs.push(BasicOpKind::Essa(essaop));
            // Insert this definition in defmap

            self.defmap.insert(sink, bop_index);
        } else {
            let vbm = self.values_branchmap.get(source1.unwrap()).unwrap();
            if block == *vbm.get_bb_true() {
                rap_trace!("essa_op true branch{:?}\n", block);
                BI = vbm.get_itv_t();
            } else {
                rap_trace!("essa_op false branch{:?}\n", block);
                BI = vbm.get_itv_f();
            }
            let source2 = match op {
                Operand::Copy(place) | Operand::Move(place) => {
                    self.use_add_varnode_sym(place, rvalue);
                    Some(place)
                }
                _ => None,
            };
            self.usemap
                .entry(source1.unwrap())
                .or_default()
                .insert(bop_index);
            let essaop = EssaOp::new(BI, sink, inst, source1.unwrap(), true);
            // Insert the operation in the graph.
            rap_trace!(
                "addvar_in_essa_op {:?} from {:?}\n",
                essaop,
                source1.unwrap()
            );

            self.oprs.push(BasicOpKind::Essa(essaop));

            self.defmap.insert(sink, bop_index);
        }
    }

    pub fn add_aggregate_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        operands: &'tcx IndexVec<FieldIdx, Operand<'tcx>>,
        unique_adt: usize,
    ) {
        rap_trace!("aggregate_op {:?}\n", inst);

        let BI: BasicInterval<T> = BasicInterval::default();
        let mut agg_operands: Vec<AggregateOperand<'tcx>> = Vec::with_capacity(operands.len());

        for operand in operands {
            match operand {
                Operand::Copy(place) | Operand::Move(place) => {
                    if sink.local == RETURN_PLACE && sink.projection.is_empty() {
                        self.rerurn_places.insert(place);
                        self.def_add_varnode_sym(sink, rvalue);
                        rap_debug!("add_return_place {:?}\n", place);
                    } else {
                        self.use_add_varnode_sym(place, rvalue);
                        rap_trace!("addvar_in_aggregate_op {:?}\n", place);
                        agg_operands.push(AggregateOperand::Place(place));
                    }
                }
                Operand::Constant(c) => {
                    rap_trace!("add_constant_aggregate_op {:?}\n", c);
                    agg_operands.push(AggregateOperand::Const(c.const_));

                    let sink_node = self.def_add_varnode_sym(sink, rvalue);
                    if let Some(value) = T::from_const(&c.const_) {
                        sink_node.set_range(Range::new(
                            value.clone(),
                            value.clone(),
                            RangeType::Regular,
                        ));
                        rap_trace!("set_const {:?} value: {:?}\n", sink_node, value);
                    } else {
                        sink_node.set_range(Range::bottom());
                    }
                }
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => {}
            }
        }

        if agg_operands.is_empty() {
            rap_trace!("aggregate_op has no operands, skipping\n");
            return;
        }

        let agg_op = AggregateOp::new(
            IntervalType::Basic(BI),
            sink,
            inst,
            agg_operands,
            unique_adt,
        );
        let bop_index = self.oprs.len();
        self.oprs.push(BasicOpKind::Aggregate(agg_op));

        for operand in operands {
            if let Operand::Copy(place) | Operand::Move(place) = operand {
                self.usemap.entry(place).or_default().insert(bop_index);
            }
        }

        self.defmap.insert(sink, bop_index);

        self.def_add_varnode_sym(sink, rvalue);
    }

    fn add_unary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        operand: &'tcx Operand<'tcx>,
        op: UnOp,
    ) {
        rap_trace!("unary_op{:?}\n", inst);

        let sink_node = self.def_add_varnode_sym(sink, rvalue);
        rap_trace!("addsink_in_unary_op{:?}\n", sink_node);

        let BI: BasicInterval<T> = BasicInterval::default();
        let loc_1: usize = 0;

        let source = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.add_varnode(place);
                Some(place)
            }
            _ => None,
        };

        rap_trace!("addvar_in_unary_op{:?}\n", source.unwrap());
        self.use_add_varnode_sym(&source.unwrap(), rvalue);

        let unaryop = UnaryOp::new(IntervalType::Basic(BI), sink, inst, source.unwrap(), op);
        // Insert the operation in the graph.
        let bop_index = self.oprs.len();

        self.oprs.push(BasicOpKind::Unary(unaryop));
        // Insert this definition in defmap

        self.defmap.insert(sink, bop_index);
    }

    fn add_binary_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        op1: &'tcx Operand<'tcx>,
        op2: &'tcx Operand<'tcx>,
        bin_op: BinOp,
    ) {
        rap_trace!("binary_op{:?}\n", inst);

        // Define the sink node (Def)
        let sink_node = self.def_add_varnode_sym(sink, rvalue);
        rap_trace!("addsink_in_binary_op{:?}\n", sink_node);

        let bop_index = self.oprs.len();
        let bi: BasicInterval<T> = BasicInterval::default();

        // Match both operands simultaneously to handle all combinations.
        // Goal: Ensure source1 is always a Place if at least one Place exists.
        let (source1_place, source2_place, const_val) = match (op1, op2) {
            // Case 1: Place + Place
            (Operand::Copy(p1) | Operand::Move(p1), Operand::Copy(p2) | Operand::Move(p2)) => {
                self.use_add_varnode_sym(p1, rvalue);
                self.use_add_varnode_sym(p2, rvalue);
                rap_trace!("addvar_in_binary_op p1:{:?}, p2:{:?}\n", p1, p2);

                (Some(p1), Some(p2), None)
            }

            // Case 2: Place + Constant
            (Operand::Copy(p1) | Operand::Move(p1), Operand::Constant(c2)) => {
                self.use_add_varnode_sym(p1, rvalue);
                rap_trace!("addvar_in_binary_op p1:{:?}\n", p1);

                (Some(p1), None, Some(c2.const_))
            }

            // Case 3: Constant + Place
            // Here we normalize: Treat the Place (op2) as source1, and the Constant (op1) as the const value.
            // NOTE: Be careful with non-commutative operations (Sub, Div) in your interval logic later,
            // as the physical order is swapped here.
            (Operand::Constant(c1), Operand::Copy(p2) | Operand::Move(p2)) => {
                self.use_add_varnode_sym(p2, rvalue);
                rap_trace!("addvar_in_binary_op p2(as source1):{:?}\n", p2);

                // Assign p2 to the first return position to make it source1
                (Some(p2), None, Some(c1.const_))
            }

            // Case 4: Constant + Constant
            (Operand::Constant(c1), Operand::Constant(_)) => {
                // Logic depends on how you want to handle two constants.
                // Usually keeping one is sufficient for the struct signature.
                (None, None, Some(c1.const_))
            }
            #[cfg(rapx_rustc_ge_196)]
            _ => (None, None, None),
        };

        // Construct the BinaryOp
        let bop = BinaryOp::new(
            IntervalType::Basic(bi),
            sink,
            inst,
            source1_place, // This is guaranteed to be the Place (if one exists)
            source2_place,
            const_val,
            bin_op.clone(),
        );

        self.oprs.push(BasicOpKind::Binary(bop));

        // Update DefMap
        self.defmap.insert(sink, bop_index);

        // Update UseMap
        if let Some(place) = source1_place {
            self.usemap.entry(place).or_default().insert(bop_index);
        }

        if let Some(place) = source2_place {
            self.usemap.entry(place).or_default().insert(bop_index);
        }
    }

    fn add_ref_op(
        &mut self,
        sink: &'tcx Place<'tcx>,
        inst: &'tcx Statement<'tcx>,
        rvalue: &'tcx Rvalue<'tcx>,
        place: &'tcx Place<'tcx>,
        borrowkind: BorrowKind,
    ) {
        rap_trace!("ref_op {:?}\n", inst);

        let BI: BasicInterval<T> = BasicInterval::default();

        let source_node = self.use_add_varnode_sym(place, rvalue);

        let sink_node = self.def_add_varnode_sym(sink, rvalue);

        let refop = RefOp::new(IntervalType::Basic(BI), sink, inst, place, borrowkind);
        let bop_index = self.oprs.len();
        self.oprs.push(BasicOpKind::Ref(refop));

        self.usemap.entry(place).or_default().insert(bop_index);

        self.defmap.insert(sink, bop_index);

        rap_trace!(
            "add_ref_op: created RefOp from {:?} to {:?} at {:?}\n",
            place,
            sink,
            inst
        );
    }
}
