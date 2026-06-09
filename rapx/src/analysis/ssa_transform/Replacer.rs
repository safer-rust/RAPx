#![allow(non_snake_case)]
#![allow(unused_variables)]
#![allow(dead_code)]
use super::SSATransformer::SSATransformer;
use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefIdMap;
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_middle::{mir::*, ty::GenericArgs};
use rustc_span::sym::new;
use std::collections::{HashMap, HashSet, VecDeque};
// use stable_mir::mir::FieldIdx;
// use stable_mir::ty::ConstantKind;
// // use rustc_middle::mir::visit::*;
// // use rustc_index::IndexSlice;

pub struct Replacer<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) ssatransformer: super::SSATransformer::SSATransformer<'tcx>,
    pub(crate) new_local_collection: HashSet<Local>,
    pub(crate) new_locals_to_declare: HashMap<Local, Local>,
}
impl<'tcx> Replacer<'tcx> {
    pub fn insert_phi_statment(&mut self, body: &mut Body<'tcx>) {
        for (block_index, blockdata) in body.basic_blocks.iter_enumerated() {}
        let mut phi_functions: HashMap<BasicBlock, HashSet<Local>> = HashMap::new();
        for bb in body.basic_blocks.indices() {
            phi_functions.insert(bb, HashSet::new());
        }
        let variables: Vec<Local> = self
            .ssatransformer
            .local_assign_blocks
            .iter()
            .filter(|(_, blocks)| blocks.len() >= 2)
            .map(|(&local, _)| local)
            .collect();
        for var in &variables {
            if let Some(def_blocks) = self.ssatransformer.local_assign_blocks.get(var) {
                let mut worklist: VecDeque<BasicBlock> = def_blocks.iter().cloned().collect();
                let mut processed: HashSet<BasicBlock> = HashSet::new();
                while let Some(block) = worklist.pop_front() {
                    if let Some(df_blocks) = self.ssatransformer.df.get(&block) {
                        for &df_block in df_blocks {
                            if !processed.contains(&df_block) {
                                phi_functions.get_mut(&df_block).unwrap().insert(*var);
                                processed.insert(df_block);

                                worklist.push_back(df_block);
                            }
                        }
                    }
                }
                // while let Some(block) = worklist.pop_front() {
                //     if let Some(df_blocks) = self.ssatransformer.df.get(&block) {
                //         for &df_block in df_blocks {
                //             if !processed.contains(&df_block) {
                //                 phi_functions.get_mut(&df_block).unwrap().insert(*var);
                //                 processed.insert(df_block);
                //                 if self.ssatransformer.local_assign_blocks[var].contains(&df_block)
                //                 {
                //                     worklist.push_back(df_block);
                //                 }
                //             }
                //         }
                //     }
                // }
            }
        }

        for (block, vars) in phi_functions {
            for var in vars.clone() {
                let decl = body.local_decls[var].clone();
                // let new_var = body.local_decls.push(decl);

                // print!("body.local_decls.len():{:?}\n", body.local_decls.len());
                let predecessors = body.basic_blocks.predecessors()[block].clone();

                let mut operands = IndexVec::with_capacity(predecessors.len());
                for _ in 0..predecessors.len() {
                    operands.push(Operand::Copy(Place::from(var)));
                }
                let phi_stmt: Statement<'_> = Statement::new(
                    SourceInfo::outermost(body.span),
                    StatementKind::Assign(Box::new((
                        Place::from(var),
                        Rvalue::Aggregate(
                            Box::new(AggregateKind::Adt(
                                self.ssatransformer.phi_def_id.clone(),
                                rustc_abi::VariantIdx::from_u32(0),
                                GenericArgs::empty(),
                                None,
                                None,
                            )),
                            operands,
                        ),
                    ))),
                );
                // let phi_stmt = Statement {
                //     source_info: SourceInfo::outermost(body.span),
                //     kind: StatementKind::Assign(Box::new((
                //         Place::from(var),
                //         Rvalue::Aggregate(Box::new(AggregateKind::Tuple), operands),
                //     ))),
                // };
                body.basic_blocks_mut()[block]
                    .statements
                    .insert(0, phi_stmt);
            }
        }
    }
    pub fn insert_essa_statement(&mut self, body: &mut Body<'tcx>) {
        let order = SSATransformer::depth_first_search_preorder(
            &self.ssatransformer.dom_tree,
            body.basic_blocks.indices().next().unwrap(),
        );

        for &bb in &order {
            self.essa_process_basic_block(bb, body);
        }
    }

    fn essa_process_basic_block(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
        let switch_block_data = body.basic_blocks[bb].clone();

        if let Some(terminator) = &switch_block_data.terminator {
            if let TerminatorKind::SwitchInt { discr, targets, .. } = &terminator.kind {
                if targets.iter().count() == 1 {
                    let (value, target) = targets.iter().next().unwrap();
                    self.essa_assign_statement(&target, &bb, value, discr, body);

                    let otherwise = targets.otherwise();
                    self.essa_assign_statement(&otherwise, &bb, 1, discr, body);
                }
            }
        }
    }

    fn extract_condition(
        &self,
        place: &Place<'tcx>,
        switch_block: &BasicBlockData<'tcx>,
    ) -> Option<(Operand<'tcx>, Operand<'tcx>, BinOp)> {
        for stmt in &switch_block.statements {
            if let StatementKind::Assign(box (lhs, Rvalue::BinaryOp(bin_op, box (op1, op2)))) =
                &stmt.kind
            {
                if lhs == place {
                    let return_op1: &Operand<'tcx> = &op1;
                    let return_op2: &Operand<'tcx> = &op2;

                    return Some((return_op1.clone(), return_op2.clone(), *bin_op));
                }
            }
        }
        None
    }
    fn make_const_operand(&self, val: u64) -> Operand<'tcx> {
        Operand::Constant(Box::new(ConstOperand {
            span: rustc_span::DUMMY_SP,
            user_ty: None,
            const_: Const::from_usize(self.tcx, val),
        }))
    }

    fn op_to_code(op: BinOp) -> u64 {
        match op {
            BinOp::Lt => 1,
            BinOp::Le => 2,
            BinOp::Ge => 3,
            BinOp::Gt => 4,
            BinOp::Eq => 5,
            BinOp::Ne => 6,
            _ => 7,
        }
    }
    fn trace_operand_source(
        &self,
        body: &Body<'tcx>,
        mut current_block: BasicBlock,
        target_place: Place<'tcx>,
    ) -> Operand<'tcx> {
        let mut visited = HashSet::new();
        let current_place = target_place;

        while visited.insert(current_block) {
            let data = &body.basic_blocks[current_block];
            for stmt in data.statements.iter().rev() {
                if let StatementKind::Assign(box (lhs, rvalue)) = &stmt.kind {
                    if *lhs == current_place {
                        match rvalue {
                            Rvalue::Use(op) => return op.clone(),
                            _ => return Operand::Copy(current_place),
                        }
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

        Operand::Copy(current_place)
    }
    // This function inserts eSSA (extended SSA) assignment statements into the basic block.
    // These statements capture control flow information by asserting conditions on variables
    // based on the outcome of a switch (branching) instruction.
    fn essa_assign_statement(
        &mut self,
        bb: &BasicBlock,
        switch_block: &BasicBlock,
        value: u128,
        discr: &Operand<'tcx>,
        body: &mut Body<'tcx>,
    ) {
        let switch_block_data = &body.basic_blocks[*switch_block];

        let magic_number_operand = self.make_const_operand(switch_block.as_usize() as u64);

        // Helper: verify if the discriminant is a Place (variable).
        if let Operand::Copy(switch_place) | Operand::Move(switch_place) = discr {
            // Attempt to extract the binary condition that led to this switch.
            if let Some((op1, op2, cmp_op)) =
                self.extract_condition(switch_place, switch_block_data)
            {
                let op1 = if let Some(p1) = op1.place() {
                    self.trace_operand_source(body, *switch_block, p1)
                } else {
                    op1
                };

                let op2 = if let Some(p2) = op2.place() {
                    self.trace_operand_source(body, *switch_block, p2)
                } else {
                    op2
                };
                rap_debug!(
                    "essa trace_operand_source op1:{:?} op2:{:?} cmp_op:{:?} value:{:?}\n",
                    op1,
                    op2,
                    cmp_op,
                    value
                );
                let block_data: &mut BasicBlockData<'tcx> = &mut body.basic_blocks.as_mut()[*bb];

                let const_op1: Option<&ConstOperand<'_>> = op1.constant();
                let const_op2: Option<&ConstOperand<'_>> = op2.constant();

                // Generate operands for the comparison operators.
                let cmp_operand = self.make_const_operand(Self::op_to_code(cmp_op));
                let flip_cmp_operand =
                    self.make_const_operand(Self::op_to_code(Self::flip(cmp_op)));
                let reverse_cmp_operand =
                    self.make_const_operand(Self::op_to_code(Self::reverse(cmp_op)));
                let flip_reverse_cmp_operand =
                    self.make_const_operand(Self::op_to_code(Self::flip(Self::reverse(cmp_op))));

                match (const_op1, const_op2) {
                    // Case 1: Both operands are places (variables).
                    (None, None) => {
                        match (op1, op2) {
                            (
                                Operand::Copy(p1) | Operand::Move(p1),
                                Operand::Copy(p2) | Operand::Move(p2),
                            ) => {
                                let adt_kind = AggregateKind::Adt(
                                    self.ssatransformer.essa_def_id.clone(),
                                    rustc_abi::VariantIdx::from_u32(0),
                                    GenericArgs::empty(),
                                    None,
                                    None,
                                );
                                let place1 = Place::from(p1);
                                let place2 = Place::from(p2);
                                let rvalue1;
                                let rvalue2;
                                let mut operand1: IndexVec<_, _> = IndexVec::with_capacity(4);
                                let mut operand2: IndexVec<_, _> = IndexVec::with_capacity(4);

                                // Determine constraints based on whether the condition was true (value != 0) or false (value == 0).
                                if value == 0 {
                                    // False branch: Use flipped operators.
                                    // For p1: p1 (negated_op) p2
                                    operand1.push(Operand::Copy(Place::from(p1)));
                                    operand1.push(Operand::Copy(Place::from(p2)));
                                    operand1.push(flip_cmp_operand.clone());
                                    operand1.push(magic_number_operand.clone());

                                    // For p2: p2 (negated_reversed_op) p1
                                    operand2.push(Operand::Copy(Place::from(p2)));
                                    operand2.push(Operand::Copy(Place::from(p1)));
                                    operand2.push(flip_reverse_cmp_operand.clone());
                                    operand2.push(magic_number_operand.clone());

                                    rvalue1 =
                                        Rvalue::Aggregate(Box::new(adt_kind.clone()), operand1);
                                    rvalue2 =
                                        Rvalue::Aggregate(Box::new(adt_kind.clone()), operand2);
                                } else {
                                    // True branch: Use original operators.
                                    // For p1: p1 (op) p2
                                    operand1.push(Operand::Copy(Place::from(p1)));
                                    operand1.push(Operand::Copy(Place::from(p2)));
                                    operand1.push(cmp_operand.clone());
                                    operand1.push(magic_number_operand.clone());

                                    // For p2: p2 (reversed_op) p1
                                    operand2.push(Operand::Copy(Place::from(p2)));
                                    operand2.push(Operand::Copy(Place::from(p1)));
                                    operand2.push(reverse_cmp_operand.clone());
                                    operand2.push(magic_number_operand.clone());

                                    rvalue1 =
                                        Rvalue::Aggregate(Box::new(adt_kind.clone()), operand1);
                                    rvalue2 =
                                        Rvalue::Aggregate(Box::new(adt_kind.clone()), operand2);
                                }

                                let assign_stmt1 = Statement::new(
                                    SourceInfo::outermost(body.span),
                                    StatementKind::Assign(Box::new((place1, rvalue1))),
                                );
                                let assign_stmt2 = Statement::new(
                                    SourceInfo::outermost(body.span),
                                    StatementKind::Assign(Box::new((place2, rvalue2))),
                                );

                                let mut insert_index = 0;
                                for (i, stmt) in block_data.statements.iter().enumerate() {
                                    if !SSATransformer::is_essa_statement(
                                        &self.ssatransformer,
                                        stmt,
                                    ) {
                                        break;
                                    }
                                    insert_index = i + 1;
                                }

                                block_data.statements.insert(insert_index, assign_stmt1);
                                block_data.statements.insert(insert_index + 1, assign_stmt2);

                                for i in insert_index..insert_index + 2 {
                                    let essa_in_body = block_data.statements.get_mut(i).unwrap();
                                    rap_trace!(
                                        "Inserted eSSA statement {:?}  in block {:?}",
                                        essa_in_body,
                                        magic_number_operand
                                    );
                                }
                            }
                            _ => panic!("Expected a place"),
                        };
                    }

                    // Case 2: One operand is a constant.
                    (None, Some(_)) | (Some(_), None) => {
                        let mut operand: IndexVec<_, _> = IndexVec::with_capacity(3);
                        let place;

                        // normalize operands: place always extracted as 'place', and stored first in operand list?
                        // Actually logic keeps place as the key, but operand order in Aggregate is [Place, Other] or [Other, Place]?
                        // Looking at logic below:
                        // If op1 is place: operand.push(op1), operand.push(op2) -> [Place, Const]
                        // If op2 is place: operand.push(op2), operand.push(op1) -> [Place, Const]
                        // So the first element in Aggregate is always the Place (variable).

                        if op1.constant().is_none() {
                            place = match op1 {
                                Operand::Copy(p) | Operand::Move(p) => Place::from(p),
                                _ => panic!("Expected a place"),
                            };
                            operand.push(op1.clone());
                            operand.push(op2.clone());
                        } else {
                            place = match op2 {
                                Operand::Copy(p) | Operand::Move(p) => Place::from(p),
                                _ => panic!("Expected a place"),
                            };
                            operand.push(op2.clone());
                            operand.push(op1.clone());
                        }

                        let rvalue;
                        if value == 0 {
                            operand.push(flip_cmp_operand.clone());
                        } else {
                            operand.push(cmp_operand.clone());
                        }
                        operand.push(magic_number_operand.clone());
                        let adt_kind = AggregateKind::Adt(
                            self.ssatransformer.essa_def_id.clone(),
                            rustc_abi::VariantIdx::from_u32(0),
                            GenericArgs::empty(),
                            None,
                            None,
                        );
                        rvalue = Rvalue::Aggregate(Box::new(adt_kind.clone()), operand);

                        let assign_stmt = Statement::new(
                            SourceInfo::outermost(body.span),
                            StatementKind::Assign(Box::new((place, rvalue))),
                        );
                        let mut insert_index = 0;
                        for (i, stmt) in block_data.statements.iter().enumerate() {
                            if !SSATransformer::is_essa_statement(&self.ssatransformer, stmt) {
                                break;
                            }
                            insert_index = i + 1;
                        }

                        block_data.statements.insert(insert_index, assign_stmt);

                        let essa_in_body = block_data.statements.get_mut(insert_index).unwrap();
                        let essa_ptr = essa_in_body as *const _;

                        rap_trace!(
                            "Inserted eSSA statement {:?}  in block {:?}",
                            essa_in_body,
                            magic_number_operand
                        );
                    }

                    (Some(_), Some(_)) => {}
                }
            };
        }

        // block_data.statements.insert(0, assign_stmt);
    }
    pub fn flip(binOp: BinOp) -> BinOp {
        match binOp {
            BinOp::Lt => BinOp::Ge,
            BinOp::Le => BinOp::Gt,
            BinOp::Gt => BinOp::Le,
            BinOp::Ge => BinOp::Lt,
            BinOp::Eq => BinOp::Ne,
            BinOp::Ne => BinOp::Eq,
            _ => panic!("flip() called on non-comparison operator"),
        }
    }
    pub fn reverse(binOp: BinOp) -> BinOp {
        match binOp {
            BinOp::Lt => BinOp::Gt,
            BinOp::Le => BinOp::Ge,
            BinOp::Gt => BinOp::Lt,
            BinOp::Ge => BinOp::Le,
            BinOp::Eq => BinOp::Ne,
            BinOp::Ne => BinOp::Eq,
            _ => panic!("flip() called on non-comparison operator"),
        }
    }
    pub fn rename_variables(&mut self, body: &mut Body<'tcx>) {
        for local in body.local_decls.indices() {
            self.ssatransformer.reaching_def.insert(local, None);
        }
        // self.ssatransformer.local_defination_block = Self::map_locals_to_definition_block(&self.body.borrow());

        let order = SSATransformer::depth_first_search_preorder(
            &self.ssatransformer.dom_tree,
            body.basic_blocks.indices().next().unwrap().clone(),
        );
        for bb in order {
            self.process_basic_block(bb, body);
        }

        rap_debug!("new_locals_to_declare {:?}", self.new_locals_to_declare);

        let mut locals_to_add: Vec<_> = self.new_locals_to_declare.iter().collect();
        locals_to_add.sort_by_key(|(new_local, _)| new_local.index());
        rap_debug!("locals_to_add {:?}", locals_to_add);
        for (new_local, original_local) in locals_to_add {
            let original_decl = &body.local_decls[*original_local];

            let new_decl = original_decl.clone();

            let pushed_index = body.local_decls.push(new_decl);
            rap_debug!("Ok with {:?} {:?}", pushed_index, *new_local);
            assert_eq!(pushed_index, *new_local);
        }
    }

    fn process_basic_block(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
        self.rename_statement(bb, body);
        self.rename_terminator(bb, body);
        let terminator = body.basic_blocks[bb].terminator();
        let successors: Vec<_> = terminator.successors().collect();
        if let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind {
            if targets.iter().count() == 1 {
                for succ_bb in successors.clone() {
                    self.rename_essa_statments(succ_bb, body, bb);
                }
            }
        }

        for succ_bb in successors {
            self.rename_phi_functions(succ_bb, body, bb);
        }
    }
    fn rename_essa_statments(
        &mut self,
        succ_bb: BasicBlock,
        body: &mut Body<'tcx>,
        do_bb: BasicBlock,
    ) {
        // Iterate through all statements in the successor basic block to find and update ESSA nodes.
        for statement in body.basic_blocks.as_mut()[succ_bb].statements.iter_mut() {
            // Check if the current statement is an ESSA statement (identified by specific DefId).
            if self.ssatransformer.is_essa_statement(statement) {
                // Retrieve the source basic block ID encoded in the statement's operands.
                // This replaces the unstable pointer-based lookup map.
                if let Some(pred_block) = self.ssatransformer.get_essa_source_block(statement) {
                    // Check if this ESSA statement corresponds to the predecessor block (`do_bb`)
                    // we are currently processing. If not, skip it.
                    if pred_block != do_bb {
                        continue;
                    }

                    // Proceed to rename the variable in the ESSA statement.
                    if let StatementKind::Assign(box (_, rvalue)) = &mut statement.kind {
                        if let Rvalue::Aggregate(_, operands) = rvalue {
                            // The first operand (index 0) is the variable that needs to be renamed/replaced.
                            let index = 0;
                            if index < operands.len() {
                                // Replace the operand with the correct SSA version for the current path.
                                self.replace_operand(
                                    &mut operands[FieldIdx::from_usize(index)],
                                    &do_bb,
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    fn rename_phi_functions(
        &mut self,
        succ_bb: BasicBlock,
        body: &mut Body<'tcx>,
        do_bb: BasicBlock,
    ) {
        for (stmt_idx, statement) in body.basic_blocks.as_mut()[succ_bb]
            .statements
            .iter_mut()
            .enumerate()
        {
            let location = Location {
                block: succ_bb,
                statement_index: stmt_idx,
            };

            if SSATransformer::is_phi_statement(&self.ssatransformer, statement) {
                if let StatementKind::Assign(box (_, rvalue)) = &mut statement.kind {
                    if let Rvalue::Aggregate(_, operands) = rvalue {
                        let operand_count = operands.len();
                        let index = *self.ssatransformer.phi_index.entry(location).or_insert(0);

                        if index < operand_count {
                            match &mut operands[FieldIdx::from_usize(index)] {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    self.replace_place(place, &do_bb);
                                }
                                _ => {}
                            }
                            *self.ssatransformer.phi_index.entry(location).or_insert(0) += 1;
                        }
                    }
                }
            }
        }
    }
    pub fn rename_statement(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
        for statement in body.basic_blocks.as_mut()[bb].statements.iter_mut() {
            // let rc_stat = Rc::new(RefCell::new(statement));
            let is_phi = SSATransformer::is_phi_statement(&self.ssatransformer, statement);
            let is_essa = SSATransformer::is_essa_statement(&self.ssatransformer, statement);
            rap_trace!(
                "IS in statement at block {:?}: {:?}, is_phi: {}, is_essa: {}",
                bb,
                statement.clone(),
                is_phi,
                is_essa
            );
            match &mut statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if !is_phi {
                        if !is_essa {
                            rap_trace!(
                                "Renaming in statement at block {:?}: {:?}",
                                bb,
                                rvalue.clone()
                            );
                            self.replace_rvalue(rvalue, &bb);
                            self.rename_local_def(place, &bb, true);
                        } else {
                            self.ssa_rename_local_def(place, &bb, true);
                        }
                    } else {
                        self.ssa_rename_local_def(place, &bb, false);
                    }
                }
                // StatementKind::FakeRead(_, place)
                StatementKind::StorageLive(local) => {
                    // self.rename_local_def(*local);
                }
                StatementKind::StorageDead(local) => {
                    // self.replace_local(local);
                }
                _ => {}
            }
        }
    }

    fn rename_terminator(&mut self, bb: BasicBlock, body: &mut Body<'tcx>) {
        let terminator: &mut Terminator<'tcx> = body.basic_blocks.as_mut()[bb].terminator_mut();
        match &mut terminator.kind {
            TerminatorKind::Call {
                args, destination, ..
            } => {
                for op in args.iter_mut() {
                    match &mut op.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            self.replace_place(place, &bb);
                        }
                        Operand::Constant(const_operand) => {}
                    }
                }
                self.rename_local_def(destination, &bb, true);
            }
            TerminatorKind::Assert { cond, .. } => {
                self.replace_operand(cond, &bb);
            }
            TerminatorKind::Drop { place, .. } => {
                self.replace_place(place, &bb);
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                self.replace_operand(discr, &bb);
            }
            _ => {}
        }
    }

    fn replace_rvalue(&mut self, rvalue: &mut Rvalue<'tcx>, bb: &BasicBlock) {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::ShallowInitBox(operand, _) => {
                self.replace_operand(operand, &bb);
            }
            Rvalue::BinaryOp(_, box (lhs, rhs)) => {
                self.replace_operand(lhs, &bb);
                self.replace_operand(rhs, &bb);
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    self.replace_operand(operand, &bb);
                }
            }
            _ => {}
        }
    }

    fn replace_operand(&mut self, operand: &mut Operand<'tcx>, bb: &BasicBlock) {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                self.replace_place(place, bb);
                // print!("replace_operand: {:?} -> {:?}\n", place.local, place.local);
            }
            _ => {}
        }
    }

    fn replace_place(&mut self, place: &mut Place<'tcx>, bb: &BasicBlock) {
        // let old_local = place.local;
        self.update_reachinf_def(&place.local, &bb);

        if let Some(Some(reaching_local)) = self.ssatransformer.reaching_def.get(&place.local) {
            let local = reaching_local.clone();
            let mut new_place: Place<'_> = Place::from(local);
            new_place.projection = place.projection;

            *place = new_place;
        } else {
        }
    }

    fn ssa_rename_local_def(&mut self, place: &mut Place<'tcx>, bb: &BasicBlock, not_phi: bool) {
        // let old_local = place.as_local().as_mut().unwrap();
        self.update_reachinf_def(&place.local, &bb);
        let Place {
            local: old_local,
            projection: _,
        } = place.clone();
        let old_place = place.clone();
        if old_local.as_u32() == 0 {
            return;
        }
        let new_local = Local::from_usize(self.ssatransformer.local_index);
        self.ssatransformer.local_index += 1;
        let new_place: Place<'_> = Place::from(new_local);
        *place = new_place.clone();
        self.new_locals_to_declare.insert(new_local, old_local);

        let _old_local = old_local.clone();
        self.ssatransformer
            .ssa_locals_map
            .entry(old_place)
            .or_insert_with(HashSet::new)
            .insert(new_place);

        self.ssatransformer
            .local_defination_block
            .insert(new_local.clone(), bb.clone());
        let old_local_reaching = self
            .ssatransformer
            .reaching_def
            .get(&_old_local.clone())
            .unwrap();

        self.ssatransformer
            .reaching_def
            .insert(new_local.clone(), *old_local_reaching);
        self.ssatransformer
            .reaching_def
            .insert(_old_local.clone(), Some(new_local.clone()));

        // self.reaching_def
        //     .entry(old_local)
        //     .or_default()
        //     .replace(Some(old_local));
    }
    fn rename_local_def(&mut self, place: &mut Place<'tcx>, bb: &BasicBlock, not_phi: bool) {
        // let old_local = place.as_local().as_mut().unwrap();
        self.update_reachinf_def(&place.local, &bb);
        let Place {
            local: old_local,
            projection: _,
        } = place.clone();
        let old_place = place.clone();
        if old_local.as_u32() == 0 {
            return;
        }

        if self.ssatransformer.skipped.contains(&old_local.as_usize()) && not_phi {
            self.ssatransformer.skipped.remove(&old_local.as_usize());
            self.ssatransformer
                .reaching_def
                .insert(old_local, Some(old_local));
            self.ssatransformer
                .places_map
                .entry(old_place)
                .or_insert_with(HashSet::new)
                .insert(old_place);
            return;
        }
        let new_local = Local::from_usize(self.ssatransformer.local_index);
        let mut new_place: Place<'_> = Place::from(new_local);
        self.new_locals_to_declare.insert(new_local, old_local);

        new_place.projection = place.projection;
        *place = new_place.clone();

        //find the original local defination assign statement
        if old_local.as_u32() == 0 {
            return;
        }

        self.ssatransformer.local_index += 1;
        self.ssatransformer
            .places_map
            .entry(old_place)
            .or_insert_with(HashSet::new)
            .insert(new_place);

        let _old_local = old_local.clone();
        self.ssatransformer
            .local_defination_block
            .insert(new_local.clone(), bb.clone());
        let old_local_reaching = self
            .ssatransformer
            .reaching_def
            .get(&_old_local.clone())
            .unwrap();

        self.ssatransformer
            .reaching_def
            .insert(new_local.clone(), *old_local_reaching);
        self.ssatransformer
            .reaching_def
            .insert(_old_local.clone(), Some(new_local.clone()));

        // self.reaching_def
        //     .entry(old_local)
        //     .or_default()
        //     .replace(Some(old_local));
    }

    pub fn dominates_(&self, def_bb: &BasicBlock, bb: &BasicBlock) -> bool {
        let mut visited = HashSet::new();

        let mut stack = self.ssatransformer.dom_tree.get(def_bb).unwrap().clone();
        while let Some(block) = stack.pop() {
            if !visited.insert(block) {
                continue;
            }

            if block == *bb {
                return true;
            }

            if let Some(children) = self.ssatransformer.dom_tree.get(&block) {
                stack.extend(children);
            }
        }

        false
    }
    fn update_reachinf_def(&mut self, local: &Local, bb: &BasicBlock) {
        // if self.ssatransformer.reaching_def[local]!= None {
        //     return;
        // }
        let mut r = self.ssatransformer.reaching_def[local];
        let mut dominate_bool = true;
        if r != None {
            let def_bb = self.ssatransformer.local_defination_block[&r.unwrap()];
        }

        while !(r == None || dominate_bool) {
            r = self.ssatransformer.reaching_def[&r.unwrap()];
            if r != None {
                let def_bb = self.ssatransformer.local_defination_block[&r.unwrap()];

                dominate_bool = self.dominates_(&def_bb, bb);
            }
        }

        if let Some(entry) = self.ssatransformer.reaching_def.get_mut(local) {
            *entry = r.clone();
        }
    }
}

// impl<'tcx> MutVisitor<'tcx> for Replacer< 'tcx> {
//     fn tcx(&self) -> TyCtxt<'tcx> {
//         self.tcx
//     }

//     fn visit_local(&mut self, local: &mut Local, ctxt: PlaceContext, _: Location) {
//         let new_local = self.copy_classes[*local];
//         // We must not unify two locals that are borrowed. But this is fine if one is borrowed and
//         // the other is not. We chose to check the original local, and not the target. That way, if
//         // the original local is borrowed and the target is not, we do not pessimize the whole class.
//         if self.borrowed_locals.contains(*local) {
//             return;
//         }
//         match ctxt {
//             // Do not modify the local in storage statements.
//             PlaceContext::NonUse(NonUseContext::StorageLive | NonUseContext::StorageDead) => {}
//             // The local should have been marked as non-SSA.
//             PlaceContext::MutatingUse(_) => assert_eq!(*local, new_local),
//             // We access the value.
//             _ => *local = new_local,
//             // _ => *local = new_local,
//         }
//     }

//     fn visit_place(&mut self, place: &mut Place<'tcx>, _: PlaceContext, loc: Location) {
//         if let Some(new_projection) = self.process_projection(place.projection, loc) {
//             place.projection = self.tcx().mk_place_elems(&new_projection);
//         }
//         // Any non-mutating use context is ok.
//         let ctxt = PlaceContext::NonMutatingUse(NonMutatingUseContext::Copy);
//         self.visit_local(&mut place.local, ctxt, loc);
//         print!("{:?}", place);
//     }

//     fn visit_operand(&mut self, operand: &mut Operand<'tcx>, loc: Location) {
//         if let Operand::Move(place) = *operand
//             // A move out of a projection of a copy is equivalent to a copy of the original
//             // projection.
//             && !place.is_indirect_first_projection()
//             && !self.fully_moved.contains(place.local)
//         {
//             *operand = Operand::Copy(place);
//         }
//         self.super_operand(operand, loc);
//     }

//     fn visit_statement(&mut self, stmt: &mut Statement<'tcx>, loc: Location) {
//         // When removing storage statements, we need to remove both (#107511).
//         if let StatementKind::StorageLive(l) | StatementKind::StorageDead(l) = stmt.kind
//             && self.storage_to_remove.contains(l)
//         {
//             stmt.make_nop();
//             return;
//         }

//         self.super_statement(stmt, loc);

//         // Do not leave tautological assignments around.
//         if let StatementKind::Assign(box (lhs, ref rhs)) = stmt.kind
//             && let Rvalue::Use(Operand::Copy(rhs) | Operand::Move(rhs)) | Rvalue::CopyForDeref(rhs) =
//                 *rhs
//             && lhs == rhs
//         {
//             stmt.make_nop();
//         }
//     }
//     fn visit_body_preserves_cfg(&mut self, body: &mut Body<'tcx>) {}
//     fn visit_basic_block_data(&mut self, block: BasicBlock, data: &mut BasicBlockData<'tcx>) {
//         let BasicBlockData {
//             statements,
//             terminator,
//             is_cleanup: _,
//         } = data;
//     }
// }
