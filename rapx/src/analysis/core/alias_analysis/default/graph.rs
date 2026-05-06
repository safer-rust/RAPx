use super::{MopFnAliasPairs, assign::*, block::*, types::*, value::*};
use crate::{
    analysis::graphs::scc::{Scc, SccExit},
    def_id::*,
    utils::source::*,
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, Const, Operand, Rvalue, StatementKind, TerminatorKind,
        UnwindAction,
    },
    ty::{self, TyCtxt, TypingEnv},
};
use rustc_span::{Span, def_id::DefId};
use std::{
    fmt::{self, Display},
    vec::Vec,
};

#[derive(Clone)]
pub struct MopGraph<'tcx> {
    pub def_id: DefId,
    pub tcx: TyCtxt<'tcx>,
    // The field is used to detect dangling pointers in arguments after the function returns.
    pub arg_size: usize,
    pub span: Span,
    // All values (including fields) of the function.
    // For general variables, we use its Local as the value index;
    // For fields, the value index is determined via auto increment.
    pub values: Vec<Value>,
    // All blocks of the function;
    // Each block is initialized as a basic block of the mir;
    // The blocks are then aggregated into strongly-connected components.
    pub blocks: Vec<Block<'tcx>>,
    // We record the constant value for path sensitivity.
    pub constants: FxHashMap<usize, usize>,
    // We record the decision of enumerate typed values for path sensitivity.
    pub discriminants: FxHashMap<usize, usize>,
    // a threhold to avoid path explosion.
    pub visit_times: usize,
    pub alias_sets: Vec<FxHashSet<usize>>,
    // contains the return results for inter-procedure analysis.
    pub ret_alias: MopFnAliasPairs,
    pub terminators: Vec<TerminatorKind<'tcx>>,
}

impl<'tcx> MopGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> MopGraph<'tcx> {
        let fn_name = get_fn_name(tcx, def_id);
        rap_debug!("New a MopGraph for: {:?}", fn_name);
        // handle variables
        let body = tcx.optimized_mir(def_id);
        //display_mir(def_id, body);
        let locals = &body.local_decls;
        let arg_size = body.arg_count;
        let mut values = Vec::<Value>::new();
        let ty_env = TypingEnv::post_analysis(tcx, def_id);
        for (local, local_decl) in locals.iter_enumerated() {
            let need_drop = local_decl.ty.needs_drop(tcx, ty_env); // the type is drop
            let may_drop = !is_not_drop(tcx, local_decl.ty);
            let mut node = Value::new(
                local.as_usize(),
                local.as_usize(),
                need_drop,
                need_drop || may_drop,
            );
            node.kind = kind(local_decl.ty);
            values.push(node);
        }

        let basicblocks = &body.basic_blocks;
        let mut blocks = Vec::<Block<'tcx>>::new();
        let mut discriminants = FxHashMap::default();
        let mut terminators = Vec::new();

        // handle each basicblock
        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cur_bb = Block::new(i, bb.is_cleanup);

            // handle general statements
            for stmt in &bb.statements {
                let span = stmt.source_info.span;
                match &stmt.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let lv_place = *place;
                        let lv_local = place.local.as_usize();
                        cur_bb.assigned_locals.insert(lv_local);
                        match rvalue.clone() {
                            // rvalue is a Rvalue
                            Rvalue::Use(operand) => {
                                match operand {
                                    Operand::Copy(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::Copy,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Move(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::Move,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Constant(constant) => {
                                        /* We should check the correctness due to the update of rustc
                                         * https://doc.rust-lang.org/beta/nightly-rustc/rustc_middle/mir/enum.Const.html
                                         */
                                        match constant.const_ {
                                            Const::Ty(_ty, const_value) => {
                                                if let Some(val) =
                                                    const_value.try_to_target_usize(tcx)
                                                {
                                                    cur_bb.const_value.push(ConstValue::new(
                                                        lv_local,
                                                        val as usize,
                                                    ));
                                                }
                                            }
                                            Const::Unevaluated(_const_value, _ty) => {}
                                            Const::Val(const_value, _ty) => {
                                                if let Some(scalar) =
                                                    const_value.try_to_scalar_int()
                                                {
                                                    let val = scalar.to_uint(scalar.size());
                                                    cur_bb.const_value.push(ConstValue::new(
                                                        lv_local,
                                                        val as usize,
                                                    ));
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                            Rvalue::Ref(_, _, rv_place)
                            | Rvalue::RawPtr(_, rv_place)
                            | Rvalue::CopyForDeref(rv_place) => {
                                let rv_local = rv_place.local.as_usize();
                                if values[lv_local].may_drop && values[rv_local].may_drop {
                                    let assign =
                                        Assignment::new(lv_place, rv_place, AssignType::Copy, span);
                                    cur_bb.assignments.push(assign);
                                }
                            }
                            Rvalue::ShallowInitBox(operand, _) => {
                                /*
                                 * Original ShllowInitBox is a two-level pointer: lvl0 -> lvl1 -> lvl2
                                 * Since our alias analysis does not consider multi-level pointer,
                                 * We simplify it as: lvl0
                                 */
                                if !values[lv_local].fields.contains_key(&0) {
                                    let mut lvl0 = Value::new(values.len(), lv_local, false, true);
                                    lvl0.father = Some(FatherInfo::new(lv_local, 0));
                                    values[lv_local].fields.insert(0, lvl0.index);
                                    values.push(lvl0);
                                }
                                match operand {
                                    Operand::Copy(rv_place) | Operand::Move(rv_place) => {
                                        let rv_local = rv_place.local.as_usize();
                                        if values[lv_local].may_drop && values[rv_local].may_drop {
                                            let assign = Assignment::new(
                                                lv_place,
                                                rv_place,
                                                AssignType::InitBox,
                                                span,
                                            );
                                            cur_bb.assignments.push(assign);
                                        }
                                    }
                                    Operand::Constant(_) => {}
                                }
                            }
                            Rvalue::Cast(_, operand, _) => match operand {
                                Operand::Copy(rv_place) => {
                                    let rv_local = rv_place.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let assign = Assignment::new(
                                            lv_place,
                                            rv_place,
                                            AssignType::Copy,
                                            span,
                                        );
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Move(rv_place) => {
                                    let rv_local = rv_place.local.as_usize();
                                    if values[lv_local].may_drop && values[rv_local].may_drop {
                                        let assign = Assignment::new(
                                            lv_place,
                                            rv_place,
                                            AssignType::Move,
                                            span,
                                        );
                                        cur_bb.assignments.push(assign);
                                    }
                                }
                                Operand::Constant(_) => {}
                            },
                            Rvalue::Aggregate(kind, operands) => {
                                match kind.as_ref() {
                                    // For tuple aggregation such as _10 = (move _11, move _12)
                                    // we create `_10.0 = move _11` and `_10.1 = move _12` to achieve field sensitivity
                                    // and prevent transitive alias: (_10, _11) + (_10, _12) => (_11, _12)
                                    AggregateKind::Tuple => {
                                        let lv_ty = lv_place.ty(&body.local_decls, tcx).ty;
                                        for (field_idx, operand) in operands.iter_enumerated() {
                                            match operand {
                                                Operand::Copy(rv_place)
                                                | Operand::Move(rv_place) => {
                                                    let rv_local = rv_place.local.as_usize();
                                                    if values[lv_local].may_drop
                                                        && values[rv_local].may_drop
                                                    {
                                                        // Get field type from tuple or array
                                                        let field_ty = match lv_ty.kind() {
                                                            ty::Tuple(fields) => {
                                                                fields[field_idx.as_usize()]
                                                            }
                                                            _ => {
                                                                continue;
                                                            }
                                                        };

                                                        // Create lv.field_idx Place using tcx.mk_place_field
                                                        let lv_field_place = tcx.mk_place_field(
                                                            lv_place, field_idx, field_ty,
                                                        );

                                                        let assign = Assignment::new(
                                                            lv_field_place,
                                                            *rv_place,
                                                            if matches!(operand, Operand::Move(_)) {
                                                                AssignType::Move
                                                            } else {
                                                                AssignType::Copy
                                                            },
                                                            span,
                                                        );
                                                        cur_bb.assignments.push(assign);
                                                        rap_debug!(
                                                            "Aggregate field assignment: {:?}.{} = {:?}",
                                                            lv_place,
                                                            field_idx.as_usize(),
                                                            rv_place
                                                        );
                                                    }
                                                }
                                                Operand::Constant(_) => {
                                                    // Constants don't need alias analysis
                                                }
                                            }
                                        }
                                    }
                                    AggregateKind::Adt(_, _, _, _, _) => {
                                        // For ADTs (structs/enums), handle field assignments field-sensitively.
                                        // NOTE: Here we treat the ADT similarly to tuples,
                                        // but fields might be named and ADT type info is available, so more precise field indexing is possible if needed.
                                        let lv_ty = lv_place.ty(&body.local_decls, tcx).ty;
                                        for (field_idx, operand) in operands.iter_enumerated() {
                                            match operand {
                                                Operand::Copy(rv_place)
                                                | Operand::Move(rv_place) => {
                                                    let rv_local = rv_place.local.as_usize();
                                                    if values[lv_local].may_drop
                                                        && values[rv_local].may_drop
                                                    {
                                                        // If possible, resolve field type for better analysis. Here we use tuple logic as a template.
                                                        let field_ty = match lv_ty.kind() {
                                                            ty::Adt(adt_def, substs) => {
                                                                // Try getting the field type if available.
                                                                if field_idx.as_usize()
                                                                    < adt_def.all_fields().count()
                                                                {
                                                                    adt_def
                                                                        .all_fields()
                                                                        .nth(field_idx.as_usize())
                                                                        .map(|f| f.ty(tcx, substs))
                                                                        .unwrap_or(lv_ty) // fallback
                                                                } else {
                                                                    lv_ty
                                                                }
                                                            }
                                                            _ => lv_ty,
                                                        };

                                                        // Create lv.field_idx Place using tcx.mk_place_field, as for tuples.
                                                        let lv_field_place = tcx.mk_place_field(
                                                            lv_place, field_idx, field_ty,
                                                        );

                                                        let assign = Assignment::new(
                                                            lv_field_place,
                                                            *rv_place,
                                                            if matches!(operand, Operand::Move(_)) {
                                                                AssignType::Move
                                                            } else {
                                                                AssignType::Copy
                                                            },
                                                            span,
                                                        );
                                                        cur_bb.assignments.push(assign);
                                                        rap_debug!(
                                                            "Aggregate ADT field assignment: {:?}.{} = {:?}",
                                                            lv_place,
                                                            field_idx.as_usize(),
                                                            rv_place
                                                        );
                                                    }
                                                }
                                                Operand::Constant(_) => {
                                                    // Constants don't need alias analysis for this context.
                                                }
                                            }
                                        }
                                    }
                                    // TODO: Support alias for array
                                    AggregateKind::Array(_) => {}
                                    // For other aggregate types, simply create an assignment for each aggregated operand
                                    _ => {
                                        for operand in operands {
                                            match operand {
                                                Operand::Copy(rv_place)
                                                | Operand::Move(rv_place) => {
                                                    let rv_local = rv_place.local.as_usize();
                                                    if values[lv_local].may_drop
                                                        && values[rv_local].may_drop
                                                    {
                                                        let assign = Assignment::new(
                                                            lv_place,
                                                            rv_place,
                                                            AssignType::Copy,
                                                            span,
                                                        );
                                                        cur_bb.assignments.push(assign);
                                                    }
                                                }
                                                Operand::Constant(_) => {}
                                            }
                                        }
                                    }
                                }
                            }
                            Rvalue::Discriminant(rv_place) => {
                                let assign =
                                    Assignment::new(lv_place, rv_place, AssignType::Variant, span);
                                cur_bb.assignments.push(assign);
                                discriminants.insert(lv_local, rv_place.local.as_usize());
                            }
                            _ => {}
                        }
                    }
                    StatementKind::SetDiscriminant {
                        place: _,
                        variant_index: _,
                    } => {
                        rap_warn!("SetDiscriminant: {:?} is not handled in RAPx!", stmt);
                    }
                    _ => {}
                }
            }

            let Some(terminator) = &bb.terminator else {
                rap_info!(
                    "Basic block BB{} has no terminator in function {:?}",
                    i,
                    fn_name
                );
                continue;
            };
            terminators.push(terminator.kind.clone());
            // handle terminator statements
            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target } => {
                    cur_bb.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    cur_bb.terminator = Term::Switch(terminator.clone());
                    for (_, ref target) in targets.iter() {
                        cur_bb.add_next(target.as_usize());
                    }
                    cur_bb.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    cur_bb.add_next(target.as_usize());
                    cur_bb.terminator = Term::Drop(terminator.clone());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref func,
                    args: _,
                    destination: _,
                    ref target,
                    ref unwind,
                    call_source: _,
                    fn_span: _,
                } => {
                    if let Operand::Constant(c) = func {
                        if let &ty::FnDef(id, ..) = c.ty().kind() {
                            if is_drop_fn(id) {
                                cur_bb.terminator = Term::Drop(terminator.clone());
                            } else {
                                cur_bb.terminator = Term::Call(terminator.clone());
                            }
                        }
                    } else {
                        cur_bb.terminator = Term::Call(terminator.clone());
                    }
                    if let Some(tt) = target {
                        cur_bb.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cur_bb.add_next(tt.as_usize());
                    }
                }

                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cur_bb.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cur_bb.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cur_bb.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cur_bb.add_next(real_target.as_usize());
                }
                TerminatorKind::InlineAsm {
                    template: _,
                    operands: _,
                    options: _,
                    line_spans: _,
                    ref unwind,
                    targets,
                    asm_macro: _,
                } => {
                    for target in targets {
                        cur_bb.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cur_bb.add_next(target.as_usize());
                    }
                }
                _ => {}
            }
            blocks.push(cur_bb);
        }

        MopGraph {
            def_id,
            tcx,
            span: body.span,
            blocks,
            values,
            arg_size,
            alias_sets: Vec::<FxHashSet<usize>>::new(),
            constants: FxHashMap::default(),
            ret_alias: MopFnAliasPairs::new(arg_size),
            visit_times: 0,
            discriminants,
            terminators,
        }
    }

    /// Enumerate acyclic CFG paths from the current block to an exit block.
    ///
    /// MIR loops are represented as back edges in `Block::next`. The path
    /// consumer only needs one finite traversal that reaches each unsafe
    /// callsite, so this DFS cuts a path when it would revisit a block already
    /// on the current stack. Non-cycle successors are still explored, which
    /// keeps loop exits visible without risking unbounded path growth.
    pub fn dfs_on_spanning_tree(
        &self,
        index: usize,
        stack: &mut Vec<usize>,
        paths: &mut Vec<Vec<usize>>,
    ) {
        const PATH_ENUM_LIMIT: usize = 4000;

        if paths.len() >= PATH_ENUM_LIMIT {
            return;
        }
        if index >= self.blocks.len() {
            return;
        }

        let mut nexts: Vec<usize> = self.blocks[index].next.iter().copied().collect();
        nexts.sort_unstable();

        if nexts.is_empty() {
            paths.push(stack.clone());
            return;
        }

        let mut followed = false;
        for next in nexts {
            if paths.len() >= PATH_ENUM_LIMIT {
                break;
            }
            if next >= self.blocks.len() {
                continue;
            }
            if stack.contains(&next) {
                paths.push(stack.clone());
                continue;
            }

            followed = true;
            stack.push(next);
            self.dfs_on_spanning_tree(next, stack, paths);
            stack.pop();
        }

        if !followed {
            paths.push(stack.clone());
        }
    }

    /// Return all finite MIR CFG paths starting from the entry block.
    pub fn get_paths(&self) -> Vec<Vec<usize>> {
        let mut paths: Vec<Vec<usize>> = Vec::new();
        if self.blocks.is_empty() {
            return paths;
        }
        let mut stack: Vec<usize> = vec![0];
        self.dfs_on_spanning_tree(0, &mut stack, &mut paths);
        paths
    }
    pub fn get_all_branch_sub_blocks_paths(&self) -> Vec<Vec<usize>> {
        // 1. Get all execution paths
        let all_paths = self.get_paths();

        // Use FxHashSet to collect all unique lists of dominated_scc_bbs.
        // Vec<usize> implements Hash, so it can be inserted directly into the set.
        let mut unique_branch_sub_blocks = FxHashSet::<Vec<usize>>::default();

        // 2. Iterate over each path
        for path in all_paths {
            // 3. For the current path, get the corresponding dominated_scc_bbs for branch nodes
            let branch_blocks_for_this_path = self.get_branch_sub_blocks_for_path(&path);
            rap_debug!(
                "Branch blocks for path {:?}: {:?}",
                path,
                branch_blocks_for_this_path
            );
            // 4. Add these dominated_scc_bbs to the set
            //    Use insert to avoid duplicates
            unique_branch_sub_blocks.insert(branch_blocks_for_this_path);
        }

        // 5. Convert the set of unique results back to a Vec and return
        unique_branch_sub_blocks.into_iter().collect()
    }

    pub fn get_branch_sub_blocks_for_path(&self, path: &[usize]) -> Vec<usize> {
        let mut expanded_path = Vec::new();
        // Use FxHashSet to track which SCCs have already been expanded in this path,
        // preventing repeated expansion due to cycles.
        let mut processed_scc_indices = FxHashSet::default();

        for &block_idx in path {
            // 1. Get the representative SCC index of the current basic block
            let scc_idx = self.blocks[block_idx].scc.enter;

            // 2. Try inserting scc_idx into the set. If successful (returns true),
            // it means this SCC is encountered for the first time.
            if processed_scc_indices.insert(scc_idx) {
                // First time encountering this SCC: perform full expansion

                // a. First, add the SCC representative itself to the path
                expanded_path.push(scc_idx);

                // b. Then, retrieve the SCC node information
                let scc_enter = &self.blocks[scc_idx];

                // c. If it has sub-blocks (i.e., it’s a multi-node SCC),
                // append all sub-blocks to the path.
                // dominated_scc_bbs are already ordered (topologically or near-topologically)
                if !scc_enter.scc.nodes.is_empty() {
                    //expanded_path.extend_from_slice(&scc_enter.scc.nodes);
                }
            } else {
                // SCC already seen before (e.g., due to a cycle in the path):
                // Only add the representative node as a connector, skip internal blocks.
                expanded_path.push(scc_idx);
            }
        }

        expanded_path
    }
}

pub trait SccHelper<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx>;
    fn defid(&self) -> DefId;
    fn blocks(&self) -> &Vec<Block<'tcx>>; // or whatever the actual type is
    fn blocks_mut(&mut self) -> &mut Vec<Block<'tcx>>;
}

impl<'tcx> SccHelper<'tcx> for MopGraph<'tcx> {
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }
    fn defid(&self) -> DefId {
        self.def_id
    }
    fn blocks(&self) -> &Vec<Block<'tcx>> {
        &self.blocks
    }
    fn blocks_mut(&mut self) -> &mut Vec<Block<'tcx>> {
        &mut self.blocks
    }
}

pub fn scc_handler<'tcx, T: SccHelper<'tcx> + Scc + Clone + Display>(
    graph: &mut T,
    root: usize,
    scc_components: &[usize],
) {
    rap_debug!(
        "Scc found: root = {}, components = {:?}",
        root,
        scc_components
    );
    graph.blocks_mut()[root].scc.enter = root;
    if scc_components.len() <= 1 {
        return;
    }

    // If the scc enter is also an exit of the scc; add it to the scc exit;
    let nexts = graph.blocks_mut()[root].next.clone();
    for next in nexts {
        if !&scc_components.contains(&next) {
            let scc_exit = SccExit::new(root, next);
            graph.blocks_mut()[root].scc.exits.insert(scc_exit);
        }
    }
    // Handle other nodes of the scc;
    for &node in &scc_components[1..] {
        graph.blocks_mut()[root].scc.nodes.insert(node);
        graph.blocks_mut()[node].scc.enter = root;
        let nexts = graph.blocks_mut()[node].next.clone();
        for next in nexts {
            // The node is an scc exit.
            if !&scc_components.contains(&next) {
                let scc_exit = SccExit::new(node, next);
                graph.blocks_mut()[root].scc.exits.insert(scc_exit);
            }
            // The node initiates a back edge to the scc enter.
            if next == root {
                graph.blocks_mut()[root].scc.backnodes.insert(node);
            }
        }
    }

    rap_debug!("Scc Info: {:?}", graph.blocks_mut()[root].scc);
    // Recursively detect sub sccs within the scc.
    // This is performed on a modified graph with the starting node and scc components only;
    // Before modification, we have to backup corresponding information.
    let mut backups: Vec<(usize, FxHashSet<usize>)> = Vec::new();

    let block0 = &mut graph.blocks_mut()[0];
    backups.push((0, block0.next.clone()));

    // Change the next of block0 to the scc enter.
    block0.next.clear();
    block0.next.insert(root);

    let scc_exits = graph.blocks()[root].scc.exits.clone();
    let backnodes = graph.blocks()[root].scc.backnodes.clone();

    for &node in scc_components.iter() {
        let block = &mut graph.blocks_mut()[node];
        if backnodes.contains(&node) {
            backups.push((node, block.next.clone()));
            block.next.remove(&root);
        }
    }
    // isolate the scc components from other parts of the graph.
    for exit in &scc_exits {
        let block_to = &mut graph.blocks_mut()[exit.to];
        backups.push((exit.to, block_to.next.clone()));
        block_to.next.clear();
    }
    graph.find_scc();

    // Restore the original graph.
    for backup in &backups {
        graph.blocks_mut()[backup.0].next = backup.1.clone();
    }
}

impl<'tcx> Scc for MopGraph<'tcx> {
    fn on_scc_found(&mut self, root: usize, scc_components: &[usize]) {
        scc_handler(self, root, scc_components);
    }
    fn get_next(&mut self, root: usize) -> FxHashSet<usize> {
        self.blocks[root].next.clone()
    }
    fn get_size(&mut self) -> usize {
        self.blocks.len()
    }
}

// Implement Display for debugging / printing purposes.
// Prints selected fields: def_id, values, blocks, constants, discriminants, scc_indices, child_scc.
impl<'tcx> std::fmt::Display for MopGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MopGraph {{")?;
        writeln!(f, "  def_id: {:?}", self.def_id)?;
        writeln!(f, "  values: {:?}", self.values)?;
        writeln!(f, "  blocks: {:?}", self.blocks)?;
        writeln!(f, "  constants: {:?}", self.constants)?;
        writeln!(f, "  discriminants: {:?}", self.discriminants)?;
        writeln!(f, "  terminators: {:?}", self.terminators)?;
        write!(f, "}}")
    }
}
