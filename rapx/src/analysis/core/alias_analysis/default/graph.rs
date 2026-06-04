use super::{MopFnAliasPairs, assign::*, block::*, types::*, value::*};
use crate::{
    graphs::{
        cfg::{CfgBlock, ControlFlowGraph},
        mop::{MeetOverPathsGraph, MopBlockInfo},
        scc::{Scc, SccInfo},
    },
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
use std::{fmt, vec::Vec};

#[derive(Clone)]
pub struct MopGraph<'tcx> {
    pub graph: MeetOverPathsGraph<'tcx>,
    // All values (including fields) of the function.
    // For general variables, we use its Local as the value index;
    // For fields, the value index is determined via auto increment.
    pub values: Vec<Value>,
    // Alias-analysis-specific facts extracted from each MIR block.
    pub block_facts: Vec<AliasBlockFacts<'tcx>>,
    // We record the constant value for path sensitivity.
    pub constants: FxHashMap<usize, usize>,
    // We record the decision of enumerate typed values for path sensitivity.
    pub discriminants: FxHashMap<usize, usize>,
    pub alias_sets: Vec<FxHashSet<usize>>,
    // contains the return results for inter-procedure analysis.
    pub ret_alias: MopFnAliasPairs,
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
        let mut cfg_blocks = Vec::<CfgBlock<'tcx>>::new();
        let mut mop_blocks = Vec::<MopBlockInfo>::new();
        let mut block_facts = Vec::<AliasBlockFacts<'tcx>>::new();
        let mut discriminants = FxHashMap::default();

        // handle each basicblock
        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut cfg_block = CfgBlock::new(i, bb.is_cleanup);
            let mut mop_block = MopBlockInfo::new(i);
            let mut alias_block = AliasBlockFacts::new();

            // handle general statements
            for stmt in &bb.statements {
                let span = stmt.source_info.span;
                match &stmt.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let lv_place = *place;
                        let lv_local = place.local.as_usize();
                        mop_block.assigned_locals.insert(lv_local);
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
                                            alias_block.assignments.push(assign);
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
                                            alias_block.assignments.push(assign);
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
                                                    alias_block.const_value.push(ConstValue::new(
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
                                                    alias_block.const_value.push(ConstValue::new(
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
                                    alias_block.assignments.push(assign);
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
                                            alias_block.assignments.push(assign);
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
                                        alias_block.assignments.push(assign);
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
                                        alias_block.assignments.push(assign);
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
                                                        alias_block.assignments.push(assign);
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
                                                                        .unwrap_or(lv_ty)
                                                                // fallback
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
                                                        alias_block.assignments.push(assign);
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
                                                        alias_block.assignments.push(assign);
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
                                alias_block.assignments.push(assign);
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
            cfg_block.terminator = Some(terminator.clone());
            // handle terminator statements
            match terminator.kind.clone() {
                TerminatorKind::Goto { ref target } => {
                    cfg_block.add_next(target.as_usize());
                }
                TerminatorKind::SwitchInt {
                    discr: _,
                    ref targets,
                } => {
                    for (_, ref target) in targets.iter() {
                        cfg_block.add_next(target.as_usize());
                    }
                    cfg_block.add_next(targets.otherwise().as_usize());
                }
                TerminatorKind::Drop {
                    place: _,
                    target,
                    unwind,
                    replace: _,
                    drop: _,
                    async_fut: _,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Call {
                    ref target,
                    ref unwind,
                    ..
                } => {
                    if let Some(tt) = target {
                        cfg_block.add_next(tt.as_usize());
                    }
                    if let UnwindAction::Cleanup(tt) = unwind {
                        cfg_block.add_next(tt.as_usize());
                    }
                }

                TerminatorKind::Assert {
                    cond: _,
                    expected: _,
                    msg: _,
                    ref target,
                    ref unwind,
                } => {
                    cfg_block.add_next(target.as_usize());
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::Yield {
                    value: _,
                    ref resume,
                    resume_arg: _,
                    ref drop,
                } => {
                    cfg_block.add_next(resume.as_usize());
                    if let Some(target) = drop {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                TerminatorKind::FalseEdge {
                    ref real_target,
                    imaginary_target: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
                }
                TerminatorKind::FalseUnwind {
                    ref real_target,
                    unwind: _,
                } => {
                    cfg_block.add_next(real_target.as_usize());
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
                        cfg_block.add_next(target.as_usize());
                    }
                    if let UnwindAction::Cleanup(target) = unwind {
                        cfg_block.add_next(target.as_usize());
                    }
                }
                _ => {}
            }
            cfg_blocks.push(cfg_block);
            mop_blocks.push(mop_block);
            block_facts.push(alias_block);
        }

        let cfg = ControlFlowGraph::new(def_id, tcx, body.span, arg_size, cfg_blocks);
        let graph = MeetOverPathsGraph::new(cfg, mop_blocks);

        MopGraph {
            graph,
            values,
            block_facts,
            alias_sets: Vec::<FxHashSet<usize>>::new(),
            constants: FxHashMap::default(),
            ret_alias: MopFnAliasPairs::new(arg_size),
            discriminants,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.graph.cfg.def_id
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.graph.cfg.tcx
    }

    pub fn arg_size(&self) -> usize {
        self.graph.cfg.arg_size
    }

    pub fn span(&self) -> Span {
        self.graph.cfg.span
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock<'tcx> {
        self.graph.cfg_block(index)
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock<'tcx> {
        self.graph.cfg_block_mut(index)
    }

    pub fn mop_block(&self, index: usize) -> &MopBlockInfo {
        self.graph.mop_block(index)
    }

    pub fn mop_block_mut(&mut self, index: usize) -> &mut MopBlockInfo {
        self.graph.mop_block_mut(index)
    }

    pub fn find_scc(&mut self) {
        self.graph.find_scc();
    }

    pub fn get_paths(&self) -> Vec<Vec<usize>> {
        self.graph.get_paths()
    }

    pub fn get_all_branch_sub_blocks_paths(&self) -> Vec<Vec<usize>> {
        self.graph.get_all_branch_sub_blocks_paths()
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.graph.sort_scc_tree(scc)
    }

    pub fn visit_times(&self) -> usize {
        self.graph.visit_times
    }

    pub fn increment_visit_times(&mut self) -> usize {
        self.graph.visit_times += 1;
        self.graph.visit_times
    }
}

// Implement Display for debugging / printing purposes.
// Prints selected fields: def_id, values, blocks, constants, discriminants, scc_indices, child_scc.
impl<'tcx> std::fmt::Display for MopGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "MopGraph {{")?;
        writeln!(f, "  def_id: {:?}", self.def_id())?;
        writeln!(f, "  values: {:?}", self.values)?;
        writeln!(f, "  cfg_blocks: {:?}", self.graph.cfg.blocks)?;
        writeln!(f, "  mop_blocks: {:?}", self.graph.blocks)?;
        writeln!(f, "  block_facts: {:?}", self.block_facts)?;
        writeln!(f, "  constants: {:?}", self.constants)?;
        writeln!(f, "  discriminants: {:?}", self.discriminants)?;
        write!(f, "}}")
    }
}
