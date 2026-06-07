use super::{MopFnAliasPairs, assign::*, block::*, types::*, value::*};
use crate::{
    analysis::core::path_analysis::graph::PathGraph,
    graphs::{
        cfg::CfgBlock,
        scc::SccInfo,
    },
    utils::source::*,
};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{AggregateKind, BasicBlock, Const, Operand, Rvalue, StatementKind, Terminator},
    ty::{self, TyCtxt, TypingEnv},
};
use rustc_span::{Span, def_id::DefId};
use std::{fmt, vec::Vec};

#[derive(Clone)]
pub struct AliasGraph<'tcx> {
    pub path_graph: PathGraph<'tcx>,
    /// Path-sensitive state used by alias/safedrop traversal.
    pub constants: FxHashMap<usize, usize>,
    /// Traversal visit counter for recursion limiting.
    pub visit_times: usize,
    // All values (including fields) of the function.
    // For general variables, we use its Local as the value index;
    // For fields, the value index is determined via auto increment.
    pub values: Vec<Value>,
    // Alias-analysis-specific facts extracted from each MIR block.
    pub block_facts: Vec<AliasBlockFacts<'tcx>>,
    pub alias_sets: Vec<FxHashSet<usize>>,
    // contains the return results for inter-procedure analysis.
    pub ret_alias: MopFnAliasPairs,
    pub arg_size: usize,
    pub span: Span,
}

pub type MopGraph<'tcx> = AliasGraph<'tcx>;

impl<'tcx> AliasGraph<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId) -> AliasGraph<'tcx> {
        let fn_name = get_fn_name(tcx, def_id);
        rap_debug!("New an AliasGraph for: {:?}", fn_name);
        let path_graph = PathGraph::new(tcx, def_id);
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
        let mut block_facts = Vec::<AliasBlockFacts<'tcx>>::new();

        // handle each basicblock
        for i in 0..basicblocks.len() {
            let bb = &basicblocks[BasicBlock::from(i)];
            let mut alias_block = AliasBlockFacts::new();

            // handle general statements
            for stmt in &bb.statements {
                let span = stmt.source_info.span;
                match &stmt.kind {
                    StatementKind::Assign(box (place, rvalue)) => {
                        let lv_place = *place;
                        let lv_local = place.local.as_usize();
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

            if bb.terminator.is_none() {
                rap_info!(
                    "Basic block BB{} has no terminator in function {:?}",
                    i,
                    fn_name
                );
                continue;
            }
            block_facts.push(alias_block);
        }

        AliasGraph {
            path_graph,
            constants: FxHashMap::default(),
            visit_times: 0,
            values,
            block_facts,
            alias_sets: Vec::<FxHashSet<usize>>::new(),
            ret_alias: MopFnAliasPairs::new(arg_size),
            arg_size,
            span: body.span,
        }
    }

    pub fn def_id(&self) -> DefId {
        self.path_graph.def_id()
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.path_graph.tcx()
    }

    pub fn arg_size(&self) -> usize {
        self.arg_size
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn cfg_block(&self, index: usize) -> &CfgBlock {
        self.path_graph.cfg_block(index)
    }

    pub fn cfg_block_mut(&mut self, index: usize) -> &mut CfgBlock {
        self.path_graph.cfg_block_mut(index)
    }

    /// Retrieve the MIR terminator for the block at `index` on demand.
    pub fn terminator(&self, index: usize) -> Option<&Terminator<'tcx>> {
        self.path_graph.terminator(index)
    }

    pub fn find_scc(&mut self) {
        self.path_graph.find_scc();
    }

    pub fn enumerate_paths(&mut self) -> Vec<Vec<usize>> {
        self.path_graph.enumerate_paths()
    }

    pub fn sort_scc_tree(&mut self, scc: &SccInfo) -> SccInfo {
        self.path_graph.sort_scc_tree(scc)
    }

    pub fn visit_times(&self) -> usize {
        self.visit_times
    }

    pub fn increment_visit_times(&mut self) -> usize {
        self.visit_times += 1;
        self.visit_times
    }

    pub fn assigned_locals(&self, index: usize) -> Option<&FxHashSet<usize>> {
        self.path_graph.assigned_locals(index)
    }
}

// Implement Display for debugging / printing purposes.
// Prints selected fields: def_id, values, blocks, constants, discriminants, scc_indices, child_scc.
impl<'tcx> std::fmt::Display for AliasGraph<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "AliasGraph {{")?;
        writeln!(f, "  def_id: {:?}", self.def_id())?;
        writeln!(f, "  values: {:?}", self.values)?;
        writeln!(f, "  cfg_blocks: {:?}", self.path_graph.cfg.blocks)?;
        writeln!(f, "  block_facts: {:?}", self.block_facts)?;
        writeln!(f, "  constants: {:?}", self.constants)?;
        writeln!(f, "  discriminants: {:?}", self.path_graph.discriminants)?;
        write!(f, "}}")
    }
}
