use crate::{
    analysis::{
        Analysis,
        core::{
            alias_analysis::FnAliasPairs,
            ownedheap_analysis::OHAResultMap,
            range_analysis::{RangeAnalysis, default::RangeAnalyzer},
        },
        graphs::scc::Scc,
        safedrop::graph::SafeDropGraph,
        senryx::{
            contracts::{
                abstract_state::AlignState,
                property::{CisRangeItem, PropertyContract},
            },
            dominated_graph::FunctionSummary,
            symbolic_analysis::{AnaOperand, SymbolicDef, ValueDomain},
        },
        utils::{
            draw_dot::{DotGraph, render_dot_string},
            fn_info::*,
            show_mir::display_mir,
        },
    },
    rap_debug, rap_warn,
};
use rustc_middle::ty::GenericParamDefKind;
use serde::de;
use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
};
use syn::Constraint;

use super::dominated_graph::DominatedGraph;
use super::dominated_graph::InterResultNode;
use super::generic_check::GenericChecker;
use super::matcher::UnsafeApi;
use super::matcher::{get_arg_place, parse_unsafe_api};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        self, AggregateKind, BasicBlock, BasicBlockData, BinOp, CastKind, Local, Operand, Place,
        ProjectionElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    ty::{self, GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, source_map::Spanned};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct CheckResult {
    pub func_name: String,
    pub func_span: Span,
    pub failed_contracts: HashMap<usize, HashSet<String>>,
    pub passed_contracts: HashMap<usize, HashSet<String>>,
}

impl CheckResult {
    /// Create a new CheckResult for a function.
    /// func_name: cleaned function path, func_span: source span of the function.
    pub fn new(func_name: &str, func_span: Span) -> Self {
        Self {
            func_name: func_name.to_string(),
            func_span,
            failed_contracts: HashMap::new(),
            passed_contracts: HashMap::new(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum PlaceTy<'tcx> {
    Ty(usize, usize), // layout(align,size) of one specific type
    GenericTy(String, HashSet<Ty<'tcx>>, HashSet<(usize, usize)>), // get specific type in generic map
    Unknown,
}

impl<'tcx> PlaceTy<'tcx> {
    /// Return the set of possible ABI alignments for this place/type.
    /// - For concrete types returns a single-element set with the ABI alignment.
    /// - For generic type parameters returns all candidate alignments collected from
    ///   the generic instantiation set.
    pub fn possible_aligns(&self) -> HashSet<usize> {
        match self {
            PlaceTy::Ty(align, _size) => {
                let mut set = HashSet::new();
                set.insert(*align);
                set
            }
            PlaceTy::GenericTy(_, _, tys) => tys.iter().map(|ty| ty.0).collect(),
            _ => HashSet::new(),
        }
    }
}

impl<'tcx> Hash for PlaceTy<'tcx> {
    /// Custom hash implementation placeholder for `PlaceTy`.
    /// Currently a no-op because `PlaceTy` is used primarily as a key in internal
    /// analysis maps where exact hashing is not required. This keeps behavior stable.
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}

/// Visitor that traverses MIR body and builds symbolic and pointer chains.
/// Holds analysis state such as type mappings, value domains and constraints.
pub struct BodyVisitor<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub def_id: DefId,
    pub safedrop_graph: SafeDropGraph<'tcx>,
    pub local_ty: HashMap<usize, PlaceTy<'tcx>>,
    pub visit_time: usize,
    pub check_results: Vec<CheckResult>,
    pub generic_map: HashMap<String, HashSet<Ty<'tcx>>>,
    pub proj_ty: HashMap<usize, Ty<'tcx>>,
    pub chains: DominatedGraph<'tcx>,
    pub value_domains: HashMap<usize, ValueDomain<'tcx>>,
    pub path_constraints: Vec<SymbolicDef<'tcx>>,
}

// === Partition: Initialization & state ===
// Initialization and visitor state: constructors, field maps and helpers used globally
// by subsequent analysis phases.
impl<'tcx> BodyVisitor<'tcx> {
    /// Construct a new BodyVisitor for `def_id`.
    /// Initializes helper structures and generic type map.
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, visit_time: usize) -> Self {
        let body = tcx.optimized_mir(def_id);
        let param_env = tcx.param_env(def_id);
        let satisfied_ty_map_for_generic =
            GenericChecker::new(tcx, param_env).get_satisfied_ty_map();
        let mut chains = DominatedGraph::new(tcx, def_id);
        chains.init_arg();
        Self {
            tcx,
            def_id,
            safedrop_graph: SafeDropGraph::new(tcx, def_id, OHAResultMap::default()),
            local_ty: HashMap::new(),
            visit_time,
            check_results: Vec::new(),
            generic_map: satisfied_ty_map_for_generic,
            proj_ty: HashMap::new(),
            chains,
            value_domains: HashMap::new(),
            path_constraints: Vec::new(),
        }
    }
}

/// === Partition: Path-sensitive analysis driver ===
/// Compute and iterate control-flow paths and merge results.
impl<'tcx> BodyVisitor<'tcx> {
    /// Perform path-sensitive forward analysis.
    /// Uses Tarjan-produced paths and performs per-path symbolic and pointer analysis.
    /// Returns an InterResultNode merging all path results.
    pub fn path_forward_check(
        &mut self,
        fn_map: &FxHashMap<DefId, FnAliasPairs>,
    ) -> InterResultNode<'tcx> {
        let mut inter_return_value =
            InterResultNode::construct_from_var_node(self.chains.clone(), 0);
        if self.visit_time >= 1000 {
            return inter_return_value;
        }
        // get path and body
        let paths = self.get_all_paths();
        let body = self.tcx.optimized_mir(self.def_id);
        let target_name = get_cleaned_def_path_name(self.tcx, self.def_id);
        // initialize local vars' types
        let locals = body.local_decls.clone();
        for (idx, local) in locals.iter().enumerate() {
            let local_ty = local.ty;
            let layout = self.visit_ty_and_get_layout(local_ty);
            self.local_ty.insert(idx, layout);
        }

        // Iterate all the paths. Paths have been handled by tarjan.
        let tmp_chain = self.chains.clone();
        for (index, (path, constraint)) in paths.iter().enumerate() {
            // Init three data structures in every path
            self.value_domains.clear();
            for (arg_index, _) in body.args_iter().enumerate() {
                let local = arg_index + 1;
                self.record_value_def(local, SymbolicDef::Param(local));
            }
            self.path_constraints = Vec::new();
            self.chains = tmp_chain.clone();
            self.set_constraint(constraint);
            for (i, block_index) in path.iter().enumerate() {
                if block_index >= &body.basic_blocks.len() {
                    continue;
                }
                let next_block = path.get(i + 1).cloned();
                self.path_analyze_block(
                    &body.basic_blocks[BasicBlock::from_usize(*block_index)].clone(),
                    index,
                    *block_index,
                    next_block,
                    fn_map,
                );
                let tem_basic_blocks = &self.safedrop_graph.mop_graph.blocks[*block_index]
                    .scc
                    .nodes
                    .clone();
                // also analyze basic blocks that belong to dominated SCCs
                if tem_basic_blocks.len() > 0 {
                    for sub_block in tem_basic_blocks {
                        self.path_analyze_block(
                            &body.basic_blocks[BasicBlock::from_usize(*sub_block)].clone(),
                            index,
                            *block_index,
                            next_block,
                            fn_map,
                        );
                    }
                }
            }

            // Used for debug
            // If running detailed (visit_time == 0), show debug reports.
            if self.visit_time == 0 {
                // self.display_combined_debug_info();
            }

            // merge path analysis results
            let curr_path_inter_return_value =
                InterResultNode::construct_from_var_node(self.chains.clone(), 0);
            inter_return_value.merge(curr_path_inter_return_value);
        }

        inter_return_value
    }

    /// Analyze one basic block: process statements then its terminator for the current path.
    pub fn path_analyze_block(
        &mut self,
        block: &BasicBlockData<'tcx>,
        path_index: usize,
        bb_index: usize,
        next_block: Option<usize>,
        fn_map: &FxHashMap<DefId, FnAliasPairs>,
    ) {
        for statement in block.statements.iter() {
            self.path_analyze_statement(statement, path_index);
        }
        self.path_analyze_terminator(
            &block.terminator(),
            path_index,
            bb_index,
            next_block,
            fn_map,
        );
    }

    /// Retrieve all paths and optional range-based constraints for this function.
    /// Falls back to safedrop graph paths if range analysis did not produce constraints.
    pub fn get_all_paths(&mut self) -> HashMap<Vec<usize>, Vec<(Place<'tcx>, Place<'tcx>, BinOp)>> {
        let mut range_analyzer = RangeAnalyzer::<i64>::new(self.tcx, false);
        let path_constraints_option =
            range_analyzer.start_path_constraints_analysis_for_defid(self.def_id); // if def_id does not exist, this will break down
        let mut path_constraints: HashMap<Vec<usize>, Vec<(_, _, _)>> =
            if path_constraints_option.is_none() {
                let mut results = HashMap::new();
                let paths: Vec<Vec<usize>> = self.safedrop_graph.mop_graph.get_paths();
                for path in paths {
                    results.insert(path, Vec::new());
                }
                results
            } else {
                path_constraints_option.unwrap()
            };
        self.safedrop_graph.mop_graph.find_scc();
        // If this is the top-level analysis, keep only paths that contain unsafe calls.
        if self.visit_time == 0 {
            let contains_unsafe_blocks = get_all_std_unsafe_callees_block_id(self.tcx, self.def_id);
            path_constraints.retain(|path, cons| {
                path.iter()
                    .any(|block_id| contains_unsafe_blocks.contains(block_id))
            });
        }
        path_constraints
    }
}

// === Partition: Statement and Rvalue handlers ===
// Assignment and rvalue processing, symbolic defs and chains.
impl<'tcx> BodyVisitor<'tcx> {
    /// Dispatch analysis for a single MIR statement (assignments, intrinsics, etc.).
    pub fn path_analyze_statement(&mut self, statement: &Statement<'tcx>, _path_index: usize) {
        // Examine MIR statements and dispatch to specific handlers.
        match statement.kind {
            StatementKind::Assign(box (ref lplace, ref rvalue)) => {
                self.path_analyze_assign(lplace, rvalue, _path_index);
            }
            StatementKind::Intrinsic(box ref intrinsic) => match intrinsic {
                mir::NonDivergingIntrinsic::CopyNonOverlapping(cno) => {
                    if cno.src.place().is_some() && cno.dst.place().is_some() {
                        let _src_pjc_local =
                            self.handle_proj(true, cno.src.place().unwrap().clone());
                        let _dst_pjc_local =
                            self.handle_proj(true, cno.dst.place().unwrap().clone());
                    }
                }
                _ => {}
            },
            StatementKind::StorageDead(local) => {}
            _ => {}
        }
    }

    /// Handle assignment rvalues: record symbolic defs and update pointer/alias chains.
    pub fn path_analyze_assign(
        &mut self,
        lplace: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        path_index: usize,
    ) {
        let lpjc_local = self.handle_proj(false, lplace.clone());
        match rvalue {
            Rvalue::Use(op) => {
                if let Some(ana_op) = self.lift_operand(op) {
                    let def = match ana_op {
                        AnaOperand::Local(src) => SymbolicDef::Use(src),
                        AnaOperand::Const(val) => SymbolicDef::Constant(val),
                    };
                    self.record_value_def(lpjc_local, def);
                }
                match op {
                    Operand::Move(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        self.chains.merge(lpjc_local, rpjc_local);
                    }
                    Operand::Copy(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        self.chains.copy_node(lpjc_local, rpjc_local);
                    }
                    _ => {}
                }
            }
            Rvalue::Repeat(op, _const) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::Ref(_, _, rplace) | Rvalue::RawPtr(_, rplace) => {
                // Recording that the left-hand side is a reference to right-hand side.
                let rpjc_local = self.handle_proj(true, rplace.clone());
                self.record_value_def(lpjc_local, SymbolicDef::Ref(rpjc_local));
                self.chains.point(lpjc_local, rpjc_local);
            }
            // ThreadLocalRef: x = &thread_local_static
            Rvalue::ThreadLocalRef(_def_id) => {
                // todo
            }
            // Cast: x = y as T
            Rvalue::Cast(cast_kind, op, ty) => {
                if let Some(AnaOperand::Local(src_idx)) = self.lift_operand(op) {
                    self.record_value_def(
                        lpjc_local,
                        SymbolicDef::Cast(src_idx, format!("{:?}", cast_kind)),
                    );
                }
                match op {
                    Operand::Move(rplace) | Operand::Copy(rplace) => {
                        let rpjc_local = self.handle_proj(true, rplace.clone());
                        let r_point_to = self.chains.get_point_to_id(rpjc_local);
                        if r_point_to == rpjc_local {
                            self.chains.merge(lpjc_local, rpjc_local);
                        } else {
                            self.chains.point(lpjc_local, r_point_to);
                        }
                    }
                    _ => {}
                }
            }
            Rvalue::BinaryOp(bin_op, box (op1, op2)) => {
                // Binary operator: try to form a symbolic binary definition when possible.
                if let (Some(ana_op1), Some(ana_op2)) =
                    (self.lift_operand(op1), self.lift_operand(op2))
                {
                    // Handle pointer offset operations specially
                    if *bin_op == BinOp::Offset {
                        if let AnaOperand::Local(base) = ana_op1 {
                            let base_ty = self.get_ptr_pointee_layout(base);
                            self.record_value_def(
                                lpjc_local,
                                SymbolicDef::PtrOffset(*bin_op, base, ana_op2, base_ty),
                            );
                            return;
                        }
                    }
                    // Handle other binary operations
                    let def = match (ana_op1.clone(), ana_op2) {
                        (AnaOperand::Local(l), rhs) => Some(SymbolicDef::Binary(*bin_op, l, rhs)),
                        (AnaOperand::Const(_), AnaOperand::Local(l)) => match bin_op {
                            BinOp::Add
                            | BinOp::Mul
                            | BinOp::BitAnd
                            | BinOp::BitOr
                            | BinOp::BitXor
                            | BinOp::Eq
                            | BinOp::Ne => Some(SymbolicDef::Binary(*bin_op, l, ana_op1)),
                            _ => None,
                        },
                        _ => None,
                    };

                    if let Some(d) = def {
                        self.record_value_def(lpjc_local, d);
                    } else if let (AnaOperand::Const(c), AnaOperand::Local(l)) = (
                        self.lift_operand(op1).unwrap(),
                        self.lift_operand(op2).unwrap(),
                    ) {
                        if matches!(bin_op, BinOp::Add | BinOp::Mul | BinOp::Eq) {
                            self.record_value_def(
                                lpjc_local,
                                SymbolicDef::Binary(*bin_op, l, AnaOperand::Const(c)),
                            );
                        }
                    }
                }
            }
            // NullaryOp: x = SizeOf(T); This is runtime checks
            Rvalue::NullaryOp(_null_op) => {
                // todo
            }
            // UnaryOp: x = !y / x = -y
            Rvalue::UnaryOp(un_op, op) => {
                // Unary op: record unary operation on LHS (operand value not stored here).
                self.record_value_def(lpjc_local, SymbolicDef::UnOp(*un_op));
            }
            // Discriminant: x = discriminant(y); read enum tag
            Rvalue::Discriminant(_place) => {
                // todo
            }
            // Aggregate: x = (y, z) / x = [y, z] / x = S { f: y }
            Rvalue::Aggregate(box agg_kind, op_vec) => match agg_kind {
                AggregateKind::Array(_ty) => {}
                AggregateKind::Adt(_adt_def_id, _, _, _, _) => {
                    for (idx, op) in op_vec.into_iter().enumerate() {
                        let (is_const, val) = get_arg_place(op);
                        if is_const {
                            self.chains.insert_field_node(
                                lpjc_local,
                                idx,
                                Some(Ty::new_uint(self.tcx, rustc_middle::ty::UintTy::Usize)),
                            );
                        } else {
                            let node = self.chains.get_var_node_mut(lpjc_local).unwrap();
                            node.field.insert(idx, val);
                        }
                    }
                }
                _ => {}
            },
            Rvalue::ShallowInitBox(op, _ty) => match op {
                Operand::Move(rplace) | Operand::Copy(rplace) => {
                    let _rpjc_local = self.handle_proj(true, rplace.clone());
                }
                _ => {}
            },
            Rvalue::CopyForDeref(p) => {
                let op = Operand::Copy(p.clone());
                if let Some(ana_op) = self.lift_operand(&op) {
                    let def = match ana_op {
                        AnaOperand::Local(src) => SymbolicDef::Use(src),
                        AnaOperand::Const(val) => SymbolicDef::Constant(val),
                    };
                    self.record_value_def(lpjc_local, def);
                }
            }
            _ => {}
        }
    }

    /// Get the layout of the pointee type of a pointer or reference.
    pub fn get_ptr_pointee_layout(&self, ptr_local: usize) -> PlaceTy<'tcx> {
        if let Some(node) = self.chains.get_var_node(ptr_local) {
            if let Some(ty) = node.ty {
                if is_ptr(ty) || is_ref(ty) {
                    let pointee = get_pointee(ty);
                    return self.visit_ty_and_get_layout(pointee);
                }
            }
        }
        PlaceTy::Unknown
    }
}

/// === Partition: Terminator handling ===
/// Terminator handling: calls, drops and branch-switch translation into constraints.
impl<'tcx> BodyVisitor<'tcx> {
    /// Analyze a MIR terminator (calls, drops, switches, etc.) for a path.
    /// Updates chains/value domains based on call, drop and switch semantics.
    pub fn path_analyze_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        path_index: usize,
        bb_index: usize,
        next_block: Option<usize>,
        fn_map: &FxHashMap<DefId, FnAliasPairs>,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination: dst_place,
                target: _,
                unwind: _,
                call_source: _,
                fn_span,
            } => {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, raw_list) = func_constant.const_.ty().kind() {
                        let mut mapping = FxHashMap::default();
                        self.get_generic_mapping(raw_list.as_slice(), callee_def_id, &mut mapping);
                        rap_debug!(
                            "func {:?}, generic type mapping {:?}",
                            callee_def_id,
                            mapping
                        );
                        self.handle_call(
                            dst_place,
                            callee_def_id,
                            args,
                            path_index,
                            fn_map,
                            *fn_span,
                            mapping,
                        );
                    }
                }
            }
            TerminatorKind::Drop {
                place,
                target: _,
                unwind: _,
                replace: _,
                drop: _,
                async_fut: _,
            } => {
                // Handle explicit drop: mark variable as dropped in chain graph.
                let drop_local = self.handle_proj(false, *place);
                if !self.chains.set_drop(drop_local) {
                    // double-drop detected; optionally warn for debugging.
                    // rap_warn!(
                    //     "In path {:?}, double drop {drop_local} in block {bb_index}",
                    //     self.paths[path_index]
                    // );
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                if let Some(next_bb) = next_block {
                    self.handle_switch_int(discr, targets, next_bb);
                }
            }
            _ => {}
        }
    }

    /// Return the MIR type of a local given its numeric `p` index.
    pub fn get_ty_by_place(&self, p: usize) -> Ty<'tcx> {
        let body = self.tcx.optimized_mir(self.def_id);
        let locals = body.local_decls.clone();
        return locals[Local::from(p)].ty;
    }

    /// Update field state graph from an inter-procedural result node.
    pub fn update_fields_states(&mut self, inter_result: InterResultNode<'tcx>) {
        self.chains.init_self_with_inter(inter_result);
    }

    /// Get the generic name to an actual type mapping when used for a def_id.
    /// If current def_id doesn't have generic, then search its parent.
    /// The generic set include type and allocator.
    /// Example: generic_mapping (T -> u32, A -> std::alloc::Global)
    fn get_generic_mapping(
        &self,
        raw_list: &[rustc_middle::ty::GenericArg<'tcx>],
        def_id: &DefId,
        generic_mapping: &mut FxHashMap<String, Ty<'tcx>>,
    ) {
        let generics = self.tcx.generics_of(def_id);
        for param in &generics.own_params {
            if let GenericParamDefKind::Type {
                has_default: _,
                synthetic: _,
            } = param.kind
            {
                if let Some(ty) = raw_list.get(param.index as usize) {
                    if let GenericArgKind::Type(actual_ty) = (*ty).kind() {
                        let param_name = param.name.to_string();
                        generic_mapping.insert(param_name, actual_ty);
                    }
                }
            }
        }
        if generics.own_params.len() == 0 && generics.parent.is_some() {
            let parent_def_id = generics.parent.unwrap();
            self.get_generic_mapping(raw_list, &parent_def_id, generic_mapping);
        }
    }

    /// Handle a function call: record symbolic Call, check unsafe contracts, and merge aliases.
    pub fn handle_call(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        args: &Box<[Spanned<Operand<'tcx>>]>,
        path_index: usize,
        fn_map: &FxHashMap<DefId, FnAliasPairs>,
        fn_span: Span,
        generic_mapping: FxHashMap<String, Ty<'tcx>>,
    ) {
        // Record call as a symbolic definition for the destination local.
        let dst_local = self.handle_proj(false, *dst_place);
        let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
        let mut call_arg_indices = Vec::new();
        for arg in args.iter() {
            if let Some(ana_op) = self.lift_operand(&arg.node) {
                call_arg_indices.push(ana_op);
            }
        }
        self.record_value_def(dst_local, SymbolicDef::Call(func_name, call_arg_indices));

        if !self.tcx.is_mir_available(def_id) {
            return;
        }

        // Find std unsafe API call, then check the contracts.
        if let Some(fn_result) =
            parse_unsafe_api(get_cleaned_def_path_name(self.tcx, *def_id).as_str())
        {
            self.handle_std_unsafe_call(
                dst_place,
                def_id,
                args,
                path_index,
                fn_map,
                fn_span,
                fn_result,
                generic_mapping,
            );
        }

        self.handle_offset_call(dst_place, def_id, args);

        self.set_bound(def_id, dst_place, args);

        // merge alias results
        self.handle_ret_alias(dst_place, def_id, fn_map, args);
    }

    /// For certain library calls (e.g. `slice::len`), bind computed values into object contracts.
    fn set_bound(
        &mut self,
        def_id: &DefId,
        dst_place: &Place<'tcx>,
        args: &Box<[Spanned<Operand>]>,
    ) {
        if args.len() == 0 || !get_cleaned_def_path_name(self.tcx, *def_id).contains("slice::len") {
            return;
        }
        let d_local = self.handle_proj(false, dst_place.clone());
        let ptr_local = get_arg_place(&args[0].node).1;
        let mem_local = self.chains.get_point_to_id(ptr_local);
        let mem_var = self.chains.get_var_node_mut(mem_local).unwrap();
        for cis in &mut mem_var.cis.contracts {
            if let PropertyContract::InBound(cis_ty, len) = cis {
                *len = CisRangeItem::new_var(d_local);
            }
        }
    }

    /// Merge function-level alias results into internal chains and value domains.
    /// Uses cached alias analysis (FnAliasPairs) to connect return/arg relationships.
    pub fn handle_ret_alias(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        fn_map: &FxHashMap<DefId, FnAliasPairs>,
        args: &Box<[Spanned<Operand>]>,
    ) {
        let d_local = self.handle_proj(false, dst_place.clone());
        if let Some(retalias) = fn_map.get(def_id) {
            for alias_set in retalias.aliases() {
                let (l, r) = (alias_set.left_local, alias_set.right_local);
                let (l_fields, r_fields) =
                    (alias_set.lhs_fields.clone(), alias_set.rhs_fields.clone());
                let (l_place, r_place) = (
                    if l != 0 {
                        get_arg_place(&args[l - 1].node)
                    } else {
                        (false, d_local)
                    },
                    if r != 0 {
                        get_arg_place(&args[r - 1].node)
                    } else {
                        (false, d_local)
                    },
                );
                // if left value is a constant, then update right variable's value
                if l_place.0 {
                    let snd_var = self
                        .chains
                        .find_var_id_with_fields_seq(r_place.1, &r_fields);
                    self.chains
                        .update_value(self.chains.get_point_to_id(snd_var), l_place.1);
                    continue;
                }
                // if right value is a constant, then update left variable's value
                if r_place.0 {
                    let fst_var = self
                        .chains
                        .find_var_id_with_fields_seq(l_place.1, &l_fields);
                    self.chains
                        .update_value(self.chains.get_point_to_id(fst_var), r_place.1);
                    continue;
                }
                let (fst_var, snd_var) = (
                    self.chains
                        .find_var_id_with_fields_seq(l_place.1, &l_fields),
                    self.chains
                        .find_var_id_with_fields_seq(r_place.1, &r_fields),
                );
                // If this var is a pointer/ref, prefer the pointed node when merging.
                let fst_to = self.chains.get_point_to_id(fst_var);
                let snd_to = self.chains.get_point_to_id(snd_var);
                let is_fst_point = fst_to != fst_var;
                let is_snd_point = snd_to != snd_var;
                let fst_node = self.chains.get_var_node(fst_var).unwrap();
                let snd_node = self.chains.get_var_node(snd_var).unwrap();
                let is_fst_ptr = is_ptr(fst_node.ty.unwrap()) || is_ref(fst_node.ty.unwrap());
                let is_snd_ptr = is_ptr(snd_node.ty.unwrap()) || is_ref(snd_node.ty.unwrap());
                rap_debug!(
                    "{:?}: {fst_var},{fst_to},{is_fst_ptr} -- {snd_var},{snd_to},{is_snd_ptr}",
                    def_id
                );
                match (is_fst_ptr, is_snd_ptr) {
                    (false, true) => {
                        // left is value, right is pointer: point right to left or merge appropriately.
                        if is_snd_point {
                            self.chains.point(snd_var, fst_var);
                        } else {
                            self.chains.merge(fst_var, snd_to);
                        }
                    }
                    (false, false) => {
                        // both are values: merge value nodes.
                        self.chains.merge(fst_var, snd_var);
                    }
                    (true, true) => {
                        // both are pointers: prefer merging what they point-to if available.
                        if is_fst_point && is_snd_point {
                            self.chains.merge(fst_to, snd_to);
                        } else if !is_fst_point && is_snd_point {
                            self.chains.point(fst_var, snd_to);
                        } else if is_fst_point && !is_snd_point {
                            self.chains.point(snd_var, fst_to);
                        } else {
                            self.chains.merge(fst_var, snd_var);
                        }
                    }
                    (true, false) => {
                        // left is pointer, right is value: point left to right or merge.
                        if is_fst_point {
                            self.chains.point(fst_var, snd_var);
                        } else {
                            self.chains.merge(snd_var, fst_to);
                        }
                    }
                }
            }
        }
        // If no alias cache is found and dst is a ptr, then initialize dst's states.
        else {
            let d_ty = self.chains.get_local_ty_by_place(d_local);
            if d_ty.is_some() && (is_ptr(d_ty.unwrap()) || is_ref(d_ty.unwrap())) {
                self.chains
                    .generate_ptr_with_obj_node(d_ty.unwrap(), d_local);
            }
        }
    }

    /// Compute a compact FunctionSummary for this function based on the return local (_0).
    /// If the return resolves to a param or const expression, include it in the summary.
    pub fn compute_function_summary(&self) -> FunctionSummary<'tcx> {
        if let Some(domain) = self.value_domains.get(&0) {
            if let Some(def) = &domain.def {
                let resolved_def = self.resolve_symbolic_def(def, 0); // 0 is the initial recursion deepth
                return FunctionSummary::new(resolved_def);
            }
        }
        FunctionSummary::new(None)
    }

    /// Resolve a SymbolicDef into a simplified form referencing params or constants.
    /// For example, given `_1 = add(_2, _3)`, attempt to express the result in terms of params.
    fn resolve_symbolic_def(
        &self,
        def: &SymbolicDef<'tcx>,
        depth: usize,
    ) -> Option<SymbolicDef<'tcx>> {
        // Limit recursion depth to avoid infinite loops in symbolic resolution.
        if depth > 10 {
            return None;
        }

        match def {
            // Base cases: parameters and constants are already resolved.
            SymbolicDef::Param(_) | SymbolicDef::Constant(_) => Some(def.clone()),
            // If this is a use/ref/cast, follow to the referenced local and resolve it.
            SymbolicDef::Use(local_idx) | SymbolicDef::Ref(local_idx) => {
                self.resolve_local(*local_idx, depth + 1)
            }
            SymbolicDef::Cast(src_idx, _ty) => self.resolve_local(*src_idx, depth + 1),
            // For binary ops, resolve LHS and RHS then rebuild a param-based result when possible.
            SymbolicDef::Binary(op, lhs_idx, rhs_op) => {
                let lhs_resolved = self.resolve_local(*lhs_idx, depth + 1)?;
                let rhs_resolved_op = match rhs_op {
                    AnaOperand::Const(c) => AnaOperand::Const(*c),
                    AnaOperand::Local(l) => match self.resolve_local(*l, depth + 1) {
                        Some(SymbolicDef::Constant(c)) => AnaOperand::Const(c),
                        Some(SymbolicDef::Param(p)) => AnaOperand::Local(p),
                        _ => return None,
                    },
                };
                match lhs_resolved {
                    // Only return a symbolic binary if LHS resolves to a parameter.
                    SymbolicDef::Param(p_idx) => {
                        Some(SymbolicDef::Binary(*op, p_idx, rhs_resolved_op))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Resolve a local's symbolic definition by consulting the value_domains map.
    fn resolve_local(&self, local_idx: usize, depth: usize) -> Option<SymbolicDef<'tcx>> {
        if let Some(domain) = self.value_domains.get(&local_idx) {
            if let Some(def) = &domain.def {
                return self.resolve_symbolic_def(def, depth);
            }
        }
        None
    }

    /// Handle calls to pointer offset functions (e.g., `ptr::add`, `ptr::sub`).
    pub fn handle_offset_call(
        &mut self,
        dst_place: &Place<'tcx>,
        def_id: &DefId,
        args: &Box<[Spanned<Operand<'tcx>>]>,
    ) {
        let func_name = get_cleaned_def_path_name(self.tcx, *def_id);

        let is_ptr_op = func_name.contains("ptr") || func_name.contains("slice");
        if !is_ptr_op {
            return;
        }

        let is_byte_sub =
            func_name.ends_with("::byte_sub") || func_name.ends_with("::wrapping_byte_sub"); // specific check for byte ops

        let is_sub =
            is_byte_sub || func_name.ends_with("::sub") || func_name.ends_with("::wrapping_sub");

        let is_byte_add =
            func_name.ends_with("::byte_add") || func_name.ends_with("::wrapping_byte_add");

        let is_add =
            is_byte_add || func_name.ends_with("::add") || func_name.ends_with("::wrapping_add");

        let is_byte_offset =
            func_name.ends_with("::byte_offset") || func_name.ends_with("::wrapping_byte_offset");

        let is_offset = is_byte_offset
            || func_name.ends_with("::offset")
            || func_name.ends_with("::wrapping_offset");

        if !is_sub && !is_add && !is_offset {
            return;
        }
        if args.len() < 2 {
            return;
        }

        let dst_local = self.handle_proj(false, *dst_place);

        let bin_op = if is_sub {
            BinOp::Sub
        } else if is_add {
            BinOp::Add
        } else {
            BinOp::Offset
        };

        let mut arg_indices = Vec::new();
        for arg in args.iter() {
            if let Some(ana_op) = self.lift_operand(&arg.node) {
                match ana_op {
                    AnaOperand::Local(l) => arg_indices.push(l),
                    AnaOperand::Const(_) => arg_indices.push(0),
                }
            } else {
                arg_indices.push(0);
            }
        }
        let base_op = &args[0].node;
        let base_local = if let Some(AnaOperand::Local(l)) = self.lift_operand(base_op) {
            l
        } else {
            return;
        };

        // judge whether it's a byte-level operation
        let is_byte_op = is_byte_sub || is_byte_add || is_byte_offset;

        let place_ty = if is_byte_op {
            // if it's a byte operation, force stride to 1 (Align 1, Size 1)
            PlaceTy::Ty(1, 1)
        } else {
            // otherwise, use the pointer's pointee type's Layout (stride = sizeof(T))
            self.get_ptr_pointee_layout(base_local)
        };

        // Create a symbolic definition for the pointer offset operation.
        let summary_def = SymbolicDef::PtrOffset(bin_op, 1, AnaOperand::Local(2), place_ty);
        let summary = FunctionSummary::new(Some(summary_def));

        // Apply the function summary to the destination local.
        self.apply_function_summary(dst_local, &summary, &arg_indices);
    }

    /// Handle SwitchInt: Convert branch selections into constraints AND refine abstract states.
    /// Convert a SwitchInt terminator into path constraints and refine state when possible.
    ///
    /// The function maps the branch target taken into a concrete equality/inequality
    /// constraint on the discriminator local and attempts to refine abstract states
    /// (e.g. alignment) when the condition corresponds to recognized helper calls.
    fn handle_switch_int(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &mir::SwitchTargets,
        next_bb: usize,
    ) {
        let discr_op = match self.lift_operand(discr) {
            Some(op) => op,
            None => return,
        };

        let discr_local_idx = match discr_op {
            AnaOperand::Local(idx) => idx,
            _ => return,
        };

        let mut matched_val = None;
        for (val, target_bb) in targets.iter() {
            if target_bb.as_usize() == next_bb {
                matched_val = Some(val);
                break;
            }
        }

        if let Some(val) = matched_val {
            // Explicit match found. Try to refine abstract state according to the boolean value.
            // Example: if discr corresponds to `is_aligned()`, matched_val==1 means true.
            self.refine_state_by_condition(discr_local_idx, val);

            // Record equality constraint for the taken branch (discr == val).
            let constraint =
                SymbolicDef::Binary(BinOp::Eq, discr_local_idx, AnaOperand::Const(val));
            self.path_constraints.push(constraint);
        } else if targets.otherwise().as_usize() == next_bb {
            // "Otherwise" branch taken.
            // Check what values were explicitly skipped to infer the current value.
            let mut explicit_has_zero = false;
            let mut explicit_has_one = false;

            for (val, _) in targets.iter() {
                if val == 0 {
                    explicit_has_zero = true;
                }
                if val == 1 {
                    explicit_has_one = true;
                }

                // Add Ne constraints for skipped targets
                let constraint =
                    SymbolicDef::Binary(BinOp::Ne, discr_local_idx, AnaOperand::Const(val));
                self.path_constraints.push(constraint);
            }

            // Inference logic for Boolean checks:
            // If only one boolean value was enumerated in explicit targets, infer the other
            // value for the otherwise branch and attempt refinement accordingly.
            if explicit_has_zero && !explicit_has_one {
                // Only 0 was explicit and skipped -> infer true
                self.refine_state_by_condition(discr_local_idx, 1);
            } else if explicit_has_one && !explicit_has_zero {
                // Only 1 was explicit and skipped -> infer false
                // This lets us mark the else-branch as unaligned when appropriate.
                self.refine_state_by_condition(discr_local_idx, 0);
            }
        }
    }

    /// Entry point for refining states based on a condition variable's value.
    fn refine_state_by_condition(&mut self, cond_local: usize, matched_val: u128) {
        // Clone the value domain entry to avoid holding a borrow while we mutate state.
        let domain = match self.value_domains.get(&cond_local).cloned() {
            Some(d) => d,
            None => return,
        };

        // If this discriminant corresponds to a call, dispatch to the specific refinement logic.
        if let Some(SymbolicDef::Call(func_name, args)) = &domain.def {
            self.apply_condition_refinement(func_name, args, matched_val);
        }
    }

    /// Dispatcher: Applies specific state updates based on function name and return value.
    fn apply_condition_refinement(
        &mut self,
        func_name: &str,
        args: &Vec<AnaOperand>,
        matched_val: u128,
    ) {
        // Handle is_aligned check
        if func_name.ends_with("is_aligned") || func_name.contains("is_aligned") {
            if let Some(AnaOperand::Local(ptr_local)) = args.get(0) {
                // Determine target state: 1 -> Aligned, 0 -> Unaligned
                let is_aligned_state = if matched_val == 1 {
                    Some(true)
                } else if matched_val == 0 {
                    Some(false)
                } else {
                    None
                };

                if let Some(aligned) = is_aligned_state {
                    // 1. Update the variable directly involved in the check (Current Node)
                    // This covers cases where the checked variable is used immediately in the block.
                    self.update_align_state(*ptr_local, aligned);

                    // 2. Trace back to the source (Root Node) and update it
                    // This covers cases where new copies are created from the source (e.g. _5 = copy _1).
                    let root_local = self.find_source_var(*ptr_local);
                    if root_local != *ptr_local {
                        self.update_align_state(root_local, aligned);
                    }
                }
            }
        }
    }

    /// Helper: Trace back through Use/Cast/Copy to find the definitive source local.
    pub fn find_source_var(&self, start_local: usize) -> usize {
        let mut curr = start_local;
        let mut depth = 0;
        while depth < 20 {
            if let Some(domain) = self.value_domains.get(&curr) {
                match &domain.def {
                    Some(SymbolicDef::Use(src)) | Some(SymbolicDef::Cast(src, _)) => {
                        curr = *src;
                    }
                    _ => return curr,
                }
            } else {
                return curr;
            }
            depth += 1;
        }
        curr
    }

    /// Apply function summary to update Visitor state and Graph
    pub fn apply_function_summary(
        &mut self,
        dst_local: usize,
        summary: &FunctionSummary<'tcx>,
        args: &Vec<usize>, // Caller's local indices for arguments
    ) {
        if let Some(def) = &summary.return_def {
            // 1. Resolve the definition to current context
            if let Some(resolved_def) = self.resolve_summary_def(def, args) {
                // 2. Record value definition in Visitor (essential for Z3 checks)
                // This ensures self.value_domains has the PtrOffset info
                self.record_value_def(dst_local, resolved_def.clone());

                // 3. Update DominatedGraph based on the resolved definition type
                match resolved_def {
                    SymbolicDef::PtrOffset(_, base_local, _, _) => {
                        // Update graph topology and node info
                        self.chains
                            .update_from_offset_def(dst_local, base_local, resolved_def);
                    }
                    _ => {}
                }
            }
        }
    }

    /// Resolve a definition from Function Summary (using Param indices)
    /// into a concrete SymbolicDef (using Caller's Locals).
    fn resolve_summary_def(
        &self,
        def: &SymbolicDef<'tcx>,
        args: &Vec<usize>,
    ) -> Option<SymbolicDef<'tcx>> {
        match def {
            // Param(i) -> Use(Arg_i)
            SymbolicDef::Param(idx) => {
                // Assuming 1-based index in Summary Params
                if *idx > 0 && idx - 1 < args.len() {
                    Some(SymbolicDef::Use(args[idx - 1]))
                } else {
                    None
                }
            }
            // PtrOffset(Param_Base, Param_Offset) -> PtrOffset(Local_Base, Local_Offset)
            SymbolicDef::PtrOffset(op, base_param_idx, offset_op, ty) => {
                if *base_param_idx > 0 && base_param_idx - 1 < args.len() {
                    let base_local = args[base_param_idx - 1];

                    // Resolve offset operand
                    let real_offset = match offset_op {
                        AnaOperand::Local(idx) => {
                            if *idx > 0 && idx - 1 < args.len() {
                                AnaOperand::Local(args[idx - 1])
                            } else {
                                AnaOperand::Const(0) // Fallback or Error handling
                            }
                        }
                        AnaOperand::Const(c) => AnaOperand::Const(*c),
                    };

                    Some(SymbolicDef::PtrOffset(
                        *op,
                        base_local,
                        real_offset,
                        ty.clone(),
                    ))
                } else {
                    None
                }
            }
            // Handle other variants if necessary (e.g., Constant)
            SymbolicDef::Constant(c) => Some(SymbolicDef::Constant(*c)),
            _ => None,
        }
    }

    // ------------------------------------------------

    /// Apply path constraints into chains and propagate simple constant equalities
    /// into value_domains for later symbolic checks.
    pub fn set_constraint(&mut self, constraint: &Vec<(Place<'tcx>, Place<'tcx>, BinOp)>) {
        for (p1, p2, op) in constraint {
            let p1_num = self.handle_proj(false, p1.clone());
            let p2_num = self.handle_proj(false, p2.clone());
            self.chains.insert_patial_op(p1_num, p2_num, op);

            if let BinOp::Eq = op {
                // If RHS is a known constant, record it as p1's value_constraint.
                let maybe_const = self.value_domains.get(&p2_num).and_then(|d| {
                    if let Some(SymbolicDef::Constant(c)) = d.def {
                        Some(c)
                    } else {
                        None
                    }
                });

                if let Some(c) = maybe_const {
                    self.value_domains
                        .entry(p1_num)
                        .and_modify(|d| d.value_constraint = Some(c))
                        .or_insert(ValueDomain {
                            def: None,
                            value_constraint: Some(c),
                        });
                }

                // Also propagate constant from p1 to p2 when available.
                let maybe_const_p1 = self.value_domains.get(&p1_num).and_then(|d| {
                    if let Some(SymbolicDef::Constant(c)) = d.def {
                        Some(c)
                    } else {
                        None
                    }
                });

                if let Some(c) = maybe_const_p1 {
                    self.value_domains
                        .entry(p2_num)
                        .and_modify(|d| d.value_constraint = Some(c))
                        .or_insert(ValueDomain {
                            def: None,
                            value_constraint: Some(c),
                        });
                }
            }
        }
    }

    /// Return layout information (align, size) or Unknown for a place via chain-derived type.
    pub fn get_layout_by_place_usize(&self, place: usize) -> PlaceTy<'tcx> {
        if let Some(ty) = self.chains.get_obj_ty_through_chain(place) {
            return self.visit_ty_and_get_layout(ty);
        } else {
            return PlaceTy::Unknown;
        }
    }

    /// Determine layout info (align,size) for a type. For generics, collect possible concrete layouts.
    pub fn visit_ty_and_get_layout(&self, ty: Ty<'tcx>) -> PlaceTy<'tcx> {
        match ty.kind() {
            TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _)
            | TyKind::Slice(ty)
            | TyKind::Array(ty, _) => self.visit_ty_and_get_layout(*ty),
            TyKind::Param(param_ty) => {
                let generic_name = param_ty.name.to_string();
                let mut layout_set: HashSet<(usize, usize)> = HashSet::new();
                let ty_set = self.generic_map.get(&generic_name.clone());
                if ty_set.is_none() {
                    if self.visit_time == 0 {
                        rap_warn!(
                            "Can not get generic type set: {:?}, def_id:{:?}",
                            generic_name,
                            self.def_id
                        );
                    }
                    return PlaceTy::GenericTy(generic_name, HashSet::new(), layout_set);
                }
                for ty in ty_set.unwrap().clone() {
                    if let PlaceTy::Ty(align, size) = self.visit_ty_and_get_layout(ty) {
                        layout_set.insert((align, size));
                    }
                }
                return PlaceTy::GenericTy(generic_name, ty_set.unwrap().clone(), layout_set);
            }
            TyKind::Adt(def, _list) => {
                if def.is_enum() {
                    return PlaceTy::Unknown;
                } else {
                    PlaceTy::Unknown
                }
            }
            TyKind::Closure(_, _) => PlaceTy::Unknown,
            TyKind::Alias(_, ty) => {
                // rap_warn!("self ty {:?}",ty.self_ty());
                return self.visit_ty_and_get_layout(ty.self_ty());
            }
            _ => {
                let param_env = self.tcx.param_env(self.def_id);
                let ty_env = ty::TypingEnv::post_analysis(self.tcx, self.def_id);
                let input = PseudoCanonicalInput {
                    typing_env: ty_env,
                    value: ty,
                };
                if let Ok(layout) = self.tcx.layout_of(input) {
                    // let layout = self.tcx.layout_of(param_env.and(ty)).unwrap();
                    let align = layout.align.abi.bytes_usize();
                    let size = layout.size.bytes() as usize;
                    return PlaceTy::Ty(align, size);
                } else {
                    // rap_warn!("Find type {:?} that can't get layout!", ty);
                    PlaceTy::Unknown
                }
            }
        }
    }

    /// Handle special binary operations (e.g., pointer offset) and extract operand places.
    pub fn handle_binary_op(
        &mut self,
        first_op: &Operand,
        bin_op: &BinOp,
        second_op: &Operand,
        path_index: usize,
    ) {
        // Currently collects arg places for Offset.
        match bin_op {
            BinOp::Offset => {
                let _first_place = get_arg_place(first_op);
                let _second_place = get_arg_place(second_op);
            }
            _ => {}
        }
    }

    /// Convert a MIR Place (with projections) into an internal numeric node id.
    /// Handles deref and field projections by consulting/creating chain nodes.
    pub fn handle_proj(&mut self, is_right: bool, place: Place<'tcx>) -> usize {
        let mut proj_id = place.local.as_usize();
        for proj in place.projection {
            match proj {
                ProjectionElem::Deref => {
                    let point_to = self.chains.get_point_to_id(place.local.as_usize());
                    if point_to == proj_id {
                        proj_id = self.chains.check_ptr(proj_id);
                    } else {
                        proj_id = point_to;
                    }
                }
                ProjectionElem::Field(field, ty) => {
                    proj_id = self
                        .chains
                        .get_field_node_id(proj_id, field.as_usize(), Some(ty));
                }
                _ => {}
            }
        }
        proj_id
    }

    /// Record or overwrite the symbolic definition for a local in value_domains.
    fn record_value_def(&mut self, local_idx: usize, def: SymbolicDef<'tcx>) {
        self.value_domains
            .entry(local_idx)
            .and_modify(|d| d.def = Some(def.clone()))
            .or_insert(ValueDomain {
                def: Some(def),
                value_constraint: None,
            });
    }

    /// Convert a MIR Operand into an AnaOperand (local node id or constant) when possible.
    fn lift_operand(&mut self, op: &Operand<'tcx>) -> Option<AnaOperand> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => {
                Some(AnaOperand::Local(self.handle_proj(true, place.clone())))
            }
            Operand::Constant(box c) => match c.const_ {
                rustc_middle::mir::Const::Ty(_ty, const_value) => {
                    if let Some(val) = const_value.try_to_target_usize(self.tcx) {
                        Some(AnaOperand::Const(val as u128))
                    } else {
                        None
                    }
                }
                rustc_middle::mir::Const::Unevaluated(_unevaluated, _ty) => None,
                rustc_middle::mir::Const::Val(const_value, _ty) => {
                    if let Some(scalar) = const_value.try_to_scalar_int() {
                        let val = scalar.to_uint(scalar.size());
                        Some(AnaOperand::Const(val))
                    } else {
                        None
                    }
                }
            },
        }
    }

    /// Trace a pointer value back to its base local and accumulate byte offsets.
    /// Returns (base_local, total_offset) when traceable.
    ///
    /// Example: p3 = p2.byte_offset(v2), p2 = p1.byte_offset(v1)
    /// returns (p1, v1 + v2) for trace_base_ptr(p3).
    pub fn trace_base_ptr(&self, local: usize) -> Option<(usize, u64)> {
        // Walk symbolic definitions backwards to find the base pointer and accumulated offset.
        let mut curr = local;
        let mut total_offset = 0;
        let mut depth = 0;

        loop {
            if depth > 10 {
                return None;
            }
            depth += 1;

            if let Some(domain) = self.value_domains.get(&curr) {
                match &domain.def {
                    Some(SymbolicDef::Binary(BinOp::Offset, base, offset_op)) => {
                        if let AnaOperand::Const(off) = offset_op {
                            total_offset += *off as u64;
                            curr = *base;
                        } else {
                            return None;
                        }
                    }
                    Some(SymbolicDef::Use(src)) | Some(SymbolicDef::Cast(src, _)) => {
                        curr = *src;
                    }
                    Some(SymbolicDef::Ref(src)) => {
                        return Some((*src, total_offset));
                    }
                    Some(SymbolicDef::Param(_)) => {
                        return Some((curr, total_offset));
                    }
                    _ => return None,
                }
            } else {
                return None;
            }
        }
    }
}

// === Partition: Debugging & display helpers ===
// Debugging and display helpers: pretty-printers and formatting utilities for analysis state.
impl<'tcx> BodyVisitor<'tcx> {
    /// Display a combined debug table merging DominatedGraph and ValueDomain info.
    /// Handles different lengths of variables in graph (includes heap nodes) vs domains.
    pub fn display_combined_debug_info(&self) {
        const TABLE_WIDTH: usize = 200; // Expanded width for all columns
        println!(
            "\n{:=^width$}",
            " Combined Analysis State Report ",
            width = TABLE_WIDTH
        );

        // 1. Collect and Sort All Unique Variable IDs
        let mut all_ids: HashSet<usize> = self.value_domains.keys().cloned().collect();
        all_ids.extend(self.chains.variables.keys().cloned());
        let mut sorted_ids: Vec<usize> = all_ids.into_iter().collect();
        sorted_ids.sort();

        if sorted_ids.is_empty() {
            println!("  [Empty Analysis State]");
            println!("{:=^width$}\n", "", width = TABLE_WIDTH);
            return;
        }

        // 2. Define Table Header
        let sep = format!(
            "+{:-^6}+{:-^25}+{:-^8}+{:-^15}+{:-^30}+{:-^25}+{:-^40}+{:-^15}+",
            "", "", "", "", "", "", "", ""
        );
        println!("{}", sep);
        println!(
            "| {:^6} | {:^25} | {:^8} | {:^15} | {:^30} | {:^25} | {:^40} | {:^15} |",
            "ID", "Type", "Pt-To", "Fields", "States", "Graph Offset", "Sym Def", "Sym Val"
        );
        println!("{}", sep);

        // 3. Iterate and Print Rows
        for id in sorted_ids {
            // -- Extract Graph Info (if exists) --
            let (ty_str, pt_str, fields_str, states_str, g_offset_str) =
                if let Some(node) = self.chains.variables.get(&id) {
                    // Type
                    let t = node
                        .ty
                        .map(|t| format!("{:?}", t))
                        .unwrap_or_else(|| "None".to_string());

                    // Points-To
                    let p = node
                        .points_to
                        .map(|p| format!("_{}", p))
                        .unwrap_or_else(|| "-".to_string());

                    // Fields
                    let f = if node.field.is_empty() {
                        "-".to_string()
                    } else {
                        let mut fs: Vec<String> = node
                            .field
                            .iter()
                            .map(|(k, v)| format!(".{}->_{}", k, v))
                            .collect();
                        fs.sort();
                        fs.join(", ")
                    };

                    // States (Align, etc.)
                    let mut s_vec = Vec::new();
                    match &node.ots.align {
                        AlignState::Aligned(ty) => {
                            if let Some(node_ty) = node.ty {
                                if is_ptr(node_ty) || is_ref(node_ty) {
                                    s_vec.push(format!("Align({:?})", ty));
                                }
                            }
                        }
                        AlignState::Unaligned(ty) => s_vec.push(format!("Unalign({:?})", ty)),
                        AlignState::Unknown => {} // Skip unknown to keep clean, or use "Unknown"
                    }
                    let s = if s_vec.is_empty() {
                        "-".to_string()
                    } else {
                        s_vec.join(", ")
                    };

                    // Graph Offset (Simplified Formatting Logic)
                    let off = if let Some(def) = &node.offset_from {
                        match def {
                            SymbolicDef::PtrOffset(op, base, idx, _) => {
                                let op_str = self.binop_to_symbol(op);
                                let idx_str = match idx {
                                    AnaOperand::Local(l) => format!("_{}", l),
                                    AnaOperand::Const(c) => format!("{}", c),
                                };
                                format!("_{} {} {}", base, op_str, idx_str)
                            }
                            SymbolicDef::Binary(BinOp::Offset, base, idx) => {
                                let idx_str = match idx {
                                    AnaOperand::Local(l) => format!("_{}", l),
                                    AnaOperand::Const(c) => format!("{}", c),
                                };
                                format!("_{} + {}", base, idx_str)
                            }
                            _ => format!("{:?}", def),
                        }
                    } else {
                        "-".to_string()
                    };

                    (t, p, f, s, off)
                } else {
                    (
                        "-".to_string(),
                        "-".to_string(),
                        "-".to_string(),
                        "-".to_string(),
                        "-".to_string(),
                    )
                };

            // -- Extract Value Domain Info (if exists) --
            let (sym_def_str, sym_val_str) = if let Some(domain) = self.value_domains.get(&id) {
                let d = self
                    .format_symbolic_def(domain.def.as_ref())
                    .replace('\n', " ");
                let v = match domain.value_constraint {
                    Some(val) => format!("== {}", val),
                    None => "-".to_string(),
                };
                (d, v)
            } else {
                ("-".to_string(), "-".to_string())
            };

            // -- Print Combined Row --
            println!(
                "| {:<6} | {:<25} | {:<8} | {:<15} | {:<30} | {:<25} | {:<40} | {:<15} |",
                id,
                self.safe_truncate(&ty_str, 25),
                pt_str,
                self.safe_truncate(&fields_str, 15),
                self.safe_truncate(&states_str, 30),
                self.safe_truncate(&g_offset_str, 25),
                self.safe_truncate(&sym_def_str, 40),
                self.safe_truncate(&sym_val_str, 15)
            );
        }

        println!("{}", sep);
        println!("{:=^width$}\n", " End Report ", width = TABLE_WIDTH);
    }

    /// Pretty-print the collected path constraints for debugging.
    /// Display the true conditions in all branches.
    pub fn display_path_constraints(&self) {
        const TABLE_WIDTH: usize = 86;
        println!(
            "\n{:=^width$}",
            " Path Constraints Report ",
            width = TABLE_WIDTH
        );

        if self.path_constraints.is_empty() {
            println!("  [Empty Path Constraints]");
            println!("{:=^width$}\n", "", width = TABLE_WIDTH);
            return;
        }

        println!("| {:^6} | {:^73} |", "Index", "Constraint Expression");
        let sep = format!("+{:-^6}+{:-^73}+", "", "");
        println!("{}", sep);

        for (i, constraint) in self.path_constraints.iter().enumerate() {
            let def_raw = self.format_symbolic_def(Some(constraint));
            let def_str = def_raw.replace('\n', " ").replace('\t', " ");

            println!("| {:<6} | {:<73} |", i, self.safe_truncate(&def_str, 73));
        }

        println!("{}", sep);
        println!("{:=^width$}\n", " End Report ", width = TABLE_WIDTH);
    }

    /// Display all variables' symbolic definitions and value constraints.
    /// Pretty-print value domains (symbolic definitions and constraints) for debug.
    pub fn display_value_domains(&self) {
        const TABLE_WIDTH: usize = 86;
        println!(
            "\n{:=^width$}",
            " Value Domain Analysis Report ",
            width = TABLE_WIDTH
        );

        let mut locals: Vec<&usize> = self.value_domains.keys().collect();
        locals.sort();

        if locals.is_empty() {
            println!("  [Empty Value Domains]");
            println!("{:=^width$}\n", "", width = TABLE_WIDTH);
            return;
        }

        let print_row = |c1: &str, c2: &str, c3: &str, is_header: bool| {
            if is_header {
                println!("| {:^6} | {:^40} | {:^15} |", c1, c2, c3);
            } else {
                println!(
                    "| {:<6} | {:<40} | {:<15} |",
                    c1,
                    self.safe_truncate(c2, 40),
                    c3,
                );
            }
        };

        let sep = format!("+{:-^6}+{:-^40}+{:-^15}+", "", "", "");
        println!("{}", sep);
        print_row("Local", "Symbolic Definition", "Constraint", true);
        println!("{}", sep);

        for local_idx in locals {
            let domain = &self.value_domains[local_idx];

            let local_str = format!("_{}", local_idx);

            let def_raw = self.format_symbolic_def(domain.def.as_ref());
            let def_str = def_raw.replace('\n', " ").replace('\t', " ");

            let constraint_str = match domain.value_constraint {
                Some(v) => format!("== {}", v),
                None => String::from("-"),
            };

            print_row(&local_str, &def_str, &constraint_str, false);
        }

        println!("{}", sep);
        println!("{:=^width$}\n", " End Report ", width = TABLE_WIDTH);
    }

    /// Truncate a string to max_width preserving character boundaries.
    /// Returns a shortened string with ".." appended when truncation occurs.
    fn safe_truncate(&self, s: &str, max_width: usize) -> String {
        let char_count = s.chars().count();
        if char_count <= max_width {
            return s.to_string();
        }
        let truncated: String = s.chars().take(max_width - 2).collect();
        format!("{}..", truncated)
    }

    /// Convert a SymbolicDef into a short human-readable string for display.
    fn format_symbolic_def(&self, def: Option<&SymbolicDef<'tcx>>) -> String {
        match def {
            None => String::from("Top (Unknown)"),
            Some(d) => match d {
                SymbolicDef::Param(idx) => format!("Param(arg_{})", idx),
                SymbolicDef::Constant(val) => format!("Const({})", val),
                SymbolicDef::Use(idx) => format!("Copy(_{})", idx),
                SymbolicDef::Ref(idx) => format!("&_{}", idx),
                SymbolicDef::Cast(idx, ty_str) => format!("_{} as {}", idx, ty_str),
                SymbolicDef::UnOp(op) => format!("{:?}(op)", op), // unary op placeholder
                SymbolicDef::Binary(op, lhs, rhs) => {
                    let op_str = self.binop_to_symbol(op);
                    let rhs_str = match rhs {
                        AnaOperand::Local(i) => format!("_{}", i),
                        AnaOperand::Const(c) => format!("{}", c),
                    };
                    format!("_{} {} {}", lhs, op_str, rhs_str)
                }
                SymbolicDef::Call(func_name, args) => {
                    let args_str: Vec<String> = args.iter().map(|a| format!("_{:?}", a)).collect();
                    format!("{}({})", func_name, args_str.join(", "))
                }
                SymbolicDef::PtrOffset(binop, ptr, offset, size) => {
                    let op_str = self.binop_to_symbol(&binop);
                    format!("ptr_offset({}, _{}, {:?}, {:?})", op_str, ptr, offset, size)
                }
            },
        }
    }

    /// Map MIR BinOp to a human-friendly operator string.
    fn binop_to_symbol(&self, op: &BinOp) -> &'static str {
        match op {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitXor => "^",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::Offset => "ptr_offset",
            _ => "",
        }
    }

    /// Display the path in DOT format.
    pub fn display_path_dot(&self, path: &[usize]) {
        let base_name = get_cleaned_def_path_name(self.tcx, self.def_id);
        let path_suffix = path
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<String>>()
            .join("_");

        let name = format!("{}_path_{}", base_name, path_suffix);
        let dot_string = self.chains.to_dot_graph();
        let dot_graph = DotGraph::new(name, dot_string);
        render_dot_string(&dot_graph);
    }
}
