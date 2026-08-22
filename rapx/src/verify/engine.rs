//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use z3::Config;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::analysis::path::PathTree;
use crate::compat::FxHashSet;

use super::{
    contract::{LeafProperty, OrProperty, Property},
    report::CheckResult,
    slicer::{RelevantItem, BackwardSlicer},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use super::{vm::SymbolicVm, property_checker::PropertyChecker};

const ENGINE_INLINE_DEPTH: usize = 3;

pub struct VerifyEngine<'tcx> {
    slicer: BackwardSlicer<'tcx>,
    vm: SymbolicVm<'tcx>,
    checker: PropertyChecker,
}

impl<'tcx> VerifyEngine<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            slicer: BackwardSlicer::new(tcx),
            vm: SymbolicVm::new(tcx),
            checker: PropertyChecker,
        }
    }

    fn new_z3_context() -> z3::Context {
        let mut cfg = Config::new();
        cfg.set_timeout_msec(10000);
        z3::Context::new(&cfg)
    }

    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);

        let bound_property = Self::bind_property_to_checkpoint(property, checkpoint);

        let ctx = Self::new_z3_context();

        // Accumulate checked-bounds facts across checkpoints.
        // A ChecksIndexBoundsDisjoint call in an earlier checkpoint
        // can discharge InBound checks in a later checkpoint.
        let mut accumulated_has_checked: bool = false;

        // Process checkpoints in forward (MIR) order so that facts
        // collected by earlier calls are available to later checks.
        let backward_items: Vec<_> = backward_items.into_iter().rev().collect();
        for backward in backward_items {
            let path_desc = backward.path.describe_indices();

            let mut items = Vec::new();
            if !caller_contracts.is_empty() {
                items.extend(
                    caller_contracts
                        .iter()
                        .filter(|c| !matches!(c.kind(), Some(super::contract::PropertyKind::Unknown)))
                        .map(|c| RelevantItem::ContractFact { property: c.clone() }),
                );
            }
            items.extend(backward.items);

            // Inject inline callees for unsupported calls.
            let items = self.inject_inline_callees(
                items,
                checkpoint.caller,
                ENGINE_INLINE_DEPTH,
            );

            let wrapped = Self::wrap_items(backward.checkpoint, backward.path, items);

            let vm_state = match self.vm.execute(&ctx, &wrapped) {
                Ok(state) => state,
                Err(reason) => {
                    results.push((CheckResult::Unknown, format!("{} (vm error: {})", path_desc, reason.message)));
                    continue;
                }
            };

            // Accumulate checked bounds/disjointness facts across
            // checkpoints so that a validator called in one checkpoint
            // can discharge InBound checks in a later checkpoint.
            accumulated_has_checked = accumulated_has_checked || vm_state.has_checked_bounds;
            let mut vm_state = vm_state;
            vm_state.has_checked_bounds = accumulated_has_checked;

            let result = self.checker.check(&vm_state, checkpoint, &bound_property);
            results.push((result, path_desc));
        }

        results
    }

    fn wrap_items(
        checkpoint: CheckpointLocation,
        path: crate::verify::path_extractor::Path,
        items: Vec<RelevantItem<'tcx>>,
    ) -> crate::verify::slicer::ProofGoal<'tcx> {
        crate::verify::slicer::ProofGoal {
            checkpoint,
            path,
            items,
        }
    }

    fn callee_is_simple(tcx: TyCtxt<'_>, callee_def_id: DefId) -> bool {
        crate::helpers::mir_utils::callee_is_linear(tcx, callee_def_id, 3)
    }

    /// Scan the relevant items for unsupported Call terminators whose callee
    /// has available MIR. For each such call, inject `CalleeEntry` + callee
    /// MIR items + `CalleeExit`, replacing the original terminator.
    fn inject_inline_callees(
        &self,
        mut items: Vec<RelevantItem<'tcx>>,
        caller_def_id: DefId,
        depth: usize,
    ) -> Vec<RelevantItem<'tcx>> {
        if depth == 0 {
            return items;
        }

        let tcx = self.slicer.tcx();
        let body = tcx.optimized_mir(caller_def_id);
        let mut result: Vec<RelevantItem<'tcx>> = Vec::new();

        for item in items.drain(..) {
            match &item {
                RelevantItem::Terminator { block, .. } => {
                    let terminator = body.basic_blocks[*block].terminator();
                    if let TerminatorKind::Call { func, args, destination, .. } = &terminator.kind {
                        if let Some(callee) = crate::helpers::mir_utils::dep_callee_def_id(func) {
                            if tcx.is_mir_available(callee) {
                                let summary = crate::verify::call_summary::effect_summary(
                                    tcx, caller_def_id, func, destination.local,
                                );

                                if summary.unsupported && Self::callee_is_simple(tcx, callee) {
                                    let arg_locals: Vec<rustc_middle::mir::Local> = args.iter()
                                        .filter_map(|arg| match &arg.node {
                                            rustc_middle::mir::Operand::Copy(p)
                                            | rustc_middle::mir::Operand::Move(p)
                                                if p.projection.is_empty() => Some(p.local),
                                            _ => None,
                                        })
                                        .collect();
                                    if arg_locals.len() == args.len() {
                                        let callee_items = self.build_callee_items(callee, depth - 1);
                                        result.push(RelevantItem::CalleeEntry {
                                            callee,
                                            args: arg_locals,
                                        });
                                        result.extend(callee_items);
                                        result.push(RelevantItem::CalleeExit {
                                            dest: destination.local,
                                        });
                                        continue; // Skip original Terminator item
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            result.push(item);
        }

        result
    }

    /// Build a linear sequence of relevant items for a callee's MIR body.
    /// Walks BFS from the entry block, collecting statements and terminators.
    fn build_callee_items(
        &self,
        callee_def_id: DefId,
        depth: usize,
    ) -> Vec<RelevantItem<'tcx>> {
        let mut items: Vec<RelevantItem<'tcx>> = Vec::new();
        let tcx = self.slicer.tcx();
        let body = tcx.optimized_mir(callee_def_id);

        let mut visited = FxHashSet::default();
        let mut queue: Vec<BasicBlock> = Vec::new();
        queue.push(BasicBlock::from_usize(0));

        while let Some(block) = queue.pop() {
            if !visited.insert(block) {
                continue;
            }

            let bb_data = &body.basic_blocks[block];

            for (si, _) in bb_data.statements.iter().enumerate() {
                items.push(RelevantItem::Statement {
                    block,
                    statement_index: si,
                });
            }

            let terminator = bb_data.terminator();

            // Recursively inline calls in the callee's terminators
            match &terminator.kind {
                TerminatorKind::Call { func, args, destination, target, .. } => {
                    if let Some(inner_callee) = crate::helpers::mir_utils::dep_callee_def_id(func) {
                        if tcx.is_mir_available(inner_callee) {
                            let summary = crate::verify::call_summary::effect_summary(
                                tcx, callee_def_id, func, destination.local,
                            );

                            if summary.unsupported && Self::callee_is_simple(tcx, inner_callee) && depth > 0 {
                                let arg_locals: Vec<rustc_middle::mir::Local> = args.iter()
                                    .filter_map(|arg| match &arg.node {
                                        rustc_middle::mir::Operand::Copy(p)
                                        | rustc_middle::mir::Operand::Move(p)
                                            if p.projection.is_empty() => Some(p.local),
                                        _ => None,
                                    })
                                    .collect();
                                if arg_locals.len() == args.len() {
                                    let inner_items = self.build_callee_items(inner_callee, depth - 1);
                                    items.push(RelevantItem::CalleeEntry {
                                        callee: inner_callee,
                                        args: arg_locals,
                                    });
                                    items.extend(inner_items);
                                    items.push(RelevantItem::CalleeExit {
                                        dest: destination.local,
                                    });
                                    if let Some(t) = target {
                                        queue.push(*t);
                                    }
                                    continue;
                                }
                            }
                        }
                    }
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                    if let Some(t) = target {
                        queue.push(*t);
                    }
                }
                TerminatorKind::Goto { target } => {
                    queue.push(*target);
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
                TerminatorKind::Return => {
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
                TerminatorKind::Assert { target, .. } => {
                    queue.push(*target);
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
                TerminatorKind::SwitchInt { targets, .. } => {
                    for (_, t) in targets.iter() {
                        queue.push(t);
                    }
                    queue.push(targets.otherwise());
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
                TerminatorKind::Drop { target, .. } => {
                    queue.push(*target);
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
                _ => {
                    items.push(RelevantItem::Terminator {
                        block,
                    });
                }
            }
        }

        items
    }

    fn bind_property_to_checkpoint(
        property: &Property<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> Property<'tcx> {
        match property {
            Property::Leaf(leaf) => {
                let new_args: Vec<super::contract::PropertyArg<'tcx>> = leaf
                    .args
                    .iter()
                    .map(|a| match a {
                        super::contract::PropertyArg::Expr(expr) => {
                            super::contract::PropertyArg::Expr(Self::rebind_contract_expr(
                                expr,
                                checkpoint,
                            ))
                        }
                        super::contract::PropertyArg::Predicates(predicates) => {
                            let rebound: Vec<_> = predicates
                                .iter()
                                .map(|p| {
                                    let lhs = Self::rebind_contract_expr(&p.lhs, checkpoint);
                                    let rhs = Self::rebind_contract_expr(&p.rhs, checkpoint);
                                    super::contract::NumericPredicate::new(lhs, p.op, rhs)
                                })
                                .collect();
                            super::contract::PropertyArg::Predicates(rebound)
                        }
                        _ => a.clone(),
                    })
                    .collect();
                Property::Leaf(LeafProperty {
                    kind: leaf.kind,
                    args: new_args,
                    contract_kind: leaf.contract_kind,
                    null_guard: leaf.null_guard.clone(),
                    for_each: leaf.for_each.clone(),
                    origin_name: None,
                    origin_args: None,
                    origin_meaning: None,
                })
            }
            Property::Or(or) => {
                let new_groups: Vec<Vec<Box<Property<'tcx>>>> = or
                    .groups
                    .iter()
                    .map(|group| {
                        group
                            .iter()
                            .map(|p| Box::new(Self::bind_property_to_checkpoint(p, checkpoint)))
                            .collect()
                    })
                    .collect();
                Property::Or(OrProperty {
                    groups: new_groups,
                    contract_kind: or.contract_kind,
                    origin_name: None,
                    origin_args: None,
                    origin_meaning: None,
                })
            }
        }
    }

    fn rebind_place(
        place: &super::contract::ContractPlace<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> super::contract::ContractPlace<'tcx> {
        let new_base = match place.base {
            super::contract::PlaceBase::Return => super::contract::PlaceBase::Return,
            super::contract::PlaceBase::Arg(n) => super::contract::PlaceBase::Arg(n),
            super::contract::PlaceBase::Local(n) => {
                if n > 0 && n <= checkpoint.args.len() {
                    super::contract::PlaceBase::Arg(n - 1)
                } else {
                    super::contract::PlaceBase::Local(n)
                }
            }
        };
        super::contract::ContractPlace {
            base: new_base,
            projections: place.projections.clone(),
        }
    }

    fn rebind_contract_expr(
        expr: &super::contract::ContractExpr<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> super::contract::ContractExpr<'tcx> {
        match expr {
            super::contract::ContractExpr::Place(place) => {
                super::contract::ContractExpr::Place(Self::rebind_place(place, checkpoint))
            }
            super::contract::ContractExpr::Len(inner) => {
                super::contract::ContractExpr::Len(Box::new(Self::rebind_contract_expr(inner, checkpoint)))
            }
            super::contract::ContractExpr::SizeOf(_) | super::contract::ContractExpr::AlignOf(_)
            | super::contract::ContractExpr::Const(_) | super::contract::ContractExpr::ConstParam { .. }
            | super::contract::ContractExpr::Unknown => expr.clone(),
            super::contract::ContractExpr::IndexAccess { slice, index } => {
                super::contract::ContractExpr::IndexAccess {
                    slice: Box::new(Self::rebind_contract_expr(slice, checkpoint)),
                    index: Box::new(Self::rebind_contract_expr(index, checkpoint)),
                }
            }
            super::contract::ContractExpr::Binary { op, lhs, rhs } => {
                super::contract::ContractExpr::Binary {
                    op: *op,
                    lhs: Box::new(Self::rebind_contract_expr(lhs, checkpoint)),
                    rhs: Box::new(Self::rebind_contract_expr(rhs, checkpoint)),
                }
            }
            super::contract::ContractExpr::Unary { op, expr: inner } => {
                super::contract::ContractExpr::Unary {
                    op: *op,
                    expr: Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                }
            }
            super::contract::ContractExpr::Min { a, b } => {
                super::contract::ContractExpr::Min {
                    a: Box::new(Self::rebind_contract_expr(a, checkpoint)),
                    b: Box::new(Self::rebind_contract_expr(b, checkpoint)),
                }
            }
            super::contract::ContractExpr::Max { a, b } => {
                super::contract::ContractExpr::Max {
                    a: Box::new(Self::rebind_contract_expr(a, checkpoint)),
                    b: Box::new(Self::rebind_contract_expr(b, checkpoint)),
                }
            }
            super::contract::ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                super::contract::ContractExpr::If {
                    cond: Box::new(super::contract::NumericPredicate::new(
                        Self::rebind_contract_expr(&cond.lhs, checkpoint),
                        cond.op,
                        Self::rebind_contract_expr(&cond.rhs, checkpoint),
                    )),
                    then_expr: Box::new(Self::rebind_contract_expr(then_expr, checkpoint)),
                    else_expr: Box::new(Self::rebind_contract_expr(else_expr, checkpoint)),
                }
            }
        }
    }

    pub fn check_invariant_from_tree(
        &self,
        def_id: DefId,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        invariant: &Property<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self.slicer.visit_path_tree_for_checkpoint(
            tree,
            target_block,
            def_id,
            checkpoint,
            invariant,
        );

        let ctx = Self::new_z3_context();

        for mut backward in backward_items {
            let path_desc = backward.path.describe_indices();

            if !entry_facts.is_empty() {
                let mut items: Vec<RelevantItem<'tcx>> = entry_facts.to_vec();
                items.extend(backward.items.drain(..));
                backward.items = items;
            }

            let vm_state = match self.vm.execute(&ctx, &backward) {
                Ok(state) => state,
                Err(reason) => {
                    results.push((CheckResult::Unknown, format!("{} (vm error: {})", path_desc, reason.message)));
                    continue;
                }
            };

            let fake_checkpoint = Checkpoint {
                caller: def_id,
                callee: None,
                block: checkpoint.block,
                span: rustc_span::DUMMY_SP,
                args: Vec::new(),
                kind: crate::helpers::mir_scan::CheckpointKind::UnsafeCall,
                is_ref: false,
                is_mut_ref: false,
                destination: None,
            };
            let result = self.checker.check(&vm_state, &fake_checkpoint, invariant);
            results.push((result, path_desc));
        }

        results
    }
}
