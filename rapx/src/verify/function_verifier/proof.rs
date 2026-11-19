//! Proof checking methods for [`FunctionVerifier`].
//!
//! Slice paths, replay retained MIR through the symbolic VM, and check properties.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use std::cell::Cell;

use crate::analysis::path::PathTree;
use crate::helpers::mir_utils;
use crate::verify::{
    checkpoint::{Checkpoint, CheckpointLocation},
    contract::{self, AndProperty, AtomProperty, OrProperty, Property, PropertyKind},
    property_checker::PropertyChecker,
    proof_cache::VmCache,
    report::{CheckResult, UnknownReason},
    slicer::{ProofGoal, RelevantItem},
    vm::VmState,
};

use super::FunctionVerifier;

enum LocalAccess {
    None,
    Read,
    Reinitialized,
}

impl<'target, 'tcx> FunctionVerifier<'target, 'tcx> {
    /// Verify a property against every path reaching `checkpoint`, one result
    /// per path. Each path is sliced backward from the checkpoint, replayed
    /// symbolically by the VM, and finally discharged by the property checker.
    ///
    /// Returns `(result, path_description)` pairs in forward MIR order.
    pub(super) fn check_callsite(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        forward_drop_alias: bool,
    ) -> Vec<(CheckResult, String)> {
        let tree = &self.path_tree;
        let target_block = checkpoint.block.as_usize();
        let goals = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);
        let bound_property = Self::bind_property_to_checkpoint(property, checkpoint);
        let entry_facts: Vec<_> = self
            .target
            .caller_requires
            .iter()
            .filter(|c| !matches!(c.kind(), Some(PropertyKind::Unknown)))
            .map(|c| RelevantItem::ContractFact {
                property: c.clone(),
            })
            .collect();
        self.check_goals(
            cache,
            tree,
            goals.into_iter().rev(),
            checkpoint,
            &bound_property,
            &entry_facts,
            forward_drop_alias,
        )
    }

    /// Path-sensitive forward scan for the `Drop` hazard.
    ///
    /// `manually_drop::drop(&mut slot)` frees the heap behind `slot`, but `slot`
    /// (a `ManuallyDrop` wrapper) stays live.  A later use of `slot` reads
    /// through the freed allocation — a use-after-free.  Unlike the other
    /// properties (checked at the checkpoint by the VM over a backward-sliced
    /// path), this is a *forward* obligation, so it walks the complete paths of
    /// the shared [`PathTree`] and checks the suffix after the drop call.
    pub(super) fn check_drop(&self, checkpoint: &Checkpoint<'tcx>) -> Vec<(CheckResult, String)> {
        let tree = &self.path_tree;
        let caller = checkpoint.caller;
        let target = checkpoint.block.as_usize();

        let mut results: Vec<(CheckResult, String)> = Vec::new();
        for path in tree.iter() {
            let mut reaches = false;
            let mut verdict = CheckResult::ProvedByRule;
            for (pos, &g) in path.iter().enumerate() {
                let Some((def, local)) = tree.block_fn_of(g) else {
                    continue;
                };
                if def == caller && local == target {
                    reaches = true;
                    let result = match self.drop_referent_local(tree, checkpoint, &path[..=pos]) {
                        Some(slot)
                            if self.drop_suffix_reads(tree, caller, slot, &path[pos + 1..]) =>
                        {
                            CheckResult::Failed
                        }
                        Some(_) => CheckResult::ProvedByRule,
                        None => CheckResult::Unknown(UnknownReason::Unimplemented),
                    };
                    verdict = verdict.and(result);
                }
            }
            if reaches {
                results.push((verdict, format!("{:?}", path)));
            }
        }

        if results.is_empty() {
            vec![(CheckResult::ProvedByRule, String::new())]
        } else {
            results
        }
    }

    /// Follow the borrow passed to `ManuallyDrop::drop` on the current path.
    /// A reference temporary can point at different slots on different paths.
    fn drop_referent_local(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        prefix: &[usize],
    ) -> Option<Local> {
        let arg = checkpoint.args.first()?;
        let place = mir_utils::operand_mir_place(arg)?;
        let mut cur = place.local;
        let body = self.tcx.optimized_mir(checkpoint.caller);
        let mut before = (prefix.len(), usize::MAX);
        loop {
            let mut source = None;
            'find: for (path_index, &global_block) in prefix.iter().enumerate().rev() {
                if path_index > before.0 {
                    continue;
                }
                let Some((def_id, local_block)) = tree.block_fn_of(global_block) else {
                    continue;
                };
                if def_id != checkpoint.caller {
                    continue;
                }
                let statements = &body.basic_blocks[BasicBlock::from_usize(local_block)].statements;
                let end = if path_index == before.0 {
                    before.1.min(statements.len())
                } else {
                    statements.len()
                };
                for statement_index in (0..end).rev() {
                    let StatementKind::Assign(assign) = &statements[statement_index].kind else {
                        continue;
                    };
                    let (target, rvalue) = assign.as_ref();
                    if target.local == cur && target.projection.is_empty() {
                        source = Some((rvalue, path_index, statement_index));
                        break 'find;
                    }
                }
            }
            let Some((rvalue, path_index, statement_index)) = source else {
                // A parameter can be the caller's `&mut slot`. A local with no
                // visible definition may come from a call, which we cannot trace.
                return (cur.as_usize() > 0 && cur.as_usize() <= body.arg_count).then_some(cur);
            };
            before = (path_index, statement_index);
            match rvalue {
                Rvalue::Ref(_, _, referent) if referent.projection.is_empty() => {
                    return Some(referent.local);
                }
                Rvalue::Ref(_, _, referent)
                    if matches!(
                        referent.projection.first(),
                        Some(rustc_middle::mir::ProjectionElem::Deref)
                    ) =>
                {
                    cur = referent.local;
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                    if place.projection.is_empty() =>
                {
                    cur = place.local;
                }
                _ => return None,
            }
        }
    }

    /// Classify the first access to `local` in `block` after a manual drop.
    fn block_local_access(
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        block: usize,
        local: Local,
    ) -> LocalAccess {
        let body = tcx.optimized_mir(caller);
        let data = &body.basic_blocks[BasicBlock::from(block)];
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (target, rvalue) = assign.as_ref();
                if mir_utils::rvalue_any_place_matching(rvalue, &mut |p| p.local == local) {
                    return LocalAccess::Read;
                }
                if target.local == local {
                    return if target.projection.is_empty() {
                        LocalAccess::Reinitialized
                    } else {
                        LocalAccess::Read
                    };
                }
            }
        }
        if let Some(terminator) = &data.terminator {
            match &terminator.kind {
                TerminatorKind::Call {
                    args, destination, ..
                } => {
                    if args.iter().any(|a| match &a.node {
                        Operand::Copy(p) | Operand::Move(p) => p.local == local,
                        Operand::Constant(_) => false,
                        Operand::RuntimeChecks(_) => false,
                    }) {
                        return LocalAccess::Read;
                    }
                    if destination.local == local {
                        return if destination.projection.is_empty() {
                            LocalAccess::Reinitialized
                        } else {
                            LocalAccess::Read
                        };
                    }
                }
                TerminatorKind::TailCall { args, .. } => {
                    if args.iter().any(|a| match &a.node {
                        Operand::Copy(p) | Operand::Move(p) => p.local == local,
                        Operand::Constant(_) => false,
                        Operand::RuntimeChecks(_) => false,
                    }) {
                        return LocalAccess::Read;
                    }
                }
                TerminatorKind::SwitchInt { discr, .. }
                | TerminatorKind::Assert { cond: discr, .. } => match discr {
                    Operand::Copy(p) | Operand::Move(p) => {
                        if p.local == local {
                            return LocalAccess::Read;
                        }
                    }
                    Operand::Constant(_) => {}
                    Operand::RuntimeChecks(_) => {}
                },
                TerminatorKind::Drop { place, .. } if place.local == local => {
                    return LocalAccess::Read;
                }
                _ => {}
            }
        }
        LocalAccess::None
    }

    fn drop_suffix_reads(
        &self,
        tree: &PathTree,
        caller: DefId,
        slot: Local,
        suffix: &[usize],
    ) -> bool {
        for &block in suffix {
            let Some((def_id, local_block)) = tree.block_fn_of(block) else {
                continue;
            };
            if def_id != caller {
                continue;
            }
            match Self::block_local_access(self.tcx, caller, local_block, slot) {
                LocalAccess::None => {}
                LocalAccess::Read => return true,
                LocalAccess::Reinitialized => return false,
            }
        }
        false
    }

    fn drop_alias_for_prefix(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        prefix: &[usize],
        slot: Option<Local>,
    ) -> CheckResult {
        let Some(slot) = slot else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let mut safe = false;
        let mut unsafe_path = false;
        for path in tree.iter().filter(|path| path.starts_with(prefix)) {
            let used = self.drop_suffix_reads(tree, checkpoint.caller, slot, &path[prefix.len()..]);
            safe |= !used;
            unsafe_path |= used;
        }
        match (safe, unsafe_path) {
            (true, false) => CheckResult::ProvedByRule,
            (false, true) => CheckResult::Failed,
            (true, true) => CheckResult::Unknown(UnknownReason::DropAliasMixedPaths),
            (false, false) => CheckResult::Unknown(UnknownReason::Unimplemented),
        }
    }

    fn check_with_forward_alias<'z3>(
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        structural: bool,
        reachability: &Cell<Option<z3::SatResult>>,
        alias_result: &CheckResult,
    ) -> CheckResult {
        match property {
            Property::Atom(atom) if atom.kind == contract::PropertyKind::Alias => {
                alias_result.clone()
            }
            Property::Atom(_) => {
                PropertyChecker.check(vm_state, checkpoint, property, structural, reachability)
            }
            Property::And(and) => {
                and.conjuncts
                    .iter()
                    .fold(CheckResult::ProvedByRule, |acc, child| {
                        acc.and(Self::check_with_forward_alias(
                            vm_state,
                            checkpoint,
                            child,
                            structural,
                            reachability,
                            alias_result,
                        ))
                    })
            }
            Property::Or(or) => CheckResult::disjunction_with_guards(
                or.disjuncts.iter().map(|child| {
                    let result = Self::check_with_forward_alias(
                        vm_state,
                        checkpoint,
                        child,
                        structural,
                        reachability,
                        alias_result,
                    );
                    let guard = matches!(
                        child.kind(),
                        Some(PropertyKind::Size | PropertyKind::Null | PropertyKind::Trait)
                    );
                    (result, guard)
                }),
            ),
        }
    }

    /// Insert callee boundaries from each retained item's callsite ancestry.
    fn inject_inline_boundaries(
        &self,
        items: Vec<RelevantItem<'tcx>>,
        tree: &PathTree,
    ) -> Vec<RelevantItem<'tcx>> {
        let mut out = Vec::new();
        let mut active: Vec<(usize, usize)> = Vec::new();

        for item in items {
            let entry = match &item {
                RelevantItem::Statement {
                    block,
                    global_block,
                    ..
                }
                | RelevantItem::Terminator {
                    block,
                    global_block,
                    ..
                } => Some(
                    global_block.expect("sliced MIR item has no global block") - block.as_usize(),
                ),
                _ => None,
            };
            if let Some(mut entry) = entry {
                if active
                    .last()
                    .map(|(active_entry, _)| *active_entry)
                    .unwrap_or(0)
                    == entry
                {
                    out.push(item);
                    continue;
                }
                let mut ancestry = Vec::new();
                while entry != 0 {
                    ancestry.push(entry);
                    entry = tree
                        .call_parent_entry(entry)
                        .expect("inlined callee has no parent entry");
                }
                ancestry.reverse();

                let shared = active
                    .iter()
                    .zip(&ancestry)
                    .take_while(|((active_entry, _), wanted)| active_entry == *wanted)
                    .count();
                while active.len() > shared {
                    let (_, dest) = active.pop().unwrap();
                    out.push(RelevantItem::CalleeExit { dest });
                }
                for entry in ancestry.into_iter().skip(shared) {
                    let (callee, _) = tree
                        .block_fn_of(entry)
                        .expect("inlined callee entry has no block metadata");
                    let binding = tree
                        .call_binding(entry)
                        .expect("inlined callee entry has no call binding");
                    out.push(RelevantItem::CalleeEntry {
                        callee,
                        body: self.slicer.body_for_entry(entry, callee),
                        args: binding.args.clone(),
                    });
                    active.push((entry, binding.dest_local));
                }
            }
            out.push(item);
        }

        while let Some((_, dest)) = active.pop() {
            out.push(RelevantItem::CalleeExit { dest });
        }
        out
    }

    /// Rewrite a property so its contract expressions refer to the caller's
    /// argument positions at `checkpoint` rather than the callee's local
    /// numbering. Recurses through `Atom`/`And`/`Or` nodes and clears `origin`
    /// metadata (which only applies to the source-level property).
    fn bind_property_to_checkpoint(
        property: &Property<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> Property<'tcx> {
        match property {
            Property::Atom(atom) => {
                let new_args: Vec<contract::PropertyArg<'tcx>> = atom
                    .args
                    .iter()
                    .map(|a| match a {
                        contract::PropertyArg::Expr(expr) => {
                            contract::PropertyArg::Expr(Self::rebind_contract_expr(
                                expr, checkpoint,
                            ))
                        }
                        contract::PropertyArg::Predicates(predicates) => {
                            let rebound: Vec<_> = predicates
                                .iter()
                                .map(|p| {
                                    let lhs = Self::rebind_contract_expr(&p.lhs, checkpoint);
                                    let rhs = Self::rebind_contract_expr(&p.rhs, checkpoint);
                                    contract::NumericPredicate::new(lhs, p.op, rhs)
                                })
                                .collect();
                            contract::PropertyArg::Predicates(rebound)
                        }
                        _ => a.clone(),
                    })
                    .collect();
                Property::Atom(AtomProperty {
                    kind: atom.kind,
                    args: new_args,
                    contract_kind: atom.contract_kind,
                    for_each: atom
                        .for_each
                        .as_ref()
                        .map(|p| Self::rebind_place(p, checkpoint)),
                    origin: None,
                })
            }
            Property::And(and) => Property::And(AndProperty {
                conjuncts: and
                    .conjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect(),
                contract_kind: and.contract_kind,
                origin: None,
            }),
            Property::Or(or) => Property::Or(OrProperty {
                disjuncts: or
                    .disjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect(),
                contract_kind: or.contract_kind,
                origin: None,
            }),
        }
    }

    /// Rewrite a contract place's base to the checkpoint's view.
    ///
    /// `Return` and `Arg` bases are unchanged; a `Local(n)` that falls within
    /// the checkpoint's argument range is remapped to `Arg(n - 1)` (locals
    /// 1..=k correspond to the callee's arguments in order).
    fn rebind_place(
        place: &contract::ContractPlace<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> contract::ContractPlace<'tcx> {
        let new_base = match place.base {
            contract::PlaceBase::Return => contract::PlaceBase::Return,
            contract::PlaceBase::Arg(n) => contract::PlaceBase::Arg(n),
            contract::PlaceBase::Local(n) => {
                if n > 0 && n <= checkpoint.args.len() {
                    contract::PlaceBase::Arg(n - 1)
                } else {
                    contract::PlaceBase::Local(n)
                }
            }
        };
        contract::ContractPlace {
            base: new_base,
            projections: place.projections.clone(),
        }
    }

    /// Recursively rewrite every place embedded in a contract expression,
    /// rebinding `Local` bases to argument positions via [`Self::rebind_place`].
    fn rebind_contract_expr(
        expr: &contract::ContractExpr<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> contract::ContractExpr<'tcx> {
        match expr {
            contract::ContractExpr::Place(place) => {
                contract::ContractExpr::Place(Self::rebind_place(place, checkpoint))
            }
            contract::ContractExpr::Len(inner, method) => {
                contract::ContractExpr::Len(
                    Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                    *method,
                )
            }
            contract::ContractExpr::MethodCall {
                receiver,
                method,
                args,
            } => contract::ContractExpr::MethodCall {
                receiver: Box::new(Self::rebind_contract_expr(receiver, checkpoint)),
                method: *method,
                args: args
                    .iter()
                    .map(|arg| Self::rebind_contract_expr(arg, checkpoint))
                    .collect(),
            },
            contract::ContractExpr::IsEmpty(inner, method) => {
                contract::ContractExpr::IsEmpty(
                    Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                    *method,
                )
            }
            contract::ContractExpr::SizeOf(_)
            | contract::ContractExpr::AlignOf(_)
            | contract::ContractExpr::Const(_)
            | contract::ContractExpr::ConstParam { .. }
            | contract::ContractExpr::Unknown => expr.clone(),
            contract::ContractExpr::IndexAccess { slice, index } => {
                contract::ContractExpr::IndexAccess {
                    slice: Box::new(Self::rebind_contract_expr(slice, checkpoint)),
                    index: Box::new(Self::rebind_contract_expr(index, checkpoint)),
                }
            }
            contract::ContractExpr::Binary { op, lhs, rhs } => {
                contract::ContractExpr::Binary {
                    op: *op,
                    lhs: Box::new(Self::rebind_contract_expr(lhs, checkpoint)),
                    rhs: Box::new(Self::rebind_contract_expr(rhs, checkpoint)),
                }
            }
            contract::ContractExpr::Unary { op, expr: inner } => {
                contract::ContractExpr::Unary {
                    op: *op,
                    expr: Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                }
            }
            contract::ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => contract::ContractExpr::If {
                cond: Box::new(contract::NumericPredicate::new(
                    Self::rebind_contract_expr(&cond.lhs, checkpoint),
                    cond.op,
                    Self::rebind_contract_expr(&cond.rhs, checkpoint),
                )),
                then_expr: Box::new(Self::rebind_contract_expr(then_expr, checkpoint)),
                else_expr: Box::new(Self::rebind_contract_expr(else_expr, checkpoint)),
            },
        }
    }

    /// Verify an invariant against every path reaching `checkpoint`.
    ///
    /// Unlike [`Self::check_callsite`], there is no callsite to bind
    /// against, so `entry_facts` are prepended to each sliced path and the
    /// checker runs directly against the invariant. Returns
    /// `(result, path_description)` pairs.
    pub(super) fn check_invariant_from_tree(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        invariant: &Property<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let def_id = self.target.def_id;
        let target_block = checkpoint.block.as_usize();
        let goals = self.slicer.visit_path_tree_for_checkpoint(
            tree,
            target_block,
            def_id,
            checkpoint,
            invariant,
        );
        let fake_checkpoint = Checkpoint {
            caller: def_id,
            callee: None,
            block: checkpoint.block,
            args: Vec::new(),
            kind: crate::verify::checkpoint::CheckpointKind::UnsafeCall,
            requires: Vec::new(),
            destination: None,
            is_mut_ref: false,
            stmt_index: 0,
        };
        self.check_goals(
            cache,
            tree,
            goals,
            &fake_checkpoint,
            invariant,
            entry_facts,
            false,
        )
    }

    /// Replay sliced paths and check one property, shared by callsite and invariant checks.
    fn check_goals(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        tree: &PathTree,
        goals: impl IntoIterator<Item = ProofGoal<'tcx>>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
        forward_drop_alias: bool,
    ) -> Vec<(CheckResult, String)> {
        goals
            .into_iter()
            .map(|mut goal| {
                let path_desc = goal.path.describe_caller_indices(tree);
                let alias_result = forward_drop_alias.then(|| {
                    let slot = self.drop_referent_local(tree, checkpoint, &goal.path.blocks);
                    self.drop_alias_for_prefix(tree, checkpoint, &goal.path.blocks, slot)
                });
                if !entry_facts.is_empty() {
                    let mut items = entry_facts.to_vec();
                    items.append(&mut goal.items);
                    goal.items = items;
                }
                goal.items = self.inject_inline_boundaries(goal.items, tree);
                let cached = cache.states_for(self.tcx, self.target.def_id, self.target.body, goal);
                let result = cached
                    .states
                    .iter()
                    .zip(&cached.reachability)
                    .map(|(vm_state, reachability)| {
                        if let Some(alias_result) = &alias_result {
                            Self::check_with_forward_alias(
                                vm_state,
                                checkpoint,
                                property,
                                tree.is_structural(),
                                reachability,
                                alias_result,
                            )
                        } else {
                            PropertyChecker.check(
                                vm_state,
                                checkpoint,
                                property,
                                tree.is_structural(),
                                reachability,
                            )
                        }
                    })
                    .fold(CheckResult::ProvedByRule, CheckResult::and);
                (result, path_desc)
            })
            .collect()
    }
}
