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
use crate::def_ids;
use crate::contract::{self, AndProperty, AtomProperty, OrProperty, Property, PropertyKind};
use crate::util::mir_utils;
use crate::vm::VmExecutor;
use crate::verify::{
    checkpoint::{Checkpoint, CheckpointKind, CheckpointLocation},
    property_checker::PropertyChecker,
    proof_cache::VmCache,
    report::{CheckResult, UnknownReason},
    slicer::{ProofGoal, RelevantItem},
};

use super::FunctionVerifier;

enum LocalAccess {
    None,
    Read,
    Reinitialized,
}

impl<'target, 'tcx> FunctionVerifier<'target, 'tcx> {
    pub(super) fn property_contains_alias(property: &Property<'_>) -> bool {
        match property {
            Property::Atom(atom) => atom.kind == PropertyKind::Alias,
            Property::And(and) => and.conjuncts.iter().any(Self::property_contains_alias),
            Property::Or(or) => or.disjuncts.iter().any(Self::property_contains_alias),
        }
    }

    /// Check a checkpoint's properties in path order.
    pub(super) fn check_checkpoint_properties(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        properties: &[Property<'tcx>],
    ) -> Vec<(String, usize, CheckResult)> {
        let conjuncts = Self::collect_conjuncts(properties);
        let path_results = self.check_flattened_conjuncts(cache, checkpoint, &conjuncts);
        let mut results = Vec::new();
        for mut conjunct_results in path_results {
            let mut next_conjunct = 0;
            for (property_index, property) in properties.iter().enumerate() {
                if let Some((result, path_desc)) = Self::combine_conjuncts_on_path(property, &mut conjunct_results, &mut next_conjunct) {
                    results.push((path_desc, property_index, result));
                }
            }
        }
        results
    }

    /// Flatten conjunctions so each child can use the shared path replay.
    fn collect_conjuncts<'a>(properties: &'a [Property<'tcx>]) -> Vec<&'a Property<'tcx>> {
        fn append<'a, 'tcx>(property: &'a Property<'tcx>, conjuncts: &mut Vec<&'a Property<'tcx>>) {
            if let Property::And(and) = property {
                for child in &and.conjuncts {
                    append(child, conjuncts);
                }
            } else {
                conjuncts.push(property);
            }
        }

        let mut conjuncts = Vec::new();
        for property in properties {
            append(property, &mut conjuncts);
        }
        conjuncts
    }

    fn combine_conjuncts_on_path(
        property: &Property<'tcx>,
        conjunct_results: &mut [Option<(CheckResult, String)>],
        next_conjunct: &mut usize,
    ) -> Option<(CheckResult, String)> {
        if let Property::And(and) = property {
            let children: Vec<_> = and.conjuncts.iter().map(|child| {
                Self::combine_conjuncts_on_path(child, conjunct_results, next_conjunct)
            }).collect();
            let description = children.iter().find_map(|child| child.as_ref().map(|(_, path)| path.clone()))?;
            let result = children.into_iter().map(|child| child.expect("each path checks every conjunct"))
                .fold(CheckResult::ProvedByRule, |acc, (result, _)| acc.and(result));
            return Some((result, description));
        }
        let result = conjunct_results[*next_conjunct].take();
        *next_conjunct += 1;
        result
    }

    /// Replay one combined slice per path, then check its properties.
    fn check_flattened_conjuncts(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        properties: &[&Property<'tcx>],
    ) -> Vec<Vec<Option<(CheckResult, String)>>> {
        let manual_drop = def_ids::is_manually_drop_drop(self.tcx, checkpoint.callee);
        let drop_alias = manual_drop && properties.iter().any(|property| property.kind() == Some(PropertyKind::Alias));
        let selected: Vec<_> = properties.iter().enumerate()
            .filter(|(_, property)| !(manual_drop && property.kind() == Some(PropertyKind::Alias)))
            .collect();
        let mut results = Vec::new();
        if !selected.is_empty() || drop_alias {
            let tree = &self.path_tree;
            let selected_properties: Vec<_> = selected.iter().map(|(_, property)| **property).collect();
            let bound: Vec<_> = selected_properties.iter()
                .map(|property| Self::bind_property_to_checkpoint(property, checkpoint))
                .collect();
            let entry_facts: Vec<_> = self.target.caller_requires.iter()
                .filter(|property| property.kind() != Some(PropertyKind::Unknown))
                .map(|property| RelevantItem::ContractFact { property: property.clone() })
                .collect();
            let needs_post_deref = checkpoint.kind == CheckpointKind::RawPtrDeref
                && selected_properties.iter().any(|property| property.kind() == Some(PropertyKind::Alias));
            let slice_properties = if selected_properties.is_empty() { properties.to_vec() } else { selected_properties };
            for goal in self.slicer.visit_path_tree_batch(tree, checkpoint, &slice_properties).into_iter().rev() {
                let mut path_results = vec![None; properties.len()];
                let description = goal.path.describe_caller_indices(tree);
                if drop_alias {
                    let result = self.check_drop_on_prefix(checkpoint, &goal.path.blocks);
                    for (index, property) in properties.iter().enumerate() {
                        if property.kind() == Some(PropertyKind::Alias) {
                            path_results[index] = Some((result.clone(), description.clone()));
                        }
                    }
                }
                if selected.is_empty() {
                    results.push(path_results);
                    continue;
                }
                let goal = self.prepare_goal(tree, goal, &entry_facts);
                let deref_position = needs_post_deref.then(|| goal.items.iter().rposition(|item| {
                    matches!(item, RelevantItem::Statement { def_id, block, stmt_index, .. }
                        if *def_id == checkpoint.caller && *block == checkpoint.block
                            && *stmt_index == checkpoint.stmt_index)
                })).flatten();
                let split = deref_position.unwrap_or(goal.items.len());
                let pre_goal = ProofGoal { path: goal.path.clone(), items: goal.items[..split].to_vec() };
                let cached = cache.states_for(self.tcx, self.target.def_id, self.target.body, pre_goal);
                let post_states = deref_position.map(|_| VmExecutor::execute_items_after(cached.states.as_ref().clone(), &goal.items[split..]));
                let post_reachability = post_states.as_ref().map(|states| states.iter().map(|_| Cell::new(None)).collect::<Vec<_>>());
                for ((index, property), bound_property) in selected.iter().zip(&bound) {
                    let post_deref = needs_post_deref && property.kind() == Some(PropertyKind::Alias);
                    if post_deref && post_states.is_none() {
                        path_results[*index] = Some((CheckResult::Unknown(UnknownReason::Unimplemented), description.clone()));
                        continue;
                    }
                    let (states, reachability) = match (&post_states, &post_reachability) {
                        (Some(states), Some(reachability)) if post_deref => (states.as_slice(), reachability.as_slice()),
                        _ => (cached.states.as_slice(), cached.reachability.as_slice()),
                    };
                    let result = states.iter().zip(reachability)
                        .map(|(state, reachability)| PropertyChecker.check(state, checkpoint, bound_property, tree.is_structural(), reachability))
                        .fold(CheckResult::ProvedByRule, CheckResult::and);
                    path_results[*index] = Some((result, description.clone()));
                }
                results.push(path_results);
            }
        }
        results
    }

    /// Check every path suffix after one occurrence of a `ManuallyDrop::drop` checkpoint.
    ///
    /// `ManuallyDrop::drop(&mut slot)` drops the contained value while the
    /// wrapper remains live. A later read can use a dropped value. This forward
    /// obligation scans each path suffix after the call.
    fn check_drop_on_prefix(&self, checkpoint: &Checkpoint<'tcx>, prefix: &[usize]) -> CheckResult {
        let tree = &self.path_tree;
        let Some(slot) = self.drop_referent_local(tree, checkpoint, prefix) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let mut found = false;
        for path in tree.iter().filter(|path| path.starts_with(prefix)) {
            found = true;
            if self.drop_suffix_reads(tree, checkpoint.caller, slot, &path[prefix.len()..]) {
                return CheckResult::Failed;
            }
        }
        if found { CheckResult::ProvedByRule } else { CheckResult::Unknown(UnknownReason::Unimplemented) }
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
                for stmt_index in (0..end).rev() {
                    let StatementKind::Assign(assign) = &statements[stmt_index].kind else {
                        continue;
                    };
                    let (target, rvalue) = assign.as_ref();
                    if target.local == cur && target.projection.is_empty() {
                        source = Some((rvalue, path_index, stmt_index));
                        break 'find;
                    }
                }
            }
            let Some((rvalue, path_index, stmt_index)) = source else {
                // A parameter can be the caller's `&mut slot`. A local with no
                // visible definition may come from a call, which we cannot trace.
                return (cur.as_usize() > 0 && cur.as_usize() <= body.arg_count).then_some(cur);
            };
            before = (path_index, stmt_index);
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
                        contract::PropertyArg::ForEach(expr) => contract::PropertyArg::ForEach(
                            Self::rebind_contract_expr(expr, checkpoint),
                        ),
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
                    origin: None,
                })
            }
            Property::And(and) => Property::And(AndProperty {
                conjuncts: and
                    .conjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect(),
                origin: None,
            }),
            Property::Or(or) => Property::Or(OrProperty {
                disjuncts: or
                    .disjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect(),
                origin: None,
            }),
        }
    }

    /// Rewrite a contract place's base to the checkpoint's view.
    ///
    /// `Return` and `Arg` bases are unchanged; a `Local(n)` that falls within
    /// the checkpoint's argument range is remapped to `Arg(n - 1)` (locals
    /// 1..=k correspond to the callee's arguments in order).
    fn rebind_base(base: &contract::PlaceBase, checkpoint: &Checkpoint<'tcx>) -> contract::PlaceBase {
        match *base {
            contract::PlaceBase::Return => contract::PlaceBase::Return,
            contract::PlaceBase::Arg(n) => contract::PlaceBase::Arg(n),
            contract::PlaceBase::Local(n) => {
                if n > 0 && n <= checkpoint.args.len() {
                    contract::PlaceBase::Arg(n - 1)
                } else {
                    contract::PlaceBase::Local(n)
                }
            }
        }
    }

    fn rebind_place(place: &contract::ContractPlace, checkpoint: &Checkpoint<'tcx>) -> contract::ContractPlace {
        contract::ContractPlace {
            base: Self::rebind_base(&place.base, checkpoint),
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

    /// Replay one exit path and check all properties active on it.
    pub(super) fn check_exit_goal(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        properties: &[&Property<'tcx>],
        entry_facts: &[RelevantItem<'tcx>],
        goal: ProofGoal<'tcx>,
    ) -> Vec<CheckResult> {
        let def_id = self.target.def_id;
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
        let goal = self.prepare_goal(tree, goal, entry_facts);
        let cached = cache.states_for(self.tcx, self.target.def_id, self.target.body, goal);
        properties.iter().map(|property| {
            cached.states.iter().zip(&cached.reachability)
                .map(|(state, reachability)| {
                    PropertyChecker.check(state, &fake_checkpoint, property, tree.is_structural(), reachability)
                })
                .fold(CheckResult::ProvedByRule, CheckResult::and)
        }).collect()
    }

    fn prepare_goal(
        &self,
        tree: &PathTree,
        mut goal: ProofGoal<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
    ) -> ProofGoal<'tcx> {
        if !entry_facts.is_empty() {
            let mut items = entry_facts.to_vec();
            items.append(&mut goal.items);
            goal.items = items;
        }
        goal.items = self.inject_inline_boundaries(goal.items, tree);
        goal
    }

}
