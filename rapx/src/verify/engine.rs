//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use crate::helpers::mir_utils;
use std::{cell::Cell, sync::Arc};
use z3::Config;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use crate::analysis::path::{CallArg, PathTree};
use crate::compat::FxHashMap;

use super::{
    checkpoint::{Checkpoint, CheckpointLocation},
    contract::{AndProperty, AtomProperty, OrProperty, Property},
    path::EntryBodies,
    property_checker::PropertyChecker,
    report::{CheckResult, UnknownReason},
    slicer::{BackwardSlicer, ProofGoal, RelevantItem},
    target::CalleeBodies,
    vm::VmState,
};

enum LocalAccess {
    None,
    Read,
    Reinitialized,
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum GoalItemKey<'tcx> {
    Statement(DefId, BasicBlock, Option<usize>, usize),
    Terminator(DefId, BasicBlock, Option<usize>, Option<BasicBlock>),
    CalleeEntry(DefId, Option<usize>, Vec<CallArg>),
    CalleeExit(usize),
    ContractFact(Property<'tcx>),
}

#[derive(Hash, PartialEq, Eq)]
struct PrefixEdge<'tcx> {
    parent: usize,
    chunk: Vec<GoalItemKey<'tcx>>,
}

/// Symbolic states shared by properties that retain the same MIR and entry facts.
pub(crate) struct VmCache<'z3, 'tcx> {
    context: &'z3 z3::Context,
    states: FxHashMap<Vec<GoalItemKey<'tcx>>, CachedGoal<'z3, 'tcx>>,
    prefix_edges: FxHashMap<PrefixEdge<'tcx>, usize>,
    prefix_states: Vec<Arc<Vec<VmState<'z3, 'tcx>>>>,
    max_entries: usize,
}

struct CachedGoal<'z3, 'tcx> {
    states: Arc<Vec<VmState<'z3, 'tcx>>>,
    reachability: Vec<Cell<Option<z3::SatResult>>>,
}

const VM_CACHE_MAX_ENTRIES: usize = 128;
const VM_PREFIX_STRIDE: usize = 16;

impl<'z3, 'tcx> VmCache<'z3, 'tcx> {
    pub(crate) fn new(context: &'z3 z3::Context) -> Self {
        Self::new_with_capacity(context, VM_CACHE_MAX_ENTRIES)
    }

    pub(crate) fn new_with_capacity(context: &'z3 z3::Context, max_entries: usize) -> Self {
        Self {
            context,
            states: FxHashMap::default(),
            prefix_edges: FxHashMap::default(),
            prefix_states: Vec::new(),
            max_entries,
        }
    }

    fn states_for(
        &mut self,
        engine: &VerifyEngine<'tcx>,
        goal: ProofGoal<'tcx>,
    ) -> &CachedGoal<'z3, 'tcx> {
        let key = goal_key(&goal.items);
        if self.states.contains_key(&key) {
            return self.states.get(&key).unwrap();
        }
        if self.states.len() >= self.max_entries {
            self.states.clear();
        }
        if self.prefix_states.len() >= self.max_entries.saturating_mul(4).max(1) {
            self.prefix_edges.clear();
            self.prefix_states.clear();
        }
        let mut prefix_len = 0;
        let mut parent = 0;
        while prefix_len + VM_PREFIX_STRIDE < key.len() {
            let edge = PrefixEdge {
                parent,
                chunk: key[prefix_len..prefix_len + VM_PREFIX_STRIDE].to_vec(),
            };
            let Some(&next) = self.prefix_edges.get(&edge) else {
                break;
            };
            parent = next;
            prefix_len += VM_PREFIX_STRIDE;
        }
        let mut states = if prefix_len > 0 {
            Arc::clone(&self.prefix_states[parent - 1])
        } else {
            Arc::new(
                VmState::new(
                    self.context,
                    engine.tcx,
                    engine.caller_def_id,
                    engine.instance_body,
                )
                .execute_items(&[]),
            )
        };
        while prefix_len < key.len() {
            let end = ((prefix_len / VM_PREFIX_STRIDE) + 1)
                .saturating_mul(VM_PREFIX_STRIDE)
                .min(key.len());
            if states
                .iter()
                .any(|state| !state.diagnostics.is_unsupported())
            {
                let owned =
                    Arc::try_unwrap(states).unwrap_or_else(|shared| shared.as_ref().clone());
                states = Arc::new(VmState::execute_items_after(
                    owned,
                    &goal.items[prefix_len..end],
                ));
            }
            if end < key.len() {
                let edge = PrefixEdge {
                    parent,
                    chunk: key[prefix_len..end].to_vec(),
                };
                parent = self.prefix_states.len() + 1;
                self.prefix_edges.insert(edge, parent);
                self.prefix_states.push(Arc::clone(&states));
            }
            prefix_len = end;
        }
        let reachability = states.iter().map(|_| Cell::new(None)).collect();
        self.states.insert(
            key.clone(),
            CachedGoal {
                states,
                reachability,
            },
        );
        self.states.get(&key).unwrap()
    }
}

fn goal_key<'tcx>(items: &[RelevantItem<'tcx>]) -> Vec<GoalItemKey<'tcx>> {
    items
        .iter()
        .map(|item| match item {
            RelevantItem::Statement {
                def_id,
                block,
                global_block,
                statement_index,
            } => GoalItemKey::Statement(*def_id, *block, *global_block, *statement_index),
            RelevantItem::Terminator {
                def_id,
                block,
                global_block,
                switch_succ,
            } => GoalItemKey::Terminator(*def_id, *block, *global_block, *switch_succ),
            RelevantItem::CalleeEntry { callee, body, args } => GoalItemKey::CalleeEntry(
                *callee,
                body.map(|body| body as *const _ as usize),
                args.clone(),
            ),
            RelevantItem::CalleeExit { dest } => GoalItemKey::CalleeExit(*dest),
            RelevantItem::ContractFact { property } => GoalItemKey::ContractFact(property.clone()),
        })
        .collect()
}

/// The three verification stages: a backward [`BackwardSlicer`], symbolic MIR
/// execution, and a [`PropertyChecker`].
pub(crate) struct VerifyEngine<'tcx> {
    tcx: TyCtxt<'tcx>,
    slicer: BackwardSlicer<'tcx>,
    caller_def_id: DefId,
    instance_body: Option<&'tcx Body<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    entry_bodies: EntryBodies<'tcx>,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Construct a fresh engine wired to `tcx`.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        caller_def_id: DefId,
        instance_body: Option<&'tcx Body<'tcx>>,
        callee_bodies: CalleeBodies<'tcx>,
        entry_bodies: EntryBodies<'tcx>,
    ) -> Self {
        Self {
            tcx,
            slicer: BackwardSlicer::new(
                tcx,
                caller_def_id,
                instance_body,
                callee_bodies.clone(),
                entry_bodies.clone(),
            ),
            caller_def_id,
            instance_body,
            callee_bodies,
            entry_bodies,
        }
    }

    /// Create a fresh Z3 context with a fixed 10s solver timeout.
    ///
    /// A new context is created per verification phase.
    pub(crate) fn new_z3_context() -> z3::Context {
        let mut cfg = Config::new();
        cfg.set_timeout_msec(10000);
        z3::Context::new(&cfg)
    }

    /// Verify a property against every path reaching `checkpoint`, one result
    /// per path. Each path is sliced backward from the checkpoint, replayed
    /// symbolically by the VM, and finally discharged by the property checker.
    ///
    /// Returns `(result, path_description)` pairs in forward MIR order.
    pub(crate) fn check_callsite_from_tree(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
        forward_drop_alias: bool,
    ) -> Vec<(CheckResult, String)> {
        let target_block = checkpoint.block.as_usize();
        let goals = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);
        let bound_property = Self::bind_property_to_checkpoint(property, checkpoint);
        let entry_facts: Vec<_> = caller_contracts
            .iter()
            .filter(|c| !matches!(c.kind(), Some(super::contract::PropertyKind::Unknown)))
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
    pub(crate) fn check_drop_from_tree(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
    ) -> Vec<(CheckResult, String)> {
        let Some(slot) = self.drop_referent_local(checkpoint) else {
            return vec![(
                CheckResult::Unknown(UnknownReason::Unimplemented),
                String::new(),
            )];
        };
        let caller = checkpoint.caller;
        let target = checkpoint.block.as_usize();

        let mut results: Vec<(CheckResult, String)> = Vec::new();
        for path in tree.iter() {
            let mut used = false;
            let mut reaches = false;
            for (pos, &g) in path.iter().enumerate() {
                let Some((def, local)) = tree.block_fn_of(g) else {
                    continue;
                };
                if def == caller && local == target {
                    reaches = true;
                    used |= self.drop_suffix_reads(tree, caller, slot, &path[pos + 1..]);
                }
            }
            if reaches {
                let desc = format!("{:?}", path);
                if used {
                    results.push((CheckResult::Failed, desc));
                } else {
                    results.push((CheckResult::ProvedByRule, desc));
                }
            }
        }

        if results.is_empty() {
            vec![(CheckResult::ProvedByRule, String::new())]
        } else {
            results
        }
    }

    /// Resolve the `&mut slot` borrow operand of a `Drop(slot)` checkpoint to the
    /// referent local (`slot` itself, e.g. `_1`).  The optimized MIR lowers
    /// `drop(&mut slot)` to a reborrow chain (`_7 = &mut (*_8)`, `_8 = &mut _1`),
    /// so follow both direct borrows (`&mut _1`) and deref reborrows
    /// (`&mut (*_8)`) back to the ultimate referent.
    fn drop_referent_local(&self, checkpoint: &Checkpoint<'tcx>) -> Option<Local> {
        let arg = checkpoint.args.first()?;
        let place = mir_utils::operand_mir_place(arg)?;
        let mut cur = place.local;
        let body = self.tcx.optimized_mir(checkpoint.caller);
        let mut seen = std::collections::HashSet::new();
        loop {
            if !seen.insert(cur) {
                return Some(cur);
            }
            let mut next: Option<Local> = None;
            'outer: for bb in body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        let (target, rvalue) = assign.as_ref();
                        if target.local == cur
                            && target.projection.is_empty()
                            && let Rvalue::Ref(_, _, referent) = rvalue
                        {
                            next = Some(referent.local);
                            break 'outer;
                        }
                    }
                }
            }
            match next {
                Some(l) => cur = l,
                None => return Some(cur),
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
                        #[cfg(rapx_ge_95)]
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
                        #[cfg(rapx_ge_95)]
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
                    #[cfg(rapx_ge_95)]
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
            Property::Atom(atom) if atom.kind == super::contract::PropertyKind::Alias => {
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
            Property::Or(or) => or.disjuncts.iter().fold(CheckResult::Failed, |acc, child| {
                acc.or(Self::check_with_forward_alias(
                    vm_state,
                    checkpoint,
                    child,
                    structural,
                    reachability,
                    alias_result,
                ))
            }),
        }
    }

    /// Insert callee boundaries from each retained item's callsite ancestry.
    fn inject_inline_boundaries(
        callee_bodies: &CalleeBodies<'tcx>,
        entry_bodies: &EntryBodies<'tcx>,
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
                        body: entry_bodies
                            .get(&entry)
                            .copied()
                            .or_else(|| callee_bodies.get(&callee).copied()),
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
                let new_args: Vec<super::contract::PropertyArg<'tcx>> = atom
                    .args
                    .iter()
                    .map(|a| match a {
                        super::contract::PropertyArg::Expr(expr) => {
                            super::contract::PropertyArg::Expr(Self::rebind_contract_expr(
                                expr, checkpoint,
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

    /// Recursively rewrite every place embedded in a contract expression,
    /// rebinding `Local` bases to argument positions via [`Self::rebind_place`].
    fn rebind_contract_expr(
        expr: &super::contract::ContractExpr<'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> super::contract::ContractExpr<'tcx> {
        match expr {
            super::contract::ContractExpr::Place(place) => {
                super::contract::ContractExpr::Place(Self::rebind_place(place, checkpoint))
            }
            super::contract::ContractExpr::Len(inner, method) => {
                super::contract::ContractExpr::Len(
                    Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                    *method,
                )
            }
            super::contract::ContractExpr::MethodCall {
                receiver,
                method,
                args,
            } => super::contract::ContractExpr::MethodCall {
                receiver: Box::new(Self::rebind_contract_expr(receiver, checkpoint)),
                method: *method,
                args: args
                    .iter()
                    .map(|arg| Self::rebind_contract_expr(arg, checkpoint))
                    .collect(),
            },
            super::contract::ContractExpr::IsEmpty(inner, method) => {
                super::contract::ContractExpr::IsEmpty(
                    Box::new(Self::rebind_contract_expr(inner, checkpoint)),
                    *method,
                )
            }
            super::contract::ContractExpr::SizeOf(_)
            | super::contract::ContractExpr::AlignOf(_)
            | super::contract::ContractExpr::Const(_)
            | super::contract::ContractExpr::ConstParam { .. }
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
            super::contract::ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => super::contract::ContractExpr::If {
                cond: Box::new(super::contract::NumericPredicate::new(
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
    /// Unlike [`Self::check_callsite_from_tree`], there is no callsite to bind
    /// against, so `entry_facts` are prepended to each sliced path and the
    /// checker runs directly against the invariant. Returns
    /// `(result, path_description)` pairs.
    pub(crate) fn check_invariant_from_tree(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        def_id: DefId,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        invariant: &Property<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
    ) -> Vec<(CheckResult, String)> {
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
            statement_index: 0,
            site_ordinal: 0,
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
        let drop_slot = forward_drop_alias.then(|| self.drop_referent_local(checkpoint));
        goals
            .into_iter()
            .map(|mut goal| {
                let path_desc = goal.path.describe_caller_indices(tree);
                let alias_result = drop_slot.map(|slot| {
                    self.drop_alias_for_prefix(tree, checkpoint, &goal.path.blocks, slot)
                });
                if !entry_facts.is_empty() {
                    let mut items = entry_facts.to_vec();
                    items.append(&mut goal.items);
                    goal.items = items;
                }
                goal.items = Self::inject_inline_boundaries(
                    &self.callee_bodies,
                    &self.entry_bodies,
                    goal.items,
                    tree,
                );
                let cached = cache.states_for(self, goal);
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
