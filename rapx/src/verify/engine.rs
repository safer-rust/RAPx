//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use crate::helpers::mir_utils;
use z3::Config;

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, Rvalue, StatementKind};
use rustc_middle::mir::Body;
use rustc_middle::ty::TyCtxt;

use crate::analysis::path::PathTree;

use super::{
    contract::{AndProperty, AtomProperty, OrProperty, Property},
    report::{CheckResult, UnknownReason},
    slicer::{BackwardSlicer, ProofGoal, RelevantItem},
};
use crate::verify::checkpoint::{Checkpoint, CheckpointLocation};

use super::property_checker::PropertyChecker;
use super::target::CalleeBodies;

enum LocalAccess {
    None,
    Read,
    Reinitialized,
}

/// The three verification stages: a backward [`BackwardSlicer`], symbolic MIR
/// execution, and a [`PropertyChecker`].
pub(crate) struct VerifyEngine<'tcx> {
    tcx: TyCtxt<'tcx>,
    slicer: BackwardSlicer<'tcx>,
    caller_def_id: DefId,
    instance_body: Option<&'tcx Body<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    assume_struct_invariants: bool,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Construct a fresh engine wired to `tcx`.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        caller_def_id: DefId,
        instance_body: Option<&'tcx Body<'tcx>>,
        callee_bodies: CalleeBodies<'tcx>,
        assume_struct_invariants: bool,
    ) -> Self {
        Self {
            tcx,
            slicer: BackwardSlicer::new(tcx, caller_def_id, instance_body, callee_bodies.clone()),
            caller_def_id,
            instance_body,
            callee_bodies,
            assume_struct_invariants,
        }
    }

    /// Create a fresh Z3 context with a fixed 10s solver timeout.
    ///
    /// A new context is created per top-level check so that each verification
    /// runs in isolation (no shared solver state leaks between checks).
    fn new_z3_context() -> z3::Context {
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
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
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
            tree,
            goals.into_iter().rev(),
            checkpoint,
            &bound_property,
            &entry_facts,
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
                    for &g2 in &path[pos + 1..] {
                        let Some((def2, local2)) = tree.block_fn_of(g2) else {
                            continue;
                        };
                        if def2 != caller {
                            continue;
                        }
                        match Self::block_local_access(self.tcx, caller, local2, slot) {
                            LocalAccess::None => {}
                            LocalAccess::Read => {
                                used = true;
                                break;
                            }
                            LocalAccess::Reinitialized => break,
                        }
                    }
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
            use rustc_middle::mir::TerminatorKind;
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

    /// Insert `CalleeEntry`/`CalleeExit` markers into a forward item stream by
    /// detecting `def_id` transitions (caller → callee → caller). Each inlined
    /// callee entry carries its argument binding; each exit writes the callee's
    /// return value back to the caller's destination.
    ///
    /// `local_to_global` maps `(def_id, local_block)` pairs to the list of
    /// their global block indices in `tree` (a callee inlined at multiple call
    /// sites has several entries, in path order); it is precomputed by the
    /// caller so it can be reused across every checkpoint instead of rebuilt
    /// per path.
    fn inject_inline_boundaries(
        tcx: TyCtxt<'tcx>,
        callee_bodies: &CalleeBodies<'tcx>,
        items: Vec<RelevantItem<'tcx>>,
        tree: &PathTree,
        local_to_global: &HashMap<(DefId, usize), Vec<usize>>,
        path_blocks: &HashSet<usize>,
        caller: DefId,
    ) -> Vec<RelevantItem<'tcx>> {
        let mut out: Vec<RelevantItem<'tcx>> = Vec::new();
        // Begin in the caller to emit the first inlined callee entry.
        let mut prev_def_id: Option<DefId> = Some(caller);
        // Distinguishes inlined call sites whose other statements were sliced out.
        let mut prev_arg: Option<usize> = None;
        // Active callees, innermost last; entry blocks identify their parents.
        let mut active: Vec<(DefId, usize, usize)> = Vec::new();
        let mut entry_cursor: HashMap<(DefId, DefId), usize> = HashMap::new();

        for item in items {
            let (cur_def_id, cur_arg, cur_is_term) = match &item {
                RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                } => {
                    let body = callee_bodies.get(def_id).copied()
                        .unwrap_or_else(|| tcx.optimized_mir(*def_id));
                    let dest = match &body.basic_blocks[*block].statements[*statement_index].kind {
                        StatementKind::Assign(assign) => Some(assign.0.local.as_usize()),
                        _ => None,
                    };
                    (Some(*def_id), dest, false)
                }
                RelevantItem::Terminator { def_id, .. } => (Some(*def_id), None, true),
                _ => (None, None, false),
            };

            if let Some(cur) = cur_def_id {
                if let Some(prev) = prev_def_id
                    && prev != cur
                {
                    if cur == caller {
                        // The slice may omit several nested return blocks.
                        while let Some((_, dest, _)) = active.pop() {
                            out.push(RelevantItem::CalleeExit { dest });
                        }
                    } else {
                        // An active `cur` is an ascent, possibly across omitted returns.
                        let is_ascent = active.iter().any(|(d, _, _)| *d == cur);
                        if is_ascent {
                            while let Some(&(top_def, _, _)) = active.last() {
                                if top_def == cur {
                                    break;
                                }
                                let (_, dest, _) = active.pop().unwrap();
                                out.push(RelevantItem::CalleeExit { dest });
                            }
                        } else {
                            let current_parent =
                                active.last().map(|(d, _, _)| *d).unwrap_or(caller);

                            // Skip ancestors with no retained slice items.
                            let eff_parent = |g: usize| -> DefId {
                                let mut p = tree.call_parent(g);
                                while let Some(pd) = p {
                                    if pd == caller || active.iter().any(|(d, _, _)| *d == pd) {
                                        return pd;
                                    }
                                    p = local_to_global
                                        .get(&(pd, 0))
                                        .and_then(|gs| gs.first().copied())
                                        .and_then(|pe| tree.call_parent(pe));
                                }
                                caller
                            };

                            let mut cur_entry: Option<usize> = None;
                            if let Some(globals) = local_to_global.get(&(cur, 0)) {
                                let mut matching: Vec<usize> = globals
                                    .iter()
                                    .copied()
                                    .filter(|&g| {
                                        path_blocks.contains(&g) && eff_parent(g) == current_parent
                                    })
                                    .collect();
                                if matching.is_empty() {
                                    matching = globals
                                        .iter()
                                        .copied()
                                        .filter(|g| path_blocks.contains(g))
                                        .collect();
                                }
                                // Match single-arg and pointer-arithmetic calls by argument;
                                // other calls use the positional cursor.
                                let all_single_arg = matching.iter().all(|&g| {
                                    tree.call_binding(g).map(|b| b.arg_locals.len()) == Some(1)
                                });
                                let is_ptr_arith =
                                    crate::verify::api_classify::is_pointer_add(Some(cur))
                                        || crate::verify::api_classify::is_pointer_sub(Some(cur));
                                if (all_single_arg || is_ptr_arith)
                                    && let Some(arg) = prev_arg
                                {
                                    let by_arg: Vec<usize> = matching
                                        .iter()
                                        .copied()
                                        .filter(|&g| {
                                            tree.call_binding(g)
                                                .is_some_and(|b| b.arg_locals.contains(&arg))
                                        })
                                        .collect();
                                    if !by_arg.is_empty() {
                                        matching = by_arg;
                                    }
                                }
                                let pool: &[usize] = matching.as_slice();
                                let idx = if pool.len() == 1 {
                                    0
                                } else {
                                    let cursor =
                                        entry_cursor.entry((cur, current_parent)).or_insert(0);
                                    let idx = *cursor;
                                    *cursor = (*cursor + 1).min(pool.len() - 1);
                                    idx
                                };
                                cur_entry = pool.get(idx).copied();
                            }

                            let eff = cur_entry.map(eff_parent).unwrap_or(caller);
                            let mut skipped: Vec<(DefId, usize)> = Vec::new();
                            {
                                let mut p = cur_entry.and_then(|g| tree.call_parent(g));
                                while let Some(pd) = p {
                                    if pd == eff {
                                        break;
                                    }
                                    if let Some(pe) = local_to_global
                                        .get(&(pd, 0))
                                        .and_then(|gs| gs.first().copied())
                                    {
                                        skipped.push((pd, pe));
                                        p = tree.call_parent(pe);
                                    } else {
                                        break;
                                    }
                                }
                            }

                            while let Some(&(top_def, _, _)) = active.last() {
                                if top_def == eff {
                                    break;
                                }
                                let (_, dest, _) = active.pop().unwrap();
                                out.push(RelevantItem::CalleeExit { dest });
                            }
                            for (pd, pe) in skipped.iter().rev() {
                                if let Some(binding) = tree.call_binding(*pe) {
                                    out.push(RelevantItem::CalleeEntry {
                                        callee: *pd,
                                        body: callee_bodies.get(pd).copied(),
                                        args: binding.arg_locals.clone(),
                                        consts: binding.arg_consts.clone(),
                                        field_offsets: binding.arg_field_offsets.clone(),
                                    });
                                    active.push((*pd, binding.dest_local, *pe));
                                }
                            }
                            if let Some(&global) = cur_entry.as_ref()
                                && let Some(binding) = tree.call_binding(global)
                            {
                                out.push(RelevantItem::CalleeEntry {
                                    callee: cur,
                                    body: callee_bodies.get(&cur).copied(),
                                    args: binding.arg_locals.clone(),
                                    consts: binding.arg_consts.clone(),
                                    field_offsets: binding.arg_field_offsets.clone(),
                                });
                                active.push((cur, binding.dest_local, global));
                            }
                        }
                    }
                }
                prev_def_id = Some(cur);
                // Non-value statements retain the last argument local; terminators clear it.
                if cur_arg.is_some() {
                    prev_arg = cur_arg;
                } else if cur_is_term {
                    prev_arg = None;
                }
            }

            out.push(item);
        }

        while let Some((_, dest, _)) = active.pop() {
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
            destination: None,
            is_mut_ref: false,
            statement_index: 0,
        };
        self.check_goals(tree, goals, &fake_checkpoint, invariant, entry_facts)
    }

    /// Replay sliced paths and check one property, shared by callsite and invariant checks.
    fn check_goals(
        &self,
        tree: &PathTree,
        goals: impl IntoIterator<Item = ProofGoal<'tcx>>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        entry_facts: &[RelevantItem<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let z3_ctx = Self::new_z3_context();
        let mut local_to_global: HashMap<(DefId, usize), Vec<usize>> = HashMap::new();
        for (global, (def_id, local)) in tree.block_fns().iter().enumerate() {
            local_to_global
                .entry((*def_id, *local))
                .or_default()
                .push(global);
        }

        goals
            .into_iter()
            .flat_map(|mut goal| {
                let path_blocks: HashSet<usize> = goal.path.blocks.iter().copied().collect();
                let path_desc = goal.path.describe_caller_indices(tree);
                if !entry_facts.is_empty() {
                    let mut items = entry_facts.to_vec();
                    items.append(&mut goal.items);
                    goal.items = items;
                }
                goal.items = Self::inject_inline_boundaries(
                    self.tcx,
                    &self.callee_bodies,
                    goal.items,
                    tree,
                    &local_to_global,
                    &path_blocks,
                    checkpoint.caller,
                );
                super::vm::execute_goal(
                    &z3_ctx,
                    self.tcx,
                    self.caller_def_id,
                    self.instance_body,
                    self.assume_struct_invariants,
                    goal,
                )
                .into_iter()
                .map(|vm_state| {
                    let result = PropertyChecker.check(
                        &vm_state,
                        checkpoint,
                        property,
                        tree.is_structural(),
                    );
                    (result, path_desc.clone())
                })
                .collect::<Vec<_>>()
            })
            .collect()
    }
}
