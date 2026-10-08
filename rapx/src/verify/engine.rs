//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use z3::Config;

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::TyCtxt;

use crate::analysis::path::PathTree;

use super::{
    contract::{AndProperty, AtomProperty, OrProperty, Property},
    report::{CheckResult, UnknownReason},
    slicer::{BackwardSlicer, RelevantItem},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use super::{
    property_checker::PropertyChecker,
    vm::SymbolicVm,
};

/// The three verification stages: a backward [`BackwardSlicer`], a
/// [`SymbolicVm`], and a [`PropertyChecker`].
pub(crate) struct VerifyEngine<'tcx> {
    tcx: TyCtxt<'tcx>,
    slicer: BackwardSlicer<'tcx>,
    vm: SymbolicVm,
    checker: PropertyChecker,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Construct a fresh engine wired to `tcx`.
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            slicer: BackwardSlicer::new(tcx),
            vm: SymbolicVm::new(),
            checker: PropertyChecker,
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
        let mut results = Vec::new();
        let backward_items = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);

        let bound_property = Self::bind_property_to_checkpoint(property, checkpoint);

        let z3_ctx = Self::new_z3_context();

        // Accumulate checked-bounds facts across checkpoints.
        // A ChecksIndexBoundsDisjoint call in an earlier checkpoint
        // can discharge InBound checks in a later checkpoint.
        let mut accumulated_has_checked: bool = false;

        // Map (def_id, local block) -> global block(s), computed once and reused
        // by `inject_inline_boundaries` for every checkpoint.  A callee inlined
        // at several call sites (e.g. `as_mut_ptr` called twice) contributes one
        // global entry block per site, so the value is a list in path order.
        let mut local_to_global: HashMap<(DefId, usize), Vec<usize>> = HashMap::new();
        for (global, (def_id, local)) in tree.block_fns().iter().enumerate() {
            local_to_global.entry((*def_id, *local)).or_default().push(global);
        }

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
                        .filter(|c| {
                            !matches!(c.kind(), Some(super::contract::PropertyKind::Unknown))
                        })
                        .map(|c| RelevantItem::ContractFact {
                            property: c.clone(),
                        }),
                );
            }
            items.extend(backward.items);
            // Insert inlined-callee boundary markers (argument binding / return
            // write-back) based on def_id transitions across the path.
            items =
                Self::inject_inline_boundaries(items, tree, &local_to_global, checkpoint.caller);

            let wrapped = crate::verify::slicer::ProofGoal {
                path: backward.path,
                items,
                block_fn: backward.block_fn,
            };

            let vm_state = self.vm.run(&z3_ctx, self.tcx, wrapped);

            // Accumulate checked bounds/disjointness facts across
            // checkpoints so that a validator called in one checkpoint
            // can discharge InBound checks in a later checkpoint.
            accumulated_has_checked =
                accumulated_has_checked || vm_state.path_facts.has_checked_bounds;
            let mut vm_state = vm_state;
            vm_state.path_facts.has_checked_bounds = accumulated_has_checked;

            let result = self.checker.check(&vm_state, checkpoint, &bound_property);
            results.push((result, path_desc));
        }

        results
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
            return vec![(CheckResult::Unknown(UnknownReason::Unimplemented), String::new())];
        };
        let caller = checkpoint.caller;
        let target = checkpoint.block.as_usize();

        let mut results: Vec<(CheckResult, String)> = Vec::new();
        for path in tree.iter() {
            // A loop-unrolled path repeats the same caller block (the SCC body);
            // its later drop occurrence is an unrolled iteration, not a genuine
            // same-path use-after-drop. Only non-unrolled paths distinguish them
            // (uaf_5 uses `slot` after the drop; uaf_false_2 drops once in a loop
            // and never uses `slot` again).
            let mut seen = std::collections::HashSet::new();
            let unrolled = path.iter().any(|&g| {
                tree.block_fn_of(g)
                    .is_some_and(|(def, local)| def == caller && !seen.insert(local))
            });
            if unrolled {
                continue;
            }
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
                        if Self::block_uses_local(self.tcx, caller, local2, slot) {
                            used = true;
                            break;
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
        let place = crate::helpers::mir_utils::operand_mir_place(arg)?;
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
                        if target.local == cur && target.projection.is_empty() {
                            if let Rvalue::Ref(_, _, referent) = rvalue {
                                next = Some(referent.local);
                                break 'outer;
                            }
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

    /// Whether any statement or terminator in `block` reads/writes `local`.
    fn block_uses_local(tcx: TyCtxt<'tcx>, caller: DefId, block: usize, local: Local) -> bool {
        let body = tcx.optimized_mir(caller);
        let data = &body.basic_blocks[BasicBlock::from(block)];
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (target, rvalue) = assign.as_ref();
                if target.local == local {
                    return true;
                }
                if crate::helpers::mir_utils::rvalue_any_place_matching(rvalue, &mut |p| {
                    p.local == local
                }) {
                    return true;
                }
            }
        }
        if let Some(terminator) = &data.terminator {
            use rustc_middle::mir::TerminatorKind;
            match &terminator.kind {
                TerminatorKind::Call { args, .. } => {
                    if args.iter().any(|a| match &a.node {
                        Operand::Copy(p) | Operand::Move(p) => p.local == local,
                        Operand::Constant(_) => false,
                        #[cfg(rapx_ge_95)]
                        Operand::RuntimeChecks(_) => false,
                    }) {
                        return true;
                    }
                }
                TerminatorKind::SwitchInt { discr, .. }
                | TerminatorKind::Assert { cond: discr, .. } => match discr {
                    Operand::Copy(p) | Operand::Move(p) => {
                        if p.local == local {
                            return true;
                        }
                    }
                    Operand::Constant(_) => {}
                    #[cfg(rapx_ge_95)]
                    Operand::RuntimeChecks(_) => {}
                },
                TerminatorKind::Drop { place, .. } => {
                    if place.local == local {
                        return true;
                    }
                }
                _ => {}
            }
        }
        false
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
        items: Vec<RelevantItem<'tcx>>,
        tree: &PathTree,
        local_to_global: &HashMap<(DefId, usize), Vec<usize>>,
        caller: DefId,
    ) -> Vec<RelevantItem<'tcx>> {
        let mut out: Vec<RelevantItem<'tcx>> = Vec::new();
        // Start in the caller so a path that begins inside an inlined callee
        // still emits its CalleeEntry on the first item.
        let mut prev_def_id: Option<DefId> = Some(caller);
        // Stack of entered callees, innermost last: (def_id, dest_local,
        // entry global block). The entry block lets us resolve each callee's
        // parent (`tree.inline_parent`) so a *nested* callee — one whose body
        // is split around a further-inlined callee (e.g. `next_unchecked`
        // calling `post_inc_start` and continuing afterwards) — is not popped
        // from the frame stack until it actually returns.
        let mut active: Vec<(DefId, usize, usize)> = Vec::new();
        // How many times each (callee, parent) pair has been entered so far, to
        // select the correct entry binding when the same callee is inlined at
        // several call sites — possibly under *different* parents — along a
        // single (loop-unrolled) path.
        let mut entry_cursor: HashMap<(DefId, DefId), usize> = HashMap::new();

        for item in items {
            let cur_def_id = match &item {
                RelevantItem::Statement { def_id, .. }
                | RelevantItem::Terminator { def_id, .. } => Some(*def_id),
                _ => None,
            };

            if let Some(cur) = cur_def_id {
                if let Some(prev) = prev_def_id {
                    if prev != cur {
                        if cur == caller {
                            // Returning to the root caller: pop *every* still-active
                            // frame. Nested inlined callees whose return blocks
                            // produced no items (a plain `return` has no relevant
                            // use/def) are skipped in the item stream, so the
                            // transition can jump several levels at once.
                            while let Some((_, dest, _)) = active.pop() {
                                out.push(RelevantItem::CalleeExit { dest });
                            }
                        } else {
                            // Distinguish an *ascent* (`prev` returns to an
                            // already-active `cur`, e.g. `post_inc_start` → the
                            // split `next_unchecked`) from a *descent* (`cur` is
                            // a fresh callee). In an ascent we pop frames down to
                            // `cur` and do NOT re-enter it (it is already active).
                            // Checking membership (rather than only the top's
                            // parent) handles multi-level skips where several
                            // callee return blocks produced no items.
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
                                // Descent into a fresh callee `cur`.
                                let current_parent =
                                    active.last().map(|(d, _, _)| *d).unwrap_or(caller);

                                // The "effective parent" of an entry block: the
                                // deepest ancestor (via `inline_parent`) that is
                                // either the root caller or a currently-active
                                // frame. Intermediate inlined callees whose blocks
                                // produced no relevant items are skipped in the
                                // item stream, so a transition can jump straight
                                // from a shallow frame to a deep descendant.
                                let eff_parent = |g: usize| -> DefId {
                                    let mut p = tree.inline_parent(g);
                                    while let Some(pd) = p {
                                        if pd == caller
                                            || active.iter().any(|(d, _, _)| *d == pd)
                                        {
                                            return pd;
                                        }
                                        p = local_to_global
                                            .get(&(pd, 0))
                                            .and_then(|gs| gs.first().copied())
                                            .and_then(|pe| tree.inline_parent(pe));
                                    }
                                    caller
                                };

                                // Select `cur`'s entry block whose effective parent
                                // matches the current innermost frame.
                                let mut cur_entry: Option<usize> = None;
                                if let Some(globals) = local_to_global.get(&(cur, 0)) {
                                    let matching: Vec<usize> = globals
                                        .iter()
                                        .copied()
                                        .filter(|&g| eff_parent(g) == current_parent)
                                        .collect();
                                    let pool: &[usize] = if matching.is_empty() {
                                        globals.as_slice()
                                    } else {
                                        matching.as_slice()
                                    };
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

                                // The frame `cur` connects to, and the inlined
                                // callees skipped between it and `cur`.
                                let eff = cur_entry.map(&eff_parent).unwrap_or(caller);
                                let mut skipped: Vec<(DefId, usize)> = Vec::new();
                                {
                                    let mut p = cur_entry.and_then(|g| tree.inline_parent(g));
                                    while let Some(pd) = p {
                                        if pd == eff {
                                            break;
                                        }
                                        if let Some(pe) = local_to_global
                                            .get(&(pd, 0))
                                            .and_then(|gs| gs.first().copied())
                                        {
                                            skipped.push((pd, pe));
                                            p = tree.inline_parent(pe);
                                        } else {
                                            break;
                                        }
                                    }
                                }

                                // Pop down to the connection frame (`eff`; if it is
                                // the root caller, pop everything).
                                while let Some(&(top_def, _, _)) = active.last() {
                                    if top_def == eff {
                                        break;
                                    }
                                    let (_, dest, _) = active.pop().unwrap();
                                    out.push(RelevantItem::CalleeExit { dest });
                                }
                                // Enter the skipped frames (farthest first), then
                                // `cur` itself.
                                for (pd, pe) in skipped.iter().rev() {
                                    if let Some(binding) = tree.inline_binding(*pe) {
                                        out.push(RelevantItem::CalleeEntry {
                                            callee: *pd,
                                            args: binding.arg_locals.clone(),
                                        });
                                        active.push((*pd, binding.dest_local, *pe));
                                    }
                                }
                                if let Some(&global) = cur_entry.as_ref()
                                    && let Some(binding) = tree.inline_binding(global)
                                {
                                    out.push(RelevantItem::CalleeEntry {
                                        callee: cur,
                                        args: binding.arg_locals.clone(),
                                    });
                                    active.push((cur, binding.dest_local, global));
                                }
                            }
                        }
                    }
                }
                prev_def_id = Some(cur);
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
            Property::And(and) => {
                Property::And(AndProperty {
                    conjuncts: and
                        .conjuncts
                        .iter()
                        .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                        .map(Box::new)
                        .collect(),
                    contract_kind: and.contract_kind,
                    origin: None,
                })
            }
            Property::Or(or) => {
                Property::Or(OrProperty {
                    disjuncts: or
                        .disjuncts
                        .iter()
                        .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                        .map(Box::new)
                        .collect(),
                    contract_kind: or.contract_kind,
                    origin: None,
                })
            }
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
            super::contract::ContractExpr::Len(inner) => super::contract::ContractExpr::Len(
                Box::new(Self::rebind_contract_expr(inner, checkpoint)),
            ),
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
        let mut results = Vec::new();
        let backward_items = self.slicer.visit_path_tree_for_checkpoint(
            tree,
            target_block,
            def_id,
            checkpoint,
            invariant,
        );

        let z3_ctx = Self::new_z3_context();

        for mut backward in backward_items {
            let path_desc = backward.path.describe_indices();

            if !entry_facts.is_empty() {
                let mut items: Vec<RelevantItem<'tcx>> = entry_facts.to_vec();
                items.extend(backward.items.drain(..));
                backward.items = items;
            }

            let vm_state = self.vm.run(&z3_ctx, self.tcx, backward);

            let fake_checkpoint = Checkpoint {
                caller: def_id,
                callee: None,
                block: checkpoint.block,
                args: Vec::new(),
                kind: crate::helpers::mir_scan::CheckpointKind::UnsafeCall,
                destination: None,
                is_mut_ref: false,
                statement_index: 0,
            };
            let result = self.checker.check(&vm_state, &fake_checkpoint, invariant);
            results.push((result, path_desc));
        }

        results
    }
}
