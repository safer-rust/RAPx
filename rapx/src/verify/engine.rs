//! Symbolic-VM-based verification engine.
//!
//! Uses a semantic MIR executor to build symbolic state,
//! then checks safety properties with a unified property checker.

use z3::Config;

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::path::PathTree;

use super::{
    contract::{AndProperty, AtomProperty, OrProperty, Property},
    report::CheckResult,
    slicer::{BackwardSlicer, RelevantItem},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use super::{property_checker::PropertyChecker, vm::SymbolicVm};

/// The three verification stages: a backward [`BackwardSlicer`], a
/// [`SymbolicVm`], and a [`PropertyChecker`].
pub(crate) struct VerifyEngine<'tcx> {
    slicer: BackwardSlicer<'tcx>,
    vm: SymbolicVm<'tcx>,
    checker: PropertyChecker,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Construct a fresh engine wired to `tcx`.
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            slicer: BackwardSlicer::new(tcx),
            vm: SymbolicVm::new(tcx),
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

        let ctx = Self::new_z3_context();

        // Accumulate checked-bounds facts across checkpoints.
        // A ChecksIndexBoundsDisjoint call in an earlier checkpoint
        // can discharge InBound checks in a later checkpoint.
        let mut accumulated_has_checked: bool = false;

        // Map (def_id, local block) -> global block, computed once and reused
        // by `inject_inline_boundaries` for every checkpoint.
        let mut local_to_global: HashMap<(DefId, usize), usize> = HashMap::new();
        for (global, (def_id, local)) in tree.block_fns().iter().enumerate() {
            local_to_global.insert((*def_id, *local), global);
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
            items = Self::inject_inline_boundaries(items, tree, &local_to_global, checkpoint.caller);

            let wrapped = crate::verify::slicer::ProofGoal {
                path: backward.path,
                items,
                block_fn: backward.block_fn,
            };

            let vm_state = self.vm.execute(&ctx, &wrapped);

            // Accumulate checked bounds/disjointness facts across
            // checkpoints so that a validator called in one checkpoint
            // can discharge InBound checks in a later checkpoint.
            accumulated_has_checked =
                accumulated_has_checked || vm_state.contract_flags.has_checked_bounds;
            let mut vm_state = vm_state;
            vm_state.contract_flags.has_checked_bounds = accumulated_has_checked;

            let result = self.checker.check(&vm_state, checkpoint, &bound_property);
            results.push((result, path_desc));
        }

        results
    }

    /// Insert `CalleeEntry`/`CalleeExit` markers into a forward item stream by
    /// detecting `def_id` transitions (caller → callee → caller). Each inlined
    /// callee entry carries its argument binding; each exit writes the callee's
    /// return value back to the caller's destination.
    ///
    /// `local_to_global` maps `(def_id, local_block)` pairs to their global
    /// block index in `tree`; it is precomputed by the caller so it can be
    /// reused across every checkpoint instead of rebuilt per path.
    fn inject_inline_boundaries(
        items: Vec<RelevantItem<'tcx>>,
        tree: &PathTree,
        local_to_global: &HashMap<(DefId, usize), usize>,
        caller: DefId,
    ) -> Vec<RelevantItem<'tcx>> {
        let mut out: Vec<RelevantItem<'tcx>> = Vec::new();
        // Start in the caller so a path that begins inside an inlined callee
        // still emits its CalleeEntry on the first item.
        let mut prev_def_id: Option<DefId> = Some(caller);
        let mut active: Option<(DefId, usize)> = None;

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
                            if let Some((_, dest)) = active.take() {
                                out.push(RelevantItem::CalleeExit { dest });
                            }
                        } else {
                            let local = match &item {
                                RelevantItem::Statement { block, .. }
                                | RelevantItem::Terminator { block, .. } => block.as_usize(),
                                _ => unreachable!(),
                            };
                            if let Some(global) = local_to_global.get(&(cur, local)).copied() {
                                if let Some(binding) = tree.inline_binding(global) {
                                    out.push(RelevantItem::CalleeEntry {
                                        callee: cur,
                                        args: binding.arg_locals.clone(),
                                    });
                                    active = Some((cur, binding.dest_local));
                                }
                            }
                        }
                    }
                }
                prev_def_id = Some(cur);
            }

            out.push(item);
        }

        if let Some((_, dest)) = active.take() {
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
                let conjuncts: Vec<Property<'tcx>> = and
                    .conjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect();
                Property::And(AndProperty {
                    conjuncts: conjuncts.into_iter().map(Box::new).collect(),
                    contract_kind: and.contract_kind,
                    origin: None,
                })
            }
            Property::Or(or) => {
                let disjuncts: Vec<Property<'tcx>> = or
                    .disjuncts
                    .iter()
                    .map(|p| Self::bind_property_to_checkpoint(p, checkpoint))
                    .collect();
                Property::Or(OrProperty {
                    disjuncts: disjuncts.into_iter().map(Box::new).collect(),
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

        let ctx = Self::new_z3_context();

        for mut backward in backward_items {
            let path_desc = backward.path.describe_indices();

            if !entry_facts.is_empty() {
                let mut items: Vec<RelevantItem<'tcx>> = entry_facts.to_vec();
                items.extend(backward.items.drain(..));
                backward.items = items;
            }

            let vm_state = self.vm.execute(&ctx, &backward);

            let fake_checkpoint = Checkpoint {
                caller: def_id,
                callee: None,
                block: checkpoint.block,
                args: Vec::new(),
                kind: crate::helpers::mir_scan::CheckpointKind::UnsafeCall,
                destination: None,
            };
            let result = self.checker.check(&vm_state, &fake_checkpoint, invariant);
            results.push((result, path_desc));
        }

        results
    }
}
