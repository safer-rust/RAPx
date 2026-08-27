//! Backward path visitor — walks a finite path backward from a checkpoint and
//! keeps only MIR items that can affect the required property.
//!
//! The def-use layer lives in [`super::super::def_use`]; this module focuses on
//! the path-level control flow decisions: calls, SCC exits, and path-condition
//! branches.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::{BasicBlock, Local, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use std::collections::{HashMap, HashSet};

use crate::analysis::dataflow::graph::build_dataflow_graph;
use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{
    contract,
    def_use::{RelevantPlaces, bind_callsite_roots, operand_uses, terminator_use_def},
    path_extractor::{Path, PathStep},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use crate::analysis::path::{PathNode, PathTree};

use super::{
    call_visit,
    types::{RelevantItem, ProofGoal},
};

/// Entry point for backward path visiting.
pub(crate) struct BackwardSlicer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardSlicer<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub(crate) fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Visit a path tree in post-order, sharing backward analysis across
    /// common prefixes. Merges child-relevance sets at branch nodes (the
    /// union is a sound over-approximation). Returns per-leaf results.
    ///
    /// Callee parameter roots are bound at checkpoint nodes.
    pub(crate) fn visit_path_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        checkpoint: &Checkpoint<'tcx>,
        property: &contract::Property<'tcx>,
    ) -> Vec<ProofGoal<'tcx>> {
        self.visit_path_tree_impl(
            tree,
            target_block,
            checkpoint.caller,
            checkpoint.block,
            Some(checkpoint),
            property,
        )
    }

    /// Like [`visit_path_tree`] but without callee-root binding (used for
    /// struct-invariant checks where property places are already in the
    /// caller's local namespace).
    pub(crate) fn visit_path_tree_for_checkpoint(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: DefId,
        checkpoint_loc: CheckpointLocation,
        property: &contract::Property<'tcx>,
    ) -> Vec<ProofGoal<'tcx>> {
        self.visit_path_tree_impl(
            tree,
            target_block,
            caller,
            checkpoint_loc.block,
            None,
            property,
        )
    }

    /// Internal: post-order recursion returning per-leaf
    /// `(block_path, backward_items)`.
    fn visit_path_tree_impl(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: DefId,
        checkpoint_block: BasicBlock,
        bind_checkpoint: Option<&Checkpoint<'tcx>>,
        property: &contract::Property<'tcx>,
    ) -> Vec<ProofGoal<'tcx>> {
        let Some(root) = tree.root() else {
            return Vec::new();
        };
        let checkpoint_loc = CheckpointLocation {
            caller,
            block: checkpoint_block,
        };

        // Pre-build the MIR body and dataflow graph for every function reachable
        // through this tree (caller + inlined callees), so inlined blocks resolve
        // to the correct body/flow.
        let mut bodies: HashMap<DefId, &'tcx Body<'tcx>> = HashMap::new();
        let mut flows: HashMap<DefId, DataflowGraph> = HashMap::new();
        let mut def_ids: HashSet<DefId> = tree.block_fns().iter().map(|(d, _)| *d).collect();
        def_ids.insert(caller);
        for d in def_ids {
            bodies.insert(d, self.tcx.optimized_mir(d));
            flows.insert(d, build_dataflow_graph(self.tcx, d));
        }

        let leaf_results = Self::build_leaf_items(
            self,
            tree,
            root,
            target_block,
            checkpoint_block,
            bind_checkpoint,
            property,
            caller,
            &bodies,
            &flows,
        );

        let mut results = Vec::new();
        for (block_path, backward_items, _relevant) in leaf_results {
            let mut items = backward_items;
            items.reverse();
            let steps: Vec<PathStep> = block_path
                .iter()
                .map(|&b| PathStep::Block(BasicBlock::from(b)))
                .chain(std::iter::once(PathStep::Checkpoint(checkpoint_loc)))
                .collect();
            results.push(ProofGoal {
                path: Path {
                    target: checkpoint_loc,
                    steps,
                },
                items,
                block_fn: tree.block_fns().to_vec(),
            });
        }
        results
    }

    /// Post-order recursion: returns one `(block_path, backward_items,
    /// relevant_before_block)` per checkpoint leaf. Each leaf is independent
    /// — no merging, no HashMap collision.
    fn build_leaf_items(
        visitor: &Self,
        tree: &PathTree,
        node: &PathNode,
        target_block: usize,
        checkpoint_block: BasicBlock,
        bind_checkpoint: Option<&Checkpoint<'tcx>>,
        property: &contract::Property<'tcx>,
        caller: DefId,
        bodies: &HashMap<DefId, &'tcx Body<'tcx>>,
        flows: &HashMap<DefId, DataflowGraph>,
    ) -> Vec<(Vec<usize>, Vec<RelevantItem<'tcx>>, RelevantPlaces)> {
        let (def_id, local_index) = tree.block_fn_of(node.block).unwrap_or((caller, node.block));
        let body = &bodies[&def_id];
        let flow = &flows[&def_id];
        let block = BasicBlock::from(local_index);
        let keep_inv = property.kind().is_some_and(|k| needs_invalidation_tracking(&k));
        let block_data = &body.basic_blocks[block];
        let mut results = Vec::new();

        // Build the checkpoint-layer items when this block IS the target.
        let (checkpoint_items, checkpoint_relevant) = if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_checkpoint {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
            }
            let mut items = Vec::new();
            items.push(RelevantItem::Terminator {
                def_id: caller,
                block: checkpoint_block,
            });
            // Pass 1: normal processing.
            for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                visitor.visit_statement(
                    def_id,
                    checkpoint_block,
                    si,
                    stmt,
                    flow,
                    &mut relevant,
                    &mut items,
                    keep_inv,
                );
            }
            // Pass 2: re-visit definitions that became relevant only
            // during pass 1.
            Self::re_visit_newly_added(visitor, def_id, checkpoint_block, block_data, flow, &mut relevant, &mut items, keep_inv);
            (items, relevant)
        } else {
            (Vec::new(), RelevantPlaces::new())
        };

        // Process children — even when this is the target block,
        // deeper checkpoint occurrences may hide below.
        for child in &node.children {
            let child_results = Self::build_leaf_items(
                visitor,
                tree,
                child,
                target_block,
                checkpoint_block,
                bind_checkpoint,
                property,
                caller,
                bodies,
                flows,
            );
            for (mut child_path, child_items, child_relevant) in child_results {
                let mut relevant = child_relevant;
                let mut items = child_items;
                // When this node is an inlined callee entry, the child's
                // relevance may carry the caller's destination local (the value
                // returned by this callee). Remap it to the callee's return
                // local `_0` so the callee body is sliced.
                if let Some(binding) = tree.inline_binding(node.block) {
                    let dest = Local::from_usize(binding.dest_local);
                    if relevant.locals.contains(&dest) {
                        relevant.locals.remove(&dest);
                        relevant.places.retain(|p| p.local() != Some(dest));
                        relevant.insert_local(Local::from_usize(0));
                    }
                }
                // Skip the `Call` terminator when this block's call was inlined:
                // the callee's statements are already sliced via the path, so
                // treating the call as atomic would double-count it.
                if !tree.is_inlined_call(node.block) {
                    visitor.visit_terminator(
                        def_id,
                        block,
                        block_data.terminator(),
                        flow,
                        body,
                        &mut relevant,
                        &mut items,
                        keep_inv,
                    );
                }
                let block_stmt_count = block_data.statements.len();
                for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                    visitor.visit_statement(
                        def_id,
                        block,
                        si,
                        stmt,
                        flow,
                        &mut relevant,
                        &mut items,
                        keep_inv,
                    );
                }
                // Leaving an inlined callee entry: remap the callee's parameter
                // locals back to the caller's argument locals so the caller's
                // argument-producing statements stay relevant.
                if let Some(binding) = tree.inline_binding(node.block) {
                    for (i, arg_local) in binding.arg_locals.iter().enumerate() {
                        let param = Local::from_usize(i + 1);
                        if relevant.locals.contains(&param) {
                            relevant.locals.remove(&param);
                            relevant.places.retain(|p| p.local() != Some(param));
                            relevant.insert_local(Local::from_usize(*arg_local));
                        }
                    }
                }
                let dist_to_target = child_path.iter().position(|&b| b == target_block);
                if block_stmt_count > 0 && dist_to_target.map_or(false, |d| d <= 2) {
                    Self::re_visit_newly_added(visitor, def_id, block, block_data, flow, &mut relevant, &mut items, keep_inv);
                }
                child_path.insert(0, node.block);
                results.push((child_path, items, relevant));
            }
        }

        // Produce a leaf for every checkpoint occurrence so that each
        // distinct path prefix reaching the target block is covered.
        // Deeper loop-unrolled occurrences provide superset backward
        // slices, but earlier occurrences are also needed for branches
        // that exit the loop (e.g. unwind/cleanup) without hitting the
        // target block again.
        if !checkpoint_items.is_empty() {
            results.push((vec![node.block], checkpoint_items, checkpoint_relevant));
        }

        results
    }

    /// After the first backward pass, re-visit statements whose defs
    /// became relevant because of discoveries made during that pass
    /// (tracked in `RelevantPlaces::just_added`).
    fn re_visit_newly_added(
        visitor: &Self,
        def_id: DefId,
        block: BasicBlock,
        block_data: &'tcx rustc_middle::mir::BasicBlockData<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_inv: bool,
    ) {
        let newly_added = std::mem::take(&mut relevant.just_added);
        if newly_added.is_empty() {
            return;
        }
        for (si, stmt) in block_data.statements.iter().enumerate().rev() {
            let defs = match &stmt.kind {
                rustc_middle::mir::StatementKind::Assign(assign) => {
                    let mut d = crate::verify::def_use::RelevantPlaces::new();
                    d.insert_mir_place(&assign.0);
                    d
                }
                _ => continue,
            };
            let any_new = defs.places.iter().any(|dp| {
                newly_added.iter().any(|np| dp.local() == np.local())
            });
            if any_new {
                visitor.visit_statement(
                    def_id,
                    block,
                    si,
                    stmt,
                    flow,
                    relevant,
                    items,
                    keep_inv,
                );
            }
        }
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        def_id: DefId,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx rustc_middle::mir::Statement<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
    ) {
        if keep_invalidations && matches!(statement.kind, StatementKind::StorageDead(_) | StatementKind::StorageLive(_))
        {
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            return;
        }

        let mut defs = RelevantPlaces::new();
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                defs.insert_mir_place(place);
            }
            StatementKind::StorageDead(local) => {
                defs.insert_local(*local);
            }
            _ => {}
        }

        if defs.intersects(relevant) {
            let mut uses = collect_statement_uses(statement, block, statement_index, flow);
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            // Save places already in the relevance set before removing
            // the current definition.  When the uses of this statement
            // (e.g. an aggregate struct literal) would re-add a field
            // whose definition was already found earlier in the walk,
            // skip it to prevent wrong (duplicate) matches.
            let mut already_seen: crate::compat::FxHashSet<crate::verify::def_use::PlaceKey> =
                relevant.places.clone();
            // For aggregate (struct literal) statements, also block uses
            // that were already saturated by a descendant block.  This
            // prevents fields like `_4` from being re-added when they
            // were already resolved outside this block (e.g. via a copy
            // `_4 = _8`).  Without this guard, the wrong definition
            // (e.g. `_4 = null_mut()` from struct field init) may match.
            let is_aggregate =
                if let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind {
                    matches!(assign.1, rustc_middle::mir::Rvalue::Aggregate(..))
                } else {
                    false
                };
            if is_aggregate {
                already_seen.extend(relevant.saturated.iter().cloned());
            }
            relevant.remove_all(&defs);
            uses.places.retain(|p| !already_seen.contains(p));
            relevant.extend(uses);
            return;
        }

        if statement_invalidates_relevant(statement, relevant) {
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
        } else if statement_can_refine(statement) {
            let mut uses = RelevantPlaces::new();
            for &local in &defs.locals {
                for &edge_idx in &flow.node(local).in_edges {
                    let edge = &flow.edges[edge_idx];
                    if edge.block == block.as_usize() && edge.statement_index == statement_index {
                        uses.insert_local(edge.src);
                    }
                }
            }
            if uses.intersects(relevant) {
                items.push(RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                });
            }
        }
    }

    /// Visit one MIR terminator against the current relevance frontier.
    fn visit_terminator(
        &self,
        def_id: DefId,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        keep_invalidations: bool,
    ) {
        if keep_invalidations && matches!(terminator.kind, TerminatorKind::Drop { .. }) {
            items.push(RelevantItem::Terminator { def_id, block });
            return;
        }

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            call_visit::visit(
                self.tcx,
                def_id,
                block,
                func,
                args,
                destination,
                flow,
                body,
                relevant,
                items,
            );
            return;
        }

        let use_def = terminator_use_def(terminator);
        if terminator_is_path_condition(terminator) {
            items.push(RelevantItem::Terminator { def_id, block });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(RelevantItem::Forget);
            }
            items.push(RelevantItem::Terminator { def_id, block });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(RelevantItem::Forget);
            }
            items.push(RelevantItem::Terminator { def_id, block });
        }
    }
}

// ── property helpers ──────────────────────────────────────────────────

/// Whether a property's checker reads allocation liveness (`alloc.dead`), so
/// the backward slice must keep `StorageDead`/`StorageLive`/`Drop` unconditionally
/// (the allocation owner may not be reachable from the pointer target, e.g. a
/// raw pointer into a separately-owned Vec/Box buffer).
fn needs_invalidation_tracking(kind: &contract::PropertyKind) -> bool {
    matches!(
        kind,
        contract::PropertyKind::Allocated
            | contract::PropertyKind::Init
            | contract::PropertyKind::Alive
            | contract::PropertyKind::ValidString
            | contract::PropertyKind::ValidCStr
            | contract::PropertyKind::Owning
    )
}

// ── classification helpers ──────────────────────────────────────────────

fn statement_can_refine(statement: &rustc_middle::mir::Statement<'_>) -> bool {
    matches!(&statement.kind, StatementKind::Assign(assign) if matches!(
        &**assign,
        (
            _,
            rustc_middle::mir::Rvalue::BinaryOp(_, _)
            | rustc_middle::mir::Rvalue::UnaryOp(_, _)
            | rustc_middle::mir::Rvalue::Cast(_, _, _),
        )
    ))
}

fn statement_invalidates_relevant(
    statement: &rustc_middle::mir::Statement<'_>,
    relevant: &RelevantPlaces,
) -> bool {
    match &statement.kind {
        StatementKind::StorageDead(local) => relevant.locals.contains(local),
        _ => false,
    }
}

fn terminator_is_path_condition(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(
        terminator.kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}

fn terminator_may_havoc(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(terminator.kind, TerminatorKind::Call { .. })
}

/// Collect all place-uses for a statement from dataflow edges and operands.
fn collect_statement_uses<'tcx>(
    statement: &'tcx rustc_middle::mir::Statement<'tcx>,
    block: BasicBlock,
    statement_index: usize,
    flow: &DataflowGraph,
) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();

    // Collect def locals (we know there are defs — caller already checked)
    let def_locals = match &statement.kind {
        StatementKind::Assign(assign) => {
            let (place, _) = &**assign;
            vec![place.local]
        }
        StatementKind::StorageDead(local) => vec![*local],
        _ => Vec::new(),
    };

    for &local in &def_locals {
        for &edge_idx in &flow.node(local).in_edges {
            let edge = &flow.edges[edge_idx];
            if edge.block == block.as_usize() && edge.statement_index == statement_index {
                uses.insert_local(edge.src);
            }
        }
    }

    // Also collect uses directly from operands — the dataflow graph
    // creates synthetic nodes for field projections (e.g. _13.0),
    // so we need the direct operand uses to reach through.
    if let StatementKind::Assign(assign) = &statement.kind {
        let (_, rvalue) = &**assign;
        for operand in super::super::def_use::rvalue_operands(rvalue) {
            uses.extend(operand_uses(operand));
        }
        // A reborrow (`_p = &(*_q)`, `_p = &raw (*_q)`) carries no operands, so
        // `rvalue_operands` misses its referent.  Only when the referent traces
        // back to a projection out of a call's returned tuple (a `split_at`
        // prefix/suffix slice) do we keep the referent's base local, so the
        // split — and its `mid` argument — stays in the backward slice and
        // feeds downstream `len(self)` obligations.  This stays narrow to avoid
        // inflating relevance for ordinary reborrows, which explodes loop path
        // enumeration.
        if let rustc_middle::mir::Rvalue::Ref(_, _, place)
        | rustc_middle::mir::Rvalue::RawPtr(_, place) = rvalue
        {
            uses.insert_local(place.local);
        }
    }

    uses
}
