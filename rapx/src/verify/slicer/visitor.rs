//! Backward path visitor — walks a finite path backward from a checkpoint and
//! keeps only MIR items that can affect the required property.
//!
//! The def-use layer lives in [`super::super::def_use`]; this module focuses on
//! the path-level control flow decisions: calls, SCC exits, and path-condition
//! branches.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::{BasicBlock, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::analysis::dataflow::graph::build_dataflow_graph;
use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{
    contract,
    def_use::{RelevantPlaces, bind_callsite_roots, operand_uses, terminator_use_def},
    helpers::{Checkpoint, CheckpointLocation},
    path_extractor::{Path, PathStep},
};

use crate::analysis::path_analysis::{PathNode, PathTree};

use super::{
    call_visit,
    types::{BackwardItem, ForgetReason, KeepReason, RelevantMirItems},
};

/// Entry point for backward path visiting.
pub struct BackwardSlicer<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardSlicer<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this visitor.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Visit a path tree in post-order, sharing backward analysis across
    /// common prefixes. Merges child-relevance sets at branch nodes (the
    /// union is a sound over-approximation). Returns per-leaf results.
    ///
    /// Callee parameter roots are bound at checkpoint nodes.
    pub fn visit_path_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        checkpoint: &Checkpoint<'tcx>,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
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
    pub fn visit_path_tree_for_checkpoint(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: DefId,
        checkpoint_loc: CheckpointLocation,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
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
    ) -> Vec<RelevantMirItems<'tcx>> {
        let Some(root) = tree.root() else {
            return Vec::new();
        };
        let checkpoint_loc = CheckpointLocation {
            caller,
            block: checkpoint_block,
        };
        let body = self.tcx.optimized_mir(caller);
        let flow = build_dataflow_graph(self.tcx, caller);
        let keep_alloc = matches!(
            property.kind,
            contract::PropertyKind::Allocated
                | contract::PropertyKind::Deref
                | contract::PropertyKind::ValidPtr
        );

        let leaf_results = Self::build_leaf_items(
            self,
            root,
            target_block,
            checkpoint_block,
            bind_checkpoint,
            property,
            &body,
            &flow,
            keep_alloc,
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
            results.push(RelevantMirItems {
                checkpoint: checkpoint_loc,
                property: property.clone(),
                path: Path {
                    target: checkpoint_loc,
                    steps,
                },
                items,
                roots: RelevantPlaces::from_property(property),
            });
        }
        results
    }

    /// Post-order recursion: returns one `(block_path, backward_items,
    /// relevant_before_block)` per checkpoint leaf. Each leaf is independent
    /// — no merging, no HashMap collision.
    fn build_leaf_items(
        visitor: &Self,
        node: &PathNode,
        target_block: usize,
        checkpoint_block: BasicBlock,
        bind_checkpoint: Option<&Checkpoint<'tcx>>,
        property: &contract::Property<'tcx>,
        body: &'tcx rustc_middle::mir::Body<'tcx>,
        flow: &DataflowGraph,
        keep_alloc: bool,
    ) -> Vec<(Vec<usize>, Vec<BackwardItem<'tcx>>, RelevantPlaces)> {
        let block = BasicBlock::from(node.block);
        let block_data = &body.basic_blocks[block];
        let mut results = Vec::new();

        // Build the checkpoint-layer items when this block IS the target.
        let (checkpoint_items, checkpoint_relevant) = if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_checkpoint {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
            }
            let mut items = Vec::new();
            items.push(BackwardItem::Terminator {
                block: checkpoint_block,
                kind: KeepReason::Checkpoint,
            });
            for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                visitor.visit_statement(
                    checkpoint_block,
                    si,
                    stmt,
                    flow,
                    body,
                    &mut relevant,
                    &mut items,
                    keep_alloc,
                );
            }
            (items, relevant)
        } else {
            (Vec::new(), RelevantPlaces::new())
        };

        // Process children — even when this is the target block,
        // deeper checkpoint occurrences may hide below.
        for child in &node.children {
            let child_results = Self::build_leaf_items(
                visitor,
                child,
                target_block,
                checkpoint_block,
                bind_checkpoint,
                property,
                body,
                flow,
                keep_alloc,
            );
            for (mut child_path, child_items, child_relevant) in child_results {
                let mut relevant = child_relevant;
                let mut items = child_items;
                // Always thread through so the backward chain reaches
                // function entry even for child (deeper SCC) paths,
                // otherwise allocation/initialization facts are missing.
                visitor.visit_terminator(
                    block,
                    block_data.terminator(),
                    flow,
                    body,
                    &mut relevant,
                    &mut items,
                    keep_alloc,
                );
                for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                    visitor.visit_statement(
                        block,
                        si,
                        stmt,
                        flow,
                        body,
                        &mut relevant,
                        &mut items,
                        keep_alloc,
                    );
                }
                child_path.insert(0, node.block);
                results.push((child_path, items, relevant));
            }
        }

        // Produce a leaf for this checkpoint occurrence.
        if !checkpoint_items.is_empty() {
            results.push((vec![node.block], checkpoint_items, checkpoint_relevant));
        }

        results
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx rustc_middle::mir::Statement<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        if keep_allocation_invalidations && matches!(statement.kind, StatementKind::StorageDead(_))
        {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
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
            let mut uses = collect_statement_uses(statement, block, statement_index, flow, body);
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: statement_keep_reason(statement),
            });
            // Save places already in the relevance set before removing
            // the current definition.  When the uses of this statement
            // (e.g. an aggregate struct literal) would re-add a field
            // whose definition was already found earlier in the walk,
            // skip it to prevent wrong (duplicate) matches.
            let mut already_seen: crate::compat::FxHashSet<
                crate::verify::def_use::PlaceKey,
            > = relevant.places.clone();
            // For aggregate (struct literal) statements, also block uses
            // that were already saturated by a descendant block.  This
            // prevents fields like `_4` from being re-added when they
            // were already resolved outside this block (e.g. via a copy
            // `_4 = _8`).  Without this guard, the wrong definition
            // (e.g. `_4 = null_mut()` from struct field init) may match.
            let is_aggregate = if let rustc_middle::mir::StatementKind::Assign(assign) =
                &statement.kind
            {
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
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
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
                items.push(BackwardItem::Statement {
                    block,
                    statement_index,
                    kind: KeepReason::RuntimeCheck,
                });
            }
        }
    }

    /// Visit one MIR terminator against the current relevance frontier.
    fn visit_terminator(
        &self,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        flow: &DataflowGraph,
        body: &Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        if keep_allocation_invalidations && matches!(terminator.kind, TerminatorKind::Drop { .. }) {
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::Invalidation,
            });
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
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::PathCondition,
            });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_definition_reason(terminator),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_use_reason(terminator),
            });
        }
    }
}

// ── classification helpers ──────────────────────────────────────────────

fn statement_keep_reason(statement: &rustc_middle::mir::Statement<'_>) -> KeepReason {
    match &statement.kind {
        StatementKind::Assign(assign) => {
            let (_, rvalue) = &**assign;
            match rvalue {
                rustc_middle::mir::Rvalue::Ref(_, _, _)
                | rustc_middle::mir::Rvalue::RawPtr(_, _)
                | rustc_middle::mir::Rvalue::Cast(_, _, _)
                | rustc_middle::mir::Rvalue::CopyForDeref(_)
                | rustc_middle::mir::Rvalue::BinaryOp(_, _) => KeepReason::PointerFlow,
                _ => KeepReason::Definition,
            }
        }
        StatementKind::StorageDead(_) => KeepReason::Invalidation,
        _ => KeepReason::Definition,
    }
}

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

fn terminator_definition_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::Definition,
    }
}

fn terminator_use_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. } => {
            KeepReason::PathCondition
        }
        TerminatorKind::Drop { .. } => KeepReason::Invalidation,
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::UnknownEffect,
    }
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
    body: &Body<'tcx>,
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
            && local_from_tuple_field_projection(body, place.local)
        {
            uses.extend(super::super::def_use::place_uses(place));
        }
    }

    uses
}

/// Return true when `local` is defined (directly or through copy/move chains)
/// by a projection out of another local's field — the shape produced when a
/// tuple returned by a call (e.g. `split_at`) is destructured into its slice
/// components.
fn local_from_tuple_field_projection<'tcx>(
    body: &Body<'tcx>,
    local: rustc_middle::mir::Local,
) -> bool {
    use rustc_middle::mir::{Operand, Rvalue};
    let mut current = local;
    let mut seen = std::collections::HashSet::new();
    for _ in 0..8 {
        if !seen.insert(current) {
            return false;
        }
        let mut next = None;
        for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != current || !dest.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) = rvalue {
                    if src
                        .projection
                        .iter()
                        .any(|p| matches!(p, rustc_middle::mir::ProjectionElem::Field(..)))
                    {
                        return true;
                    }
                    next = Some(src.local);
                }
            }
        }
        match next {
            Some(src) if src != current => current = src,
            _ => return false,
        }
    }
    false
}
