//! Backward path visitor — walks a finite path backward from a callsite and
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
    helpers::{Callsite, CallsiteLocation},
    path::{Path, PathStep},
};

use crate::analysis::path_analysis::{PathNode, PathTree};

use super::{
    call_visit,
    types::{BackwardItem, ForgetReason, KeepReason, RelevantMirItems},
};

/// Entry point for backward path visiting.
pub struct BackwardVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardVisitor<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this visitor.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Visit one `(checkpoint, path, property)` item backward for struct
    /// invariant checks.
    ///
    /// Unlike callsite checks, this does not bind callee parameter roots
    /// because the property places are already resolved in the caller's
    /// local namespace.
    pub fn visit_for_checkpoint(
        &self,
        caller: DefId,
        checkpoint: CallsiteLocation,
        path: &Path,
        property: &contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        let mut visit = RelevantMirItems {
            callsite: checkpoint,
            property: property.clone(),
            path: path.clone(),
            items: Vec::new(),
            roots: RelevantPlaces::from_property(property),
        };
        self.visit_path(caller, &checkpoint, path, &mut visit);
        visit
    }

    /// Visit a path tree in post-order, sharing backward analysis across
    /// common prefixes. Merges child-relevance sets at branch nodes (the
    /// union is a sound over-approximation). Returns per-leaf results.
    ///
    /// Callee parameter roots are bound at callsite nodes.
    pub fn visit_path_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        callsite: &Callsite<'tcx>,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        self.visit_path_tree_impl(
            tree,
            target_block,
            callsite.caller,
            callsite.block,
            Some(callsite),
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
        caller: rustc_hir::def_id::DefId,
        callsite_loc: CallsiteLocation,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        self.visit_path_tree_impl(
            tree,
            target_block,
            caller,
            callsite_loc.block,
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
        caller: rustc_hir::def_id::DefId,
        callsite_block: BasicBlock,
        bind_callsite: Option<&Callsite<'tcx>>,
        property: &contract::Property<'tcx>,
    ) -> Vec<RelevantMirItems<'tcx>> {
        let Some(root) = tree.root() else {
            return Vec::new();
        };
        let callsite_loc = CallsiteLocation {
            caller,
            block: callsite_block,
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
            callsite_block,
            bind_callsite,
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
                .chain(std::iter::once(PathStep::Callsite(callsite_loc)))
                .collect();
            results.push(RelevantMirItems {
                callsite: callsite_loc,
                property: property.clone(),
                path: Path {
                    target: callsite_loc,
                    start: super::super::path::PathStart::FunctionEntry,
                    steps,
                },
                items,
                roots: RelevantPlaces::from_property(property),
            });
        }
        results
    }

    /// Post-order recursion: returns one `(block_path, backward_items,
    /// relevant_before_block)` per callsite leaf. Each leaf is independent
    /// — no merging, no HashMap collision.
    fn build_leaf_items(
        visitor: &Self,
        node: &PathNode,
        target_block: usize,
        callsite_block: BasicBlock,
        bind_callsite: Option<&Callsite<'tcx>>,
        property: &contract::Property<'tcx>,
        body: &'tcx rustc_middle::mir::Body<'tcx>,
        flow: &DataflowGraph,
        keep_alloc: bool,
    ) -> Vec<(Vec<usize>, Vec<BackwardItem<'tcx>>, RelevantPlaces)> {
        if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_callsite {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
            }
            let mut items = Vec::new();
            items.push(BackwardItem::Terminator {
                block: callsite_block,
                kind: KeepReason::Callsite,
            });
            let block_data = &body.basic_blocks[callsite_block];
            for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                visitor.visit_statement(
                    callsite_block,
                    si,
                    stmt,
                    flow,
                    &mut relevant,
                    &mut items,
                    keep_alloc,
                );
            }
            return vec![(vec![node.block], items, relevant)];
        }

        let mut results = Vec::new();
        let block = BasicBlock::from(node.block);
        let block_data = &body.basic_blocks[block];

        for child in &node.children {
            let child_results = Self::build_leaf_items(
                visitor,
                child,
                target_block,
                callsite_block,
                bind_callsite,
                property,
                body,
                flow,
                keep_alloc,
            );
            for (mut child_path, child_items, child_relevant) in child_results {
                let mut relevant = child_relevant;
                let mut items = child_items;
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
                        &mut relevant,
                        &mut items,
                        keep_alloc,
                    );
                }
                child_path.insert(0, node.block);
                results.push((child_path, items, relevant));
            }
        }
        results
    }

    fn visit_path(
        &self,
        caller: DefId,
        callsite_loc: &CallsiteLocation,
        path: &Path,
        visit: &mut RelevantMirItems<'tcx>,
    ) {
        let mut relevant = visit.roots.clone();
        let mut items: Vec<BackwardItem<'tcx>> = Vec::new();
        let body = self.tcx.optimized_mir(caller);
        let flow = build_dataflow_graph(self.tcx, caller);

        let keep_allocation_invalidations = matches!(
            visit.property.kind,
            contract::PropertyKind::Allocated
                | contract::PropertyKind::Deref
                | contract::PropertyKind::ValidPtr
        );

        for step in path.steps.iter().rev() {
            self.visit_path_step_inner(
                step,
                &callsite_loc,
                &body,
                &flow,
                &mut relevant,
                &mut items,
                keep_allocation_invalidations,
            );
        }

        items.reverse();
        visit.items = items;
    }

    fn visit_path_step_inner(
        &self,
        step: &PathStep,
        callsite_loc: &CallsiteLocation,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
        keep_allocation_invalidations: bool,
    ) {
        match step {
            PathStep::Callsite(location) => {
                if *location != *callsite_loc {
                    return;
                }
                items.push(BackwardItem::Terminator {
                    block: location.block,
                    kind: KeepReason::Callsite,
                });
            }
            PathStep::Block(block) => {
                let block_data = &body.basic_blocks[*block];
                if *block != callsite_loc.block {
                    self.visit_terminator(
                        *block,
                        block_data.terminator(),
                        flow,
                        body,
                        relevant,
                        items,
                        keep_allocation_invalidations,
                    );
                }
                for (statement_index, statement) in block_data.statements.iter().enumerate().rev() {
                    self.visit_statement(
                        *block,
                        statement_index,
                        statement,
                        flow,
                        relevant,
                        items,
                        keep_allocation_invalidations,
                    );
                }
            }
        }
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &'tcx rustc_middle::mir::Statement<'tcx>,
        flow: &DataflowGraph,
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
            let uses = collect_statement_uses(statement, block, statement_index, flow);
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: statement_keep_reason(statement),
            });
            relevant.remove_all(&defs);
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
    }

    uses
}
