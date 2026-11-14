//! Backward path visitor — walks a finite path backward from a checkpoint and
//! keeps only MIR items that can affect the required property.
//!
//! MIR relevance decisions live in `rules`; this module traverses path trees
//! and carries the backward relevance frontier between blocks.

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{BasicBlock, Body, Local}, ty::TyCtxt};

use std::collections::{HashMap, HashSet};

use crate::analysis::dataflow::graph::build_dataflow_graph_from_body;
use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{contract, path::Path};
use super::bind_callsite_roots;
use crate::helpers::def_use::RelevantPlaces;
use crate::verify::checkpoint::{Checkpoint, CheckpointKind, CheckpointLocation};
use crate::verify::path::EntryBodies;
use crate::verify::target::CalleeBodies;

use crate::analysis::path::{CallArg, PathNode, PathTree};

use super::types::{ProofGoal, RelevantItem};

type LeafItem<'tcx> = (
    Vec<usize>,
    Vec<RelevantItem<'tcx>>,
    RelevantPlaces,
    Vec<(DefId, Vec<CallArg>, RelevantPlaces)>,
);

/// Entry point for backward path visiting.
pub(crate) struct BackwardSlicer<'tcx> {
    pub(in crate::verify::slicer) tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    instance_body: Option<&'tcx Body<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    entry_bodies: EntryBodies<'tcx>,
}

impl<'tcx> BackwardSlicer<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        caller_def_id: DefId,
        instance_body: Option<&'tcx Body<'tcx>>,
        callee_bodies: CalleeBodies<'tcx>,
        entry_bodies: EntryBodies<'tcx>,
    ) -> Self {
        Self {
            tcx,
            caller_def_id,
            instance_body,
            callee_bodies,
            entry_bodies,
        }
    }

    pub(in crate::verify::slicer) fn body_for(&self, def_id: DefId) -> &'tcx Body<'tcx> {
        if def_id == self.caller_def_id
            && let Some(body) = self.instance_body
        {
            body
        } else if let Some(body) = self.callee_bodies.get(&def_id) {
            body
        } else {
            self.tcx.optimized_mir(def_id)
        }
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
        let mut bodies: HashMap<usize, &'tcx Body<'tcx>> = HashMap::new();
        let mut flows: HashMap<usize, DataflowGraph> = HashMap::new();
        for (global, &(def_id, local)) in tree.block_fns().iter().enumerate() {
            let entry = global - local;
            if bodies.contains_key(&entry) {
                continue;
            }
            let body = self
                .entry_bodies
                .get(&entry)
                .copied()
                .unwrap_or_else(|| self.body_for(def_id));
            flows.insert(entry, build_dataflow_graph_from_body(def_id, body));
            bodies.insert(entry, body);
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
        for (block_path, backward_items, _relevant, _) in leaf_results {
            let mut items = backward_items;
            items.reverse();
            results.push(ProofGoal {
                path: Path {
                    target: checkpoint_loc,
                    blocks: block_path,
                },
                items,
            });
        }
        results
    }

    /// Post-order recursion: returns one `(block_path, backward_items,
    /// relevant_before_block, parked_caller_relevant)` per checkpoint leaf.
    /// Each leaf is independent — no merging, no HashMap collision.
    #[allow(clippy::too_many_arguments)]
    fn build_leaf_items(
        visitor: &Self,
        tree: &PathTree,
        node: &PathNode,
        target_block: usize,
        checkpoint_block: BasicBlock,
        bind_checkpoint: Option<&Checkpoint<'tcx>>,
        property: &contract::Property<'tcx>,
        caller: DefId,
        bodies: &HashMap<usize, &'tcx Body<'tcx>>,
        flows: &HashMap<usize, DataflowGraph>,
    ) -> Vec<LeafItem<'tcx>> {
        let (def_id, local_index) = tree.block_fn_of(node.block).unwrap_or((caller, node.block));
        let entry = node.block - local_index;
        let body = &bodies[&entry];
        let flow = &flows[&entry];
        let block = BasicBlock::from(local_index);
        let keep_inv = property
            .kind()
            .is_some_and(|k| needs_invalidation_tracking(&k));
        // `Allocated` also needs the construction chain of owners that may be
        // dropped before the checkpoint.
        let keep_owner = matches!(
            property.kind(),
            Some(contract::PropertyKind::Owning | contract::PropertyKind::Allocated)
        );
        let block_data = &body.basic_blocks[block];
        let mut results = Vec::new();

        let (checkpoint_items, checkpoint_relevant) = if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_checkpoint {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
            }
            let mut items = Vec::new();
            let skip_terminator = matches!(
                bind_checkpoint.map(|c| c.kind),
                Some(CheckpointKind::RawPtrDeref)
                    | Some(CheckpointKind::StaticMutAccess)
                    | Some(CheckpointKind::CopyNonOverlapping)
                    | Some(CheckpointKind::UnsafeCall)
            ) || crate::verify::api_classify::is_manually_drop_drop(
                visitor.tcx,
                bind_checkpoint.and_then(|c| c.callee),
            );
            if !skip_terminator {
                items.push(RelevantItem::Terminator {
                    def_id: caller,
                    block: checkpoint_block,
                    global_block: Some(target_block),
                    switch_succ: None,
                });
            }
            for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                visitor.visit_statement(
                    def_id,
                    checkpoint_block,
                    si,
                    stmt,
                    body,
                    flow,
                    &mut relevant,
                    &mut items,
                    keep_inv,
                    keep_owner,
                );
            }
            Self::re_visit_newly_added(
                visitor,
                def_id,
                checkpoint_block,
                block_data,
                body,
                flow,
                &mut relevant,
                &mut items,
                0,
                keep_inv,
                keep_owner,
            );
            for item in &mut items {
                item.set_global_block(node.block);
            }
            (items, relevant)
        } else {
            (Vec::new(), RelevantPlaces::new())
        };

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
            for (mut child_path, child_items, child_relevant, mut frames) in child_results {
                let mut relevant = child_relevant;
                let mut items = child_items;
                // Entering an inlined callee (its first block in backward order,
                // i.e. the return block): the caller's destination local becomes
                // the callee's `_0`, and the rest of the caller's relevance is
                // parked on a per-level frame stack. A single `Option` cannot
                // express nested callees (get_ext → NonZero::get), whose bodies
                // are split around the inner callee.
                if def_id != caller
                    && frames.last().map(|f| f.0) != Some(def_id)
                    && let Some(binding) = tree.call_binding(node.block - local_index)
                {
                    let dest = Local::from_usize(binding.dest_local);
                    let mut callee_relevant = RelevantPlaces::new();
                    if relevant.locals.contains(&dest) {
                        relevant.locals.remove(&dest);
                        relevant.places.retain(|p| p.local() != Some(dest));
                        callee_relevant.insert_local(Local::from_usize(0));
                    }
                    frames.push((
                        def_id,
                        binding.args.clone(),
                        std::mem::replace(&mut relevant, callee_relevant),
                    ));
                }
                // Skip the `Call` terminator when this block's call was inlined:
                // the callee's statements are already sliced via the path, so
                // treating the call as atomic would double-count it.
                let node_items_start = items.len();
                if !tree.is_expanded_call(node.block) || tree.call_binding(child.block).is_none() {
                    // The successor this path takes out of `node` (only used for
                    // `SwitchInt`, whose branch is resolved here rather than by
                    // the forward VM). `child.block` is a global index; map back
                    // to the local MIR block.
                    let successor = tree
                        .block_fn_of(child.block)
                        .map(|(_, li)| BasicBlock::from(li))
                        .or(Some(BasicBlock::from(child.block)));
                    visitor.visit_terminator(
                        def_id,
                        block,
                        block_data.terminator(),
                        flow,
                        body,
                        &mut relevant,
                        &mut items,
                        keep_inv,
                        keep_owner,
                        successor,
                    );
                }
                let block_stmt_count = block_data.statements.len();
                let block_items_start = items.len();
                for (si, stmt) in block_data.statements.iter().enumerate().rev() {
                    visitor.visit_statement(
                        def_id,
                        block,
                        si,
                        stmt,
                        body,
                        flow,
                        &mut relevant,
                        &mut items,
                        keep_inv,
                        keep_owner,
                    );
                }
                let dist_to_target = child_path.iter().position(|&b| b == target_block);
                if block_stmt_count > 0 && dist_to_target.is_some_and(|d| d <= 2) {
                    Self::re_visit_newly_added(
                        visitor,
                        def_id,
                        block,
                        block_data,
                        body,
                        flow,
                        &mut relevant,
                        &mut items,
                        block_items_start,
                        keep_inv,
                        keep_owner,
                    );
                }
                for item in &mut items[node_items_start..] {
                    item.set_global_block(node.block);
                }
                // Leaving an inlined callee entry: remap the callee's parameter
                // locals back to the caller's argument locals so the caller's
                // argument-producing statements stay relevant.
                if let Some(binding) = tree.call_binding(node.block) {
                    let (_, frame_args, parked) = frames.pop().unwrap_or((
                        def_id,
                        binding.args.clone(),
                        RelevantPlaces::new(),
                    ));
                    let mut caller_relevant = parked;
                    for (i, arg) in frame_args.iter().enumerate() {
                        if relevant.locals.contains(&Local::from_usize(i + 1))
                            && let CallArg::Local(arg_local) = arg
                        {
                            caller_relevant.insert_local(Local::from_usize(*arg_local));
                        }
                    }
                    relevant = caller_relevant;
                }
                child_path.insert(0, node.block);
                results.push((child_path, items, relevant, frames));
            }
        }

        // Produce a leaf for every checkpoint occurrence so that each
        // distinct path prefix reaching the target block is covered.
        // Deeper loop-unrolled occurrences provide superset backward
        // slices, but earlier occurrences are also needed for branches
        // that exit the loop (e.g. unwind/cleanup) without hitting the
        // target block again.
        if node.block == target_block {
            results.push((
                vec![node.block],
                checkpoint_items,
                checkpoint_relevant,
                Vec::new(),
            ));
        }

        results
    }

    /// After the first backward pass, re-visit statements whose defs
    /// became relevant because of discoveries made during that pass
    /// (tracked in `RelevantPlaces::just_added`).
    #[allow(clippy::too_many_arguments)]
    fn re_visit_newly_added(
        visitor: &Self,
        def_id: DefId,
        block: BasicBlock,
        block_data: &'tcx rustc_middle::mir::BasicBlockData<'tcx>,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        block_items_start: usize,
        keep_inv: bool,
        keep_owner: bool,
    ) {
        let newly_added = std::mem::take(&mut relevant.just_added);
        if newly_added.is_empty() {
            return;
        }
        for (si, stmt) in block_data.statements.iter().enumerate().rev() {
            let defs = match &stmt.kind {
                rustc_middle::mir::StatementKind::Assign(assign) => {
                    let mut d = crate::helpers::def_use::RelevantPlaces::new();
                    d.insert_mir_place(&assign.0);
                    d
                }
                _ => continue,
            };
            let any_new = defs
                .places
                .iter()
                .any(|dp| newly_added.iter().any(|np| dp.local() == np.local()));
            if any_new {
                visitor.visit_statement(
                    def_id, block, si, stmt, body, flow, relevant, items, keep_inv, keep_owner,
                );
            }
        }
        let mut seen = HashSet::new();
        let mut block_items: Vec<_> = items.drain(block_items_start..).collect();
        block_items.retain(|item| match item {
            RelevantItem::Statement {
                statement_index, ..
            } => seen.insert(*statement_index),
            _ => true,
        });
        block_items.sort_by_key(|item| match item {
            RelevantItem::Terminator { .. } => (0, 0),
            RelevantItem::Statement {
                statement_index, ..
            } => (1, usize::MAX - statement_index),
            _ => (2, 0),
        });
        items.extend(block_items);
    }
}

// ── property helpers ──────────────────────────────────────────────────

/// Whether a property can depend on state changes outside its direct value
/// dependencies, including drops and raw-share updates before an index read.
fn needs_invalidation_tracking(kind: &contract::PropertyKind) -> bool {
    matches!(
        kind,
        contract::PropertyKind::InBound
            | contract::PropertyKind::Allocated
            | contract::PropertyKind::Init
            | contract::PropertyKind::Alive
            | contract::PropertyKind::ValidString
            | contract::PropertyKind::ValidCStr
            | contract::PropertyKind::Owning
            | contract::PropertyKind::RefCountShare
    )
}
