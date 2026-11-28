//! Backward data-dependency slicer.
//!
//! Given a path tree, a checkpoint, and properties, it walks each path backward
//! to keep only the MIR items relevant to those properties, producing
//! one [`SlicedPath`] per path for the symbolic VM to execute forward.

mod relevance;
mod rules;

pub(crate) use relevance::bind_callsite_roots;

use crate::compat::MirTerminatorExt as _;
use std::{cell::RefCell, collections::{HashMap, HashSet}, rc::Rc};

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::{BasicBlock, Body, Local}, ty::TyCtxt};

use crate::analysis::dataflow::{graph::build_dataflow_graph_from_body, types::DataflowGraph};
use crate::analysis::path::{CallArg, PathNode, PathTree};
use crate::contract;
use crate::util::def_use::RelevantPlaces;
use crate::verify::checkpoint::{Checkpoint, CheckpointKind, CheckpointLocation};
use crate::verify::path::{CalleeBodies, EntryBodies};

use super::path::Path;
pub(crate) use crate::vm::RelevantItem;

/// Relevant MIR items and path context for one checkpoint occurrence.
#[derive(Clone, Debug)]
pub(crate) struct SlicedPath<'tcx> {
    /// Path being visited; `path.target` identifies the checkpoint.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<RelevantItem<'tcx>>,
}

type LeafItem<'tcx> = (
    Vec<usize>,
    Vec<RelevantItem<'tcx>>,
    RelevantPlaces,
    Vec<(DefId, Vec<CallArg>, RelevantPlaces)>,
);
type EntryData<'tcx> = (&'tcx Body<'tcx>, Rc<DataflowGraph>);

/// Entry point for backward path visiting.
pub(crate) struct BackwardSlicer<'tcx> {
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    instance_body: Option<&'tcx Body<'tcx>>,
    callee_bodies: CalleeBodies<'tcx>,
    entry_bodies: EntryBodies<'tcx>,
    flow_cache: RefCell<HashMap<(DefId, usize), Rc<DataflowGraph>>>,
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
            flow_cache: RefCell::new(HashMap::new()),
        }
    }

    fn body_for(&self, def_id: DefId) -> &'tcx Body<'tcx> {
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

    /// Return the selected MIR body for an inlined call entry, if available.
    pub(crate) fn body_for_entry(&self, entry: usize, callee: DefId) -> Option<&'tcx Body<'tcx>> {
        self.entry_bodies.get(&entry).copied().or_else(|| self.callee_bodies.get(&callee).copied())
    }

    /// Visit the path tree once for the union of checkpoint requirements.
    pub(crate) fn visit_path_tree_batch(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        properties: &[&contract::Property<'tcx>],
    ) -> Vec<SlicedPath<'tcx>> {
        let combined = contract::Property::new_and(properties.iter().map(|property| (*property).clone()).collect());
        self.visit_path_tree_impl(
            tree,
            checkpoint.block.as_usize(),
            checkpoint.caller,
            checkpoint.block,
            Some(checkpoint),
            &combined,
        )
    }

    /// Slice a checkpoint without callee-root binding, for properties already
    /// expressed in the caller's local namespace.
    pub(crate) fn visit_exit_properties(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: DefId,
        checkpoint_loc: CheckpointLocation,
        properties: &[&contract::Property<'tcx>],
    ) -> Vec<SlicedPath<'tcx>> {
        let combined = contract::Property::new_and(properties.iter().map(|property| (*property).clone()).collect());
        self.visit_path_tree_impl(
            tree,
            target_block,
            caller,
            checkpoint_loc.block,
            None,
            &combined,
        )
    }

    /// Walk the path tree backward and convert each leaf into a sliced path.
    fn visit_path_tree_impl(
        &self,
        tree: &PathTree,
        target_block: usize,
        caller: DefId,
        checkpoint_block: BasicBlock,
        bind_checkpoint: Option<&Checkpoint<'tcx>>,
        property: &contract::Property<'tcx>,
    ) -> Vec<SlicedPath<'tcx>> {
        let Some(root) = tree.root() else {
            return Vec::new();
        };
        let checkpoint_loc = CheckpointLocation { caller, block: checkpoint_block };

        // Pre-build the MIR body and dataflow graph for every function reachable
        // through this tree (caller + inlined callees), so inlined blocks resolve
        // to the correct body/flow.
        let mut entries: HashMap<usize, EntryData<'tcx>> = HashMap::new();
        for (global, &(def_id, local)) in tree.block_fns().iter().enumerate() {
            let entry = global - local;
            if entries.contains_key(&entry) {
                continue;
            }
            let body = self.entry_bodies.get(&entry).copied().unwrap_or_else(|| self.body_for(def_id));
            let key = (def_id, body as *const Body<'tcx> as usize);
            let flow = self.flow_cache.borrow_mut().entry(key)
                .or_insert_with(|| Rc::new(build_dataflow_graph_from_body(def_id, body)))
                .clone();
            entries.insert(entry, (body, flow));
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
            &entries,
        );

        let mut results = Vec::new();
        for (block_path, backward_items, _relevant, _) in leaf_results {
            let mut items = backward_items;
            items.reverse();
            results.push(SlicedPath {
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
        entries: &HashMap<usize, EntryData<'tcx>>,
    ) -> Vec<LeafItem<'tcx>> {
        let (def_id, local_index) = tree.block_fn_of(node.block).unwrap_or((caller, node.block));
        let entry = node.block - local_index;
        let (body, flow) = &entries[&entry];
        let block = BasicBlock::from(local_index);
        let block_data = &body.basic_blocks[block];
        let mut results = Vec::new();

        let (checkpoint_items, checkpoint_relevant) = if node.block == target_block {
            let mut relevant = RelevantPlaces::from_property(property);
            if let Some(cs) = bind_checkpoint {
                bind_callsite_roots(visitor.tcx, &mut relevant, cs);
                if cs.kind == CheckpointKind::RawPtrDeref && property.contains_kind(contract::PropertyKind::Alias)
                    && let Some(destination) = cs.destination
                {
                    relevant.insert_local(destination);
                }
            }
            let mut items = Vec::new();
            if bind_checkpoint.is_none() {
                items.push(RelevantItem::Terminator {
                    def_id: caller,
                    block: checkpoint_block,
                    global_block: Some(target_block),
                    switch_succ: None,
                });
            }
            let statement_end = bind_checkpoint
                .map(|checkpoint| {
                    // A relevant result includes the statement that creates it.
                    // Other requirements use the state before the checkpoint.
                    checkpoint.stmt_index
                        + usize::from(checkpoint.kind == CheckpointKind::RawPtrDeref
                            && checkpoint.destination.is_some_and(|destination| relevant.locals.contains(&destination)))
                })
                .unwrap_or(block_data.statements.len())
                .min(block_data.statements.len());
            for (si, stmt) in block_data.statements[..statement_end].iter().enumerate().rev() {
                visitor.visit_statement(
                    def_id,
                    checkpoint_block,
                    si,
                    stmt,
                    body,
                    flow,
                    &mut relevant,
                    &mut items,
                );
            }
            Self::re_visit_newly_added(
                visitor,
                def_id,
                checkpoint_block,
                block_data,
                statement_end,
                body,
                flow,
                &mut relevant,
                &mut items,
                0,
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
                entries,
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
                    let successor = Some(BasicBlock::from(tree.block_fn_of(child.block).map_or(child.block, |(_, local)| local)));
                    visitor.visit_terminator(
                        def_id,
                        block,
                        &block_data.rapx_terminator(),
                        flow,
                        body,
                        &mut relevant,
                        &mut items,
                        successor,
                    );
                }
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
                    );
                }
                let dist_to_target = child_path.iter().position(|&b| b == target_block);
                if !block_data.statements.is_empty() && dist_to_target.is_some_and(|d| d <= 2) {
                    Self::re_visit_newly_added(
                        visitor,
                        def_id,
                        block,
                        block_data,
                        block_data.statements.len(),
                        body,
                        flow,
                        &mut relevant,
                        &mut items,
                        block_items_start,
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
            results.push((vec![node.block], checkpoint_items, checkpoint_relevant, Vec::new()));
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
        statement_end: usize,
        body: &'tcx Body<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
        block_items_start: usize,
    ) {
        let newly_added = std::mem::take(&mut relevant.just_added);
        if newly_added.is_empty() {
            return;
        }
        for (si, stmt) in block_data.statements[..statement_end].iter().enumerate().rev() {
            let defs = match &stmt.kind {
                rustc_middle::mir::StatementKind::Assign(assign) => {
                    let mut d = crate::util::def_use::RelevantPlaces::new();
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
                visitor.visit_statement(def_id, block, si, stmt, body, flow, relevant, items);
            }
        }
        let mut seen = HashSet::new();
        let mut block_items: Vec<_> = items.drain(block_items_start..).collect();
        block_items.retain(|item| match item {
            RelevantItem::Statement { stmt_index, .. } => seen.insert(*stmt_index),
            _ => true,
        });
        block_items.sort_by_key(|item| match item {
            RelevantItem::Terminator { .. } => (0, 0),
            RelevantItem::Statement { stmt_index, .. } => (1, usize::MAX - stmt_index),
            _ => (2, 0),
        });
        items.extend(block_items);
    }
}
