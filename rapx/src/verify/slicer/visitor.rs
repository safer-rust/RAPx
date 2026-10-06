//! Backward path visitor — walks a finite path backward from a checkpoint and
//! keeps only MIR items that can affect the required property.
//!
//! The def-use layer lives in [`super::super::def_use`]; this module focuses on
//! the path-level control flow decisions: calls, SCC exits, and path-condition
//! branches.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Body;
use rustc_middle::mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use std::collections::{HashMap, HashSet};

use crate::analysis::dataflow::graph::build_dataflow_graph;
use crate::analysis::dataflow::types::DataflowGraph;

use super::super::{
    contract,
    def_use::{
        RelevantPlaces, bind_callsite_roots, call_args_uses_at, operand_uses, terminator_use_def,
    },
    path_extractor::{Path, PathStep},
};
use crate::helpers::mir_scan::{Checkpoint, CheckpointLocation};

use crate::analysis::path::{PathNode, PathTree};

use super::{
    call_visit,
    types::{ProofGoal, RelevantItem},
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
        for (block_path, backward_items, _relevant, _) in leaf_results {
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
    /// relevant_before_block, parked_caller_relevant)` per checkpoint leaf.
    /// Each leaf is independent — no merging, no HashMap collision.
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
    ) -> Vec<(
        Vec<usize>,
        Vec<RelevantItem<'tcx>>,
        RelevantPlaces,
        Vec<(DefId, Vec<usize>, RelevantPlaces)>,
    )> {
        let (def_id, local_index) = tree.block_fn_of(node.block).unwrap_or((caller, node.block));
        let body = &bodies[&def_id];
        let flow = &flows[&def_id];
        let block = BasicBlock::from(local_index);
        let keep_inv = property
            .kind()
            .is_some_and(|k| needs_invalidation_tracking(&k));
        // Only `Owning` needs the owner's construction chain; other invalidations
        // (Allocated/Init/…) must not be perturbed by the extra needs_drop keeps.
        let keep_owner = matches!(property.kind(), Some(contract::PropertyKind::Owning));
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
                switch_succ: None,
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
                    keep_owner,
                );
            }
            // Pass 2: re-visit definitions that became relevant only
            // during pass 1.
            Self::re_visit_newly_added(
                visitor,
                def_id,
                checkpoint_block,
                block_data,
                flow,
                &mut relevant,
                &mut items,
                keep_inv,
                keep_owner,
            );
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
                    && let Some(binding) = tree.inline_binding(node.block - local_index)
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
                        binding.arg_locals.clone(),
                        std::mem::replace(&mut relevant, callee_relevant),
                    ));
                }
                // Skip the `Call` terminator when this block's call was inlined:
                // the callee's statements are already sliced via the path, so
                // treating the call as atomic would double-count it.
                if !tree.is_inlined_call(node.block) {
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
                        flow,
                        &mut relevant,
                        &mut items,
                        keep_inv,
                        keep_owner,
                    );
                }
                // Leaving an inlined callee entry: remap the callee's parameter
                // locals back to the caller's argument locals so the caller's
                // argument-producing statements stay relevant.
                if let Some(binding) = tree.inline_binding(node.block) {
                    let (_, frame_arg_locals, parked) = frames
                        .pop()
                        .unwrap_or((def_id, binding.arg_locals.clone(), RelevantPlaces::new()));
                    let mut caller_relevant = parked;
                    for (i, arg_local) in frame_arg_locals.iter().enumerate() {
                        if relevant.locals.contains(&Local::from_usize(i + 1)) {
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
        if !checkpoint_items.is_empty() {
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
    fn re_visit_newly_added(
        visitor: &Self,
        def_id: DefId,
        block: BasicBlock,
        block_data: &'tcx rustc_middle::mir::BasicBlockData<'tcx>,
        flow: &DataflowGraph,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<RelevantItem<'tcx>>,
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
                    let mut d = crate::verify::def_use::RelevantPlaces::new();
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
                    def_id, block, si, stmt, flow, relevant, items, keep_inv, keep_owner,
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
        keep_owner: bool,
    ) {
        if keep_invalidations
            && matches!(
                statement.kind,
                StatementKind::StorageDead(_) | StatementKind::StorageLive(_)
            )
        {
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            return;
        }

        // Keep the definition of a `needs_drop` local (an owner's construction
        // chain) so `Owning` can trace its field provenance.
        if keep_owner {
            if let StatementKind::Assign(assign) = &statement.kind {
                let (place, _) = &**assign;
                let body = self.tcx.optimized_mir(def_id);
                let ty = body.local_decls[place.local].ty;
                let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, def_id);
                if ty.needs_drop(self.tcx, typing_env) {
                    let mut defs = RelevantPlaces::new();
                    defs.insert_mir_place(place);
                    let uses =
                        collect_statement_uses(statement, block, statement_index, flow, &defs);
                    items.push(RelevantItem::Statement {
                        def_id,
                        block,
                        statement_index,
                    });
                    relevant.remove_all(&defs);
                    relevant.extend(uses);
                    return;
                }
            }
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

        // A provenance-carrying assignment — a pointer cast (`*const T as
        // *const U`, a reference→pointer cast) or a reborrow through a
        // reference/pointer (`&mut (*_1)`) — carries the source's
        // provenance/align_n even when its destination is not *value*-relevant
        // to the property.  Keep it — and follow its source — so the forward VM
        // propagates the provenance instead of relying on the backward
        // `propagate_single_assign` fill-in.
        let is_provenance_carrier = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                let dest_is_ptr = matches!(
                    self.tcx.optimized_mir(def_id).local_decls[place.local].ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
                );
                match rvalue {
                    Rvalue::Cast(..) => dest_is_ptr,
                    Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place) => src_place
                        .projection
                        .iter()
                        .any(|p| {
                            matches!(
                                p.kind(),
                                rustc_middle::mir::ProjectionElem::Deref
                            )
                        }),
                    #[cfg(rapx_rvalue_use_with_retag)]
                    Rvalue::Use(operand, _) => {
                        let is_projected = match operand {
                            Operand::Copy(p) | Operand::Move(p) => p.projection.iter().any(|e| {
                                matches!(e.kind(), rustc_middle::mir::ProjectionElem::Deref)
                            }),
                            _ => false,
                        };
                        dest_is_ptr || is_projected
                    }
                    #[cfg(not(rapx_rvalue_use_with_retag))]
                    Rvalue::Use(operand) => {
                        let is_projected = match operand {
                            Operand::Copy(p) | Operand::Move(p) => p.projection.iter().any(|e| {
                                matches!(e.kind(), rustc_middle::mir::ProjectionElem::Deref)
                            }),
                            _ => false,
                        };
                        dest_is_ptr || is_projected
                    }
                    Rvalue::CopyForDeref(p) => dest_is_ptr || !p.projection.is_empty(),
                    _ => false,
                }
            }
            _ => false,
        };

        // A statement that writes an iterator's `ptr` field (`(*self).0 = ...`,
        // the inlined `post_inc_start`) must be kept even when it is not
        // *value*-relevant to the property: the forward VM tracks the iterator's
        // cumulative offset from this write (`track_iter_ptr_update`), which is
        // what makes the loop-carried `i < n` invariant provable.
        let is_iter_ptr_write = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                let mut proj = place.projection.iter();
                if !matches!(
                    proj.next().map(|p| p.kind()),
                    Some(rustc_middle::mir::ProjectionElem::Deref)
                ) {
                    false
                } else {
                    let is_field0 = matches!(
                        (proj.next().map(|p| p.kind()), proj.next()),
                        (Some(rustc_middle::mir::ProjectionElem::Field(f, _)), None)
                            if f.as_usize() == 0
                    );
                    if !is_field0 {
                        false
                    } else {
                        let base_ty = self.tcx.optimized_mir(def_id).local_decls[place.local].ty;
                        match base_ty.kind() {
                            rustc_middle::ty::TyKind::Ref(_, pointee, _) => {
                                match pointee.kind() {
                                    rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                                        crate::verify::api_classify::is_std_iter_or_itermut(
                                            adt_def.did(),
                                        )
                                    }
                                    _ => false,
                                }
                            }
                            _ => false,
                        }
                    }
                }
            }
            _ => false,
        };

        // A write into a `[u8; N]`/`[u8]` buffer (e.g. `box [a, b, 0]`'s element
        // store `((*_8).1).0 = [a, b, 0]`) must be kept even when it is not
        // *value*-relevant to the property: the forward VM records these stores
        // as per-byte values, and `ValidCStr`/`ValidString` reason over them.
        // The backward def-use graph is place-level (it cannot follow the
        // `Box`/`Vec` → buffer indirection), so this structural keep is what
        // preserves the byte-level dataflow.
        let is_byte_write = match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, _) = &**assign;
                let ty = place.ty(self.tcx.optimized_mir(def_id), self.tcx).ty;
                crate::helpers::mir_utils::is_u8_array_or_slice(ty)
            }
            _ => false,
        };

        if defs.intersects(relevant) || is_provenance_carrier || is_iter_ptr_write || is_byte_write
        {
            let mut uses = collect_statement_uses(statement, block, statement_index, flow, &defs);
            items.push(RelevantItem::Statement {
                def_id,
                block,
                statement_index,
            });
            // Save places already in the relevance set before removing
            // the current definition.  When the uses of this statement
            // would re-add a place whose definition was already found earlier
            // in the walk, skip it to prevent wrong (duplicate) matches.
            let already_seen: crate::compat::FxHashSet<crate::verify::def_use::PlaceKey> =
                relevant.places.clone();
            relevant.remove_all(&defs);
            uses.places.retain(|p| !already_seen.contains(p));
            relevant.extend(uses);
            return;
        }

        if statement_can_refine(statement) {
            let uses = collect_flow_uses(flow, block, statement_index, &defs);
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
        keep_owner: bool,
        successor: Option<BasicBlock>,
    ) {
        if keep_invalidations {
            if matches!(terminator.kind, TerminatorKind::Drop { .. }) {
                items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                return;
            }
            // A manual drop (`std::mem::drop` / `ManuallyDrop::drop`) also frees
            // the pointee's heap: keep the call and its argument's construction
            // chain so `Allocated`/`Owning` can see the freed allocation and
            // detect a later use / second drop.
            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let is_drop_call =
                    crate::helpers::mir_utils::dep_callee_def_id(func).is_some_and(|c| {
                        crate::verify::api_classify::is_manually_drop_drop(Some(c))
                            || crate::verify::api_classify::is_std_drop(Some(c))
                    });
                if is_drop_call {
                    items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                    relevant.extend(call_args_uses_at(args, &[0]));
                    return;
                }
            }
        }

        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            // `Owning` traces an owner's construction chain: keep a call whose
            // destination is a `needs_drop` value even when that local is not
            // itself relevant, so its field provenance survives.
            if keep_owner {
                let dest_ty = body.local_decls[destination.local].ty;
                let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx, def_id);
                if dest_ty.needs_drop(self.tcx, typing_env) {
                    let use_def = terminator_use_def(terminator);
                    items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
                    relevant.remove_all(&use_def.defs);
                    relevant.extend(use_def.uses);
                    return;
                }
            }
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
            let switch_succ = match terminator.kind {
                TerminatorKind::SwitchInt { .. } => successor,
                _ => None,
            };
            items.push(RelevantItem::Terminator { def_id, block, switch_succ });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            items.push(RelevantItem::Terminator { def_id, block, switch_succ: None });
        }
    }
}

// ── property helpers ──────────────────────────────────────────────────

/// Whether a property's checker reads allocation liveness (`alloc.facts.dead`), so
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

fn terminator_is_path_condition(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(
        terminator.kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}

/// Collect all place-uses for a statement from dataflow edges and operands.
fn collect_statement_uses<'tcx>(
    statement: &'tcx rustc_middle::mir::Statement<'tcx>,
    block: BasicBlock,
    statement_index: usize,
    flow: &DataflowGraph,
    defs: &RelevantPlaces,
) -> RelevantPlaces {
    let mut uses = collect_flow_uses(flow, block, statement_index, defs);

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

/// Collect the source locals of the dataflow edges entering
/// `(block, statement_index)` from the def locals of `defs`.
fn collect_flow_uses(
    flow: &DataflowGraph,
    block: BasicBlock,
    statement_index: usize,
    defs: &RelevantPlaces,
) -> RelevantPlaces {
    let mut uses = RelevantPlaces::new();
    for &local in &defs.locals {
        for &edge_idx in &flow.node(local).in_edges {
            let edge = &flow.edges[edge_idx];
            if edge.block == block.as_usize() && edge.statement_index == statement_index {
                uses.insert_local(edge.src);
            }
        }
    }
    uses
}
