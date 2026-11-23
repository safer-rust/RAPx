//! Path-sensitive verification for one function.
//!
//! Extract paths, slice retained MIR, and check checkpoints, invariants, and postconditions.

mod proof;

use std::rc::Rc;

use indexmap::IndexMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use crate::analysis::path::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::contract::{ContractExpr, PlaceBase, Property, PropertyArg, PropertyKind};
use crate::util::{
    fn_info::{FnKind, get_type},
    mir_utils::{collect_return_block_indices, is_return_block},
};

use super::{
    config::VerifyConfig,
    checkpoint::{Checkpoint, CheckpointKind, CheckpointLocation},
    path::PathExtractor,
    proof_cache::{VmCache, new_z3_context},
    report::{CheckResult, PropertyCheckResult, UnknownReason, VerificationLimits},
    slicer::BackwardSlicer,
    target::FunctionTarget,
};

/// Verifies one function at a selected path repetition limit.
///
/// Borrows the collected target and owns the extracted paths and backward
/// slicer. Checks unsafe checkpoints, invariants, and postconditions.
///
/// # Agent Rules
/// Do not add new fields without human approval.
pub(crate) struct FunctionVerifier<'target, 'tcx> {
    /// Compiler context for type and MIR queries.
    tcx: TyCtxt<'tcx>,
    /// Options shared by path extraction and VM execution.
    config: Rc<VerifyConfig>,
    /// Collected checkpoints, contracts, and invariants for this function.
    target: &'target FunctionTarget<'tcx>,
    /// Paths through the function and expanded callees for this verification run.
    path_tree: PathTree,
    /// Backward slicer shared by all property checks.
    slicer: BackwardSlicer<'tcx>,
}

impl<'target, 'tcx> FunctionVerifier<'target, 'tcx> {
    /// Coverage limits reached while extracting this function's paths.
    pub(crate) fn limits(&self) -> VerificationLimits {
        VerificationLimits {
            path_limited: self.path_tree.is_truncated(),
            mono_limited: self.path_tree.is_trait_impl_limited(),
        }
    }

    /// Build paths for all checkpoints, or one checkpoint when specified.
    pub(crate) fn new(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>, allow_repeat: usize, checkpoint: Option<&Checkpoint<'tcx>>, config: Rc<VerifyConfig>) -> Self {
        let locations = checkpoint.map_or_else(
            || target.all_checkpoints().map(Checkpoint::location).collect::<Vec<_>>(),
            |checkpoint| vec![checkpoint.location()],
        );
        let terminal_target = checkpoint
            .filter(|checkpoint| !target.properties_for_callsite(checkpoint).iter().any(Self::property_contains_alias))
            .map(|checkpoint| checkpoint.block.as_usize());
        let (path_tree, callee_bodies, entry_bodies) =
            PathExtractor::new_with_body(tcx, Rc::clone(&config), target.def_id, allow_repeat, target.body)
                .with_callee_bodies(target.callee_bodies.clone())
                .with_checkpoints(&locations)
                .with_terminal_target(terminal_target)
                .run_with_bodies();
        Self {
            tcx,
            config,
            target,
            path_tree,
            slicer: BackwardSlicer::new(tcx, target.def_id, target.body, callee_bodies, entry_bodies),
        }
    }

    /// Enumerate and check paths independently for each unsafe operation.
    pub(crate) fn verify_checkpoints(tcx: TyCtxt<'tcx>, target: &'target FunctionTarget<'tcx>, allow_repeat: usize, config: Rc<VerifyConfig>, cache: &mut VmCache<'_, 'tcx>) -> (Vec<PropertyCheckResult<'tcx>>, VerificationLimits) {
        let mut results = Vec::new();
        let mut limits = VerificationLimits::default();
        for (checkpoint_index, checkpoint) in target.all_checkpoints().enumerate() {
            if target.properties_for_callsite(checkpoint).is_empty()
                && !(checkpoint.kind == CheckpointKind::UnsafeCall && checkpoint.callee.is_none()) {
                continue;
            }
            let verifier = Self::new(tcx, target, allow_repeat, Some(checkpoint), Rc::clone(&config));
            limits.merge(verifier.limits());
            verifier.verify_checkpoint(cache, checkpoint, checkpoint_index, &mut results);
        }
        (results, limits)
    }

    /// Append a checkpoint's property results or an unresolved-call UNKNOWN.
    fn verify_checkpoint(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        checkpoint_index: usize,
        results: &mut Vec<PropertyCheckResult<'tcx>>,
    ) {
        let properties = self.target.properties_for_callsite(checkpoint);
        let unresolved_call = checkpoint.kind == CheckpointKind::UnsafeCall
            && checkpoint.callee.is_none()
            && properties.is_empty();
        if unresolved_call {
            results.push(PropertyCheckResult {
                checkpoint: checkpoint.location(),
                checkpoint_index,
                property: Property::new(self.tcx, self.target.def_id, "Unknown", &[]),
                result: CheckResult::Unknown(UnknownReason::UnresolvedUnsafeCall),
                path_desc: String::new(),
                callee_name: checkpoint.callee_name(self.tcx),
            });
            return;
        }
        let path_results = self.check_checkpoint_properties(cache, checkpoint, properties);
        for (path_desc, property_index, result) in path_results {
            results.push(PropertyCheckResult {
                checkpoint: checkpoint.location(),
                checkpoint_index,
                property: properties[property_index].clone(),
                result,
                path_desc,
                callee_name: checkpoint.callee_name(self.tcx),
            });
        }
    }

    /// Recheck all collected invariants at exits.
    pub(crate) fn verify_invariants(&self) -> Vec<PropertyCheckResult<'tcx>> {
        let is_constructor = get_type(self.tcx, self.target.def_id) == FnKind::Constructor;
        let entry_facts: Vec<Property<'tcx>> = self.target.caller_requires.iter()
            .filter(|c| !matches!(c.kind(), Some(PropertyKind::Unknown)))
            .cloned()
            .collect();
        self.check_exit_properties(&self.target.invariants, &entry_facts, !is_constructor, "invariants")
    }

    /// Check postconditions at normal return blocks using entry requirements.
    pub(crate) fn verify_postconditions(&self, postconditions: &[Property<'tcx>]) -> Vec<PropertyCheckResult<'tcx>> {
        let entry_facts: Vec<Property<'tcx>> = self.target.caller_requires.iter()
            .filter(|property| !matches!(property.kind(), Some(PropertyKind::Unknown)))
            .cloned()
            .collect();
        self.check_exit_properties(postconditions, &entry_facts, false, "postconditions")
    }

    /// Check exit properties together when they share the same eligible paths.
    fn check_exit_properties(
        &self,
        invariants: &[Property<'tcx>],
        entry_facts: &[Property<'tcx>],
        check_unwind: bool,
        label: &str,
    ) -> Vec<PropertyCheckResult<'tcx>> {
        let mut results = Vec::new();
        let z3_ctx = new_z3_context();
        let mut cache = VmCache::new(&z3_ctx, self.config.constructor_mir_mode());
        for (checkpoint, tree) in self.build_exit_trees(check_unwind) {
            let all_paths = tree.to_vecs();
            let path_indices: FxHashMap<_, _> = all_paths.iter().cloned().enumerate().map(|(index, path)| (path, index)).collect();
            let mut goals_by_path = vec![None; all_paths.len()];
            let mut properties_by_path = Vec::with_capacity(all_paths.len());
            // Return-value properties apply only to normal returns. Other
            // exits can still carry obligations on the receiver or arguments.
            let is_return = is_return_block(self.tcx, self.target.def_id, checkpoint.block);
            let eligible: Vec<_> = invariants.iter().enumerate()
                .filter_map(|(index, invariant)| (is_return || !targets_return_value(invariant)).then_some(index))
                .collect();
            let stable: Vec<_> = invariants.iter().map(|invariant| {
                label == "invariants"
                    && entry_facts.contains(invariant)
                    && is_preserved_slice_ref_invariant(self.tcx, self.target.def_id, invariant)
            }).collect();
            let mut groups: IndexMap<Vec<usize>, FxHashSet<Vec<usize>>> = IndexMap::new();
            for path in &all_paths {
                let indices: Vec<_> = eligible.iter().copied().filter(|&index| {
                    label != "invariants" || type_invariant_subject(&invariants[index]).is_none_or(|local| {
                        type_invariant_subject_live(self.tcx, self.target.def_id, &tree, path, local)
                    })
                }).collect();
                if !indices.is_empty() {
                    groups.entry(indices.clone()).or_default().insert(path.clone());
                }
                properties_by_path.push(indices);
            }
            for (indices, paths) in groups {
                let selected: Vec<_> = indices.iter().copied()
                    .filter(|&index| !stable[index])
                    .collect();
                if selected.is_empty() {
                    continue;
                }
                let check_tree = tree.filter_paths(|path| paths.contains(path));
                let properties: Vec<_> = selected.iter().map(|&index| &invariants[index]).collect();
                let goals = self.slicer.visit_exit_properties(&check_tree, checkpoint.block.as_usize(), self.target.def_id, checkpoint, &properties);
                for (path, goal) in check_tree.to_vecs().into_iter().zip(goals) {
                    goals_by_path[path_indices[&path]] = Some(goal);
                }
            }
            for (path_index, path) in all_paths.iter().enumerate() {
                let indices = &properties_by_path[path_index];
                let selected: Vec<_> = indices.iter().copied().filter(|&index| !stable[index]).collect();
                let properties: Vec<_> = selected.iter().map(|&index| &invariants[index]).collect();
                let checked = goals_by_path[path_index].take().map(|goal| {
                    self.check_exit_goal(&mut cache, &tree, checkpoint, &properties, entry_facts, goal)
                });
                let path_desc = format!("{:?}", super::path::caller_blocks(&tree, self.target.def_id, path.iter().copied()));
                let mut slot = 0;
                for &property_index in indices {
                    let result = if stable[property_index] {
                        CheckResult::ProvedByRule
                    } else {
                        let result = checked.as_ref().and_then(|results| results.get(slot)).cloned();
                        slot += 1;
                        let Some(result) = result else { continue };
                        result
                    };
                    results.push(PropertyCheckResult {
                        checkpoint,
                        checkpoint_index: checkpoint.block.as_usize(),
                        property: invariants[property_index].clone(),
                        result,
                        path_desc: path_desc.clone(),
                        callee_name: format!("{label}(bb{})", checkpoint.block.as_usize()),
                    });
                }
            }
        }
        results
    }

    fn build_exit_trees(&self, check_unwind: bool) -> FxHashMap<CheckpointLocation, PathTree> {
        let mut trees_by_checkpoint: FxHashMap<CheckpointLocation, PathTree> = FxHashMap::default();

        if !check_unwind {
            let return_blocks = collect_return_block_indices(self.tcx, self.target.def_id);
            for &return_block in &return_blocks {
                let checkpoint = CheckpointLocation {
                    caller: self.target.def_id,
                    block: return_block,
                };
                let tree = self.path_tree.subtree_to(return_block.as_usize());
                if !tree.is_empty() {
                    trees_by_checkpoint.insert(checkpoint, tree);
                }
            }
        } else {
            let mut exit_blocks: FxHashSet<usize> = FxHashSet::default();
            for path in self.path_tree.to_vecs() {
                if let Some(&last) = path.last() {
                    exit_blocks.insert(last);
                }
            }
            for exit_block in exit_blocks {
                // An inlined callee can end a whole-CFG path. Check exit
                // properties only at the caller's own blocks; its global and
                // local block indices coincide because it is the CFG root.
                let Some((def_id, local)) = self.path_tree.block_fn_of(exit_block) else {
                    continue;
                };
                if def_id != self.target.def_id {
                    continue;
                }
                let checkpoint = CheckpointLocation {
                    caller: self.target.def_id,
                    block: BasicBlock::from_usize(local),
                };
                let tree = self.path_tree.subtree_to(exit_block);
                if !tree.is_empty() {
                    trees_by_checkpoint.insert(checkpoint, tree);
                }
            }
        }

        trees_by_checkpoint
    }
}

fn targets_return_value(property: &Property<'_>) -> bool {
    property.target_place().is_some_and(|cp| matches!(cp.base, PlaceBase::Return))
}

/// Reuse a slice reference's entry `NonNull`, `Align`, or `ValidNum` fact at exits
/// when its MIR local is neither changed nor exposed by address. Memory-state
/// properties such as `Allocated`, `Init`, and `Typed` still need VM checks.
fn is_preserved_slice_ref_invariant(tcx: TyCtxt<'_>, def_id: DefId, property: &Property<'_>) -> bool {
    let Some(kind) = property.kind() else {
        return false;
    };
    if !matches!(kind, PropertyKind::NonNull | PropertyKind::Align | PropertyKind::ValidNum) {
        return false;
    }
    let Some(local) = type_invariant_subject(property) else {
        return false;
    };
    let body = tcx.optimized_mir(def_id);
    if local.as_usize() > body.arg_count {
        return false;
    }
    let TyKind::Ref(_, inner, _) = body.local_decls[local].ty.kind() else {
        return false;
    };
    if !matches!(inner.kind(), TyKind::Slice(_)) {
        return false;
    }
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (destination, value) = assign.as_ref();
                    if destination.local == local && destination.projection.is_empty() {
                        return false;
                    }
                    if matches!(value, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
                        if place.local == local && place.projection.is_empty())
                    {
                        return false;
                    }
                }
                StatementKind::StorageDead(dead) if *dead == local => return false,
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call { destination, .. }
                if destination.local == local && destination.projection.is_empty() =>
            {
                return false;
            }
            TerminatorKind::InlineAsm { .. } => return false,
            _ => {}
        }
    }
    true
}

fn type_invariant_subject(property: &Property<'_>) -> Option<Local> {
    fn collect_expr(expr: &ContractExpr<'_>, roots: &mut FxHashSet<Local>) {
        match expr {
            ContractExpr::Place(place) => {
                roots.insert(place.base.to_local());
            }
            ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
                collect_expr(inner, roots);
            }
            ContractExpr::IndexAccess { slice, index } => {
                collect_expr(slice, roots);
                collect_expr(index, roots);
            }
            ContractExpr::Binary { lhs, rhs, .. } => {
                collect_expr(lhs, roots);
                collect_expr(rhs, roots);
            }
            ContractExpr::Unary { expr, .. } => collect_expr(expr, roots),
            ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                collect_expr(&cond.lhs, roots);
                collect_expr(&cond.rhs, roots);
                collect_expr(then_expr, roots);
                collect_expr(else_expr, roots);
            }
            _ => {}
        }
    }

    let mut roots = FxHashSet::default();
    for arg in property.args() {
        match arg {
            PropertyArg::Expr(expr) | PropertyArg::ForEach(expr) => collect_expr(expr, &mut roots),
            PropertyArg::Predicates(predicates) => {
                for predicate in predicates {
                    collect_expr(&predicate.lhs, &mut roots);
                    collect_expr(&predicate.rhs, &mut roots);
                }
            }
            _ => {}
        }
    }
    if roots.len() == 1 {
        roots.into_iter().next().filter(|local| local.as_usize() > 0)
    } else {
        None
    }
}

fn type_invariant_subject_live(tcx: TyCtxt<'_>, def_id: DefId, tree: &PathTree, path: &[usize], local: Local) -> bool {
    let body = tcx.optimized_mir(def_id);
    let mut live = true;
    for &global_block in path {
        let Some((block_def_id, local_block)) = tree.block_fn_of(global_block) else {
            continue;
        };
        if block_def_id != def_id {
            continue;
        }
        let block = &body.basic_blocks[BasicBlock::from_usize(local_block)];
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (destination, value) = &**assign;
                    let moved = match value {
                        Rvalue::Use(Operand::Move(place), _) => {
                            place.local == local && place.projection.is_empty()
                        }
                        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| {
                            matches!(operand, Operand::Move(place) if place.local == local && place.projection.is_empty())
                        }),
                        _ => false,
                    };
                    if moved {
                        live = false;
                    }
                    if destination.local == local && destination.projection.is_empty() {
                        live = true;
                    }
                }
                StatementKind::StorageDead(dead) | StatementKind::StorageLive(dead)
                    if *dead == local =>
                {
                    live = false;
                }
                _ => {}
            }
        }
        match &block.terminator().kind {
            TerminatorKind::Call {
                args, destination, ..
            } => {
                if args.iter().any(|arg| {
                    matches!(&arg.node, Operand::Move(place) if place.local == local && place.projection.is_empty())
                }) {
                    live = false;
                }
                if destination.local == local && destination.projection.is_empty() {
                    live = true;
                }
            }
            TerminatorKind::Drop { place, .. }
                if place.local == local && place.projection.is_empty() =>
            {
                live = false;
            }
            _ => {}
        }
    }
    live
}
