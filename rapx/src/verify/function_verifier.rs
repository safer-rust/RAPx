//! Path-sensitive verification for one function.
//!
//! Extract paths, slice retained MIR, and check checkpoints, invariants, and postconditions.

mod proof;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use crate::analysis::path::PathTree;
use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::{
    fn_info::{FnKind, get_type},
    mir_utils::{collect_return_block_indices, is_return_block},
};

use super::{
    api_classify,
    checkpoint::{Checkpoint, CheckpointKind, CheckpointLocation},
    contract::{
        ContractExpr, PlaceBase, Property, PropertyArg, PropertyKind,
    },
    path::PathExtractor,
    proof_cache::{VmCache, new_z3_context},
    report::{
        CheckResult, PATH_LIMIT_DESCRIPTION, PropertyCheckResult, UnknownReason, VerificationReport,
    },
    slicer::{BackwardSlicer, RelevantItem},
    target::FunctionTarget,
};

/// Verifies one function at a selected path repetition limit.
///
/// Borrows the collected target and owns the extracted paths and backward
/// slicer. Checks unsafe checkpoints, struct/type invariants, and postconditions.
///
/// # Agent Rules
/// Do not add new fields without human approval.
pub(crate) struct FunctionVerifier<'target, 'tcx> {
    /// Compiler context for type and MIR queries.
    tcx: TyCtxt<'tcx>,
    /// Collected checkpoints, contracts, and invariants for this function.
    target: &'target FunctionTarget<'tcx>,
    /// Paths through the function and expanded callees used by all checks.
    path_tree: PathTree,
    /// Backward slicer shared by all property checks.
    slicer: BackwardSlicer<'tcx>,
}

impl<'target, 'tcx> FunctionVerifier<'target, 'tcx> {
    /// Whether path extraction reached its trait implementation limit.
    pub(crate) fn is_trait_impl_limited(&self) -> bool {
        self.path_tree.is_trait_impl_limited()
    }

    pub(crate) fn new_with_repeat(
        tcx: TyCtxt<'tcx>,
        target: &'target FunctionTarget<'tcx>,
        allow_repeat: usize,
    ) -> Self {
        let locations = target.all_checkpoints().map(Checkpoint::location).collect::<Vec<_>>();
        let (path_tree, callee_bodies, entry_bodies) =
            PathExtractor::new_with_body(tcx, target.def_id, allow_repeat, target.body)
                .with_callee_bodies(target.callee_bodies.clone())
                .with_checkpoints(&locations)
                .run_with_bodies();
        Self {
            tcx,
            target,
            path_tree,
            slicer: BackwardSlicer::new(
                tcx,
                target.def_id,
                target.body,
                callee_bodies,
                entry_bodies,
            ),
        }
    }

    /// Check unsafe-operation requirements and report unresolved calls.
    pub(crate) fn verify_checkpoints(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
    ) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        for (checkpoint_index, checkpoint) in self.target.all_checkpoints().enumerate() {
            self.verify_checkpoint(cache, checkpoint, checkpoint_index, &mut report);
        }
        report
    }

    /// Append a checkpoint's property results or an unresolved-call UNKNOWN.
    fn verify_checkpoint(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        checkpoint_index: usize,
        report: &mut VerificationReport<'tcx>,
    ) {
        let properties = self.target.properties_for_callsite(checkpoint);
        let unresolved_call = checkpoint.kind == CheckpointKind::UnsafeCall
            && checkpoint.callee.is_none()
            && properties.is_empty();
        if unresolved_call {
            report.results.push(PropertyCheckResult {
                checkpoint: checkpoint.location(),
                checkpoint_index,
                path_index: 0,
                property_index: 0,
                property: Property::new(self.tcx, self.target.def_id, "Unknown", &[]),
                result: CheckResult::Unknown(UnknownReason::UnresolvedUnsafeCall),
                diagnostics: Some("unsafe operation has no resolvable contract".to_string()),
                path_description: String::new(),
                callee_name: checkpoint.callee_name(self.tcx),
            });
            return;
        }
        // A resolved unsafe callee with empty requirements needs no check;
        // missing contracts already have an Unknown property.
        if properties.is_empty() {
            return;
        }

        for (property_index, property) in properties.iter().enumerate() {
            let bulk = self.check_property_paths(cache, checkpoint, property);
            let path_count = bulk.len();
            for (path_index, (result, path_desc)) in bulk.into_iter().enumerate() {
                report.results.push(PropertyCheckResult {
                    checkpoint: checkpoint.location(),
                    checkpoint_index,
                    path_index,
                    property_index,
                    property: property.clone(),
                    diagnostics: Some(format!("vm-check: {result:?}")),
                    result,
                    path_description: path_desc,
                    callee_name: checkpoint.callee_name(self.tcx),
                });
            }
            // The path limit bounds precision. Mark omitted paths as proved
            // so only results from enumerated paths affect the verdict.
            if self.path_tree.is_truncated() {
                report.results.push(PropertyCheckResult {
                    checkpoint: checkpoint.location(),
                    checkpoint_index,
                    path_index: path_count,
                    property_index,
                    property: property.clone(),
                    result: CheckResult::ProvedByRule,
                    diagnostics: Some("path enumeration stopped at its limit".to_string()),
                    path_description: PATH_LIMIT_DESCRIPTION.to_string(),
                    callee_name: checkpoint.callee_name(self.tcx),
                });
            }
        }
    }

    fn property_contains_alias(property: &Property<'_>) -> bool {
        match property {
            Property::Atom(atom) => atom.kind == PropertyKind::Alias,
            Property::And(and) => and.conjuncts.iter().any(Self::property_contains_alias),
            Property::Or(or) => or.disjuncts.iter().any(Self::property_contains_alias),
        }
    }

    /// Check one property across all paths. `Or` evaluates its disjuncts on the
    /// same VM states; `And` keeps per-child slicing.
    fn check_property_paths(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Vec<(CheckResult, String)> {
        if let Property::And(and) = property {
            return self.combine_check_paths(cache, checkpoint, &and.conjuncts);
        }
        let is_manual_drop = api_classify::is_manually_drop_drop(self.tcx, checkpoint.callee);
        if matches!(property, Property::Atom(atom) if atom.kind == PropertyKind::Alias)
            && is_manual_drop
        {
            self.check_drop(checkpoint)
        } else {
            self.check_callsite(
                cache,
                checkpoint,
                property,
                is_manual_drop && Self::property_contains_alias(property),
            )
        }
    }

    /// Combine independently sliced conjuncts after aligning structural paths.
    fn combine_check_paths(
        &self,
        cache: &mut VmCache<'_, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        children: &[Property<'tcx>],
    ) -> Vec<(CheckResult, String)> {
        let mut children = children.iter();
        let Some(first) = children.next() else {
            return Vec::new();
        };
        let mut per_path = self.check_property_paths(cache, checkpoint, first);
        for child in children {
            let bulk = self.check_property_paths(cache, checkpoint, child);
            if per_path.len() != bulk.len()
                || per_path
                    .iter()
                    .zip(&bulk)
                    .any(|(left, right)| left.1 != right.1)
            {
                let descriptions = if bulk.len() > per_path.len() {
                    bulk.into_iter()
                        .map(|(_, description)| description)
                        .collect::<Vec<_>>()
                } else {
                    per_path
                        .into_iter()
                        .map(|(_, description)| description)
                        .collect::<Vec<_>>()
                };
                return descriptions
                    .into_iter()
                    .map(|description| {
                        (
                            CheckResult::Unknown(UnknownReason::InconsistentPathResults),
                            description,
                        )
                    })
                    .collect();
            }
            for (slot, (result, _)) in per_path.iter_mut().zip(bulk) {
                slot.0 = slot.0.clone().and(result);
            }
        }
        per_path
    }

    /// Recheck the target's struct invariants at its exits.
    ///
    /// For constructors (functions returning `Self`), paths are filtered to
    /// return blocks to avoid unwinding paths where the struct may not be
    /// fully initialised. For methods, the invariant is re-proved at every
    /// exit block of the shared whole-CFG path tree.
    pub(crate) fn verify_struct_invariants(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let invariants = &self.target.struct_invariants;
        if invariants.is_empty() {
            return report;
        }

        let is_constructor = get_type(self.tcx, self.target.def_id) == FnKind::Constructor;
        let caller_contracts = &self.target.caller_requires;

        // Entry facts: the full `caller_requires` (explicit `#[rapx::requires]`
        // preconditions + the implicit struct invariants).  The preconditions
        // are needed to re-prove the invariant after a field mutation — e.g.
        // `set_len` sets `self.len = new_len`, so `len <= cap` only follows
        // from the `new_len <= self.cap` precondition.
        let entry_facts: Vec<RelevantItem<'tcx>> = caller_contracts
            .iter()
            .filter(|c| !matches!(c.kind(), Some(PropertyKind::Unknown)))
            .map(|c| RelevantItem::ContractFact {
                property: c.clone(),
            })
            .collect();

        report.results.extend(self.check_exit_properties(
            invariants,
            &entry_facts,
            !is_constructor,
            "struct",
        ));

        report
    }

    /// Recheck built-in type invariants at exits when unsafe operations are
    /// present. Skip paths where the subject was moved or dropped.
    pub(crate) fn verify_type_invariants(&self) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let invariants = &self.target.type_invariants;
        if invariants.is_empty() || !self.target.has_checkable_checkpoint() {
            return report;
        }

        let entry_facts: Vec<RelevantItem<'tcx>> = invariants
            .iter()
            .map(|inv| RelevantItem::ContractFact {
                property: inv.clone(),
            })
            .collect();

        report.results.extend(self.check_exit_properties(
            invariants,
            &entry_facts,
            false,
            "type",
        ));

        report
    }

    /// Check postconditions at normal return blocks using entry requirements.
    pub(crate) fn verify_postconditions(
        &self,
        postconditions: &[Property<'tcx>],
    ) -> VerificationReport<'tcx> {
        let mut report = VerificationReport::new(self.target.def_id);
        let entry_facts: Vec<RelevantItem<'tcx>> = self
            .target
            .caller_requires
            .iter()
            .filter(|property| !matches!(property.kind(), Some(PropertyKind::Unknown)))
            .map(|property| RelevantItem::ContractFact {
                property: property.clone(),
            })
            .collect();
        report.results.extend(self.check_exit_properties(
            postconditions,
            &entry_facts,
            false,
            "postcond",
        ));
        report
    }

    /// Check eligible struct invariants, type invariants, or postconditions
    /// on each path to the selected exits.
    fn check_exit_properties(
        &self,
        invariants: &[Property<'tcx>],
        entry_facts: &[RelevantItem<'tcx>],
        check_unwind: bool,
        label: &str,
    ) -> Vec<PropertyCheckResult<'tcx>> {
        let mut results = Vec::new();
        let z3_ctx = new_z3_context();
        let mut cache = if label == "type" {
            VmCache::new_with_capacity(&z3_ctx, 512)
        } else {
            VmCache::new(&z3_ctx)
        };
        for (checkpoint, tree) in self.build_exit_trees(check_unwind) {
            let paths = tree.to_vecs();

            // Return-value properties apply only to normal returns. Other
            // exits can still carry obligations on the receiver or arguments.
            let is_return = is_return_block(self.tcx, self.target.def_id, checkpoint.block);

            for (property_index, invariant) in invariants.iter().enumerate() {
                if !is_return && targets_return_value(invariant) {
                    continue;
                }
                let filtered_tree = if label == "type" {
                    type_invariant_subject(invariant).map(|local| {
                        tree.filter_paths(|path| {
                            type_invariant_subject_live(
                                self.tcx,
                                self.target.def_id,
                                &tree,
                                path,
                                local,
                            )
                        })
                    })
                } else {
                    None
                };
                let check_tree = filtered_tree.as_ref().unwrap_or(&tree);
                if check_tree.is_empty() {
                    continue;
                }
                let filtered_paths = filtered_tree.as_ref().map(PathTree::to_vecs);
                let check_paths = filtered_paths.as_ref().unwrap_or(&paths);
                let check_results = if label == "type"
                    && entry_facts.iter().any(|item| {
                        matches!(item, RelevantItem::ContractFact { property } if property == invariant)
                    })
                    && stable_reference_metadata(self.tcx, self.target.def_id, invariant)
                {
                    vec![(CheckResult::ProvedByRule, String::new()); check_tree.len()]
                } else {
                    self.check_invariant_from_tree(
                        &mut cache,
                        check_tree,
                        checkpoint,
                        invariant,
                        entry_facts,
                    )
                };

                for (path_index, (result, _path_desc)) in check_results.into_iter().enumerate() {
                    let path_description = check_paths
                        .get(path_index)
                        .map(|path| {
                            format!(
                                "{:?}",
                                super::path::caller_blocks(
                                    check_tree,
                                    self.target.def_id,
                                    path.iter().copied(),
                                )
                            )
                        })
                        .unwrap_or_default();
                    results.push(PropertyCheckResult {
                        checkpoint,
                        checkpoint_index: checkpoint.block.as_usize(),
                        path_index,
                        property_index,
                        property: invariant.clone(),
                        diagnostics: Some(format!("vm-{label}-invariant: {result:?}")),
                        result,
                        path_description,
                        callee_name: format!(
                            "{label}-invariant(bb{})",
                            checkpoint.block.as_usize()
                        ),
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
    property
        .target_place()
        .is_some_and(|cp| matches!(cp.base, PlaceBase::Return))
}

fn stable_reference_metadata(tcx: TyCtxt<'_>, def_id: DefId, property: &Property<'_>) -> bool {
    let Some(kind) = property.kind() else {
        return false;
    };
    if !matches!(
        kind,
        PropertyKind::NonNull | PropertyKind::Align | PropertyKind::ValidNum
    ) {
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
            PropertyArg::Expr(expr) => collect_expr(expr, &mut roots),
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
        roots
            .into_iter()
            .next()
            .filter(|local| local.as_usize() > 0)
    } else {
        None
    }
}

fn type_invariant_subject_live(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    tree: &PathTree,
    path: &[usize],
    local: Local,
) -> bool {
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
