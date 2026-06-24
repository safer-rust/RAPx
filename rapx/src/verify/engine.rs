//! Shared verification engine for the staged verifier pipeline.
//!
//! This module extracts the common backward-visit → forward-visit → SMT-check
//! flow that is shared between unsafe-checkpoint verification and struct-invariant
//! verification, keeping both pipelines thin and focused on their own
//! path-preparation logic.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::path_analysis::PathTree;

use super::{
    contract::Property,
    helpers::{Checkpoint, CheckpointLocation},
    report::CheckResult,
    slicer::{BackwardItem, BackwardSlicer},
    smt_check::{SmtCheckResult, SmtChecker},
    verifier::{ForwardVerifier, ForwardVisitResult},
};

/// Result of checking one invariant along one reachability path.
pub struct InvariantCheckResult {
    /// Whether the invariant was proved, violated, or undecided.
    pub result: CheckResult,
    /// Backward slicing summary (MIR items kept along this path).
    pub slicing_diag: String,
    /// Combined forward verification and SMT check summary.
    pub verification_diag: String,
}

/// Thin wrapper around the three-stage verification pipeline.
///
/// Each structural check (checkpoint or invariant) delegates to one of the two
/// public methods; the engine handles visitor bookkeeping internally.
pub struct VerifyEngine<'tcx> {
    slicer: BackwardSlicer<'tcx>,
    verifier: ForwardVerifier<'tcx>,
    checker: SmtChecker<'tcx>,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Create an engine for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            slicer: BackwardSlicer::new(tcx),
            verifier: ForwardVerifier::new(tcx),
            checker: SmtChecker::new(tcx),
        }
    }

    /// Run the invariant-check pipeline in bulk using a per-checkpoint path tree.
    ///
    /// Calls `visit_path_tree_for_checkpoint` once, then forward + SMT per
    /// path.  The tree already contains only paths reaching `checkpoint`;
    /// common prefixes are shared to avoid redundant backward analysis.
    pub fn check_invariant_from_tree(
        &self,
        def_id: DefId,
        tree: &PathTree,
        checkpoint: CheckpointLocation,
        invariant: &Property<'tcx>,
        entry_facts: &[BackwardItem<'tcx>],
    ) -> Vec<InvariantCheckResult> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self.slicer.visit_path_tree_for_checkpoint(
            tree,
            target_block,
            def_id,
            checkpoint,
            invariant,
        );

        for mut backward in backward_items {
            if !entry_facts.is_empty() {
                let mut items: Vec<BackwardItem<'tcx>> = entry_facts.to_vec();
                items.extend(backward.items.clone());
                backward.items = items;
            }
            let forward = self.verifier.visit(&backward);
            let smt = self
                .checker
                .check_for_checkpoint(def_id, invariant, &forward);

            let tcx = self.slicer.tcx();
            let slicing_diag = backward.describe_for_checkpoint(tcx, checkpoint, 0);
            let verification_diag = format!("{}\n{}", forward.describe(), smt.describe());

            results.push(InvariantCheckResult {
                result: smt.result,
                slicing_diag,
                verification_diag,
            });
        }

        results
    }

    /// Run the checkpoint-check pipeline in bulk using a per-checkpoint path tree.
    ///
    /// Calls `visit_path_tree` once, then forward + SMT per path.
    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<(ForwardVisitResult<'tcx>, SmtCheckResult)> {
        let target_block = checkpoint.block.as_usize();
        let mut results = Vec::new();
        let backward_items = self
            .slicer
            .visit_path_tree(tree, target_block, checkpoint, property);

        for mut backward in backward_items {
            if !caller_contracts.is_empty() {
                let mut items: Vec<BackwardItem<'tcx>> = caller_contracts
                    .iter()
                    .filter(|c| !matches!(c.kind, super::contract::PropertyKind::Unknown))
                    .map(|c| BackwardItem::ContractFact {
                        property: c.clone(),
                    })
                    .collect();
                items.extend(backward.items.clone());
                backward.items = items;
            }
            let forward = self.verifier.visit(&backward);
            let smt = self.checker.check(checkpoint, property, &forward);
            results.push((forward, smt));
        }

        results
    }
}
