//! Shared verification engine for the staged verifier pipeline.
//!
//! This module extracts the common backward-visit → forward-visit → SMT-check
//! flow that is shared between unsafe-callsite verification and struct-invariant
//! verification, keeping both pipelines thin and focused on their own
//! path-preparation logic.

use rustc_middle::ty::TyCtxt;

use crate::analysis::path_analysis::PathTree;

use super::{
    contract::Property,
    forward_visit::{ForwardVisitResult, ForwardVisitor},
    helpers::{Callsite, CallsiteLocation},
    path::Path,
    path_refine::{BackwardItem, BackwardVisitor, RelevantMirItems},
    smt_check::{SmtCheckResult, SmtChecker},
};

/// Thin wrapper around the three-stage verification pipeline.
///
/// Each structural check (callsite or invariant) delegates to one of the two
/// public methods; the engine handles visitor bookkeeping internally.
pub struct VerifyEngine<'tcx> {
    backward: BackwardVisitor<'tcx>,
    forward: ForwardVisitor<'tcx>,
    smt: SmtChecker<'tcx>,
}

impl<'tcx> VerifyEngine<'tcx> {
    /// Create an engine for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            backward: BackwardVisitor::new(tcx),
            forward: ForwardVisitor::new(tcx),
            smt: SmtChecker::new(tcx),
        }
    }

    /// Run the full pipeline for one struct-invariant checkpoint check.
    ///
    /// For non-constructor methods, all struct invariants are prepended as
    /// entry `ContractFact` assumptions so the SMT model can assume the
    /// invariant holds at function entry.
    ///
    /// For constructors, `caller_contracts` (from `#[rapx::requires]`
    /// annotations) are used as entry assumptions instead, since the
    /// constructor must establish the invariants from scratch.
    pub fn check_invariant(
        &self,
        def_id: rustc_hir::def_id::DefId,
        checkpoint: CallsiteLocation,
        path: &Path,
        property: &Property<'tcx>,
        invariants: &[Property<'tcx>],
        is_constructor: bool,
        caller_contracts: &[Property<'tcx>],
    ) -> (
        RelevantMirItems<'tcx>,
        ForwardVisitResult<'tcx>,
        SmtCheckResult,
    ) {
        let mut backward = self
            .backward
            .visit_for_checkpoint(def_id, checkpoint, path, property);

        if is_constructor {
            let mut items: Vec<BackwardItem<'tcx>> = caller_contracts
                .iter()
                .filter(|c| !matches!(c.kind, super::contract::PropertyKind::Unknown))
                .map(|c| BackwardItem::ContractFact {
                    property: c.clone(),
                })
                .collect();
            items.extend(backward.items.clone());
            backward.items = items;
        } else {
            let mut items: Vec<BackwardItem<'tcx>> = invariants
                .iter()
                .map(|inv| BackwardItem::ContractFact {
                    property: inv.clone(),
                })
                .collect();
            items.extend(backward.items.clone());
            backward.items = items;
        }

        let forward = self.forward.visit(&backward);
        let smt = self.smt.check_for_checkpoint(def_id, property, &forward);
        (backward, forward, smt)
    }

    /// Run the callsite-check pipeline in bulk using a shared path tree.
    ///
    /// Calls `visit_path_tree` once, then forward + SMT per path.
    pub fn check_callsite_from_tree(
        &self,
        tree: &PathTree,
        target_block: usize,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        caller_contracts: &[Property<'tcx>],
    ) -> Vec<(ForwardVisitResult<'tcx>, SmtCheckResult)> {
        let mut results = Vec::new();
        let backward_items = self
            .backward
            .visit_path_tree(tree, target_block, callsite, property);

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
            let forward = self.forward.visit(&backward);
            let smt = self.smt.check(callsite, property, &forward);
            results.push((forward, smt));
        }

        results
    }
}
