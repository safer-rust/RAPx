//! Shared verification engine for the staged verifier pipeline.
//!
//! This module extracts the common backward-visit → forward-visit → SMT-check
//! flow that is shared between unsafe-callsite verification and struct-invariant
//! verification, keeping both pipelines thin and focused on their own
//! path-preparation logic.

use rustc_middle::ty::TyCtxt;

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

    /// Run the full pipeline for one unsafe-callsite check.
    pub fn check_callsite(
        &self,
        callsite: &Callsite<'tcx>,
        path: &Path,
        property: &Property<'tcx>,
    ) -> (ForwardVisitResult<'tcx>, SmtCheckResult) {
        let backward = self.backward.visit(callsite, path, property);
        let forward = self.forward.visit(&backward);
        let smt = self.smt.check(callsite, property, &forward);
        (forward, smt)
    }

    /// Run the full pipeline for one struct-invariant checkpoint check.
    ///
    /// For non-constructor methods, all struct invariants are prepended as
    /// entry `ContractFact` assumptions so the SMT model can assume the
    /// invariant holds at function entry.
    pub fn check_invariant(
        &self,
        def_id: rustc_hir::def_id::DefId,
        checkpoint: CallsiteLocation,
        path: &Path,
        property: &Property<'tcx>,
        invariants: &[Property<'tcx>],
        is_constructor: bool,
    ) -> (
        RelevantMirItems<'tcx>,
        ForwardVisitResult<'tcx>,
        SmtCheckResult,
    ) {
        let mut backward = self
            .backward
            .visit_for_checkpoint(def_id, checkpoint, path, property);

        if !is_constructor {
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
}
