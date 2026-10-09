//! Symbolic MIR Virtual Machine.
//!
//! This module replaces the pattern-matching `ForwardVerifier` with a
//! semantic MIR executor.  Instead of deriving ad-hoc `StateFact`s from
//! MIR patterns, the VM executes retained MIR items and directly builds
//! symbolic state (`VmState`) with Z3 terms for every value.

pub(crate) mod alias;
pub(crate) mod alias_hazard;
pub(crate) mod alias_tree;
pub(crate) mod call;
pub(crate) mod display;
pub(crate) mod exec;
pub(crate) mod memory;
pub(crate) mod region;
pub(crate) mod state;

use rustc_middle::ty::TyCtxt;
use z3::Context;

use crate::verify::slicer::ProofGoal;

pub(crate) use self::state::VmState;

/// Entry point for symbolic MIR execution.
///
/// Stateless: the inputs to a run (the Z3 context, compiler type context, and
/// the sliced program) are passed to [`run`], so this struct carries no state
/// of its own.
pub(crate) struct SymbolicVm;

impl SymbolicVm {
    /// Create a symbolic VM.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Run the sliced program `goal` (the path and its retained MIR items) and
    /// produce the resulting symbolic state.
    ///
    /// The Z3 context is borrowed (not owned) so a single context can be reused
    /// across property checks; `run` is a pure `input -> state` mapping — the
    /// program to execute (`goal`) is consumed here and is never stored in the
    /// returned [`VmState`].
    pub(crate) fn run<'z3, 'tcx>(
        &self,
        z3_ctx: &'z3 Context,
        tcx: TyCtxt<'tcx>,
        goal: ProofGoal<'tcx>,
    ) -> VmState<'z3, 'tcx> {
        let mut state = VmState::new(z3_ctx, tcx, goal.path.target.caller);
        state.execute_items(&goal.items);
        state
    }
}
