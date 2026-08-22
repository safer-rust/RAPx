//! Symbolic MIR Virtual Machine.
//!
//! This module replaces the pattern-matching `ForwardVerifier` with a
//! semantic MIR executor.  Instead of deriving ad-hoc `StateFact`s from
//! MIR patterns, the VM executes retained MIR items and directly builds
//! symbolic state (`VmState`) with Z3 terms for every value.

pub mod alias;
pub mod call;
pub mod display;
pub mod exec;
pub mod memory;
pub mod state;

use rustc_middle::ty::TyCtxt;
use z3::Context;

use crate::verify::slicer::ProofGoal;

use self::state::{UnsupportedReason, VmState};

/// Entry point for symbolic MIR execution.
///
/// Stateless wrapper around a `TyCtxt`; creates `VmState` instances
/// for each path by executing retained MIR items.
pub struct SymbolicVm<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> SymbolicVm<'tcx> {
    /// Create a symbolic VM for the given compiler context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Execute retained MIR items and produce a symbolic VM state.
    ///
    /// The `ctx` parameter provides a shared Z3 context; the resulting
    /// `VmState` borrows it so that a single context can be reused
    /// across property checks.
    pub fn execute<'ctx>(
        &self,
        ctx: &'ctx Context,
        items: &ProofGoal<'tcx>,
    ) -> Result<VmState<'ctx, 'tcx>, UnsupportedReason> {
        let body = self.tcx.optimized_mir(items.checkpoint.caller);
        let mut state = VmState::new(ctx, self.tcx, body, items.checkpoint.caller);
        state.path = Some(items.path.clone());
        state.execute_items(&items.items)?;
        state.propagate_from_checkpoint(items.checkpoint.block);
        Ok(state)
    }
}
