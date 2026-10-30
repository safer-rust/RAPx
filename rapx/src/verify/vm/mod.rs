//! Symbolic MIR Virtual Machine.
//!
//! This module replaces the pattern-matching `ForwardVerifier` with a
//! semantic MIR executor.  Instead of deriving ad-hoc `StateFact`s from
//! MIR patterns, the VM executes retained MIR items and directly builds
//! symbolic state (`VmState`) with Z3 terms for every value.

pub(crate) mod alias;
pub(crate) mod alias_hazard;
pub(crate) mod alias_tree;
pub(crate) mod arithmetic;
pub(crate) mod call;
pub(crate) mod container;
pub(crate) mod contracts;
pub(crate) mod contract_eval;
pub(crate) mod display;
pub(crate) mod effects;
pub(crate) mod comparison_simulator;
pub(crate) mod exec;
pub(crate) mod iterator;
pub(crate) mod materialize;
pub(crate) mod memory;
pub(crate) mod method_cache;
pub(crate) mod parameters;
pub(crate) mod query;
pub(crate) mod range;
pub(crate) mod region;
pub(crate) mod rules;
pub(crate) mod state;

use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::Body;
use rustc_hir::def_id::DefId;
use z3::Context;

use crate::verify::slicer::ProofGoal;

pub(crate) use self::state::VmState;

/// Run one sliced path through the symbolic MIR executor.
pub(crate) fn execute_goal<'z3, 'tcx>(
    z3_ctx: &'z3 Context,
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    instance_body: Option<&'tcx Body<'tcx>>,
    goal: ProofGoal<'tcx>,
) -> Vec<VmState<'z3, 'tcx>> {
    VmState::new(z3_ctx, tcx, caller_def_id, instance_body).execute_items(&goal.items)
}
