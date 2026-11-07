//! MIR transfer functions for the symbolic VM.

use rustc_middle::mir::{BasicBlock, Place, Rvalue, Statement, Terminator};

use super::state::{VmState, VmValue};

mod dispatch;
pub(crate) mod rvalue;
pub(crate) mod statement;
pub(crate) mod terminator;

pub(crate) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    dispatch::eval_rvalue(state, place, rvalue)
}

/// Execute a terminator and report whether the selected successor remains possible.
pub(crate) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    terminator: &Terminator<'tcx>,
    switch_succ: Option<BasicBlock>,
) -> bool {
    dispatch::exec_terminator(state, terminator, switch_succ)
}

pub(crate) fn exec_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    statement: &Statement<'tcx>,
) {
    dispatch::exec_statement(state, statement);
}
