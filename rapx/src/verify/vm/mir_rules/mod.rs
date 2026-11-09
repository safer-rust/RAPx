use rustc_middle::mir::{BasicBlock, Place, Rvalue, Statement, Terminator};

use super::state::{VmState, VmValue};

#[must_use]
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum RuleFlow {
    Continue,
    Pruned,
}

impl RuleFlow {
    pub(crate) fn continues(self) -> bool {
        self == Self::Continue
    }
}

mod call;
mod dispatch;
mod rvalue;
mod statement;
mod terminator;

pub(crate) use terminator::forced_inline_switch_target;

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
) -> RuleFlow {
    dispatch::exec_terminator(state, terminator, switch_succ)
}

pub(crate) fn exec_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    statement: &Statement<'tcx>,
) {
    dispatch::exec_statement(state, statement);
}

pub(crate) fn exec_contract_method_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    statement: &Statement<'tcx>,
) {
    dispatch::exec_statement(state, statement);
    statement::refine_contract_method_const(state, statement);
}
