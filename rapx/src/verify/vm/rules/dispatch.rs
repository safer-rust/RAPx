//! Direct MIR dispatch for symbolic execution rules.

use rustc_middle::mir::{
    BasicBlock, Local, NonDivergingIntrinsic, Place, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};

use super::super::state::{VmState, VmValue};
use super::{rvalue, statement, terminator};
use crate::verify::mir_support;

fn mir_variant(rendered: &str) -> &str {
    let name = rendered.split(['(', '{', ' ']).next().unwrap_or("Unknown");
    if name == "asm!" { "InlineAsm" } else { name }
}

pub(super) fn exec_statement<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, stmt: &Statement<'tcx>) {
    let was_unsupported = state.diagnostics.is_unsupported();
    let name = match &stmt.kind {
        StatementKind::Assign(assign) => {
            let (place, value) = &**assign;
            statement::exec_assign(state, place, value);
            "Assign"
        }
        StatementKind::SetDiscriminant {
            place,
            variant_index,
        } => {
            statement::exec_set_discriminant(state, place, *variant_index);
            "SetDiscriminant"
        }
        StatementKind::StorageLive(local) => {
            statement::exec_storage_live(state, *local);
            "StorageLive"
        }
        StatementKind::StorageDead(local) => {
            statement::exec_storage_dead(state, *local);
            "StorageDead"
        }
        StatementKind::Intrinsic(intrinsic)
            if let NonDivergingIntrinsic::Assume(operand) = &**intrinsic =>
        {
            statement::exec_assume(state, operand);
            "Assume"
        }
        StatementKind::Intrinsic(intrinsic)
            if let NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic =>
        {
            statement::exec_copy_nonoverlapping(state, copy);
            "CopyNonOverlapping"
        }
        kind if mir_support::ignored_statement(kind) => "Ignored",
        _ => {
            let rendered = format!("{:?}", stmt.kind);
            state.record_unsupported(&format!(
                "StatementKind::{}: {rendered}",
                mir_variant(&rendered)
            ));
            "Unsupported"
        }
    };
    if state.diagnostics.needs_statement_fallback(was_unsupported) {
        state.record_unsupported(&format!(
            "StatementKind::{name} (model incomplete): {:?}",
            stmt.kind
        ));
    }
    log::trace!("vm statement rule: {name}");
}

pub(super) fn exec_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    term: &Terminator<'tcx>,
    successor: Option<BasicBlock>,
) -> bool {
    let was_unsupported = state.diagnostics.is_unsupported();
    let previous_missing_mir = state.diagnostics.missing_mir_count();
    let name = match &term.kind {
        TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } => {
            let caller_id = state.current_frame.current_def_id;
            if !state.exec_call(func, args, destination.local, caller_id) {
                return false;
            }
            "Call"
        }
        TerminatorKind::TailCall { func, args, .. } => {
            let caller_id = state.current_frame.current_def_id;
            if !state.exec_call(func, args, Local::from_usize(0), caller_id) {
                return false;
            }
            "TailCall"
        }
        TerminatorKind::SwitchInt { discr, targets } => {
            if !terminator::exec_switch_int(state, discr, targets, successor) {
                return false;
            }
            "SwitchInt"
        }
        TerminatorKind::Assert { cond, expected, .. } => {
            terminator::exec_assert(state, cond, *expected);
            "Assert"
        }
        TerminatorKind::Drop { place, .. } => {
            terminator::exec_drop(state, place);
            "Drop"
        }
        kind if mir_support::ignored_terminator(kind) => "Ignored",
        _ => {
            let rendered = format!("{:?}", term.kind);
            state.record_unsupported(&format!(
                "TerminatorKind::{}: {rendered}",
                mir_variant(&rendered)
            ));
            "Unsupported"
        }
    };
    if state
        .diagnostics
        .needs_terminator_fallback(was_unsupported, previous_missing_mir)
    {
        state.record_unsupported(&format!(
            "TerminatorKind::{name} (model incomplete): {:?}",
            term.kind
        ));
    }
    log::trace!("vm terminator rule: {name}");
    true
}

pub(super) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rv: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let was_unsupported = state.diagnostics.is_unsupported();
    #[allow(unreachable_patterns)]
    let (name, value) = match rv {
        Rvalue::Use(operand, ..) => ("Use", rvalue::eval_use(state, place, operand)),
        Rvalue::Ref(_, _, source) => ("Ref", rvalue::eval_ref(state, place, source)),
        Rvalue::RawPtr(_, source) => ("RawPtr", rvalue::eval_raw_ptr(state, place, source)),
        Rvalue::BinaryOp(op, pair) => ("BinaryOp", rvalue::eval_binary_op(state, place, *op, pair)),
        Rvalue::UnaryOp(op, operand) => {
            ("UnaryOp", rvalue::eval_unary_op(state, place, *op, operand))
        }
        Rvalue::Cast(kind, operand, ty) => ("Cast", rvalue::eval_cast(state, *kind, operand, *ty)),
        Rvalue::Aggregate(kind, operands) => (
            "Aggregate",
            rvalue::eval_aggregate(state, place, kind, operands),
        ),
        Rvalue::Discriminant(source) => (
            "Discriminant",
            rvalue::eval_discriminant(state, place, source),
        ),
        #[cfg(not(rapx_ge_99))]
        Rvalue::ShallowInitBox(operand, _) => (
            "ShallowInitBox",
            rvalue::eval_shallow_init_box(state, place, operand),
        ),
        Rvalue::CopyForDeref(source) => (
            "CopyForDeref",
            rvalue::eval_copy_for_deref(state, place, source),
        ),
        Rvalue::Repeat(operand, _) => ("Repeat", rvalue::eval_repeat(state, place, operand)),
        Rvalue::ThreadLocalRef(def_id) => (
            "ThreadLocalRef",
            rvalue::eval_thread_local_ref(state, place, *def_id),
        ),
        #[cfg(not(rapx_ge_95))]
        Rvalue::NullaryOp(op) => ("NullaryOp", rvalue::eval_nullary_op(state, place, op)),
        Rvalue::WrapUnsafeBinder(operand, _) => (
            "WrapUnsafeBinder",
            rvalue::eval_wrap_unsafe_binder(state, place, operand),
        ),
        #[cfg(rapx_rvalue_has_reborrow)]
        Rvalue::Reborrow(_, mutability, source) => (
            "Reborrow",
            rvalue::eval_reborrow(state, place, source, *mutability),
        ),
        _ => {
            let rendered = format!("{rv:?}");
            state.record_unsupported(&format!("Rvalue::{}: {rendered}", mir_variant(&rendered)));
            (
                "Unsupported",
                rvalue::eval_fresh_value(state, place, "unsupported_rvalue"),
            )
        }
    };
    if state.diagnostics.needs_statement_fallback(was_unsupported) {
        state.record_unsupported(&format!("Rvalue::{name} (model incomplete): {rv:?}"));
    }
    log::trace!("vm rvalue rule: {name}");
    value
}
