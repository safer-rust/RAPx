use rustc_middle::mir::{
    BasicBlock, Local, NonDivergingIntrinsic, Place, Rvalue, Statement, StatementKind, Terminator,
    TerminatorKind,
};

use super::super::state::{VmState, VmValue};
use super::{RuleFlow, call, rvalue, statement, terminator};

fn mir_variant(rendered: &str) -> &str {
    let name = rendered.split(['(', '{', ' ']).next().unwrap_or("Unknown");
    if name == "asm!" { "InlineAsm" } else { name }
}

struct RvalueEntry {
    name: &'static str,
    eval: for<'z3, 'tcx> fn(
        &mut VmState<'z3, 'tcx>,
        &Place<'tcx>,
        &Rvalue<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>>,
}

macro_rules! rvalue_registry {
    ($state:ident, $place:ident, $rv:ident;
        $( $(#[$meta:meta])* $handler:ident: $variant:ident $args:tt => $eval:expr, )*
    ) => {
        $(
            $(#[$meta])*
            #[allow(unused_variables)]
            fn $handler<'z3, 'tcx>(
                $state: &mut VmState<'z3, 'tcx>,
                $place: &Place<'tcx>,
                $rv: &Rvalue<'tcx>,
            ) -> Option<VmValue<'z3, 'tcx>> {
                if let Rvalue::$variant $args = $rv {
                    Some($eval)
                } else {
                    None
                }
            }
        )*
        static RVALUE_REGISTRY: &[RvalueEntry] = &[
            $( $(#[$meta])* RvalueEntry { name: stringify!($variant), eval: $handler }, )*
        ];
    };
}

rvalue_registry!(state, place, rv;
    rule_use: Use(operand, ..) => rvalue::eval_use(state, place, operand),
    rule_ref: Ref(_, _, source) => rvalue::eval_ref(state, place, source),
    rule_raw_ptr: RawPtr(_, source) => rvalue::eval_raw_ptr(state, place, source),
    rule_binary_op: BinaryOp(op, pair) => rvalue::eval_binary_op(state, place, *op, pair),
    rule_unary_op: UnaryOp(op, operand) => rvalue::eval_unary_op(state, place, *op, operand),
    rule_cast: Cast(kind, operand, ty) => rvalue::eval_cast(state, *kind, operand, *ty),
    rule_aggregate: Aggregate(kind, operands) => rvalue::eval_aggregate(state, place, kind, operands),
    rule_discriminant: Discriminant(source) => rvalue::eval_discriminant(state, place, source),
    #[cfg(not(rapx_ge_99))]
    rule_shallow_init_box: ShallowInitBox(operand, _) => rvalue::eval_shallow_init_box(state, place, operand),
    rule_copy_for_deref: CopyForDeref(source) => rvalue::eval_copy_for_deref(state, place, source),
    rule_repeat: Repeat(operand, _) => rvalue::eval_repeat(state, place, operand),
    rule_thread_local_ref: ThreadLocalRef(def_id) => rvalue::eval_thread_local_ref(state, place, *def_id),
    #[cfg(not(rapx_ge_95))]
    rule_nullary_op: NullaryOp(op) => rvalue::eval_nullary_op(state, place, op),
    rule_wrap_unsafe_binder: WrapUnsafeBinder(operand, _) => rvalue::eval_wrap_unsafe_binder(state, place, operand),
    #[cfg(rapx_rvalue_has_reborrow)]
    rule_reborrow: Reborrow(_, mutability, source) => rvalue::eval_reborrow(state, place, source, *mutability),
);

fn unsupported_statement<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    stmt: &Statement<'tcx>,
) -> &'static str {
    let rendered = format!("{:?}", stmt.kind);
    state.record_unsupported(&format!(
        "StatementKind::{}: {rendered}",
        mir_variant(&rendered)
    ));
    "Unsupported"
}

struct StatementEntry {
    name: &'static str,
    apply: for<'z3, 'tcx> fn(&mut VmState<'z3, 'tcx>, &Statement<'tcx>) -> bool,
}

macro_rules! statement_registry {
    ($state:ident, $stmt:ident;
        $( $handler:ident: $variant:ident $args:tt => $exec:expr, )*
        ; Intrinsic($intrinsic:ident) {
            $( $inner_handler:ident: $inner_variant:ident($inner_arg:ident) => $inner_exec:expr, )*
        }
        ; NoOp => $noop:ident
    ) => {
        $(
            fn $handler<'z3, 'tcx>($state: &mut VmState<'z3, 'tcx>, $stmt: &Statement<'tcx>) -> bool {
                if let StatementKind::$variant $args = &$stmt.kind {
                    $exec;
                    true
                } else {
                    false
                }
            }
        )*
        $(
            fn $inner_handler<'z3, 'tcx>($state: &mut VmState<'z3, 'tcx>, $stmt: &Statement<'tcx>) -> bool {
                if let StatementKind::Intrinsic($intrinsic) = &$stmt.kind
                    && let NonDivergingIntrinsic::$inner_variant($inner_arg) = &**$intrinsic
                {
                    $inner_exec;
                    true
                } else {
                    false
                }
            }
        )*
        static STATEMENT_REGISTRY: &[StatementEntry] = &[
            $( StatementEntry { name: stringify!($variant), apply: $handler }, )*
            $( StatementEntry { name: stringify!($inner_variant), apply: $inner_handler }, )*
            StatementEntry { name: "NoOp", apply: $noop },
        ];
    };
}

fn noop_statement_rule<'z3, 'tcx>(_state: &mut VmState<'z3, 'tcx>, stmt: &Statement<'tcx>) -> bool {
    matches!(
        stmt.kind,
        StatementKind::FakeRead(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop
            | StatementKind::BackwardIncompatibleDropHint { .. }
    )
}

statement_registry!(state, stmt;
    rule_assign: Assign(assign) => { let (place, value) = &**assign; statement::exec_assign(state, place, value); },
    rule_set_discriminant: SetDiscriminant { place, variant_index } => statement::exec_set_discriminant(state, place, *variant_index),
    rule_storage_live: StorageLive(local) => statement::exec_storage_live(state, *local),
    rule_storage_dead: StorageDead(local) => statement::exec_storage_dead(state, *local),
    ; Intrinsic(intrinsic) {
        rule_assume: Assume(operand) => statement::exec_assume(state, operand),
        rule_copy_nonoverlapping: CopyNonOverlapping(copy) => statement::exec_copy_nonoverlapping(state, copy),
    }
    ; NoOp => noop_statement_rule
);

fn unsupported_terminator<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    term: &Terminator<'tcx>,
) -> &'static str {
    let rendered = format!("{:?}", term.kind);
    state.record_unsupported(&format!(
        "TerminatorKind::{}: {rendered}",
        mir_variant(&rendered)
    ));
    "Unsupported"
}

struct TerminatorEntry {
    name: &'static str,
    apply: for<'z3, 'tcx> fn(
        &mut VmState<'z3, 'tcx>,
        &Terminator<'tcx>,
        Option<BasicBlock>,
    ) -> Option<RuleFlow>,
}

macro_rules! terminator_registry {
    ($state:ident, $term:ident, $successor:ident;
        $( $handler:ident: $variant:ident $args:tt => $exec:expr, )*
    ) => {
        $(
            #[allow(unused_variables)]
            fn $handler<'z3, 'tcx>(
                $state: &mut VmState<'z3, 'tcx>,
                $term: &Terminator<'tcx>,
                $successor: Option<BasicBlock>,
            ) -> Option<RuleFlow> {
                if let TerminatorKind::$variant $args = &$term.kind {
                    Some($exec)
                } else {
                    None
                }
            }
        )*
        static TERMINATOR_REGISTRY: &[TerminatorEntry] = &[
            $( TerminatorEntry { name: stringify!($variant), apply: $handler }, )*
            TerminatorEntry { name: "ControlOnly", apply: control_only_terminator_rule },
        ];
    };
}

fn control_only_terminator_rule<'z3, 'tcx>(
    _state: &mut VmState<'z3, 'tcx>,
    term: &Terminator<'tcx>,
    _successor: Option<BasicBlock>,
) -> Option<RuleFlow> {
    matches!(
        term.kind,
        TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
    )
    .then_some(RuleFlow::Continue)
}

terminator_registry!(state, term, successor;
    rule_call: Call { func, args, destination, .. } => {
        let caller_id = state.current_frame.current_def_id;
        call::exec_call(state, func, args, destination.local, caller_id)
    },
    rule_tail_call: TailCall { func, args, .. } => {
        let caller_id = state.current_frame.current_def_id;
        call::exec_call(state, func, args, Local::from_usize(0), caller_id)
    },
    rule_switch_int: SwitchInt { discr, targets } => terminator::exec_switch_int(state, discr, targets, successor),
    rule_assert: Assert { cond, expected, .. } => {
        terminator::exec_assert(state, cond, *expected);
        RuleFlow::Continue
    },
    rule_drop: Drop { place, .. } => {
        terminator::exec_drop(state, place);
        RuleFlow::Continue
    },
);

pub(super) fn exec_statement<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, stmt: &Statement<'tcx>) {
    let was_unsupported = state.diagnostics.is_unsupported();
    let name = STATEMENT_REGISTRY
        .iter()
        .find(|rule| (rule.apply)(state, stmt))
        .map(|rule| rule.name)
        .unwrap_or_else(|| unsupported_statement(state, stmt));
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
) -> RuleFlow {
    let was_unsupported = state.diagnostics.is_unsupported();
    let previous_missing_mir = state.diagnostics.missing_mir_count();
    let (name, flow) = TERMINATOR_REGISTRY
        .iter()
        .find_map(|rule| (rule.apply)(state, term, successor).map(|flow| (rule.name, flow)))
        .unwrap_or_else(|| (unsupported_terminator(state, term), RuleFlow::Continue));
    if flow == RuleFlow::Pruned {
        return flow;
    }
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
    RuleFlow::Continue
}

pub(super) fn eval_rvalue<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rv: &Rvalue<'tcx>,
) -> VmValue<'z3, 'tcx> {
    let was_unsupported = state.diagnostics.is_unsupported();
    let (name, value) = RVALUE_REGISTRY
        .iter()
        .find_map(|rule| (rule.eval)(state, place, rv).map(|value| (rule.name, value)))
        .unwrap_or_else(|| {
            let rendered = format!("{rv:?}");
            state.record_unsupported(&format!("Rvalue::{}: {rendered}", mir_variant(&rendered)));
            (
                "Unsupported",
                rvalue::eval_fresh_value(state, place, "unsupported_rvalue"),
            )
        });
    if state.diagnostics.needs_statement_fallback(was_unsupported) {
        state.record_unsupported(&format!("Rvalue::{name} (model incomplete): {rv:?}"));
    }
    log::trace!("vm rvalue rule: {name}");
    value
}
