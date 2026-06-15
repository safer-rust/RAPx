//! Diagnostic formatting for path-refinement types.

use std::fmt::Write;

use rustc_middle::ty::TyCtxt;

use crate::verify::{
    helpers::CallsiteLocation,
    path::{PathStart, PathStep},
};

use super::types::{BackwardItem, ForgetReason, KeepReason, RelevantMirItems};

impl<'tcx> RelevantMirItems<'tcx> {
    /// Render a detailed, path-ordered diagnostic for a callsite visit.
    pub fn describe(
        &self,
        tcx: TyCtxt<'tcx>,
        callsite: &crate::verify::helpers::Callsite<'tcx>,
        path_index: usize,
    ) -> String {
        let header = format!(
            "      callsite: {} at bb{}",
            callsite.callee_name(tcx),
            callsite.block.as_usize()
        );
        self.describe_common(tcx, path_index, &header)
    }

    /// Render diagnostics for a struct invariant checkpoint (no callee name).
    pub fn describe_for_checkpoint(
        &self,
        tcx: TyCtxt<'tcx>,
        checkpoint: CallsiteLocation,
        path_index: usize,
    ) -> String {
        let header = format!("      checkpoint: bb{}", checkpoint.block.as_usize());
        self.describe_common(tcx, path_index, &header)
    }

    fn describe_common(&self, tcx: TyCtxt<'tcx>, path_index: usize, header: &str) -> String {
        let mut out = String::new();
        let caller = self.callsite.caller;
        let body = tcx.optimized_mir(caller);

        let _ = writeln!(out, "{header}");
        let _ = writeln!(
            out,
            "      property: kind={:?}, args={:?}",
            self.property.kind, self.property.args
        );
        let _ = writeln!(out, "      path {path_index}:");
        let _ = writeln!(
            out,
            "        |_ kind: {}",
            describe_path_start(&self.path.start)
        );
        let _ = writeln!(out, "        |_ steps: {}", self.path.describe_body());
        let _ = writeln!(
            out,
            "        |_ roots: {} place(s), {} local(s)",
            self.roots.place_count(),
            self.roots.local_count()
        );
        let _ = writeln!(out, "      relevant MIR items:");

        let mut has_relevant_item = false;
        for step in self.path.steps.iter() {
            let step_items: Vec<_> = self
                .items
                .iter()
                .filter(|item| item_belongs_to_step(item, step))
                .collect();
            if step_items.is_empty() {
                continue;
            }
            has_relevant_item = true;

            let _ = writeln!(out, "        |_ {}", describe_path_step(step));
            for item in step_items {
                let _ = writeln!(out, "        |  |_ {}", describe_backward_item(item, body));
            }
        }
        if !has_relevant_item {
            let _ = writeln!(out, "        |_ <none>");
        }

        let forgets: Vec<_> = self
            .items
            .iter()
            .filter_map(|item| match item {
                BackwardItem::Forget { reason } => Some(reason),
                _ => None,
            })
            .collect();
        if !forgets.is_empty() {
            let _ = writeln!(out, "      precision loss:");
            for reason in forgets {
                let _ = writeln!(out, "        |_ {}", describe_forget_reason(reason));
            }
        }

        out
    }
}

// ── diagnostic helpers ──────────────────────────────────────────────────

fn item_belongs_to_step(item: &BackwardItem<'_>, step: &PathStep) -> bool {
    match (item, step) {
        (BackwardItem::Statement { block, .. }, PathStep::Block(step_block)) => block == step_block,
        (BackwardItem::Terminator { block, kind }, PathStep::Block(step_block)) => {
            block == step_block && *kind != KeepReason::Callsite
        }
        (BackwardItem::Terminator { block, kind }, PathStep::Callsite(location)) => {
            *kind == KeepReason::Callsite && *block == location.block
        }

        (
            BackwardItem::PathStep {
                step: item_step, ..
            },
            step,
        ) => same_path_step(item_step, step),
        _ => false,
    }
}

fn same_path_step(lhs: &PathStep, rhs: &PathStep) -> bool {
    match (lhs, rhs) {
        (PathStep::Block(lhs), PathStep::Block(rhs)) => lhs == rhs,
        (PathStep::Callsite(lhs), PathStep::Callsite(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn describe_path_start(start: &PathStart) -> String {
    match start {
        PathStart::FunctionEntry => "entry".to_string(),
    }
}

fn describe_path_step(step: &PathStep) -> String {
    match step {
        PathStep::Block(block) => format!("bb{}", block.as_usize()),
        PathStep::Callsite(location) => format!("callsite(bb{})", location.block.as_usize()),
    }
}

fn describe_backward_item(item: &BackwardItem<'_>, body: &rustc_middle::mir::Body<'_>) -> String {
    match item {
        BackwardItem::Statement {
            block,
            statement_index,
            kind,
            ..
        } => {
            let statement = &body.basic_blocks[*block].statements[*statement_index];
            format!("stmt#{} [{:?}] {:?}", statement_index, kind, statement.kind)
        }
        BackwardItem::Terminator { block, kind } => {
            let terminator = body.basic_blocks[*block].terminator();
            format!("terminator [{:?}] {:?}", kind, terminator.kind)
        }
        BackwardItem::PathStep { kind, .. } => format!("path-step {:?}", kind),
        BackwardItem::ContractFact { property } => {
            format!(
                "contract kind={:?}, args={:?}",
                property.kind, property.args
            )
        }
        BackwardItem::Forget { reason } => format!("forget {:?}", reason),
    }
}

fn describe_forget_reason(reason: &ForgetReason) -> &'static str {
    match reason {
        ForgetReason::UnknownCall => {
            "UnknownCall: a retained call may affect relevant state and has no summary yet"
        }
        ForgetReason::SccWithoutSummary => {
            "SccWithoutSummary: a relevant SCC exit has no verified SCC summary yet"
        }
        ForgetReason::MayAliasWrite => {
            "MayAliasWrite: a write may alias relevant state and is not modeled precisely yet"
        }
        ForgetReason::UnsupportedEffect => {
            "UnsupportedEffect: a relevant MIR effect is not modeled precisely yet"
        }
    }
}
