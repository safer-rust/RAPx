//! Backward path visitor for the staged verifier.
//!
//! This module walks a finite path backward from an unsafe callsite and keeps
//! only MIR statements, terminators, and path steps that can affect the required
//! property. The def-use layer (place tracking, statement/terminator dissection)
//! lives in [`super::def_use`]; this module focuses on the path-level control
//! flow decisions: calls, SCC exits, and path-condition branches.

use std::fmt::Write;

use rustc_middle::mir::{BasicBlock, Operand, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::Spanned;

use super::{
    call_summary,
    def_use::{
        bind_callsite_roots, call_args_uses, call_args_uses_at, operand_uses,
        statement_use_def, terminator_use_def, RelevantPlaces,
    },
    helpers::{Callsite, CallsiteLocation},
    path::{Path, PathStep},
};

/// Entry point for backward path visiting.
pub struct BackwardVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> BackwardVisitor<'tcx> {
    /// Create a backward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Return the compiler type context owned by this visitor.
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    /// Build the initial relevant-MIR item set for a path and property.
    pub fn start_visit(
        &self,
        callsite: CallsiteLocation,
        path: &Path,
        property: &super::contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        RelevantMirItems {
            callsite,
            property: property.clone(),
            path: path.clone(),
            items: Vec::new(),
            roots: RelevantPlaces::from_property(property),
        }
    }

    /// Visit one `(callsite, path, property)` item backward.
    pub fn visit(
        &self,
        callsite: &Callsite<'tcx>,
        path: &Path,
        property: &super::contract::Property<'tcx>,
    ) -> RelevantMirItems<'tcx> {
        let mut visit = self.start_visit(callsite.location(), path, property);
        bind_callsite_roots(&mut visit.roots, callsite);

        let mut relevant = visit.roots.clone();
        let mut items = Vec::new();
        let body = self.tcx.optimized_mir(callsite.caller);

        for step in path.steps.iter().rev() {
            self.visit_path_step(step, callsite, &body, &mut relevant, &mut items);
        }

        for step in path.entry_prefix.iter().rev() {
            self.visit_path_step(step, callsite, &body, &mut relevant, &mut items);
        }

        items.reverse();
        visit.items = items;
        visit
    }

    /// Visit one path step against the current relevance frontier.
    fn visit_path_step(
        &self,
        step: &PathStep,
        callsite: &Callsite<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        match step {
            PathStep::Callsite(location) => {
                if *location != callsite.location() {
                    return;
                }
                items.push(BackwardItem::Terminator {
                    block: location.block,
                    kind: KeepReason::Callsite,
                });
            }
            PathStep::Block(block) => {
                let block_data = &body.basic_blocks[*block];
                if *block != callsite.block {
                    self.visit_terminator(*block, block_data.terminator(), relevant, items);
                }
                for (statement_index, statement) in block_data.statements.iter().enumerate().rev() {
                    self.visit_statement(*block, statement_index, statement, relevant, items);
                }
            }
            PathStep::SccExit { .. } => {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::SccWithoutSummary,
                });
                items.push(BackwardItem::PathStep {
                    step: step.clone(),
                    kind: KeepReason::LoopExit,
                });
            }
        }
    }

    /// Visit one MIR statement against the current relevance frontier.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        statement: &rustc_middle::mir::Statement<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        let use_def = statement_use_def(statement);
        if use_def.defs.intersects(relevant) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: statement_keep_reason(statement),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if statement_invalidates_relevant(statement, relevant) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::Invalidation,
            });
        } else if use_def.uses.intersects(relevant) && statement_can_refine(statement) {
            items.push(BackwardItem::Statement {
                block,
                statement_index,
                kind: KeepReason::RuntimeCheck,
            });
        }
    }

    /// Visit one MIR terminator against the current relevance frontier.
    fn visit_terminator(
        &self,
        block: BasicBlock,
        terminator: &rustc_middle::mir::Terminator<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &terminator.kind
        {
            self.visit_call_terminator(block, func, args, destination, relevant, items);
            return;
        }

        let use_def = terminator_use_def(terminator);
        if terminator_is_path_condition(terminator) {
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::PathCondition,
            });
            relevant.extend(use_def.uses.clone());
            return;
        }

        if use_def.defs.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_definition_reason(terminator),
            });
            relevant.remove_all(&use_def.defs);
            relevant.extend(use_def.uses);
            return;
        }

        if use_def.uses.intersects(relevant) {
            if terminator_may_havoc(terminator) {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: terminator_use_reason(terminator),
            });
        }
    }

    /// Visit a retained/intermediate call using an interprocedural dependency summary.
    fn visit_call_terminator(
        &self,
        block: BasicBlock,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: &rustc_middle::mir::Place<'tcx>,
        relevant: &mut RelevantPlaces,
        items: &mut Vec<BackwardItem<'tcx>>,
    ) {
        let mut defs = RelevantPlaces::new();
        defs.insert_mir_place(destination);
        let arg_uses = call_args_uses(args);
        let summary = call_summary::dependency_summary(self.tcx, func, args.len());

        if defs.intersects(relevant) {
            if summary.unsupported {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: if summary.unsupported {
                    KeepReason::UnknownEffect
                } else {
                    KeepReason::PointerFlow
                },
            });
            relevant.remove_all(&defs);
            relevant.extend(call_args_uses_at(args, &summary.return_depends_on_args));
            return;
        }

        let relevant_written_arg = summary.may_write_args.iter().any(|index| {
            args.get(*index)
                .is_some_and(|arg| operand_uses(&arg.node).intersects(relevant))
        });
        if relevant_written_arg || (summary.unsupported && arg_uses.intersects(relevant)) {
            if summary.unsupported {
                items.push(BackwardItem::Forget {
                    reason: ForgetReason::UnknownCall,
                });
            }
            items.push(BackwardItem::Terminator {
                block,
                kind: KeepReason::UnknownEffect,
            });
        }
    }
}

/// MIR items relevant to one `(callsite, path, property)` item.
#[derive(Clone, Debug)]
pub struct RelevantMirItems<'tcx> {
    /// Unsafe callsite whose obligation is being checked.
    pub callsite: CallsiteLocation,
    /// Required property that determines the relevance roots.
    pub property: super::contract::Property<'tcx>,
    /// Path being visited.
    pub path: Path,
    /// Items kept from the path.
    pub items: Vec<BackwardItem<'tcx>>,
    /// Initial roots extracted from the property.
    pub roots: RelevantPlaces,
}

impl<'tcx> RelevantMirItems<'tcx> {
    /// Append one kept item to the visited path.
    pub fn push(&mut self, item: BackwardItem<'tcx>) {
        self.items.push(item);
    }

    /// Return true when no MIR/path item has been kept yet.
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Render a detailed, path-ordered diagnostic for the relevant MIR items.
    pub fn describe(
        &self,
        tcx: TyCtxt<'tcx>,
        callsite: &Callsite<'tcx>,
        path_index: usize,
    ) -> String {
        let mut out = String::new();
        let body = tcx.optimized_mir(self.callsite.caller);
        let _ = writeln!(
            out,
            "      callsite: {} at bb{}",
            callsite.callee_name(tcx),
            callsite.block.as_usize()
        );
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
        if self.path.entry_prefix.is_empty() {
            let _ = writeln!(out, "        |_ steps: {}", self.path.describe_body());
        } else {
            let _ = writeln!(
                out,
                "        |_ entry prefix: {}",
                self.path.describe_entry_prefix()
            );
            let _ = writeln!(out, "        |_ loop body: {}", self.path.describe_body());
        }
        let _ = writeln!(
            out,
            "        |_ roots: {} place(s), {} local(s)",
            self.roots.place_count(),
            self.roots.local_count()
        );
        let _ = writeln!(out, "      relevant MIR items:");

        let mut has_relevant_item = false;
        for step in self.path.entry_prefix.iter().chain(self.path.steps.iter()) {
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

/// One item kept while walking a path backward.
#[derive(Clone, Debug)]
pub enum BackwardItem<'tcx> {
    /// A MIR statement retained from a basic block.
    Statement {
        block: BasicBlock,
        statement_index: usize,
        kind: KeepReason,
    },
    /// A MIR terminator retained from a basic block.
    Terminator { block: BasicBlock, kind: KeepReason },
    /// A path-level step retained as structural context.
    PathStep { step: PathStep, kind: KeepReason },
    /// A contract fact retained as a visit input.
    ContractFact { property: super::contract::Property<'tcx> },
    /// A conservative loss of precision for relevant state.
    Forget { reason: ForgetReason },
}

/// Why a retained item is relevant.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum KeepReason {
    /// The item defines a relevant place.
    Definition,
    /// The item contributes a branch/path condition.
    PathCondition,
    /// The item contributes pointer provenance or pointer arithmetic.
    PointerFlow,
    /// The item refines state through a runtime check.
    RuntimeCheck,
    /// The item is the unsafe callsite being checked.
    Callsite,
    /// The item represents a loop summary or loop exit.
    LoopExit,
    /// The item may invalidate a relevant fact.
    Invalidation,
    /// The item may affect relevant state but is not modeled precisely yet.
    UnknownEffect,
}

/// Reason for conservatively forgetting relevant state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ForgetReason {
    /// A call may modify relevant state but has no summary yet.
    UnknownCall,
    /// An SCC region may modify relevant state but has no summary yet.
    SccWithoutSummary,
    /// A write may alias relevant state.
    MayAliasWrite,
    /// A relevant statement or terminator is not supported yet.
    UnsupportedEffect,
}

// ── classification helpers (kept here; use only backward_visit types) ────

fn statement_keep_reason(statement: &rustc_middle::mir::Statement<'_>) -> KeepReason {
    match &statement.kind {
        StatementKind::Assign(box (_, rvalue)) => match rvalue {
            rustc_middle::mir::Rvalue::Ref(_, _, _)
            | rustc_middle::mir::Rvalue::RawPtr(_, _)
            | rustc_middle::mir::Rvalue::Cast(_, _, _)
            | rustc_middle::mir::Rvalue::CopyForDeref(_)
            | rustc_middle::mir::Rvalue::BinaryOp(_, _) => KeepReason::PointerFlow,
            _ => KeepReason::Definition,
        },
        StatementKind::StorageDead(_) => KeepReason::Invalidation,
        _ => KeepReason::Definition,
    }
}

fn statement_can_refine(statement: &rustc_middle::mir::Statement<'_>) -> bool {
    matches!(
        &statement.kind,
        StatementKind::Assign(box (
            _,
            rustc_middle::mir::Rvalue::BinaryOp(_, _)
                | rustc_middle::mir::Rvalue::UnaryOp(_, _)
                | rustc_middle::mir::Rvalue::Cast(_, _, _),
        ))
    )
}

fn statement_invalidates_relevant(
    statement: &rustc_middle::mir::Statement<'_>,
    relevant: &RelevantPlaces,
) -> bool {
    match &statement.kind {
        StatementKind::StorageDead(local) => relevant.locals.contains(local),
        _ => false,
    }
}

fn terminator_is_path_condition(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(
        terminator.kind,
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. }
    )
}

fn terminator_definition_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::Definition,
    }
}

fn terminator_use_reason(terminator: &rustc_middle::mir::Terminator<'_>) -> KeepReason {
    match terminator.kind {
        TerminatorKind::SwitchInt { .. } | TerminatorKind::Assert { .. } => {
            KeepReason::PathCondition
        }
        TerminatorKind::Drop { .. } => KeepReason::Invalidation,
        TerminatorKind::Call { .. } => KeepReason::UnknownEffect,
        _ => KeepReason::UnknownEffect,
    }
}

fn terminator_may_havoc(terminator: &rustc_middle::mir::Terminator<'_>) -> bool {
    matches!(terminator.kind, TerminatorKind::Call { .. })
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
        (
            PathStep::SccExit {
                representative: lhs_representative,
                from: lhs_from,
                to: lhs_to,
            },
            PathStep::SccExit {
                representative: rhs_representative,
                from: rhs_from,
                to: rhs_to,
            },
        ) => lhs_representative == rhs_representative && lhs_from == rhs_from && lhs_to == rhs_to,
        (PathStep::Callsite(lhs), PathStep::Callsite(rhs)) => lhs == rhs,
        _ => false,
    }
}

fn describe_path_start(start: &super::path::PathStart) -> String {
    match start {
        super::path::PathStart::FunctionEntry => "entry".to_string(),
        super::path::PathStart::SccRepresentative { representative } => {
            format!("scc-representative(bb{})", representative.as_usize())
        }
    }
}

fn describe_path_step(step: &PathStep) -> String {
    match step {
        PathStep::Block(block) => format!("bb{}", block.as_usize()),
        PathStep::SccExit {
            representative,
            from,
            to,
        } => format!(
            "SccRegion(bb{}).exit(bb{} -> bb{})",
            representative.as_usize(),
            from.as_usize(),
            to.as_usize()
        ),
        PathStep::Callsite(location) => format!("callsite(bb{})", location.block.as_usize()),
    }
}

fn describe_backward_item(
    item: &BackwardItem<'_>,
    body: &rustc_middle::mir::Body<'_>,
) -> String {
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
