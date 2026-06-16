//! Forward visitor for relevant MIR items.
//!
//! This module consumes the MIR items produced by `backward_visit` and visits
//! them in path order.  The current implementation is a skeleton: it records
//! simple value/fact summaries and leaves unsupported MIR effects as notes so
//! later property checkers can be added incrementally.

use std::collections::HashSet;

use crate::compat::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Body, Local, Operand, Place, Rvalue, Statement,
        StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use crate::compat::Spanned;

use super::{
    call_summary::{self, CallEffect, CallEffectSummary},
    contract::Property,
    def_use::{PlaceBaseKey, PlaceKey},
    helpers::CallsiteLocation,
    path::{Path, PathStep},
    path_refine::{BackwardItem, ForgetReason, KeepReason, RelevantMirItems},
};

/// Visits relevant MIR items forward and builds an abstract state.
pub struct ForwardVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> ForwardVisitor<'tcx> {
    /// Create a forward visitor over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Visit relevant MIR items in path order and produce an abstract state.
    pub fn visit(&self, items: &RelevantMirItems<'tcx>) -> ForwardVisitResult<'tcx> {
        let mut result =
            ForwardVisitResult::new(items.callsite, items.property.clone(), items.path.clone());
        let body = self.tcx.optimized_mir(items.callsite.caller);

        for item in &items.items {
            match item {
                BackwardItem::Statement {
                    block,
                    statement_index,
                    kind,
                } => {
                    let statement = &body.basic_blocks[*block].statements[*statement_index];
                    self.visit_statement(
                        *block,
                        *statement_index,
                        *kind,
                        statement,
                        body,
                        &mut result,
                    );
                }
                BackwardItem::Terminator { block, kind } => {
                    let terminator = body.basic_blocks[*block].terminator();
                    self.visit_terminator(*block, *kind, terminator, &mut result);
                }
                BackwardItem::PathStep { step, kind } => {
                    result.steps.push(ForwardStep::PathStep {
                        step: step.clone(),
                        reason: *kind,
                    });
                }
                BackwardItem::ContractFact { property } => {
                    result.facts.push(StateFact::Contract(property.clone()));
                }
                BackwardItem::Forget { reason } => {
                    result.forgets.push(reason.clone());
                }
            }
        }

        result
    }

    /// Visit one retained MIR statement.
    fn visit_statement(
        &self,
        block: BasicBlock,
        statement_index: usize,
        reason: KeepReason,
        statement: &Statement<'tcx>,
        body: &Body<'tcx>,
        result: &mut ForwardVisitResult<'tcx>,
    ) {
        result.steps.push(ForwardStep::Statement {
            block,
            statement_index,
            reason,
        });

        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                let value = self.value_from_rvalue(rvalue);
                result.values.insert(place.local, value);
                self.record_rvalue_facts(place, rvalue, body, result);
            }
            StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::StorageLive(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Intrinsic(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {}
            #[cfg(not(rapx_rustc_ge_198))]
            StatementKind::Retag(..) => {}
            StatementKind::StorageDead(local) => {
                result.values.remove(local);
                result.facts.push(StateFact::LocalDead(*local));
            }
            _ => result.notes.push(format!(
                "unsupported statement at bb{}#{statement_index}",
                block.as_usize()
            )),
        }
    }

    /// Visit one retained MIR terminator.
    fn visit_terminator(
        &self,
        block: BasicBlock,
        reason: KeepReason,
        terminator: &Terminator<'tcx>,
        result: &mut ForwardVisitResult<'tcx>,
    ) {
        result.steps.push(ForwardStep::Terminator { block, reason });

        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let arg_values = args
                    .iter()
                    .map(|arg| value_from_operand(&arg.node))
                    .collect();
                let effect_summary = call_summary::effect_summary(
                    self.tcx,
                    result.callsite.caller,
                    func,
                    destination.local,
                );
                let call = CallSummary {
                    destination: destination.local,
                    func: call_summary::call_name(self.tcx, func),
                    arg_count: args.len(),
                    args: arg_values,
                    effects: effect_summary.effects.clone(),
                    unsupported: effect_summary.unsupported,
                };
                result
                    .values
                    .insert(destination.local, AbstractValue::CallResult(call.clone()));
                result.facts.push(StateFact::Call(call));
                self.apply_call_effects(
                    &effect_summary,
                    args,
                    reason == KeepReason::Callsite,
                    result,
                );
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                if let Some(equals) = chosen_switch_value(&result.path, block, terminator) {
                    let value = value_from_operand(discr);
                    result.facts.push(StateFact::BranchEq {
                        value: value.clone(),
                        equals,
                    });
                    if let Some((place, align)) = align_guard_value(&value, equals, result) {
                        result.facts.push(StateFact::KnownAligned {
                            place,
                            align,
                            ty_name: format!("{align}-aligned"),
                            reason: format!("{align}-byte alignment guard on path"),
                        });
                    }
                } else {
                    result
                        .facts
                        .push(StateFact::PathCondition(format!("{discr:?}")));
                }
            }
            TerminatorKind::Assert { cond, expected, .. } => {
                result.facts.push(StateFact::BranchEq {
                    value: value_from_operand(cond),
                    equals: u128::from(*expected),
                });
            }
            TerminatorKind::Drop { place, .. } => {
                result
                    .facts
                    .push(StateFact::Drop(PlaceKey::from_mir_place(place)));
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::TailCall { .. } => {}
        }
    }

    /// Build an abstract value for a MIR rvalue.
    fn value_from_rvalue(&self, rvalue: &Rvalue<'tcx>) -> AbstractValue<'tcx> {
        match rvalue {
            Rvalue::Use(operand, ..) => value_from_operand(operand),
            Rvalue::Repeat(operand, _) => {
                AbstractValue::Repeat(Box::new(value_from_operand(operand)))
            }
            Rvalue::Ref(_, _, place) => AbstractValue::Ref(PlaceKey::from_mir_place(place)),
            Rvalue::RawPtr(_, place) => AbstractValue::RawPtr(PlaceKey::from_mir_place(place)),
            Rvalue::ThreadLocalRef(def_id) => AbstractValue::ThreadLocal(format!("{def_id:?}")),
            Rvalue::Cast(_, operand, ty) => {
                AbstractValue::Cast(Box::new(value_from_operand(operand)), *ty)
            }
            Rvalue::BinaryOp(op, pair) => {
                let (lhs, rhs) = &**pair;
                AbstractValue::Binary(
                    *op,
                    Box::new(value_from_operand(lhs)),
                    Box::new(value_from_operand(rhs)),
                )
            },
            #[cfg(all(rapx_rustc_ge_193, not(rapx_rustc_ge_196)))]
            Rvalue::NullaryOp(op) => AbstractValue::Nullary(format!("{op:?}")),
            #[cfg(all(not(rapx_rustc_ge_193), not(rapx_rustc_ge_196)))]
            Rvalue::NullaryOp(op, _) => AbstractValue::Nullary(format!("{op:?}")),
            Rvalue::UnaryOp(op, operand) => {
                AbstractValue::Unary(*op, Box::new(value_from_operand(operand)))
            }
            Rvalue::Discriminant(place) => {
                AbstractValue::Discriminant(PlaceKey::from_mir_place(place))
            }
            Rvalue::Aggregate(kind, operands) => {
                AbstractValue::Aggregate(aggregate_name(kind), operands.len())
            }
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(operand, ty) => {
                AbstractValue::ShallowInitBox(Box::new(value_from_operand(operand)), *ty)
            }
            Rvalue::CopyForDeref(place) => AbstractValue::Place(PlaceKey::from_mir_place(place)),
            _ => AbstractValue::Unknown(format!("{rvalue:?}")),
        }
    }

    /// Record initial facts directly implied by selected rvalues.
    fn record_rvalue_facts(
        &self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        body: &Body<'tcx>,
        result: &mut ForwardVisitResult<'tcx>,
    ) {
        let target = PlaceKey::from_mir_place(place);
        match rvalue {
            Rvalue::Ref(_, _, source) | Rvalue::RawPtr(_, source) => {
                let source = PlaceKey::from_mir_place(source);
                result.facts.push(StateFact::PointsTo {
                    pointer: target,
                    source,
                });
            }
            Rvalue::Aggregate(kind, operands) => {
                let is_decomposable = matches!(
                    kind.as_ref(),
                    AggregateKind::Adt(..) | AggregateKind::Tuple
                );
                if !is_decomposable {
                    return;
                }
                for (field_index, operand) in operands.iter().enumerate() {
                    let mut field_place = target.clone();
                    field_place.fields.push(field_index);
                    let source_val = value_from_operand(operand);
                    let op_ty = operand.ty(&body.local_decls, self.tcx);
                    result.facts.push(StateFact::Cast {
                        target: field_place,
                        source: source_val,
                        ty: op_ty,
                    });
                }
            }
            Rvalue::Cast(_, operand, ty) => {
                let source_val = value_from_operand(operand);
                result.facts.push(StateFact::Cast {
                    target: target.clone(),
                    source: source_val.clone(),
                    ty: *ty,
                });
                if let Some(align) = known_alignment_of(&source_val, result) {
                    result.facts.push(StateFact::KnownAligned {
                        place: target,
                        align,
                        ty_name: format!("cast-{align}"),
                        reason: format!("cast preserves {align}-byte alignment"),
                    });
                }
            }
            #[cfg(not(rapx_rustc_ge_198))]
            Rvalue::Use(operand) => {
                let source_place = match operand {
                    Operand::Copy(place) | Operand::Move(place) => Some(place),
                    _ => None,
                };
                if let Some(source_place) = source_place {
                    let has_deref = source_place
                        .projection
                        .iter()
                        .any(|p| matches!(p, rustc_middle::mir::ProjectionElem::Deref));
                    if !has_deref {
                        return;
                    }
                    let source_key = PlaceKey::from_mir_place(source_place);
                    let op_ty = operand.ty(&body.local_decls, self.tcx);
                    result.facts.push(StateFact::Cast {
                        target: target.clone(),
                        source: AbstractValue::Place(source_key),
                        ty: op_ty,
                    });
                }
            }
            #[cfg(rapx_rustc_ge_198)]
            Rvalue::Use(operand, _retag) => {
                let source_place = match operand {
                    Operand::Copy(place) | Operand::Move(place) => Some(place),
                    _ => None,
                };
                if let Some(source_place) = source_place {
                    let has_deref = source_place
                        .projection
                        .iter()
                        .any(|p| matches!(p, rustc_middle::mir::ProjectionElem::Deref));
                    if !has_deref {
                        return;
                    }
                    let source_key = PlaceKey::from_mir_place(source_place);
                    let op_ty = operand.ty(&body.local_decls, self.tcx);
                    result.facts.push(StateFact::Cast {
                        target: target.clone(),
                        source: AbstractValue::Place(source_key),
                        ty: op_ty,
                    });
                }
            }
            Rvalue::CopyForDeref(place) => {
                let source_place = PlaceKey::from_mir_place(place);
                result.facts.push(StateFact::Cast {
                    target: target.clone(),
                    source: AbstractValue::Place(source_place),
                    ty: self.tcx.types.usize,
                });
            }
            Rvalue::BinaryOp(op, pair) => {
                let (lhs, rhs) = &**pair;
                let lhs_val = value_from_operand(lhs);
                let rhs_val = value_from_operand(rhs);
                let target_key = target.clone();
                result.facts.push(StateFact::Binary {
                    target: target_key.clone(),
                    op: *op,
                    lhs: lhs_val.clone(),
                    rhs: rhs_val.clone(),
                });
                // If multiplying by a known constant multiple of an alignment
                // (e.g. i * 4), the result inherits that alignment property.
                if *op == BinOp::Mul || *op == BinOp::MulWithOverflow {
                    let rhs_resolved = resolve_value_chain(&rhs_val, result);
                    if let Some(divisor) = const_int_value(&rhs_resolved) {
                        if divisor > 0 && is_power_of_two(divisor) {
                            result.facts.push(StateFact::KnownAligned {
                                place: target_key.clone(),
                                align: divisor as u64,
                                ty_name: format!("result of mul by {divisor}"),
                                reason: format!("multiply by {divisor} (power of two)"),
                            });
                        }
                    }
                }
                if *op == BinOp::Add || *op == BinOp::AddWithOverflow {
                    if let Some(a) = known_alignment_of(&lhs_val, result).and_then(|a| {
                        known_alignment_of(&rhs_val, result)
                            .filter(|&b| b == a)
                            .map(|_| a)
                    }) {
                        result.facts.push(StateFact::KnownAligned {
                            place: target_key.clone(),
                            align: a,
                            ty_name: format!("sum of {a}-aligned"),
                            reason: "sum of two aligned values".into(),
                        });
                    }
                }
                if *op == BinOp::Div {
                    if let Some(src_align) = known_alignment_of(&lhs_val, result) {
                        let rhs_resolved = resolve_value_chain(&rhs_val, result);
                        if let Some(divisor) = const_int_value(&rhs_resolved) {
                            if divisor > 0 && src_align % divisor as u64 == 0 {
                                let new_align = src_align / divisor as u64;
                                result.facts.push(StateFact::KnownAligned {
                                    place: target_key.clone(),
                                    align: new_align,
                                    ty_name: format!("result of div by {divisor}"),
                                    reason: format!("dividing {src_align}-aligned by {divisor}"),
                                });
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Apply a summarized call effect to the path-local abstract state.
    fn apply_call_effects(
        &self,
        summary: &CallEffectSummary,
        args: &[Spanned<Operand<'tcx>>],
        is_target_callsite: bool,
        result: &mut ForwardVisitResult<'tcx>,
    ) {
        result.facts.push(StateFact::CallEffect(summary.clone()));
        let Some(destination) = summary.destination else {
            return;
        };
        let destination_place = PlaceKey {
            base: super::def_use::PlaceBaseKey::Local(destination.as_usize()),
            fields: Vec::new(),
        };

        for effect in &summary.effects {
            match effect {
                CallEffect::ReturnAliasArg { arg } | CallEffect::ReturnPointerFromArg { arg } => {
                    if let Some(source) = args.get(*arg).and_then(|arg| operand_place(&arg.node)) {
                        result.facts.push(StateFact::PointsTo {
                            pointer: destination_place.clone(),
                            source,
                        });
                    }
                }
                CallEffect::ReturnPointerAdd { base_arg, .. }
                | CallEffect::ReturnPointerSub { base_arg, .. } => {
                    if let Some(source) =
                        args.get(*base_arg).and_then(|arg| operand_place(&arg.node))
                    {
                        result.facts.push(StateFact::PointsTo {
                            pointer: destination_place.clone(),
                            source,
                        });
                    }
                }
                CallEffect::ReturnNonZero => result.facts.push(StateFact::KnownNonZero {
                    place: destination_place.clone(),
                    reason: format!("returned by {}", summary.name),
                }),
                CallEffect::ReturnAligned { align, ty_name } => {
                    result.facts.push(StateFact::KnownAligned {
                        place: destination_place.clone(),
                        align: *align,
                        ty_name: ty_name.clone(),
                        reason: format!("returned by {}", summary.name),
                    });
                }
                CallEffect::ReturnConst { value, label } => {
                    result
                        .values
                        .insert(destination, AbstractValue::ConstInt(u128::from(*value)));
                    result.facts.push(StateFact::KnownConst {
                        place: destination_place.clone(),
                        value: *value,
                        reason: label.clone(),
                    });
                }
                CallEffect::ReadMemory { .. } => {}
                CallEffect::WriteMemory { pointer_arg } => {
                    if let Some(pointer) = args
                        .get(*pointer_arg)
                        .and_then(|arg| operand_place(&arg.node))
                    {
                        let mut init_places = copy_chain_places(&pointer, result);
                        if init_places.is_empty() {
                            init_places.push(pointer);
                        }

                        for place in init_places {
                            let ty_name = self
                                .pointee_ty_name(result.callsite.caller, &place)
                                .unwrap_or_else(|| "?".to_string());
                            result.facts.push(StateFact::KnownInit {
                                place,
                                ty_name,
                                elements: 1,
                                reason: format!("written by {}", summary.name),
                            });
                        }
                    }
                }
                CallEffect::ReturnLengthOfArg { .. } => {}
                CallEffect::ForgetArgFacts { reason, .. } => {
                    result.forgets.push(reason.clone());
                }
            }
        }

        if summary.unsupported && !is_target_callsite {
            result.forgets.push(ForgetReason::UnknownCall);
            result
                .notes
                .push(format!("unsupported call effect: {}", summary.name));
        } else if summary.unsupported {
            result.notes.push(format!(
                "unsupported target call effect ignored for precondition proof: {}",
                summary.name
            ));
        }
    }

    /// Return a compact pointee type name for a raw pointer local.
    fn pointee_ty_name(&self, caller: DefId, place: &PlaceKey) -> Option<String> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = place.local()?;
        let ty = self.tcx.optimized_mir(caller).local_decls[local].ty;
        match ty.kind() {
            TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(format!("{ty:?}")),
            _ => Some(format!("{ty:?}")),
        }
    }
}

/// Result produced by visiting relevant MIR items forward.
#[derive(Clone, Debug)]
pub struct ForwardVisitResult<'tcx> {
    /// Unsafe callsite being checked.
    pub callsite: CallsiteLocation,
    /// Required property checked at the callsite.
    pub property: Property<'tcx>,
    /// Path whose relevant items were visited.
    pub path: Path,
    /// Abstract values currently known for MIR locals.
    pub values: FxHashMap<Local, AbstractValue<'tcx>>,
    /// Facts recorded during the forward visit.
    pub facts: Vec<StateFact<'tcx>>,
    /// Places whose facts were conservatively forgotten.
    pub forgets: Vec<ForgetReason>,
    /// Ordered visit trace.
    pub steps: Vec<ForwardStep>,
    /// Unsupported items kept as notes rather than modeled facts.
    pub notes: Vec<String>,
}

impl<'tcx> ForwardVisitResult<'tcx> {
    /// Create an empty forward visit result.
    pub fn new(callsite: CallsiteLocation, property: Property<'tcx>, path: Path) -> Self {
        Self {
            callsite,
            property,
            path,
            values: FxHashMap::default(),
            facts: Vec::new(),
            forgets: Vec::new(),
            steps: Vec::new(),
            notes: Vec::new(),
        }
    }

    /// Render a compact diagnostic summary of this forward visit.
    pub fn describe(&self) -> String {
        let mut lines = Vec::new();
        lines.push("      forward visit:".to_string());
        lines.push(format!(
            "        |_ values: {}, facts: {}, precision loss: {}",
            self.values.len(),
            self.facts.len(),
            self.forgets.len()
        ));
        if !self.facts.is_empty() {
            lines.push("        |_ facts:".to_string());
            for fact in &self.facts {
                lines.push(format!("        |  |_ {fact:?}"));
            }
        }
        if !self.notes.is_empty() {
            lines.push("        |_ unsupported:".to_string());
            for note in &self.notes {
                lines.push(format!("        |  |_ {note}"));
            }
        }
        lines.join("\n")
    }
}

/// One step visited by the forward visitor.
#[derive(Clone, Debug)]
pub enum ForwardStep {
    Statement {
        block: BasicBlock,
        statement_index: usize,
        reason: KeepReason,
    },
    Terminator {
        block: BasicBlock,
        reason: KeepReason,
    },
    PathStep {
        step: PathStep,
        reason: KeepReason,
    },
}

/// Abstract value assigned to a MIR local by the forward visitor.
#[derive(Clone, Debug)]
pub enum AbstractValue<'tcx> {
    Unknown(String),
    Place(PlaceKey),
    Ref(PlaceKey),
    RawPtr(PlaceKey),
    ThreadLocal(String),
    ConstInt(u128),
    Const(String),
    Repeat(Box<AbstractValue<'tcx>>),
    Cast(Box<AbstractValue<'tcx>>, Ty<'tcx>),
    Unary(UnOp, Box<AbstractValue<'tcx>>),
    Binary(BinOp, Box<AbstractValue<'tcx>>, Box<AbstractValue<'tcx>>),
    Nullary(String),
    Discriminant(PlaceKey),
    Aggregate(String, usize),
    #[cfg(not(rapx_rustc_ge_196))]
    ShallowInitBox(Box<AbstractValue<'tcx>>, Ty<'tcx>),
    CallResult(CallSummary<'tcx>),
}

/// Fact recorded from a relevant MIR item.
#[derive(Clone, Debug)]
pub enum StateFact<'tcx> {
    Contract(Property<'tcx>),
    PointsTo {
        pointer: PlaceKey,
        source: PlaceKey,
    },
    Cast {
        target: PlaceKey,
        source: AbstractValue<'tcx>,
        ty: Ty<'tcx>,
    },
    Binary {
        target: PlaceKey,
        op: BinOp,
        lhs: AbstractValue<'tcx>,
        rhs: AbstractValue<'tcx>,
    },
    BranchEq {
        value: AbstractValue<'tcx>,
        equals: u128,
    },
    PathCondition(String),
    Drop(PlaceKey),
    LocalDead(Local),
    Call(CallSummary<'tcx>),
    CallEffect(CallEffectSummary),
    KnownNonZero {
        place: PlaceKey,
        reason: String,
    },
    KnownAligned {
        place: PlaceKey,
        align: u64,
        ty_name: String,
        reason: String,
    },
    KnownInit {
        place: PlaceKey,
        ty_name: String,
        elements: u64,
        reason: String,
    },
    KnownConst {
        place: PlaceKey,
        value: u64,
        reason: String,
    },
}

/// Summary for a retained call terminator.
#[derive(Clone, Debug)]
pub struct CallSummary<'tcx> {
    pub destination: Local,
    pub func: String,
    pub arg_count: usize,
    pub args: Vec<AbstractValue<'tcx>>,
    pub effects: Vec<CallEffect>,
    pub unsupported: bool,
}

/// Convert a MIR operand to an abstract value.
fn value_from_operand<'tcx>(operand: &Operand<'tcx>) -> AbstractValue<'tcx> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            AbstractValue::Place(PlaceKey::from_mir_place(place))
        }
        Operand::Constant(constant) => {
            let text = format!("{:?}", constant.const_);
            const_int_from_debug(&text)
                .map(AbstractValue::ConstInt)
                .unwrap_or(AbstractValue::Const(text))
        }
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => AbstractValue::Unknown("RuntimeChecks".to_string()),
    }
}

/// Convert an operand into a place key when it names a MIR place.
fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }
}

/// Extract a small integer constant from rustc's debug representation.
fn const_int_from_debug(text: &str) -> Option<u128> {
    let text = text.trim();
    if text == "const true" {
        return Some(1);
    }
    if text == "const false" {
        return Some(0);
    }
    if let Some(rest) = text.strip_prefix("const ") {
        let digits = rest
            .chars()
            .take_while(|ch| ch.is_ascii_digit())
            .collect::<String>();
        if digits.is_empty() {
            return None;
        }
        return digits.parse().ok();
    }

    let scalar = text.strip_prefix("Val(Scalar(0x")?;
    let digits = scalar
        .chars()
        .take_while(|ch| ch.is_ascii_hexdigit())
        .collect::<String>();
    if digits.is_empty() {
        None
    } else {
        u128::from_str_radix(&digits, 16).ok()
    }
}

/// Return the concrete SwitchInt value that selects the next path block.
fn chosen_switch_value(
    path: &Path,
    block: BasicBlock,
    terminator: &Terminator<'_>,
) -> Option<u128> {
    let TerminatorKind::SwitchInt { targets, .. } = &terminator.kind else {
        return None;
    };
    let chosen = chosen_successor(path, block)?;
    let mut explicit_values = Vec::new();
    for (value, target) in targets.iter() {
        explicit_values.push(value);
        if target == chosen {
            return Some(value);
        }
    }

    if targets.otherwise() == chosen && explicit_values.len() == 1 {
        return match explicit_values[0] {
            0 => Some(1),
            1 => Some(0),
            _ => None,
        };
    }

    None
}

/// Return the next MIR block after `block` in a finite verification path.
fn chosen_successor(path: &Path, block: BasicBlock) -> Option<BasicBlock> {
    let mut previous = None;
    for step in path.steps.iter() {
        match step {
            PathStep::Block(current) => {
                if previous == Some(block) {
                    return Some(*current);
                }
                previous = Some(*current);
            }
            PathStep::Callsite(_) => return None,
        }
    }
    None
}

/// Return a compact aggregate kind name.
fn aggregate_name<'tcx>(kind: &AggregateKind<'tcx>) -> String {
    match kind {
        AggregateKind::Array(_) => "array".to_string(),
        AggregateKind::Tuple => "tuple".to_string(),
        AggregateKind::Adt(def_id, ..) => format!("adt({def_id:?})"),
        AggregateKind::Closure(def_id, _) => format!("closure({def_id:?})"),
        AggregateKind::Coroutine(def_id, _) => format!("coroutine({def_id:?})"),
        AggregateKind::CoroutineClosure(def_id, _) => format!("coroutine_closure({def_id:?})"),
        AggregateKind::RawPtr(_, _) => "raw_ptr".to_string(),
    }
}

fn const_int_value(val: &AbstractValue<'_>) -> Option<u128> {
    match val {
        AbstractValue::ConstInt(v) => Some(*v),
        _ => None,
    }
}

fn is_power_of_two(n: u128) -> bool {
    n > 0 && (n & (n - 1)) == 0
}

fn is_const_zero(val: &AbstractValue<'_>) -> bool {
    matches!(val, AbstractValue::ConstInt(0))
}

fn align_guard_value<'tcx>(
    value: &AbstractValue<'tcx>,
    equals: u128,
    result: &ForwardVisitResult<'tcx>,
) -> Option<(PlaceKey, u64)> {
    let resolved = resolve_value_chain(value, result);
    if equals == 0 {
        // MIR encodes `value % n == 0` as switchInt(value) -> [0: ...].
        match &resolved {
            AbstractValue::Binary(BinOp::Rem, rem_l, rem_r) => {
                let d = const_int_value(rem_r)?;
                if d > 0 && is_power_of_two(d) {
                    let place = match resolve_value_chain(rem_l, result) {
                        AbstractValue::Place(p) => p,
                        AbstractValue::Cast(inner, _) => match inner.as_ref() {
                            AbstractValue::Place(p) => p.clone(),
                            _ => return None,
                        },
                        _ => return None,
                    };
                    return Some((place, d as u64));
                }
            }
            _ => {}
        }
    }
    if equals == 1 {
        // Guards expressed as `(value % n) == 0` produce Eq(Rem(place, n), 0).
        let AbstractValue::Binary(BinOp::Eq, eq_l, eq_r) = &resolved else {
            return None;
        };
        if !is_const_zero(eq_r) {
            return None;
        }
        let eq_resolved = resolve_value_chain(eq_l, result);
        let AbstractValue::Binary(BinOp::Rem, rem_l, rem_r) = &eq_resolved else {
            return None;
        };
        let d = const_int_value(rem_r)?;
        if d == 0 || !is_power_of_two(d) {
            return None;
        }
        let place = match resolve_value_chain(rem_l, result) {
            AbstractValue::Place(p) => p,
            AbstractValue::Cast(inner, _) => match inner.as_ref() {
                AbstractValue::Place(p) => p.clone(),
                _ => return None,
            },
            _ => return None,
        };
        return Some((place, d as u64));
    }
    None
}

fn resolve_value_chain<'tcx>(
    value: &AbstractValue<'tcx>,
    result: &ForwardVisitResult<'tcx>,
) -> AbstractValue<'tcx> {
    let mut cur = value.clone();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(format!("{cur:?}")) {
            return cur;
        }
        cur = match &cur {
            AbstractValue::Place(p) => {
                if let PlaceBaseKey::Local(ix) = &p.base {
                    match result.values.get(&Local::from_usize(*ix)) {
                        Some(v) => v.clone(),
                        None => return cur,
                    }
                } else {
                    return cur;
                }
            }
            _ => return cur,
        };
    }
}

fn copy_chain_places<'tcx>(
    place: &PlaceKey,
    result: &ForwardVisitResult<'tcx>,
) -> Vec<PlaceKey> {
    let mut places = Vec::new();
    let mut cur = place.clone();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(cur.clone()) {
            break;
        }
        if !places.contains(&cur) {
            places.push(cur.clone());
        }

        let Some(local) = cur.local() else {
            break;
        };
        let Some(value) = result.values.get(&local) else {
            break;
        };
        match value {
            AbstractValue::Place(next) => cur = next.clone(),
            AbstractValue::Cast(inner, _) => match inner.as_ref() {
                AbstractValue::Place(next) => cur = next.clone(),
                _ => break,
            },
            _ => break,
        }
    }
    places
}

fn known_alignment_of<'tcx>(
    value: &AbstractValue<'tcx>,
    result: &ForwardVisitResult<'tcx>,
) -> Option<u64> {
    let mut best: Option<u64> = None;
    let mut cur = value.clone();
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(format!("{cur:?}")) {
            break;
        }
        if let AbstractValue::Place(ref p) = cur {
            for f in &result.facts {
                if let StateFact::KnownAligned { place, align, .. } = f {
                    if place == p {
                        best = best.map_or(Some(*align), |b| Some(b.max(*align)));
                    }
                    if place.fields.is_empty() != p.fields.is_empty() && place.base == p.base {
                        best = best.map_or(Some(*align), |b| Some(b.max(*align)));
                    }
                }
            }
        }
        cur = match &cur {
            AbstractValue::Place(p) => {
                if let PlaceBaseKey::Local(ix) = &p.base {
                    match result.values.get(&Local::from_usize(*ix)) {
                        Some(v) => v.clone(),
                        None => break,
                    }
                } else {
                    break;
                }
            }
            AbstractValue::Cast(inner, _) => (**inner).clone(),
            _ => break,
        };
    }
    best
}
