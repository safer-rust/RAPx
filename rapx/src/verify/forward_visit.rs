//! Forward visitor for relevant MIR items.
//!
//! This module consumes the MIR items produced by `backward_visit` and visits
//! them in path order.  The current implementation is a skeleton: it records
//! simple value/fact summaries and leaves unsupported MIR effects as notes so
//! later property checkers can be added incrementally.

use std::collections::{HashMap, HashSet};

use if_chain::if_chain;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{ImplPolarity, ItemId, ItemKind, def_id::DefId, hir_id::OwnerId};
use rustc_middle::{
    mir::{
        AggregateKind, BasicBlock, BinOp, Local, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind, UnOp,
    },
    ty::{FloatTy, IntTy, ParamEnv, Ty, TyCtxt, TyKind, UintTy},
};

use super::{
    backward_visit::{BackwardItem, ForgetReason, KeepReason, PlaceKey, RelevantMirItems},
    contract::Property,
    helpers::CallsiteLocation,
    path::{Path, PathStep},
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
                    self.visit_statement(*block, *statement_index, *kind, statement, &mut result);
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
        result: &mut ForwardVisitResult<'tcx>,
    ) {
        result.steps.push(ForwardStep::Statement {
            block,
            statement_index,
            reason,
        });

        match &statement.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let value = self.value_from_rvalue(rvalue);
                result.values.insert(place.local, value);
                self.record_rvalue_facts(place, rvalue, result);
            }
            StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::StorageLive(..)
            | StatementKind::Retag(..)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Intrinsic(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {}
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
                let call = CallSummary {
                    destination: destination.local,
                    func: format!("{func:?}"),
                    arg_count: args.len(),
                    args: arg_values,
                };
                result
                    .values
                    .insert(destination.local, AbstractValue::CallResult(call.clone()));
                result.facts.push(StateFact::Call(call));
            }
            TerminatorKind::SwitchInt { discr, .. } => {
                result
                    .facts
                    .push(StateFact::PathCondition(format!("{discr:?}")));
            }
            TerminatorKind::Assert { cond, .. } => {
                result
                    .facts
                    .push(StateFact::PathCondition(format!("assert({cond:?})")));
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
            Rvalue::Use(operand) => value_from_operand(operand),
            Rvalue::Repeat(operand, _) => {
                AbstractValue::Repeat(Box::new(value_from_operand(operand)))
            }
            Rvalue::Ref(_, _, place) => AbstractValue::Ref(PlaceKey::from_mir_place(place)),
            Rvalue::RawPtr(_, place) => AbstractValue::RawPtr(PlaceKey::from_mir_place(place)),
            Rvalue::ThreadLocalRef(def_id) => AbstractValue::ThreadLocal(format!("{def_id:?}")),
            Rvalue::Cast(_, operand, ty) => {
                AbstractValue::Cast(Box::new(value_from_operand(operand)), *ty)
            }
            Rvalue::BinaryOp(op, box (lhs, rhs)) => AbstractValue::Binary(
                *op,
                Box::new(value_from_operand(lhs)),
                Box::new(value_from_operand(rhs)),
            ),
            Rvalue::NullaryOp(op) => AbstractValue::Nullary(format!("{op:?}")),
            Rvalue::UnaryOp(op, operand) => {
                AbstractValue::Unary(*op, Box::new(value_from_operand(operand)))
            }
            Rvalue::Discriminant(place) => {
                AbstractValue::Discriminant(PlaceKey::from_mir_place(place))
            }
            Rvalue::Aggregate(kind, operands) => {
                AbstractValue::Aggregate(aggregate_name(kind), operands.len())
            }
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
            Rvalue::Cast(_, operand, ty) => {
                result.facts.push(StateFact::Cast {
                    target,
                    source: value_from_operand(operand),
                    ty: *ty,
                });
            }
            Rvalue::BinaryOp(op, box (lhs, rhs)) => {
                result.facts.push(StateFact::Binary {
                    target,
                    op: *op,
                    lhs: value_from_operand(lhs),
                    rhs: value_from_operand(rhs),
                });
            }
            _ => {}
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
    Const(String),
    Repeat(Box<AbstractValue<'tcx>>),
    Cast(Box<AbstractValue<'tcx>>, Ty<'tcx>),
    Unary(UnOp, Box<AbstractValue<'tcx>>),
    Binary(BinOp, Box<AbstractValue<'tcx>>, Box<AbstractValue<'tcx>>),
    Nullary(String),
    Discriminant(PlaceKey),
    Aggregate(String, usize),
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
    PathCondition(String),
    Drop(PlaceKey),
    LocalDead(Local),
    Call(CallSummary<'tcx>),
}

/// Summary for a retained call terminator.
#[derive(Clone, Debug)]
pub struct CallSummary<'tcx> {
    pub destination: Local,
    pub func: String,
    pub arg_count: usize,
    pub args: Vec<AbstractValue<'tcx>>,
}

/// Computes representative concrete types for generic parameters.
pub struct GenericTypeCandidates<'tcx> {
    trait_map: HashMap<String, HashSet<Ty<'tcx>>>,
}

impl<'tcx> GenericTypeCandidates<'tcx> {
    /// Build generic type candidates from a function definition.
    pub fn for_def(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        Self::new(tcx, tcx.param_env(def_id))
    }

    /// Build generic type candidates from a parameter environment.
    pub fn new(tcx: TyCtxt<'tcx>, param_env: ParamEnv<'tcx>) -> Self {
        let mut trait_bounds: HashMap<String, HashSet<String>> = HashMap::new();
        let mut satisfied_types: HashMap<String, HashSet<Ty<'tcx>>> = HashMap::new();

        for clause in param_env.caller_bounds() {
            let Some(trait_clause) = clause.as_trait_clause() else {
                continue;
            };
            let trait_def_id = trait_clause.def_id();
            let generic_name = trait_clause.self_ty().skip_binder().to_string();
            let trait_name = tcx.def_path_str(trait_def_id);
            trait_bounds
                .entry(generic_name.clone())
                .or_default()
                .insert(trait_name.clone());

            let type_set = satisfied_types.entry(generic_name).or_default();
            for impl_def_id in tcx.all_impls(trait_def_id) {
                if !impl_def_id.is_local() {
                    continue;
                }
                let impl_owner_id = tcx
                    .hir_owner_node(OwnerId {
                        def_id: impl_def_id.expect_local(),
                    })
                    .def_id();
                let item = tcx.hir_item(ItemId {
                    owner_id: impl_owner_id,
                });
                if_chain! {
                    if let ItemKind::Impl(impl_item) = item.kind;
                    if let Some(trait_impl_header) = impl_item.of_trait;
                    if trait_impl_header.polarity == ImplPolarity::Positive;
                    if let Some(binder) = tcx.impl_opt_trait_ref(impl_def_id);
                    then {
                        let impl_ty = binder.skip_binder().self_ty();
                        match impl_ty.kind() {
                            TyKind::Adt(adt_def, _) => {
                                type_set.insert(tcx.type_of(adt_def.did()).skip_binder());
                            }
                            TyKind::Param(_) => {}
                            _ => {
                                type_set.insert(impl_ty);
                            }
                        }
                    }
                }
            }

            if trait_name == "bytemuck::Pod" || trait_name == "plain::Plain" {
                type_set.extend(Self::pod_types(tcx));
            }
        }

        let std_marker_traits = HashSet::from([
            String::from("std::marker::Copy"),
            String::from("std::clone::Clone"),
            String::from("std::marker::Sized"),
        ]);
        for (name, type_set) in &mut satisfied_types {
            if trait_bounds
                .get(name)
                .map(|bounds| bounds.is_subset(&std_marker_traits))
                .unwrap_or(false)
            {
                type_set.clear();
            }
        }

        Self {
            trait_map: satisfied_types,
        }
    }

    /// Return the representative types grouped by generic parameter name.
    pub fn candidates(&self) -> &HashMap<String, HashSet<Ty<'tcx>>> {
        &self.trait_map
    }

    /// Return known primitive representatives for Pod-like bounds.
    fn pod_types(tcx: TyCtxt<'tcx>) -> HashSet<Ty<'tcx>> {
        [
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::Isize)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I8)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I16)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I32)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I64)),
            tcx.mk_ty_from_kind(TyKind::Int(IntTy::I128)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::Usize)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U8)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U16)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U32)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U64)),
            tcx.mk_ty_from_kind(TyKind::Uint(UintTy::U128)),
            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F32)),
            tcx.mk_ty_from_kind(TyKind::Float(FloatTy::F64)),
        ]
        .into_iter()
        .collect()
    }
}

/// Convert a MIR operand to an abstract value.
fn value_from_operand<'tcx>(operand: &Operand<'tcx>) -> AbstractValue<'tcx> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            AbstractValue::Place(PlaceKey::from_mir_place(place))
        }
        Operand::Constant(constant) => AbstractValue::Const(format!("{:?}", constant.const_)),
    }
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
