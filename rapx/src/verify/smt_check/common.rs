//! Common SMT checking backend for the staged verifier.
//!
//! The SMT layer consumes the abstract facts produced by `forward_visit` and
//! exposes one property-oriented entry point. Safety properties do not call Z3
//! directly. Instead, each property-specific module lowers its requirement into
//! one of the common SMT obligations below, and the common backend discharges
//! that obligation against the path-local abstract facts.
//!
//! Current common obligations:
//!
//! - `SmtObligation::Aligned`: prove `addr(place) % align == 0`.
//! - `SmtObligation::NonZero`: prove `addr(place) != 0`.
//! - `SmtObligation::Range`: reserved for future bounds-style checks.
//!
//! Current property lowering:
//!
//! - `Align(p, T)` lowers to `Aligned { place: p, align: align_of(T) }`.
//! - `NonNull(p)` lowers to `NonZero { place: p }`.
//! - `ValidPtr(p, T, n)` is decomposed by `valid_ptr.rs` into primitive SMT
//!   checks that are implemented today, while unsupported primitives remain
//!   explicit `Unknown` notes.
//!
//! Future SPs should add small lowering modules next to `align.rs` and reuse
//! `SmtModel`, `SmtQuery`, and `SmtCheckResult` instead of constructing solver
//! queries ad hoc.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{BinOp, Local, Operand, TerminatorKind},
    ty::{GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind},
};
use z3::{
    Context, Solver,
    ast::{Ast, Int},
};

use super::{align, non_null, valid_ptr};

use crate::verify::{
    backward_visit::{PlaceBaseKey, PlaceKey},
    contract::{ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind},
    forward_visit::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
    helpers::Callsite,
    report::CheckResult,
};

/// SMT backend for verifier properties.
pub struct SmtChecker<'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
}

impl<'tcx> SmtChecker<'tcx> {
    /// Create an SMT checker for the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Try to prove one property using SMT.
    pub fn check(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> SmtCheckResult {
        match property.kind {
            PropertyKind::Align => align::check(self, callsite, property, forward),
            PropertyKind::NonNull => non_null::check(self, callsite, property, forward),
            PropertyKind::ValidPtr => valid_ptr::check(self, callsite, property, forward),
            _ => SmtCheckResult::unknown("no SMT lowering for this property yet"),
        }
    }

    /// Resolve the target place of a property at a concrete callsite.
    pub(crate) fn property_target(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<PlaceKey> {
        let arg = property.args.first()?;
        match arg {
            PropertyArg::Place(place) => self.contract_place_to_callsite_place(callsite, place),
            PropertyArg::Expr(ContractExpr::Place(place)) => {
                self.contract_place_to_callsite_place(callsite, place)
            }
            PropertyArg::Expr(ContractExpr::Const(index)) => {
                let index = usize::try_from(*index).ok()?;
                self.callsite_arg_place(callsite, index)
            }
            _ => None,
        }
    }

    /// Resolve the type argument used by an alignment property.
    pub(crate) fn property_required_ty(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<Ty<'tcx>> {
        property.args.iter().find_map(|arg| {
            let PropertyArg::Ty(ty) = arg else {
                return None;
            };
            Some(self.instantiate_callsite_ty(callsite, *ty))
        })
    }

    /// Convert a contract place into a concrete MIR place when possible.
    pub(crate) fn contract_place_to_callsite_place(
        &self,
        callsite: &Callsite<'tcx>,
        place: &ContractPlace<'tcx>,
    ) -> Option<PlaceKey> {
        match place.base {
            PlaceBase::Arg(index) => self.callsite_arg_place(callsite, index),
            PlaceBase::Return | PlaceBase::Local(_) => Some(PlaceKey::from_contract_place(place)),
        }
    }

    /// Return the concrete MIR place used as the `index`-th call argument.
    pub(crate) fn callsite_arg_place(
        &self,
        callsite: &Callsite<'tcx>,
        index: usize,
    ) -> Option<PlaceKey> {
        let operand = callsite.args.get(index)?;
        operand_place(operand)
    }

    /// Replace a callee generic parameter with its concrete callsite type.
    pub(crate) fn instantiate_callsite_ty(
        &self,
        callsite: &Callsite<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let TyKind::Param(param) = ty.kind() else {
            return ty;
        };

        let body = self.tcx.optimized_mir(callsite.caller);
        let terminator = body.basic_blocks[callsite.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return ty;
        };
        let Operand::Constant(func_constant) = func else {
            return ty;
        };
        let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
            return ty;
        };
        let Some(arg) = args.get(param.index as usize) else {
            return ty;
        };
        match arg.kind() {
            GenericArgKind::Type(actual_ty) => actual_ty,
            _ => ty,
        }
    }

    /// Return ABI alignment and size for a type.
    pub(crate) fn type_layout(
        &self,
        caller: rustc_hir::def_id::DefId,
        ty: Ty<'tcx>,
    ) -> Option<(u64, u64)> {
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, caller);
        let input = PseudoCanonicalInput {
            typing_env,
            value: ty,
        };
        let layout = self.tcx.layout_of(input).ok()?;
        Some((layout.align.abi.bytes(), layout.size.bytes()))
    }
}

/// General SMT obligation produced by an SP-specific lowering.
#[derive(Clone, Debug)]
pub enum SmtObligation {
    /// Prove that the address denoted by `place` is aligned to `align` bytes.
    Aligned {
        place: PlaceKey,
        align: u64,
        ty_name: String,
    },
    /// Future form for non-zero integer/address requirements.
    NonZero { place: PlaceKey },
    /// Future form for interval/bounds requirements.
    Range {
        value: PlaceKey,
        lower: i128,
        upper: Option<i128>,
    },
}

impl SmtObligation {
    /// Render a compact obligation description for diagnostics.
    pub fn describe(&self) -> String {
        match self {
            SmtObligation::Aligned {
                place,
                align,
                ty_name,
            } => {
                format!(
                    "Align({}, {}, {}-byte boundary)",
                    place_label(place),
                    ty_name,
                    align
                )
            }
            SmtObligation::NonZero { place } => format!("NonZero({})", place_label(place)),
            SmtObligation::Range {
                value,
                lower,
                upper,
            } => match upper {
                Some(upper) => format!("Range({}, {lower}..{upper})", place_label(value)),
                None => format!("Range({}, {lower}..)", place_label(value)),
            },
        }
    }
}

/// Solver query built from path facts plus one negated obligation.
#[derive(Clone, Debug)]
pub struct SmtQuery {
    /// Property-specific obligation being proved.
    pub obligation: SmtObligation,
    /// Human-readable assumptions asserted from forward facts.
    pub assumptions: Vec<String>,
    /// Human-readable negated goal sent to the solver.
    pub negated_goal: String,
}

impl SmtQuery {
    /// Create a query description.
    pub fn new(
        obligation: SmtObligation,
        assumptions: Vec<String>,
        negated_goal: impl Into<String>,
    ) -> Self {
        Self {
            obligation,
            assumptions,
            negated_goal: negated_goal.into(),
        }
    }
}

/// Result of one SMT check.
#[derive(Clone, Debug)]
pub struct SmtCheckResult {
    /// Final status produced by the SMT backend.
    pub result: CheckResult,
    /// Optional structured query description.
    pub query: Option<SmtQuery>,
    /// Human-readable explanation.
    pub notes: Vec<String>,
}

impl SmtCheckResult {
    /// Build a proved SMT result.
    pub fn proved(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Proved,
            query: None,
            notes: vec![note.into()],
        }
    }

    /// Build an unknown SMT result.
    pub fn unknown(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Unknown,
            query: None,
            notes: vec![note.into()],
        }
    }

    /// Attach the query that produced this result.
    pub fn with_query(mut self, query: SmtQuery) -> Self {
        self.query = Some(query);
        self
    }

    /// Add a diagnostic note to this result.
    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Render this SMT result as a diagnostic block.
    pub fn describe(&self) -> String {
        let mut lines = vec![format!("      smt check: {:?}", self.result)];
        if let Some(query) = &self.query {
            lines.push(format!("        |_ goal: {}", query.obligation.describe()));
            if !query.assumptions.is_empty() {
                lines.push("        |_ known facts:".to_string());
                for assumption in &query.assumptions {
                    lines.push(format!("        |  |_ {assumption}"));
                }
            }
            lines.push(format!("        |_ checked: {}", query.negated_goal));
        }
        if let Some((first, rest)) = self.notes.split_first() {
            lines.push(format!("        |_ verdict: {first}"));
            for note in rest {
                if let Some(hint) = note.strip_prefix("hint: ") {
                    lines.push(format!("        |_ hint: {hint}"));
                } else {
                    lines.push(format!("        |_ detail: {note}"));
                }
            }
        }
        lines.join("\n")
    }
}

/// Per-query SMT term builder over a forward visit result.
pub(crate) struct SmtModel<'a, 'ctx, 'tcx> {
    tcx: TyCtxt<'tcx>,
    callsite: &'a Callsite<'tcx>,
    forward: &'a ForwardVisitResult<'tcx>,
    ctx: &'ctx Context,
    place_terms: HashMap<PlaceKey, Int<'ctx>>,
    assumptions: Vec<String>,
}

impl<'a, 'ctx, 'tcx> SmtModel<'a, 'ctx, 'tcx> {
    /// Create a fresh SMT model builder.
    pub(crate) fn new(
        tcx: TyCtxt<'tcx>,
        callsite: &'a Callsite<'tcx>,
        forward: &'a ForwardVisitResult<'tcx>,
        ctx: &'ctx Context,
    ) -> Self {
        Self {
            tcx,
            callsite,
            forward,
            ctx,
            place_terms: HashMap::new(),
            assumptions: Vec::new(),
        }
    }

    /// Assert facts collected by the forward visitor.
    pub(crate) fn assert_forward_facts(&mut self, solver: &Solver<'ctx>) {
        for fact in &self.forward.facts {
            match fact {
                StateFact::PointsTo { pointer, source } => {
                    self.assert_place_non_zero(
                        solver,
                        pointer,
                        "created from a reference/raw pointer",
                    );
                    self.assert_place_alignment(solver, pointer);
                    self.assert_place_alignment(solver, source);
                }
                StateFact::Call(call) if is_as_ptr_call(&call.func) => {
                    let place = PlaceKey {
                        base: PlaceBaseKey::Local(call.destination.as_usize()),
                        fields: Vec::new(),
                    };
                    self.assert_place_non_zero(solver, &place, "returned by as_ptr");
                    self.assert_place_alignment(solver, &place);
                }
                StateFact::KnownNonZero { place, reason } => {
                    self.assert_place_non_zero(solver, place, reason);
                }
                StateFact::KnownAligned {
                    place,
                    align,
                    ty_name,
                    reason,
                } => {
                    self.assert_known_alignment(solver, place, *align, ty_name, reason);
                }
                StateFact::BranchEq { value, equals } => {
                    if let Some(term) = self.term_for_value(value, &mut HashSet::new()) {
                        let expected = Int::from_u64(self.ctx, *equals as u64);
                        solver.assert(&term._eq(&expected));
                        self.assumptions
                            .push(format!("{} == {equals}", value_label(value)));
                    }
                }
                StateFact::Contract(_)
                | StateFact::Cast { .. }
                | StateFact::Binary { .. }
                | StateFact::PathCondition(_)
                | StateFact::Drop(_)
                | StateFact::LocalDead(_)
                | StateFact::CallEffect(_)
                | StateFact::Call(_) => {}
            }
        }
    }

    /// Return the path assumptions asserted by this model.
    pub(crate) fn assumptions(&self) -> &[String] {
        &self.assumptions
    }

    /// Assert that a place is known to denote a non-zero address.
    pub(crate) fn assert_place_non_zero(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        reason: &str,
    ) {
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            solver.assert(&term._eq(&zero).not());
            self.assumptions
                .push(format!("{} != 0 ({reason})", place_label(place)));
        }
    }

    /// Assert known alignment for a place when its MIR type provides one.
    fn assert_place_alignment(&mut self, solver: &Solver<'ctx>, place: &PlaceKey) {
        let Some(ty) = self.place_ty(place) else {
            return;
        };
        let Some(align_ty) = pointee_ty(ty).or(Some(ty)) else {
            return;
        };
        let Some((align, _)) = self.type_layout(align_ty) else {
            return;
        };
        if align <= 1 {
            return;
        }
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            let align = Int::from_u64(self.ctx, align);
            solver.assert(&term.modulo(&align)._eq(&zero));
            self.assumptions.push(format!(
                "{} aligned for {align_ty:?} ({align} bytes)",
                place_label(place)
            ));
        }
    }

    /// Assert an explicitly summarized alignment fact.
    fn assert_known_alignment(
        &mut self,
        solver: &Solver<'ctx>,
        place: &PlaceKey,
        align: u64,
        ty_name: &str,
        reason: &str,
    ) {
        if align <= 1 {
            return;
        }
        if let Some(term) = self.term_for_place(place) {
            let zero = Int::from_u64(self.ctx, 0);
            let align_term = Int::from_u64(self.ctx, align);
            solver.assert(&term.modulo(&align_term)._eq(&zero));
            self.assumptions.push(format!(
                "{} aligned for {ty_name} ({align} bytes, {reason})",
                place_label(place)
            ));
        }
    }

    /// Build an SMT term for a place.
    pub(crate) fn term_for_place(&mut self, place: &PlaceKey) -> Option<Int<'ctx>> {
        self.term_for_place_inner(place, &mut HashSet::new())
    }

    /// Build an SMT term for a place with recursion protection.
    fn term_for_place_inner(
        &mut self,
        place: &PlaceKey,
        seen: &mut HashSet<PlaceKey>,
    ) -> Option<Int<'ctx>> {
        if let Some(term) = self.place_terms.get(place) {
            return Some(term.clone());
        }
        if !seen.insert(place.clone()) {
            return None;
        }

        if let Some(value) = value_for_place(self.forward, place) {
            if let Some(term) = self.term_for_value(value, seen) {
                self.place_terms.insert(place.clone(), term.clone());
                return Some(term);
            }
        }

        let term = Int::new_const(self.ctx, place_name(place));
        self.place_terms.insert(place.clone(), term.clone());
        Some(term)
    }

    /// Build an SMT term for an abstract value.
    fn term_for_value(
        &mut self,
        value: &AbstractValue<'tcx>,
        seen: &mut HashSet<PlaceKey>,
    ) -> Option<Int<'ctx>> {
        match value {
            AbstractValue::ConstInt(value) => Some(Int::from_u64(self.ctx, *value as u64)),
            AbstractValue::Const(text) => {
                const_int_from_debug(text).map(|value| Int::from_u64(self.ctx, value as u64))
            }
            AbstractValue::Place(place) => self.term_for_place_inner(place, seen),
            AbstractValue::Cast(inner, _) => self.term_for_value(inner, seen),
            AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => Some(Int::new_const(
                self.ctx,
                format!("addr_{}", place_name(place)),
            )),
            AbstractValue::Binary(op, lhs, rhs) => {
                let lhs = self.term_for_value(lhs, seen)?;
                let rhs = self.term_for_value(rhs, seen)?;
                self.term_for_binary(*op, &lhs, &rhs)
            }
            AbstractValue::CallResult(call) if is_pointer_add_call(&call.func) => {
                let base = call.args.first()?;
                let index = call.args.get(1)?;
                let base = self.term_for_value(base, seen)?;
                let index = self.term_for_value(index, seen)?;
                let stride = self.call_destination_stride(call).unwrap_or(1);
                let stride = Int::from_u64(self.ctx, stride);
                Some(Int::add(
                    self.ctx,
                    &[base, Int::mul(self.ctx, &[index, stride])],
                ))
            }
            AbstractValue::CallResult(call) => {
                let place = PlaceKey {
                    base: PlaceBaseKey::Local(call.destination.as_usize()),
                    fields: Vec::new(),
                };
                Some(Int::new_const(self.ctx, place_name(&place)))
            }
            AbstractValue::Unknown(_)
            | AbstractValue::ThreadLocal(_)
            | AbstractValue::Repeat(_)
            | AbstractValue::Unary(_, _)
            | AbstractValue::Nullary(_)
            | AbstractValue::Discriminant(_)
            | AbstractValue::Aggregate(_, _)
            | AbstractValue::ShallowInitBox(_, _) => None,
        }
    }

    /// Lower a binary MIR operation to an integer term.
    fn term_for_binary(&self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Option<Int<'ctx>> {
        let one = Int::from_u64(self.ctx, 1);
        let zero = Int::from_u64(self.ctx, 0);
        Some(match op {
            BinOp::Add => Int::add(self.ctx, &[lhs.clone(), rhs.clone()]),
            BinOp::Sub => Int::sub(self.ctx, &[lhs.clone(), rhs.clone()]),
            BinOp::Mul => Int::mul(self.ctx, &[lhs.clone(), rhs.clone()]),
            BinOp::Div => lhs.div(rhs),
            BinOp::Rem => lhs.modulo(rhs),
            BinOp::Eq => lhs._eq(rhs).ite(&one, &zero),
            BinOp::Ne => lhs._eq(rhs).not().ite(&one, &zero),
            BinOp::Lt => lhs.lt(rhs).ite(&one, &zero),
            BinOp::Le => lhs.le(rhs).ite(&one, &zero),
            BinOp::Gt => lhs.gt(rhs).ite(&one, &zero),
            BinOp::Ge => lhs.ge(rhs).ite(&one, &zero),
            _ => return None,
        })
    }

    /// Return the byte stride for a typed pointer-add call destination.
    fn call_destination_stride(&self, call: &CallSummary<'tcx>) -> Option<u64> {
        let place = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: Vec::new(),
        };
        let destination_ty = self.place_ty(&place)?;
        let pointee = pointee_ty(destination_ty)?;
        self.type_layout(pointee).map(|(_, size)| size)
    }

    /// Return the MIR type for a simple place key.
    fn place_ty(&self, place: &PlaceKey) -> Option<Ty<'tcx>> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        Some(self.tcx.optimized_mir(self.callsite.caller).local_decls[local].ty)
    }

    /// Return ABI alignment and size for a type.
    fn type_layout(&self, ty: Ty<'tcx>) -> Option<(u64, u64)> {
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(self.tcx, self.callsite.caller);
        let input = PseudoCanonicalInput {
            typing_env,
            value: ty,
        };
        let layout = self.tcx.layout_of(input).ok()?;
        Some((layout.align.abi.bytes(), layout.size.bytes()))
    }
}

/// Convert an operand into a place key when it names a MIR place.
fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
    }
}

/// Return the abstract value assigned to a place when it is tracked by local.
fn value_for_place<'a, 'tcx>(
    forward: &'a ForwardVisitResult<'tcx>,
    place: &PlaceKey,
) -> Option<&'a AbstractValue<'tcx>> {
    let local = place.local()?;
    forward.values.get(&local)
}

/// Return the pointee type of raw pointers and references.
fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
        _ => None,
    }
}

/// Return true when a call summary is a typed pointer addition.
fn is_pointer_add_call(func: &str) -> bool {
    func.contains("::add") || func.contains("::wrapping_add")
}

/// Return true when a call summary extracts a pointer from a slice-like object.
fn is_as_ptr_call(func: &str) -> bool {
    func.ends_with("::as_ptr") || func.contains("::as_ptr")
}

/// Stable SMT variable name for a place key.
fn place_name(place: &PlaceKey) -> String {
    let base = match place.base {
        PlaceBaseKey::Return => "return".to_string(),
        PlaceBaseKey::Local(local) => format!("local_{local}"),
        PlaceBaseKey::Arg(arg) => format!("arg_{arg}"),
    };
    if place.fields.is_empty() {
        base
    } else {
        format!(
            "{}_{}",
            base,
            place
                .fields
                .iter()
                .map(|field| field.to_string())
                .collect::<Vec<_>>()
                .join("_")
        )
    }
}

/// Compact human-readable label for a MIR place key.
pub(crate) fn place_label(place: &PlaceKey) -> String {
    let base = match place.base {
        PlaceBaseKey::Return => "return".to_string(),
        PlaceBaseKey::Local(local) => format!("_{local}"),
        PlaceBaseKey::Arg(arg) => format!("arg{arg}"),
    };
    if place.fields.is_empty() {
        base
    } else {
        format!(
            "{}.{}",
            base,
            place
                .fields
                .iter()
                .map(|field| field.to_string())
                .collect::<Vec<_>>()
                .join(".")
        )
    }
}

/// Compact human-readable label for an abstract value.
pub(crate) fn value_label(value: &AbstractValue<'_>) -> String {
    match value {
        AbstractValue::Unknown(text) => format!("unknown({text})"),
        AbstractValue::Place(place) => place_label(place),
        AbstractValue::Ref(place) => format!("&{}", place_label(place)),
        AbstractValue::RawPtr(place) => format!("raw({})", place_label(place)),
        AbstractValue::ThreadLocal(name) => format!("thread_local({name})"),
        AbstractValue::ConstInt(value) => value.to_string(),
        AbstractValue::Const(text) => const_int_from_debug(text)
            .map(|value| value.to_string())
            .unwrap_or_else(|| text.trim().to_string()),
        AbstractValue::Repeat(inner) => format!("repeat({})", value_label(inner)),
        AbstractValue::Cast(inner, ty) => format!("cast({}, {ty:?})", value_label(inner)),
        AbstractValue::Unary(op, inner) => format!("{op:?}({})", value_label(inner)),
        AbstractValue::Binary(op, lhs, rhs) => {
            format!(
                "{} {} {}",
                value_label(lhs),
                binop_label(*op),
                value_label(rhs)
            )
        }
        AbstractValue::Nullary(name) => name.clone(),
        AbstractValue::Discriminant(place) => format!("discriminant({})", place_label(place)),
        AbstractValue::Aggregate(name, len) => format!("{name}[{len}]"),
        AbstractValue::ShallowInitBox(inner, ty) => {
            format!("box({}, {ty:?})", value_label(inner))
        }
        AbstractValue::CallResult(call) if is_pointer_add_call(&call.func) => {
            let base = call
                .args
                .first()
                .map(value_label)
                .unwrap_or_else(|| "?".to_string());
            let index = call
                .args
                .get(1)
                .map(value_label)
                .unwrap_or_else(|| "?".to_string());
            format!("{base}.add({index})")
        }
        AbstractValue::CallResult(call) => {
            let destination = PlaceKey {
                base: PlaceBaseKey::Local(call.destination.as_usize()),
                fields: Vec::new(),
            };
            format!(
                "{} = call({})",
                place_label(&destination),
                short_func_name(&call.func)
            )
        }
    }
}

/// Render a compact binary operator label.
fn binop_label(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::Eq => "==",
        BinOp::Ne => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        _ => "?",
    }
}

/// Return the final path segment of a rustc debug function name.
fn short_func_name(func: &str) -> String {
    func.rsplit("::")
        .next()
        .unwrap_or(func)
        .trim_matches('"')
        .to_string()
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
