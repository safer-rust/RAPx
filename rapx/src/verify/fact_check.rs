//! Lightweight fact-based property checks.
//!
//! This module consumes the abstract facts produced by `forward_visit` and
//! proves simple properties without invoking SMT.  The checks are intentionally
//! conservative: unsupported patterns return `Unknown` instead of being treated
//! as proved.

use rustc_data_structures::fx::FxHashSet;
use rustc_middle::{
    mir::{Local, Operand, TerminatorKind},
    ty::{GenericArgKind, Ty, TyCtxt, TyKind},
};

use super::{
    backward_visit::{PlaceBaseKey, PlaceKey},
    contract::{ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind},
    forward_visit::{AbstractValue, CallSummary, ForwardVisitResult, StateFact},
    helpers::Callsite,
    report::CheckResult,
};

/// Runs fact-based checks over a forward visit result.
pub struct FactChecker<'tcx> {
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> FactChecker<'tcx> {
    /// Create a fact checker over the current compiler type context.
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self { tcx }
    }

    /// Try to prove one required property from the forward visit result.
    pub fn check(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> FactCheckResult {
        match property.kind {
            PropertyKind::NonNull => self.check_non_null(callsite, property, forward),
            PropertyKind::Align => self.check_align(callsite, property, forward),
            PropertyKind::ValidPtr => self.check_valid_ptr_partial(callsite, property, forward),
            _ => FactCheckResult::unknown("no fact-based checker for this property"),
        }
    }

    /// Try to prove the target pointer is non-null.
    fn check_non_null(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> FactCheckResult {
        let Some(target) = self.property_target(callsite, property) else {
            return FactCheckResult::unknown("property target could not be resolved");
        };

        if self.is_non_null_place(callsite, forward, &target, &mut FxHashSet::default()) {
            FactCheckResult::proved(format!("target {:?} is known non-null", target))
        } else {
            FactCheckResult::unknown(format!("target {:?} is not known non-null", target))
        }
    }

    /// Try to prove the target pointer is aligned for the requested type.
    fn check_align(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> FactCheckResult {
        let Some(target) = self.property_target(callsite, property) else {
            return FactCheckResult::unknown("property target could not be resolved");
        };
        let Some(required_ty) = self.property_required_ty(callsite, property) else {
            return FactCheckResult::unknown("alignment type could not be resolved");
        };

        if self.is_aligned_place(
            callsite,
            forward,
            &target,
            required_ty,
            &mut FxHashSet::default(),
        ) {
            FactCheckResult::proved(format!(
                "target {:?} is aligned for {:?}",
                target, required_ty
            ))
        } else {
            FactCheckResult::unknown(format!(
                "target {:?} is not known aligned for {:?}",
                target, required_ty
            ))
        }
    }

    /// Try primitive checks inside `ValidPtr` while keeping the composite result unknown.
    fn check_valid_ptr_partial(
        &self,
        callsite: &Callsite<'tcx>,
        property: &Property<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
    ) -> FactCheckResult {
        let non_null = self.check_non_null(callsite, property, forward);
        let align = self.check_align(callsite, property, forward);
        let mut result = FactCheckResult::unknown(
            "ValidPtr also requires allocation, bounds, initialization, and typing checks",
        );
        result.notes.push(format!(
            "primitive NonNull: {:?} ({})",
            non_null.result,
            non_null.notes.join("; ")
        ));
        result.notes.push(format!(
            "primitive Align: {:?} ({})",
            align.result,
            align.notes.join("; ")
        ));
        result
    }

    /// Resolve the target place of a property at a concrete callsite.
    fn property_target(
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

    /// Resolve the type argument used by an alignment-like property.
    fn property_required_ty(
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
    fn contract_place_to_callsite_place(
        &self,
        callsite: &Callsite<'tcx>,
        place: &ContractPlace<'tcx>,
    ) -> Option<PlaceKey> {
        match place.base {
            PlaceBase::Arg(index) => self.callsite_arg_place(callsite, index),
            PlaceBase::Return | PlaceBase::Local(_) => Some(PlaceKey::from_contract_place(place)),
        }
    }

    /// Return the MIR place used as the `index`-th call argument.
    fn callsite_arg_place(&self, callsite: &Callsite<'tcx>, index: usize) -> Option<PlaceKey> {
        let operand = callsite.args.get(index)?;
        operand_place(operand)
    }

    /// Replace a callee generic parameter with its concrete callsite type.
    fn instantiate_callsite_ty(&self, callsite: &Callsite<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
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

    /// Return true when a place is known to contain a non-null pointer.
    fn is_non_null_place(
        &self,
        callsite: &Callsite<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
        place: &PlaceKey,
        seen: &mut FxHashSet<PlaceKey>,
    ) -> bool {
        if !seen.insert(place.clone()) {
            return false;
        }

        if forward.facts.iter().any(|fact| {
            matches!(
                fact,
                StateFact::PointsTo { pointer, .. } if pointer == place
            )
        }) {
            return true;
        }

        let Some(value) = value_for_place(forward, place) else {
            return false;
        };
        self.is_non_null_value(callsite, forward, value, seen)
    }

    /// Return true when an abstract value is known to be non-null.
    fn is_non_null_value(
        &self,
        callsite: &Callsite<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
        value: &AbstractValue<'tcx>,
        seen: &mut FxHashSet<PlaceKey>,
    ) -> bool {
        match value {
            AbstractValue::Ref(_) | AbstractValue::RawPtr(_) => true,
            AbstractValue::Cast(inner, _) => self.is_non_null_value(callsite, forward, inner, seen),
            AbstractValue::Place(place) => self.is_non_null_place(callsite, forward, place, seen),
            AbstractValue::CallResult(call) if is_pointer_add_call(&call.func) => call
                .args
                .first()
                .map(|base| self.is_non_null_value(callsite, forward, base, seen))
                .unwrap_or(false),
            AbstractValue::CallResult(call) if is_as_ptr_call(&call.func) => true,
            _ => false,
        }
    }

    /// Return true when a place is known to be aligned for `required_ty`.
    fn is_aligned_place(
        &self,
        callsite: &Callsite<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
        place: &PlaceKey,
        required_ty: Ty<'tcx>,
        seen: &mut FxHashSet<PlaceKey>,
    ) -> bool {
        if !seen.insert(place.clone()) {
            return false;
        }

        for fact in &forward.facts {
            let StateFact::PointsTo { pointer, source } = fact else {
                continue;
            };
            if pointer != place {
                continue;
            }
            if self.place_matches_ty(callsite.caller, source, required_ty)
                || self.is_aligned_place(callsite, forward, source, required_ty, seen)
            {
                return true;
            }
        }

        let Some(value) = value_for_place(forward, place) else {
            return false;
        };
        self.is_aligned_value(callsite, forward, value, required_ty, seen)
    }

    /// Return true when an abstract value is known to be aligned for `required_ty`.
    fn is_aligned_value(
        &self,
        callsite: &Callsite<'tcx>,
        forward: &ForwardVisitResult<'tcx>,
        value: &AbstractValue<'tcx>,
        required_ty: Ty<'tcx>,
        seen: &mut FxHashSet<PlaceKey>,
    ) -> bool {
        match value {
            AbstractValue::Ref(source) | AbstractValue::RawPtr(source) => {
                self.place_matches_ty(callsite.caller, source, required_ty)
            }
            AbstractValue::Cast(inner, cast_ty) => {
                pointee_ty(*cast_ty) == Some(required_ty)
                    && self.is_aligned_value(callsite, forward, inner, required_ty, seen)
            }
            AbstractValue::Place(place) => {
                self.is_aligned_place(callsite, forward, place, required_ty, seen)
            }
            AbstractValue::CallResult(call) if is_pointer_add_call(&call.func) => call
                .args
                .first()
                .map(|base| self.is_aligned_value(callsite, forward, base, required_ty, seen))
                .unwrap_or(false),
            AbstractValue::CallResult(call) if is_as_ptr_call(&call.func) => {
                self.call_destination_pointee_matches_ty(callsite.caller, call, required_ty)
            }
            _ => false,
        }
    }

    /// Return true when a concrete place has exactly the required type.
    fn place_matches_ty(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
        ty: Ty<'tcx>,
    ) -> bool {
        self.place_ty(caller, place) == Some(ty)
    }

    /// Return true when a pointer-typed place points to the required type.
    fn place_pointee_matches_ty(
        &self,
        caller: rustc_hir::def_id::DefId,
        place: &PlaceKey,
        ty: Ty<'tcx>,
    ) -> bool {
        self.place_ty(caller, place).and_then(pointee_ty) == Some(ty)
    }

    /// Return true when a call destination is a pointer to `ty`.
    fn call_destination_pointee_matches_ty(
        &self,
        caller: rustc_hir::def_id::DefId,
        call: &CallSummary<'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        let place = PlaceKey {
            base: PlaceBaseKey::Local(call.destination.as_usize()),
            fields: Vec::new(),
        };
        self.place_pointee_matches_ty(caller, &place, ty)
    }

    /// Return the MIR type for a simple place key.
    fn place_ty(&self, caller: rustc_hir::def_id::DefId, place: &PlaceKey) -> Option<Ty<'tcx>> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = match place.base {
            PlaceBaseKey::Return => Local::from_usize(0),
            PlaceBaseKey::Local(local) => Local::from_usize(local),
            PlaceBaseKey::Arg(_) => return None,
        };
        Some(self.tcx.optimized_mir(caller).local_decls[local].ty)
    }
}

/// Result of one fact-based check.
#[derive(Clone, Debug)]
pub struct FactCheckResult {
    /// Final status from this lightweight checker.
    pub result: CheckResult,
    /// Human-readable explanation of the matched or missing facts.
    pub notes: Vec<String>,
}

impl FactCheckResult {
    /// Build a proved result with one note.
    pub fn proved(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Proved,
            notes: vec![note.into()],
        }
    }

    /// Build an unknown result with one note.
    pub fn unknown(note: impl Into<String>) -> Self {
        Self {
            result: CheckResult::Unknown,
            notes: vec![note.into()],
        }
    }

    /// Render this check as a diagnostic block.
    pub fn describe(&self) -> String {
        let mut lines = vec![format!("      fact check: {:?}", self.result)];
        for note in &self.notes {
            lines.push(format!("        |_ {note}"));
        }
        lines.join("\n")
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

/// Return true when a call summary is a slice/string/vector pointer extraction.
fn is_as_ptr_call(func: &str) -> bool {
    func.ends_with("::as_ptr") || func.contains("::as_ptr")
}
