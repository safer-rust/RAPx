//! Path-local checking for the `Typed` safety property.
//!
//! `Typed(p, T)` is not a pure numeric SMT fact.  The first verifier model
//! proves it by following the path-local provenance facts produced by the
//! forward visitor: references and slices carry their Rust element type,
//! pointer arithmetic preserves the base pointee type, same-type casts preserve
//! typedness, and `ptr.write(value)` establishes one initialized `T` element.

use std::collections::HashSet;

use rustc_abi::FieldIdx;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{
    call_summary::CallEffect,
    contract::Property,
    def_use::PlaceKey,
    helpers::Checkpoint,
    verifier::{AbstractValue, ForwardVisitResult, StateFact},
};

const MAX_TYPED_TRACE_DEPTH: usize = 32;

/// Check `Typed` using path-local provenance and initialization facts.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(target) = checker.property_target(checkpoint, property) else {
        return SmtCheckResult::unknown("Typed target could not be resolved");
    };
    let Some(required_ty) = checker.property_required_ty(checkpoint, property) else {
        return SmtCheckResult::unknown("Typed type could not be resolved");
    };

    let mut context = TypedContext {
        checker,
        caller: checkpoint.caller,
        forward,
        required_ty,
    };

    let mut seen = HashSet::new();
    if context.place_is_typed(&target, &mut seen, 0) {
        SmtCheckResult::proved(format!(
            "typed provenance proved for {} as {:?}",
            place_debug(&target),
            required_ty
        ))
    } else if let Some(reason) = super::field_invariant::discharge_from_field_invariant(
        checker.tcx,
        checkpoint.caller,
        &target,
        forward,
        crate::verify::contract::PropertyKind::Typed,
        Some(required_ty),
        None,
    ) {
        SmtCheckResult::proved(format!("Typed proved: {reason}"))
    } else if let Some(reason) =
        super::field_invariant::discharge_from_contract_fact(property, forward)
    {
        SmtCheckResult::proved(format!("Typed proved: {reason}"))
    } else {
        SmtCheckResult::unknown(format!(
            "current path facts do not prove {} is typed as {:?}",
            place_debug(&target),
            required_ty
        ))
    }
}

struct TypedContext<'a, 'tcx> {
    checker: &'a SmtChecker<'tcx>,
    caller: DefId,
    forward: &'a ForwardVisitResult<'tcx>,
    required_ty: Ty<'tcx>,
}

impl<'a, 'tcx> TypedContext<'a, 'tcx> {
    /// Prove that a place denotes storage or a pointer whose dynamic type is `required_ty`.
    fn place_is_typed(
        &mut self,
        place: &PlaceKey,
        seen: &mut HashSet<PlaceKey>,
        depth: usize,
    ) -> bool {
        if depth > MAX_TYPED_TRACE_DEPTH || !seen.insert(place.clone()) {
            return false;
        }

        if self.known_init_matches(place) {
            return true;
        }

        if let Some(value) = self.latest_value_for_place(place)
            && self.value_is_typed(&value, seen, depth + 1)
        {
            return true;
        }

        if let Some(value) = self.latest_cast_source_for_place(place)
            && self.value_is_typed(&value, seen, depth + 1)
        {
            return true;
        }

        if let Some(source) = self.latest_points_to_source(place) {
            if self.storage_place_is_typed(&source) {
                return true;
            }
            if self.place_is_typed(&source, seen, depth + 1) {
                return true;
            }
        }

        self.storage_place_is_typed(place)
    }

    /// Prove that an abstract value carries `required_ty` typed provenance.
    fn value_is_typed(
        &mut self,
        value: &AbstractValue<'tcx>,
        seen: &mut HashSet<PlaceKey>,
        depth: usize,
    ) -> bool {
        if depth > MAX_TYPED_TRACE_DEPTH {
            return false;
        }

        match value {
            AbstractValue::Place(place) => self.place_is_typed(place, seen, depth + 1),
            AbstractValue::Ref(place) | AbstractValue::RawPtr(place) => {
                self.storage_place_is_typed(place) || self.place_is_typed(place, seen, depth + 1)
            }
            AbstractValue::Cast(inner, ty) => {
                self.ty_has_required_payload(*ty) && self.value_is_typed(inner, seen, depth + 1)
            }
            AbstractValue::CallResult(call) => call.effects.iter().any(|effect| match effect {
                CallEffect::ReturnPointerFromArg { arg }
                | CallEffect::ReturnAliasArg { arg }
                | CallEffect::ReturnPointerAdd { base_arg: arg, .. }
                | CallEffect::ReturnPointerSub { base_arg: arg, .. } => call
                    .args
                    .get(*arg)
                    .is_some_and(|arg_value| self.value_is_typed(arg_value, seen, depth + 1)),
                _ => false,
            }),
            _ => false,
        }
    }

    /// Return the latest value assigned to a place in the retained path slice.
    fn latest_value_for_place(&self, place: &PlaceKey) -> Option<AbstractValue<'tcx>> {
        if !place.fields.is_empty() {
            return None;
        }
        let local = place.local()?;
        self.forward
            .latest_value_definition_before(local, self.forward.value_definitions.len())
            .map(|definition| definition.value.clone())
    }

    /// Return the latest cast source retained for a target place.
    fn latest_cast_source_for_place(&self, place: &PlaceKey) -> Option<AbstractValue<'tcx>> {
        self.forward.facts.iter().rev().find_map(|fact| {
            let StateFact::Cast { target, source, ty } = fact else {
                return None;
            };
            if target == place && self.ty_has_required_payload(*ty) {
                Some(source.clone())
            } else {
                None
            }
        })
    }

    /// Return the latest provenance source retained for a pointer place.
    fn latest_points_to_source(&self, place: &PlaceKey) -> Option<PlaceKey> {
        self.forward.facts.iter().rev().find_map(|fact| {
            let StateFact::PointsTo { pointer, source } = fact else {
                return None;
            };
            (pointer == place).then(|| source.clone())
        })
    }

    /// Return true when a previous write initialized this place as `required_ty`.
    fn known_init_matches(&self, place: &PlaceKey) -> bool {
        if self.forward.facts.iter().rev().any(|fact| {
            let StateFact::KnownInit {
                place: init_place,
                ty_name,
                elements,
                ..
            } = fact
            else {
                return false;
            };
            init_place == place && *elements > 0 && self.ty_name_matches(ty_name)
        }) {
            return true;
        }
        if !place.fields.is_empty() {
            let mut ancestor = place.clone();
            while !ancestor.fields.is_empty() {
                ancestor.fields.pop();
                if self.forward.facts.iter().rev().any(|fact| {
                    let StateFact::KnownInit {
                        place: init_place,
                        ty_name,
                        elements,
                        ..
                    } = fact
                    else {
                        return false;
                    };
                    init_place == &ancestor && *elements > 0 && self.ty_name_matches(ty_name)
                }) {
                    return true;
                }
            }
        }
        false
    }

    /// Return true when a Rust storage place itself is known to contain `required_ty`.
    fn storage_place_is_typed(&self, place: &PlaceKey) -> bool {
        let Some(ty) = self.place_ty(place) else {
            return false;
        };

        match *ty.kind() {
            TyKind::RawPtr(_, _) => false,
            TyKind::Ref(_, inner, _) => self.ty_matches(payload_ty(inner)),
            TyKind::Slice(element) | TyKind::Array(element, _) => self.ty_matches(element),
            _ => self.ty_matches(ty),
        }
    }

    /// Resolve a place type from MIR locals and field projections.
    fn place_ty(&self, place: &PlaceKey) -> Option<Ty<'tcx>> {
        let local = place.local()?;
        let body = self.checker.tcx.optimized_mir(self.caller);
        let mut ty = body.local_decls.get(local)?.ty;

        for field in &place.fields {
            ty = field_ty(self.checker.tcx, ty, *field)?;
        }

        Some(ty)
    }

    /// Return true when `ty` or its pointer/reference payload is `required_ty`.
    fn ty_has_required_payload(&self, ty: Ty<'tcx>) -> bool {
        self.ty_matches(payload_ty(ty))
    }

    /// Return true when two compiler types are the same for current verifier purposes.
    fn ty_matches(&self, ty: Ty<'tcx>) -> bool {
        ty == self.required_ty || format!("{ty:?}") == format!("{:?}", self.required_ty)
    }

    /// Return true when a stringly fact type name matches `required_ty`.
    fn ty_name_matches(&self, ty_name: &str) -> bool {
        ty_name == format!("{:?}", self.required_ty)
    }
}

/// Return the Rust payload type carried by references, pointers, slices, and arrays.
fn payload_ty<'tcx>(ty: Ty<'tcx>) -> Ty<'tcx> {
    match *ty.kind() {
        TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => payload_ty(inner),
        TyKind::Slice(element) | TyKind::Array(element, _) => element,
        _ => ty,
    }
}

/// Resolve one field projection through an aggregate type.
fn field_ty<'tcx>(tcx: TyCtxt<'tcx>, base_ty: Ty<'tcx>, field: usize) -> Option<Ty<'tcx>> {
    let peeled_ty = base_ty.peel_refs();
    match *peeled_ty.kind() {
        TyKind::Adt(adt_def, args) => {
            if !adt_def.is_struct() && !adt_def.is_union() {
                return None;
            }
            let variant = adt_def.non_enum_variant();
            if field >= variant.fields.len() {
                return None;
            }
            #[cfg(not(rapx_rustc_ge_198))]
            let ty = variant.fields[FieldIdx::from_usize(field)].ty(tcx, args);
            #[cfg(rapx_rustc_ge_198)]
            let ty = variant.fields[FieldIdx::from_usize(field)]
                .ty(tcx, args)
                .skip_norm_wip();
            Some(ty)
        }
        TyKind::Tuple(fields) => fields.get(field).copied(),
        _ => None,
    }
}

/// Return a compact label for a verifier place.
fn place_debug(place: &PlaceKey) -> String {
    format!("{place:?}")
}
