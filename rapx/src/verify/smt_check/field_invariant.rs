//! Discharge pointer obligations from struct field invariants.
//!
//! When a raw pointer handed to an ownership-consuming API (e.g.
//! `Box::from_raw`) or a raw-pointer dereference was loaded from a struct
//! field reached through a reference or raw pointer, and the field's struct
//! declares a matching invariant such as
//! `#[rapx::invariant(Owning(field.unwrap_some()))]`,
//! `#[rapx::invariant(Allocated(field, T, n))]`,
//! `#[rapx::invariant(ValidPtr(field, T, n))]` or
//! `#[rapx::invariant(Typed(field, T))]`, the invariant is a caller-provided
//! assumption about that memory (exactly like the `Align` struct invariants
//! already asserted as entry facts) and can discharge the obligation.
//!
//! The trace walks the forward value snapshot from the checkpoint argument
//! back through value copies (`x = y`, `x = (y as Some).0`, pointer-returning
//! `as_ptr`-style calls) and stops at each place of shape
//! `base_local[.field...]`.  Whenever `base_local` is a reference/raw pointer
//! to a local ADT declaring an invariant whose projection matches the
//! remaining field path, the obligation is discharged.
//!
//! Like the existing `Align` handling, this assumes the invariant holds on
//! function entry and that the traced field has not been re-established
//! mid-function; mutators are expected to restore invariants before their
//! endpoint checkpoints.

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

use crate::verify::{
    contract::{ContractExpr, Property, PropertyArg, PropertyKind},
    def_use::{PlaceBaseKey, PlaceKey},
    target::get_struct_invariants_for_adt,
    verifier::{AbstractValue, ForwardVisitResult, StateFact},
};

/// Maximum substitution steps while tracing the pointer back to a field.
const MAX_TRACE_STEPS: usize = 32;

/// Try to discharge `kind` for `target` from a struct field invariant.
///
/// When given, `required_ty` and `required_elements` must both be satisfied
/// by the declared invariant.  Returns a human-readable reason on success.
pub(super) fn discharge_from_field_invariant<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    target: &PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
    kind: PropertyKind,
    required_ty: Option<Ty<'tcx>>,
    required_elements: Option<u64>,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut current = target.clone();
    let mut visited: Vec<PlaceKey> = Vec::new();

    for _ in 0..MAX_TRACE_STEPS {
        if visited.contains(&current) {
            break;
        }
        visited.push(current.clone());

        if let Some(reason) = field_invariant_matches(
            tcx,
            caller,
            body,
            &current,
            kind.clone(),
            required_ty,
            required_elements,
        ) {
            return Some(reason);
        }

        let Some(next) = substitute_base(&current, forward) else {
            break;
        };
        current = next;
    }

    None
}

/// Replace the base local of `place` with its recorded forward value,
/// splicing the remaining field path onto the source place.
fn substitute_base<'tcx>(place: &PlaceKey, forward: &ForwardVisitResult<'tcx>) -> Option<PlaceKey> {
    let local = place.local()?;

    let source = match forward.values.get(&local) {
        Some(AbstractValue::Place(source))
        | Some(AbstractValue::Ref(source))
        | Some(AbstractValue::RawPtr(source)) => Some(source.clone()),
        Some(AbstractValue::Cast(inner, _)) => match inner.as_ref() {
            AbstractValue::Place(source)
            | AbstractValue::Ref(source)
            | AbstractValue::RawPtr(source) => Some(source.clone()),
            _ => None,
        },
        _ => None,
    };

    let source = source.or_else(|| {
        // Pointer-returning calls (`as_ptr`, `NonNull::from`, ...) record a
        // PointsTo edge from the destination to the pointer-carrying
        // argument.
        forward.facts.iter().find_map(|fact| match fact {
            StateFact::PointsTo { pointer, source }
                if pointer.base == place.base && pointer.fields.is_empty() =>
            {
                Some(source.clone())
            }
            _ => None,
        })
    })?;

    let mut fields = source.fields.clone();
    fields.extend_from_slice(&place.fields);
    Some(PlaceKey {
        base: source.base,
        fields,
    })
}

/// Check whether `place` reads a pointee field covered by a struct invariant
/// of the requested kind.
fn field_invariant_matches<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    body: &rustc_middle::mir::Body<'tcx>,
    place: &PlaceKey,
    kind: PropertyKind,
    required_ty: Option<Ty<'tcx>>,
    required_elements: Option<u64>,
) -> Option<String> {
    if place.fields.is_empty() {
        return None;
    }
    let local = place.local()?;
    if local.as_usize() >= body.local_decls.len() {
        return None;
    }
    let base_ty = body.local_decls[local].ty;
    let pointee = match base_ty.kind() {
        TyKind::Ref(_, pointee, _) | TyKind::RawPtr(pointee, _) => *pointee,
        _ => return None,
    };
    let TyKind::Adt(adt_def, _) = pointee.kind() else {
        return None;
    };
    if !adt_def.is_struct() {
        return None;
    }
    let struct_def_id = adt_def.did();

    for invariant in get_struct_invariants_for_adt(tcx, struct_def_id) {
        if !invariant_kind_implies(tcx, caller, &invariant.kind, &kind, required_ty) {
            continue;
        }
        let Some(PropertyArg::Place(contract_place)) = invariant.args.first() else {
            continue;
        };
        let invariant_key = PlaceKey::from_contract_place(contract_place);
        if invariant_key.fields != place.fields {
            continue;
        }
        if !invariant_args_cover(&invariant, required_ty, required_elements) {
            continue;
        }
        let struct_name = tcx.def_path_str(struct_def_id);
        return Some(format!(
            "{kind:?} assumed from struct invariant on `{struct_name}` for pointee field path {:?}",
            place.fields
        ));
    }

    None
}

/// True when a declared invariant of kind `declared` establishes the checked
/// kind `required`.
///
/// Besides exact matches, two documented implications are used
/// (primitive-sp.md):
/// - `Init(p, T, len)` implies `Typed(p, T)` (psp III.4: initialized memory
///   always satisfies the type invariant, while the converse does not hold).
/// - For non-ZST `T`, `ValidPtr(p, T, len)` implies
///   `Deref(p, T, len) = Allocated(p, T, len) && InBound(p, T, len)`
///   (compound-SP table).  The ZST guard matters because
///   `ValidPtr = Size(T, 0) || (!Size(T, 0) && Deref)` holds vacuously for
///   zero-sized pointees without any allocation.
fn invariant_kind_implies<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    declared: &PropertyKind,
    required: &PropertyKind,
    required_ty: Option<Ty<'tcx>>,
) -> bool {
    if declared == required {
        return true;
    }
    if matches!(declared, PropertyKind::Init) && matches!(required, PropertyKind::Typed) {
        return true;
    }
    if matches!(declared, PropertyKind::ValidPtr)
        && matches!(required, PropertyKind::Allocated | PropertyKind::InBound)
    {
        return required_ty.is_some_and(|ty| {
            super::common::safe_type_layout(tcx, caller, ty).is_some_and(|(_, size)| size > 0)
        });
    }
    false
}

/// True when a declared invariant's type/count arguments cover the requested
/// type and element count.  Kinds without type or count arguments (e.g.
/// `Owning`) are covered trivially.
fn invariant_args_cover<'tcx>(
    invariant: &Property<'tcx>,
    required_ty: Option<Ty<'tcx>>,
    required_elements: Option<u64>,
) -> bool {
    let declared_ty = invariant.args.iter().find_map(|arg| match arg {
        PropertyArg::Ty(ty) => Some(*ty),
        _ => None,
    });
    let declared_elements = invariant.args.iter().find_map(|arg| match arg {
        PropertyArg::Expr(ContractExpr::Const(value)) => u64::try_from(*value).ok(),
        _ => None,
    });

    let ty_ok = match (required_ty, declared_ty) {
        (Some(required), Some(declared)) => {
            required == declared || format!("{required:?}") == format!("{declared:?}")
        }
        (None, _) => true,
        (Some(_), None) => false,
    };
    let elements_ok = match (required_elements, declared_elements) {
        (Some(required), Some(declared)) => declared >= required,
        (None, _) => true,
        (Some(_), None) => false,
    };
    ty_ok && elements_ok
}

/// Discharge a struct-invariant checkpoint obligation from an equivalent
/// entry contract fact.
///
/// Struct invariants become entry assumptions for every method
/// (`caller_requires`), and constructor/method endpoint checks re-verify the
/// same properties at return checkpoints.  When an entry `Contract` fact of
/// the same kind covers the same place (and its type/count arguments), the
/// property is preserved by the frame unless the function re-assigned the
/// field with something weaker; this mirrors how `Align` invariants are
/// already asserted into the SMT model and then proved against themselves.
pub(super) fn discharge_from_contract_fact<'tcx>(
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> Option<String> {
    let property_key = contract_property_key(property)?;
    let target_key = substitute_base(&property_key, forward).unwrap_or(property_key.clone());

    for fact in &forward.facts {
        let StateFact::Contract(contract) = fact else {
            continue;
        };
        if contract.kind != property.kind {
            continue;
        }
        let Some(contract_key) = contract_property_key(contract) else {
            continue;
        };
        if contract_key != target_key {
            continue;
        }
        if !contract_args_cover(contract, property) {
            continue;
        }
        return Some(format!(
            "{:?} assumed from an entry contract covering the same place",
            property.kind
        ));
    }

    None
}

/// Resolve the first place argument of a property, normalising `Arg(n)` bases
/// to their MIR locals so entry facts and checkpoint targets compare equal.
fn contract_property_key<'tcx>(property: &Property<'tcx>) -> Option<PlaceKey> {
    let arg = property.args.first()?;
    let place = match arg {
        PropertyArg::Place(place) => place,
        PropertyArg::Expr(ContractExpr::Place(place)) => place,
        _ => return None,
    };
    let mut key = PlaceKey::from_contract_place(place);
    if let PlaceBaseKey::Arg(index) = key.base {
        key.base = PlaceBaseKey::Local(index + 1);
    }
    Some(key)
}

/// True when the entry contract's type/count arguments are at least as
/// strong as the checked invariant's.  Kinds without such arguments are
/// covered trivially.
fn contract_args_cover<'tcx>(contract: &Property<'tcx>, property: &Property<'tcx>) -> bool {
    let ty_of = |candidate: &Property<'tcx>| {
        candidate.args.iter().find_map(|arg| match arg {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        })
    };
    let elements_of = |candidate: &Property<'tcx>| {
        candidate.args.iter().find_map(|arg| match arg {
            PropertyArg::Expr(ContractExpr::Const(value)) => u64::try_from(*value).ok(),
            _ => None,
        })
    };

    let ty_ok = match (ty_of(property), ty_of(contract)) {
        (Some(required), Some(declared)) => {
            required == declared || format!("{required:?}") == format!("{declared:?}")
        }
        (None, _) => true,
        (Some(_), None) => false,
    };
    let elements_ok = match (elements_of(property), elements_of(contract)) {
        (Some(required), Some(declared)) => declared >= required,
        (None, _) => true,
        (Some(_), None) => false,
    };
    ty_ok && elements_ok
}
