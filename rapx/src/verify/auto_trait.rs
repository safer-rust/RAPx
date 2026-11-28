//! Checkers for the `Send`/`Sync` marker-trait predicates.
//!
//! These are intentionally *structural/behavioural* approximations
//! (sound-incomplete): a full proof of "exclusive ownership" / "no cross-thread
//! aliasing" needs an ownership + concurrency model (e.g. separation logic),
//! which the current sequential VM does not have.
//!
//! The vocabulary follows the Rust model: a raw pointer is `!Send` unless
//! *tamed* — either the type has no raw pointers at all ([`NoRawPtr`]), or its
//! raw-pointer field is `Allocated`/`Owning` (discharged via the struct's
//! `#[rapx::invariant]` annotations) and updated read-only ([`NoInternalMut`]),
//! exclusively ([`UniInternalMut`]), or under synchronization / atomically
//! ([`AtomicUpdate`]).  The composition is declared in
//! `std-trait.json` + `std-compound-properties.rs`; this module only
//! implements the primitive type-level checks.

use crate::compat::MirTerminatorExt as _;
use std::collections::HashSet;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::{ClauseKind, GenericArgKind, ParamTy, Ty, TyCtxt, TyKind},
};

use crate::analysis::dataflow::pointer_flow::trace_source_arg;
use crate::contract::{PropertyKind, annotation::get_struct_invariants_from_annotation};
use crate::def_ids::{
    intrinsic_api,
    lang_api::{self, LangItem},
    other_api,
    type_ids,
};
use crate::util::{
    mir_scan::place_has_raw_deref,
    mir_utils::{self, dep_callee_def_id},
};
use crate::verify::report::{CheckResult, UnknownReason};

/// Three-valued structural verdict: a type definitely contains a negative
/// (`Yes`), definitely does not (`No`), or contains an unresolved generic
/// parameter so the answer is unknown (`Maybe`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Contains {
    Yes,
    No,
    Maybe,
}

impl Contains {
    /// `Yes` dominates; `Maybe` dominates `No` (conservative merge).
    fn join(self, other: Contains) -> Contains {
        match (self, other) {
            (Contains::Yes, _) | (_, Contains::Yes) => Contains::Yes,
            (Contains::Maybe, _) | (_, Contains::Maybe) => Contains::Maybe,
            (Contains::No, Contains::No) => Contains::No,
        }
    }

    /// Map the three-valued verdict to a [`CheckResult`].
    fn to_check(self) -> CheckResult {
        match self {
            Contains::Yes => CheckResult::Failed,
            Contains::Maybe => CheckResult::Unknown(UnknownReason::Unimplemented),
            Contains::No => CheckResult::ProvedByRule,
        }
    }
}

/// Type-level `ContainNoType` obligation check (no VM state required): returns
/// `Failed` if `ty` structurally contains any named negative, `Unknown` if a
/// generic parameter makes the answer unresolved, else `Proved`.
pub(crate) fn contain_no_type_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    negatives: &[String],
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    let mut defs: Vec<DefId> = Vec::new();
    for name in negatives {
        let Some(group) = type_ids::negative_type_by_name(name) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let count = defs.len();
        defs.extend(type_ids::def_ids_for_type(group));
        if defs.len() == count {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
    }
    type_structurally_contains(tcx, ty, &defs, impl_def_id, is_sync).to_check()
}

/// Type-level `NoRawPtr` obligation check (no VM state required).
pub(crate) fn no_raw_ptr_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    find_raw_ptr(tcx, ty, impl_def_id, is_sync).to_check()
}

/// Type-level `NoInternalMut` obligation check (no VM state required): `Failed`
/// if any inherent method writes through a raw pointer — either a plain
/// `*ptr = ...` write or an atomic update (`Atomic*` intrinsic).
pub(crate) fn no_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if has_raw_ptr_writes(tcx, ty) || has_atomic_ptr_updates(tcx, ty) {
        CheckResult::Failed
    } else {
        CheckResult::ProvedByRule
    }
}

/// Type-level `UniInternalMut` obligation check (no VM state required): `Proved`
/// if the type writes through a raw pointer (plain or atomic) but does not
/// implement `Clone` (which would copy the pointer and alias the pointee).
pub(crate) fn uni_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if (has_raw_ptr_writes(tcx, ty) || has_atomic_ptr_updates(tcx, ty))
        && !type_implements_clone(tcx, ty)
    {
        CheckResult::ProvedByRule
    } else {
        CheckResult::Failed
    }
}

/// Type-level `AtomicUpdate` obligation check (no VM state required): `Proved`
/// when aliased updates of the type's raw pointers are safe without exclusive
/// ownership.  Two ways satisfy this:
///  1. *structural* — every interior-mutability / raw-pointer field is guarded
///     by a synchronization primitive (`Mutex`/`RwLock`/`Atomic*`), so the
///     `find_unsynchronized_mutation` scan finds nothing unsynchronized; or
///  2. *behavioural* — the type's raw-pointer updates go through an atomic
///     intrinsic (`AtomicUsize::fetch_add` & friends), as in `Arc`-style
///     reference counting.
pub(crate) fn atomic_update_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    match find_unsynchronized_mutation(tcx, ty, impl_def_id, is_sync) {
        Contains::No => CheckResult::ProvedByRule,
        Contains::Maybe => CheckResult::Unknown(UnknownReason::Unimplemented),
        Contains::Yes => {
            // An atomic call elsewhere in the type does not make a plain raw
            // pointer write safe to share across threads.
            if has_atomic_ptr_updates(tcx, ty) && !has_raw_ptr_writes(tcx, ty) {
                CheckResult::ProvedByRule
            } else {
                CheckResult::Failed
            }
        }
    }
}

/// Type-level `Allocated(ptr, T, n)` / `Owning(ptr)` obligation check (no VM
/// state required): `Proved` when `T` declares a matching
/// `#[rapx::invariant(Allocated(ptr))]` / `#[rapx::invariant(Owning(ptr))]`
/// annotation (optionally restricted to the `field` named in the property).
pub(crate) fn field_invariant_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    kind: PropertyKind,
    field: Option<&str>,
) -> CheckResult {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return CheckResult::Failed;
    };
    let adt_def_id = adt_def.did();

    let invariants = get_struct_invariants_from_annotation(tcx, adt_def_id, adt_def_id);
    let matched = invariants.iter().any(|p| p.kind() == Some(kind) && field.is_none_or(|f| {
        p.args().first().and_then(|a| crate::contract::place::field_name_from_arg(tcx, adt_def_id, a)).as_deref() == Some(f)
    }));
    if matched { CheckResult::ProvedByRule } else { CheckResult::Failed }
}

/// Type-level `RefSend` obligation check (no VM state required).
pub(crate) fn ref_send_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    find_unsynchronized_mutation(tcx, ty, impl_def_id, is_sync).to_check()
}

/// Whether `ty` implements `Clone` (which copies any raw-pointer field, aliasing
/// the pointee across a move).
fn type_implements_clone<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let Some(clone_did) = tcx.lang_items().clone_trait() else {
        return false;
    };
    tcx.all_impls(clone_did)
        .any(|impl_did| tcx.impl_trait_ref(impl_did).skip_binder().self_ty() == ty)
}

/// Whether a generic type parameter carries a `Send`/`Sync` bound on the impl,
/// letting the checker treat it as satisfied instead of `Unknown`.
fn param_bound_is_satisfied(
    tcx: TyCtxt<'_>, impl_def_id: DefId, param_ty: ParamTy, is_sync: bool,
) -> bool {
    let trait_did = if is_sync {
        tcx.get_diagnostic_item(rustc_span::sym::Sync)
    } else {
        tcx.get_diagnostic_item(rustc_span::sym::Send)
    };
    let Some(trait_did) = trait_did else {
        return false;
    };
    let predicates = tcx.clauses_of(impl_def_id);
    let iter = predicates.clauses.iter();
    for (pred, _) in iter {
        if let ClauseKind::Trait(trait_ref) = pred.kind().skip_binder()
            && trait_ref.def_id() == trait_did
            && let TyKind::Param(p) = trait_ref.self_ty().kind()
            && p.index == param_ty.index
        {
            return true;
        }
    }
    false
}

/// Whether any inherent function of `ty` may write through its first parameter.
fn has_raw_ptr_writes<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    any_inherent_method(tcx, ty, |did| has_raw_ptr_write(tcx, did))
}

fn any_inherent_method<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, predicate: impl Fn(DefId) -> bool) -> bool {
    let TyKind::Adt(adt, _) = ty.kind() else { return false };
    tcx.inherent_impls(adt.did()).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|did| {
            matches!(tcx.def_kind(*did), DefKind::Fn | DefKind::AssocFn) && predicate(*did)
        })
    })
}

/// Whether a function may write through a raw pointer derived from its first
/// parameter. Exclude writes to local storage or through later parameters;
/// unresolved origins remain possible writes.
fn has_raw_ptr_write(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            let StatementKind::Assign(assign) = &stmt.kind else {
                return false;
            };
            let (lhs, _) = &**assign;
            if !place_has_raw_deref(body, lhs) {
                return false;
            }
            match trace_source_arg(tcx, body, lhs.local, &mut HashSet::new(), 3) {
                Some(0) => true,
                Some(_) => false,
                None => !points_to_local_storage(body, lhs.local, &mut HashSet::new()),
            }
        })
    })
}

/// Prove that every definition of `pointer` takes the address of local storage.
fn points_to_local_storage(body: &Body<'_>, pointer: Local, seen: &mut HashSet<Local>) -> bool {
    if pointer.as_usize() <= body.arg_count || !seen.insert(pointer) {
        return false;
    }
    let mut found = false;
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (dest, value) = &**assign;
            if dest.local != pointer || !dest.projection.is_empty() {
                continue;
            }
            found = true;
            let local_address = match value {
                Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                    place.local.as_usize() > body.arg_count
                        && !place
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, ProjectionElem::Deref))
                }
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _) => {
                    place.projection.is_empty()
                        && points_to_local_storage(body, place.local, &mut seen.clone())
                }
                _ => false,
            };
            if !local_address {
                return false;
            }
        }
    }
    found
}

/// Detect an atomic update in a method's MIR. Reads and fences do not count.
fn has_atomic_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.iter().any(|bb| {
        let (TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. }) = &bb.rapx_terminator().kind else {
            return false;
        };
        dep_callee_def_id(func).is_some_and(|callee| {
            intrinsic_api::is_atomic_update(tcx, callee) || other_api::is_atomic_update_method(tcx, callee)
        })
    })
}

/// Whether any inherent method of `ty` performs an atomic update through an
/// atomic intrinsic or an `Atomic*` method (`fetch_add`/`store`/...), e.g. an
/// `Arc`-style `fetch_add` on a reference count reached via a raw pointer.
fn has_atomic_ptr_updates<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    any_inherent_method(tcx, ty, |did| has_atomic_call(tcx, did))
}

/// Structurally check whether `ty` (transitively) contains a raw pointer.
/// A raw pointer may also appear as a pattern type (`pattern_type!(*const T
/// is ..)`), so recurse into `TyKind::Pat`.
fn find_raw_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, impl_def_id: DefId, is_sync: bool) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_raw_ptr(tcx, *inner, impl_def_id, is_sync),
        TyKind::Adt(adt_def, substs) => {
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = mir_utils::field_ty(tcx, field, substs);
                result = result.join(find_raw_ptr(tcx, field_ty, impl_def_id, is_sync));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(find_raw_ptr(tcx, subst_ty, impl_def_id, is_sync));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            find_raw_ptr(tcx, *inner, impl_def_id, is_sync)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(find_raw_ptr(tcx, t, impl_def_id, is_sync))
        }),
        TyKind::Param(param_ty) => {
            if param_bound_is_satisfied(tcx, impl_def_id, *param_ty, is_sync) {
                Contains::No
            } else {
                Contains::Maybe
            }
        }
        _ => Contains::No,
    }
}

/// Structurally check whether `ty` (transitively) contains one of the negative
/// types identified by `negative_defs`.  A synchronization primitive (`Mutex`/
/// `RwLock`/`Atomic*`) guards its interior, so the scan stops there — a negative
/// type nested inside one (e.g. `Mutex<UnsafeCell>`) is considered tamed.
fn type_structurally_contains<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    negative_defs: &[DefId],
    impl_def_id: DefId,
    is_sync: bool,
) -> Contains {
    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            if negative_defs.contains(&adt_def.did()) {
                return Contains::Yes;
            }
            if type_ids::is_std_sync_primitive(adt_def.did()) {
                return Contains::No;
            }
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = mir_utils::field_ty(tcx, field, substs);
                result = result.join(type_structurally_contains(
                    tcx,
                    field_ty,
                    negative_defs,
                    impl_def_id,
                    is_sync,
                ));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(type_structurally_contains(
                        tcx,
                        subst_ty,
                        negative_defs,
                        impl_def_id,
                        is_sync,
                    ));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            type_structurally_contains(tcx, *inner, negative_defs, impl_def_id, is_sync)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(type_structurally_contains(
                tcx,
                t,
                negative_defs,
                impl_def_id,
                is_sync,
            ))
        }),
        TyKind::Param(param_ty) => {
            if param_bound_is_satisfied(tcx, impl_def_id, *param_ty, is_sync) {
                Contains::No
            } else {
                Contains::Maybe
            }
        }
        _ => Contains::No,
    }
}

/// Find an interior-mutability / raw-pointer field that is not guarded by a
/// synchronization primitive.  A raw pointer may also appear as a pattern type
/// (`pattern_type!(*const T is ..)`), so recurse into `TyKind::Pat`.
fn find_unsynchronized_mutation<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, impl_def_id: DefId, is_sync: bool) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_unsynchronized_mutation(tcx, *inner, impl_def_id, is_sync),
        TyKind::Adt(adt_def, substs) => {
            let did = adt_def.did();
            if type_ids::is_std_sync_primitive(did) {
                return Contains::No;
            }
            if lang_api::matches(tcx, did, LangItem::UnsafeCell) {
                return Contains::Yes;
            }
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = mir_utils::field_ty(tcx, field, substs);
                result = result.join(find_unsynchronized_mutation(
                    tcx,
                    field_ty,
                    impl_def_id,
                    is_sync,
                ));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(find_unsynchronized_mutation(
                        tcx,
                        subst_ty,
                        impl_def_id,
                        is_sync,
                    ));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            find_unsynchronized_mutation(tcx, *inner, impl_def_id, is_sync)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(find_unsynchronized_mutation(tcx, t, impl_def_id, is_sync))
        }),
        TyKind::Param(param_ty) => {
            if param_bound_is_satisfied(tcx, impl_def_id, *param_ty, is_sync) {
                Contains::No
            } else {
                Contains::Maybe
            }
        }
        _ => Contains::No,
    }
}
