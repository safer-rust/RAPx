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
//! `std-trait-ensures.json` + `std-compound-properties.rs`; this module only
//! implements the primitive type-level checks.

#[cfg(not(rapx_ge_100))]
use rustc_hir::LangItem;
#[cfg(rapx_ge_100)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ClauseKind, GenericArgKind, ParamTy, Ty, TyCtxt, TyKind};
use z3::Solver;

use crate::compat::FxHashMap;
use crate::helpers::mir_scan::{Checkpoint, has_atomic_call, has_raw_ptr_write};
use crate::verify::vm::state::VmState;
use crate::verify::{
    contract::{Property, PropertyArg, PropertyKind},
    report::CheckResult,
    target::get_struct_invariants_from_annotation,
};

use super::PropertyChecker;

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
}

impl PropertyChecker {
    /// `ContainNoType(T, bad1, bad2, ...)`: `T` must not structurally contain any of
    /// the named negative types.
    pub(super) fn check_contain_no_type<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        let negatives: Vec<String> = property.args()[1..]
            .iter()
            .filter_map(|a| match a {
                PropertyArg::Ident(name) => Some(name.clone()),
                _ => None,
            })
            .collect();
        if negatives.is_empty() {
            return CheckResult::Unknown;
        }
        contain_no_type_check(vm_state.tcx, ty, &negatives, checkpoint.caller, false)
    }

    /// `NoRawPtr(T)`: `T` must have no raw pointers.
    pub(super) fn check_no_raw_ptr<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        no_raw_ptr_check(vm_state.tcx, ty, checkpoint.caller, false)
    }

    /// `NoInternalMut(T)`: `T` must have no interior mutation through raw pointers.
    pub(super) fn check_no_internal_mut<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        _checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        no_internal_mut_check(vm_state.tcx, ty)
    }

    /// `UniInternalMut(T)`: `T`'s interior mutation must be unique (exclusive
    /// owner, no aliasing `Clone`).
    pub(super) fn check_uni_internal_mut<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        _checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        uni_internal_mut_check(vm_state.tcx, ty)
    }

    /// `AtomicUpdate(T)`: `T`'s raw-pointer updates are guarded by a
    /// synchronization primitive (`Mutex`/`RwLock`) or performed atomically
    /// (`Atomic*`).
    pub(super) fn check_atomic_update<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        atomic_update_check(vm_state.tcx, ty, checkpoint.caller, false)
    }

    /// `RefSend(T)`: every interior-mutability (`UnsafeCell`) / raw-pointer
    /// field of `T` must be guarded by a synchronization primitive.
    pub(super) fn check_ref_send<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().first().and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        ref_send_check(vm_state.tcx, ty, checkpoint.caller, true)
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
        defs.extend_from_slice(crate::def_id::negative_type_defs(name));
    }
    match type_structurally_contains(tcx, ty, &defs, impl_def_id, is_sync) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Type-level `NoRawPtr` obligation check (no VM state required).
pub(crate) fn no_raw_ptr_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    match find_raw_ptr(tcx, ty, impl_def_id, is_sync) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Type-level `NoInternalMut` obligation check (no VM state required): `Failed`
/// if any inherent method writes through a raw pointer — either a plain
/// `*ptr = ...` write or an atomic update (`Atomic*` intrinsic).
pub(crate) fn no_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if has_raw_ptr_writes(tcx, ty) || has_atomic_ptr_updates(tcx, ty) {
        CheckResult::Failed
    } else {
        CheckResult::Proved
    }
}

/// Type-level `UniInternalMut` obligation check (no VM state required): `Proved`
/// if the type writes through a raw pointer (plain or atomic) but does not
/// implement `Clone` (which would copy the pointer and alias the pointee).
pub(crate) fn uni_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if (has_raw_ptr_writes(tcx, ty) || has_atomic_ptr_updates(tcx, ty))
        && !type_implements_clone(tcx, ty)
    {
        CheckResult::Proved
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
        Contains::No => CheckResult::Proved,
        Contains::Maybe => CheckResult::Unknown,
        Contains::Yes => {
            if has_atomic_ptr_updates(tcx, ty) {
                CheckResult::Proved
            } else {
                CheckResult::Failed
            }
        }
    }
}

/// Type-level `Allocated(ptr, T, n)` / `Owning(ptr)` obligation check (no VM
/// state required): `Proved` when `T` declares a matching
/// `#[rapx::invariant(Allocated(ptr))]` / `#[rapx::invariant(Owning(ptr))]`
/// annotation (optionally restricted to the `field` named in the property) *and*
/// the already-run struct-invariant verification discharged it.
/// `invariant_results` carries the per-struct verdict; when a struct's
/// invariants failed to verify, the check fails too.
pub(crate) fn field_invariant_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    kind: PropertyKind,
    field: Option<&str>,
    invariant_results: &FxHashMap<DefId, CheckResult>,
) -> CheckResult {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return CheckResult::Failed;
    };
    let adt_def_id = adt_def.did();

    let invariants = get_struct_invariants_from_annotation(tcx, adt_def_id, adt_def_id);
    let matched = invariants.iter().any(|p| {
        p.kind() == Some(kind)
            && field.map_or(true, |f| {
                p.args()
                    .first()
                    .and_then(|a| {
                        crate::verify::contract::place::field_name_from_arg(tcx, adt_def_id, a)
                    })
                    .as_deref()
                    == Some(f)
            })
    });
    if !matched {
        return CheckResult::Failed;
    }

    // The invariant must actually hold, not just be annotated.
    if let Some(result) = invariant_results.get(&adt_def_id) {
        if *result != CheckResult::Proved {
            return CheckResult::Failed;
        }
    }
    CheckResult::Proved
}

/// Type-level `RefSend` obligation check (no VM state required).
pub(crate) fn ref_send_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> CheckResult {
    match find_unsynchronized_mutation(tcx, ty, impl_def_id, is_sync) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Whether `ty` implements `Clone` (which copies any raw-pointer field, aliasing
/// the pointee across a move).
fn type_implements_clone<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let Some(clone_did) = tcx.lang_items().clone_trait() else {
        return false;
    };
    tcx.all_impls(clone_did).any(|impl_did| {
        tcx.impl_trait_ref(impl_did).skip_binder().self_ty() == ty
    })
}

/// Whether a generic type parameter carries a `Send`/`Sync` bound on the impl,
/// letting the checker treat it as satisfied instead of `Unknown`.
fn param_bound_is_satisfied(
    tcx: TyCtxt<'_>,
    impl_def_id: DefId,
    param_ty: ParamTy,
    is_sync: bool,
) -> bool {
    let trait_did = if is_sync {
        tcx.get_diagnostic_item(rustc_span::sym::Sync)
    } else {
        tcx.get_diagnostic_item(rustc_span::sym::Send)
    };
    let Some(trait_did) = trait_did else {
        return false;
    };
    let predicates = crate::compat::predicates_of(tcx, impl_def_id);
    #[cfg(not(rapx_ge_100))]
    let iter = predicates.predicates.iter();
    #[cfg(rapx_ge_100)]
    let iter = predicates.clauses.iter();
    for (pred, _) in iter {
        if let ClauseKind::Trait(trait_ref) = pred.kind().skip_binder() {
            if trait_ref.def_id() == trait_did {
                if let TyKind::Param(p) = trait_ref.self_ty().kind() {
                    if p.index == param_ty.index {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Whether any inherent method of `ty` writes through a raw pointer.
fn has_raw_ptr_writes<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    let adt_def_id = adt_def.did();
    tcx.inherent_impls(adt_def_id).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|item| {
            matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn)
                && has_raw_ptr_write(tcx, *item)
        })
    })
}

/// Whether any inherent method of `ty` performs an atomic update through an
/// atomic intrinsic or an `Atomic*` method (`fetch_add`/`store`/...), e.g. an
/// `Arc`-style `fetch_add` on a reference count reached via a raw pointer.
fn has_atomic_ptr_updates<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> bool {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };
    let adt_def_id = adt_def.did();
    tcx.inherent_impls(adt_def_id).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|item| {
            matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn)
                && has_atomic_call(tcx, *item)
        })
    })
}

/// Structurally check whether `ty` (transitively) contains a raw pointer.
/// A raw pointer may also appear as a pattern type (`pattern_type!(*const T
/// is ..)`), so recurse into `TyKind::Pat`.
fn find_raw_ptr<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_raw_ptr(tcx, *inner, impl_def_id, is_sync),
        TyKind::Adt(adt_def, substs) => {
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
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
            if crate::def_id::sync_primitive_types().contains(&adt_def.did()) {
                return Contains::No;
            }
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
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
fn find_unsynchronized_mutation<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    impl_def_id: DefId,
    is_sync: bool,
) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_unsynchronized_mutation(tcx, *inner, impl_def_id, is_sync),
        TyKind::Adt(adt_def, substs) => {
            let did = adt_def.did();
            if crate::def_id::sync_primitive_types().contains(&did) {
                return Contains::No;
            }
            if tcx.is_lang_item(did, LangItem::UnsafeCell) {
                return Contains::Yes;
            }
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
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
