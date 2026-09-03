//! Checkers for `NotType`, `NoInternalRefMut` and `AtomicUpdate` — the
//! structural predicates used to approximate `Send`/`Sync` auto-trait safety.
//!
//! These are intentionally *structural* approximations (sound-incomplete): a
//! full proof of "no cross-thread aliasing" / "every mutation holds a lock"
//! needs an ownership + concurrency model (e.g. separation logic), which the
//! current sequential VM does not have.  What we can check here is whether a
//! type *structurally* contains a negative type (`NotType`), has interior
//! mutability (`NoInternalRefMut`), or guards its interior mutability with a
//! synchronization primitive (`AtomicUpdate`).

#[cfg(not(rapx_ge_100))]
use rustc_hir::LangItem;
#[cfg(rapx_ge_100)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgKind, Ty, TyCtxt, TyKind};
use z3::Solver;

use crate::helpers::mir_scan::{Checkpoint, has_raw_ptr_write};
use crate::verify::vm::state::VmState;
use crate::verify::{
    contract::{Property, PropertyArg},
    report::CheckResult,
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
    /// `NotType(T, bad1, bad2, ...)`: `T` must not structurally contain any of
    /// the named negative types.
    pub(super) fn check_not_type<'ctx, 'tcx>(
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
        not_type_check(vm_state.tcx, ty, &negatives)
    }

    /// `NoInternalRefMut(T)`: `T` must have no *mutable* raw pointers.
    pub(super) fn check_no_internal_ref_mut<'ctx, 'tcx>(
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
        no_internal_ref_mut_check(vm_state.tcx, ty)
    }

    /// `AtomicUpdate(T)`: every interior-mutability (`UnsafeCell`) / raw-pointer
    /// field of `T` must be guarded by a synchronization primitive.
    pub(super) fn check_atomic_update<'ctx, 'tcx>(
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
        atomic_update_check(vm_state.tcx, ty)
    }
}

/// Type-level `NotType` obligation check (no VM state required): returns
/// `Failed` if `ty` structurally contains any named negative, `Unknown` if a
/// generic parameter makes the answer unresolved, else `Proved`.
pub(crate) fn not_type_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    negatives: &[String],
) -> CheckResult {
    let mut defs: Vec<DefId> = Vec::new();
    for name in negatives {
        defs.extend_from_slice(crate::def_id::negative_type_defs(name));
    }
    match type_structurally_contains(tcx, ty, &defs) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Type-level `NoInternalRefMut` obligation check (no VM state required).
///
/// A type has "interior mutation" if one of its methods writes through a raw
/// pointer (e.g. `(*self.ptr).strong += 1`).  A write is only a cross-thread
/// data race if the type *aliases* the pointee — approximated here by whether
/// the type implements `Clone` (which copies the raw pointer).  An exclusive
/// write (no `Clone`) is Send-safe.
pub(crate) fn no_internal_ref_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return CheckResult::Proved;
    };
    let adt_def_id = adt_def.did();

    let writes = tcx.inherent_impls(adt_def_id).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|item| {
            matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn)
                && has_raw_ptr_write(tcx, *item)
        })
    });

    if writes && type_implements_clone(tcx, ty) {
        CheckResult::Failed
    } else {
        CheckResult::Proved
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

/// Type-level `AtomicUpdate` obligation check (no VM state required).
pub(crate) fn atomic_update_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    match find_unsynchronized_mutation(tcx, ty) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Structurally check whether `ty` (transitively) contains one of the negative
/// types identified by `negative_defs`.
fn type_structurally_contains<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    negative_defs: &[DefId],
) -> Contains {
    match ty.kind() {
        TyKind::Adt(adt_def, substs) => {
            if negative_defs.contains(&adt_def.did()) {
                return Contains::Yes;
            }
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
                result = result.join(type_structurally_contains(tcx, field_ty, negative_defs));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(type_structurally_contains(tcx, subst_ty, negative_defs));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            type_structurally_contains(tcx, *inner, negative_defs)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(type_structurally_contains(tcx, t, negative_defs))
        }),
        TyKind::Param(_) => Contains::Maybe,
        _ => Contains::No,
    }
}

/// Find an interior-mutability / raw-pointer field that is not guarded by a
/// synchronization primitive.  A raw pointer may also appear as a pattern type
/// (`pattern_type!(*const T is ..)`), so recurse into `TyKind::Pat`.
fn find_unsynchronized_mutation<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_unsynchronized_mutation(tcx, *inner),
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
                result = result.join(find_unsynchronized_mutation(tcx, field_ty));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(find_unsynchronized_mutation(tcx, subst_ty));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            find_unsynchronized_mutation(tcx, *inner)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(find_unsynchronized_mutation(tcx, t))
        }),
        TyKind::Param(_) => Contains::Maybe,
        _ => Contains::No,
    }
}
