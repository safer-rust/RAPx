//! Checkers for the `Send`/`Sync` marker-trait predicates.
//!
//! These are intentionally *structural/behavioural* approximations
//! (sound-incomplete): a full proof of "exclusive ownership" / "no cross-thread
//! aliasing" needs an ownership + concurrency model (e.g. separation logic),
//! which the current sequential VM does not have.
//!
//! The vocabulary follows the Rust model: a raw pointer is `!Send` unless
//! *tamed* — [`NoRawPtr`], or [`TamedRawPtr`] (the pointer is `Allocated`,
//! `Owning`, and either read-only [`NoInternalMut`] or exclusively mutated
//! [`UniInternalMut`]).  The `Allocated`/`Owning` halves are discharged by the
//! struct's `#[rapx::invariant]` annotations (verified by the VM), so
//! [`TamedRawPtr`] only checks that those invariants are present plus the
//! interior-mutability behaviour.

#[cfg(not(rapx_ge_100))]
use rustc_hir::LangItem;
#[cfg(rapx_ge_100)]
use rustc_hir::attrs::lang_items::LangItem;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgKind, Ty, TyCtxt, TyKind};
use z3::Solver;

use crate::compat::FxHashMap;
use crate::helpers::mir_scan::{Checkpoint, has_raw_ptr_write};
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

    /// `NoRawPtr(T)`: `T` must have no raw pointers.
    pub(super) fn check_no_raw_ptr<'ctx, 'tcx>(
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
        no_raw_ptr_check(vm_state.tcx, ty)
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

    /// `TamedRawPtr(T)`: `T`'s raw pointers are tamed (`Allocated` ∧ `Owning` ∧
    /// (`NoInternalMut` ∨ `UniInternalMut`)).
    pub(super) fn check_tamed_raw_ptr<'ctx, 'tcx>(
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
        tamed_raw_ptr_check(vm_state.tcx, ty, &FxHashMap::default())
    }

    /// `RefSend(T)`: every interior-mutability (`UnsafeCell`) / raw-pointer
    /// field of `T` must be guarded by a synchronization primitive.
    pub(super) fn check_ref_send<'ctx, 'tcx>(
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
        ref_send_check(vm_state.tcx, ty)
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

/// Type-level `NoRawPtr` obligation check (no VM state required).
pub(crate) fn no_raw_ptr_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    match find_raw_ptr(tcx, ty) {
        Contains::Yes => CheckResult::Failed,
        Contains::Maybe => CheckResult::Unknown,
        Contains::No => CheckResult::Proved,
    }
}

/// Type-level `NoInternalMut` obligation check (no VM state required): `Failed`
/// if any inherent method writes through a raw pointer.
pub(crate) fn no_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if has_raw_ptr_writes(tcx, ty) {
        CheckResult::Failed
    } else {
        CheckResult::Proved
    }
}

/// Type-level `UniInternalMut` obligation check (no VM state required): `Proved`
/// if the type writes through a raw pointer but does not implement `Clone`
/// (which would copy the pointer and alias the pointee).
pub(crate) fn uni_internal_mut_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    if has_raw_ptr_writes(tcx, ty) && !type_implements_clone(tcx, ty) {
        CheckResult::Proved
    } else {
        CheckResult::Failed
    }
}

/// Type-level `TamedRawPtr` obligation check (no VM state required).
///
/// The `Allocated`/`Owning` halves are discharged by the struct's
/// `#[rapx::invariant]` annotations.  `invariant_results` carries the per-struct
/// verdict of the (already-run) struct-invariant verification; when a struct's
/// invariants failed to verify, its `TamedRawPtr` fails too.
pub(crate) fn tamed_raw_ptr_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: Ty<'tcx>,
    invariant_results: &FxHashMap<DefId, CheckResult>,
) -> CheckResult {
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return CheckResult::Proved;
    };
    let adt_def_id = adt_def.did();

    let invariants = get_struct_invariants_from_annotation(tcx, adt_def_id, adt_def_id);
    let has_owning = invariants.iter().any(|p| p.kind() == Some(PropertyKind::Owning));
    let has_allocated = invariants
        .iter()
        .any(|p| p.kind() == Some(PropertyKind::Allocated));
    if !has_owning || !has_allocated {
        return CheckResult::Failed;
    }

    // The invariants must actually hold, not just be annotated.
    if let Some(result) = invariant_results.get(&adt_def_id) {
        if *result != CheckResult::Proved {
            return CheckResult::Failed;
        }
    }

    if no_internal_mut_check(tcx, ty) == CheckResult::Proved
        || uni_internal_mut_check(tcx, ty) == CheckResult::Proved
    {
        CheckResult::Proved
    } else {
        CheckResult::Failed
    }
}

/// Type-level `RefSend` obligation check (no VM state required).
pub(crate) fn ref_send_check<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CheckResult {
    match find_unsynchronized_mutation(tcx, ty) {
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

/// Structurally check whether `ty` (transitively) contains a raw pointer.
/// A raw pointer may also appear as a pattern type (`pattern_type!(*const T
/// is ..)`), so recurse into `TyKind::Pat`.
fn find_raw_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Contains {
    match ty.kind() {
        TyKind::RawPtr(..) => Contains::Yes,
        TyKind::Pat(inner, _) => find_raw_ptr(tcx, *inner),
        TyKind::Adt(adt_def, substs) => {
            let mut result = Contains::No;
            for field in adt_def.all_fields() {
                let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, substs);
                result = result.join(find_raw_ptr(tcx, field_ty));
                if result == Contains::Yes {
                    return Contains::Yes;
                }
            }
            for subst in substs.iter() {
                if let GenericArgKind::Type(subst_ty) = subst.kind() {
                    result = result.join(find_raw_ptr(tcx, subst_ty));
                    if result == Contains::Yes {
                        return Contains::Yes;
                    }
                }
            }
            result
        }
        TyKind::Ref(_, inner, _) | TyKind::Slice(inner) | TyKind::Array(inner, _) => {
            find_raw_ptr(tcx, *inner)
        }
        TyKind::Tuple(tys) => tys.iter().fold(Contains::No, |acc, t| {
            acc.join(find_raw_ptr(tcx, t))
        }),
        TyKind::Param(_) => Contains::Maybe,
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
