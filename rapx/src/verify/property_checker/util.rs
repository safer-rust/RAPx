//! Shared helpers for the property checkers.
//!
//! Argument/place resolution (`target_value`, `eval_contract_expr`), the
//! `smt_check` "negate and prove" primitive, and size/byte-width utilities used
//! by every checker family.

use crate::def_ids::type_ids;
use crate::helpers::def_use::{PlaceBaseKey, PlaceKey};
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::{
    ContractExpr, ContractPlace, ContractProjection, Property, PropertyArg,
};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::contract_eval::ContractEvalContext;
use crate::verify::vm::query::ContractTargetContext;
use crate::verify::vm::state::{VmState, VmValue};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{GenericArg, GenericArgKind, Ty, TyKind};
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn target_value<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        vm_state.contract_target_value_at(ContractTargetContext::Callsite(checkpoint), property)
    }

    /// Implicit vacuous truth for projected targets.
    ///
    /// A property over `x.unwrap_some()` / `x.iter()` talks about the contents
    /// of an `Option`/container; when that container resolves to no allocation
    /// (e.g. `Option::None`, an empty or unmodeled container) there is no
    /// element to check, so the property holds vacuously.  The explicit
    /// counterpart is the `Null(p)` guard ([`Self::is_null`]), which the user
    /// writes via `any(Null(p), …)`.
    pub(super) fn is_vacuously_true_for_nullable<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let cp = match property.args().first() {
            Some(PropertyArg::Expr(crate::verify::contract::ContractExpr::Place(cp))) => cp,
            _ => return false,
        };
        let has_nullable_proj = cp.projections.iter().any(|p| {
            matches!(
                p,
                ContractProjection::Downcast { .. } | ContractProjection::ForEach
            )
        });
        if !has_nullable_proj {
            return false;
        }
        match self.target_value(vm_state, checkpoint, property) {
            Some(val) => val.provenance.is_none(),
            None => true,
        }
    }

    /// Whether `place` is null, in the vacuity sense of the `Null(p)` guard:
    /// true when the value provably equals 0, or carries no provenance and is
    /// not known non-null (e.g. an `Option::None` or an unmodeled value).  The
    /// implicit counterpart is [`Self::is_vacuously_true_for_nullable`], which
    /// handles `unwrap_some()` / `iter()` projections without an explicit
    /// guard.
    pub(super) fn is_null<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        place: &ContractPlace<'tcx>,
    ) -> bool {
        let key = PlaceKey::from_contract_place(place);
        let local = match key.base {
            PlaceBaseKey::Local(n) => Local::from_usize(n),
            PlaceBaseKey::Arg(n) => checkpoint
                .args
                .get(n)
                .and_then(|op| match op {
                    Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                    _ => None,
                })
                .unwrap_or(Local::from_usize(n + 1)),
            PlaceBaseKey::Return => Local::from_usize(0),
        };
        let val = if key.fields.is_empty() {
            vm_state.local_value(local).cloned()
        } else {
            vm_state.field_value(local, &key.fields).cloned()
        };
        match val {
            Some(v) => {
                // A pointer without a `non_null` fact is possibly null: either it
                // carries no provenance, or its provenance is an external
                // placeholder (a raw-pointer field/param), which does not imply
                // non-nullness.
                if !v.facts.non_null {
                    let possibly_null = match &v.provenance {
                        None => true,
                        Some(prov) => vm_state.alloc(prov.alloc_id).is_external(),
                    };
                    if possibly_null {
                        return true;
                    }
                }
                if let Some(term_zero) = v.z3_term.simplify().as_u64()
                    && term_zero == 0
                {
                    return true;
                }
                false
            }
            None => true,
        }
    }

    pub(super) fn smt_check<'z3>(
        &self,
        solver: &Solver<'z3>,
        condition: &Bool<'z3>,
    ) -> CheckResult {
        solver.push();
        solver.assert(condition);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => CheckResult::Failed,
            SatResult::Unknown => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        };
        solver.pop(1);
        r
    }

    /// Prove `goal_negated` is unsatisfiable under a case split on a *generic*
    /// element size `S`: the ZST branch (`S = 0`) and the non-ZST branch
    /// (`S ≥ 1`, where the `S` factor cancels).  Both branches must be UNSAT.
    /// `on_sat` is the result when either branch is satisfiable.
    pub(super) fn smt_check_size_split<'z3, 'tcx>(
        vm_state: &VmState<'z3, 'tcx>,
        elem_size: &Int<'z3>,
        goal_negated: &Bool<'z3>,
        on_sat: CheckResult,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.z3_ctx);
        let zero = Int::from_u64(vm_state.z3_ctx, 0);
        let one = Int::from_u64(vm_state.z3_ctx, 1);

        solver.push();
        vm_state.assert_all(&solver);
        solver.assert(&elem_size._eq(&zero));
        solver.assert(goal_negated);
        let r_zst = solver.check();
        let zst_reason = (r_zst == SatResult::Unknown).then(|| UnknownReason::from_solver(&solver));
        solver.pop(1);

        solver.push();
        vm_state.assert_all(&solver);
        solver.assert(&elem_size.ge(&one));
        solver.assert(goal_negated);
        let r_non_zst = solver.check();
        let non_zst_reason =
            (r_non_zst == SatResult::Unknown).then(|| UnknownReason::from_solver(&solver));
        solver.pop(1);

        match (r_zst, r_non_zst) {
            (SatResult::Unsat, SatResult::Unsat) => CheckResult::ProvedBySmt,
            (SatResult::Sat, _) | (_, SatResult::Sat) => on_sat,
            _ => CheckResult::Unknown(match (zst_reason, non_zst_reason) {
                (Some(left), Some(right)) => left.merge(right),
                (Some(reason), None) | (None, Some(reason)) => reason,
                (None, None) => unreachable!(),
            }),
        }
    }

    pub(super) fn resolve_arg_term<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        arg: &PropertyArg<'tcx>,
    ) -> Option<Int<'z3>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) if *n <= u64::MAX as u128 => {
                Some(Int::from_u64(vm_state.z3_ctx, *n as u64))
            }
            PropertyArg::Expr(ContractExpr::Place(cp)) => {
                vm_state.contract_place_term_at(checkpoint, cp)
            }
            PropertyArg::Expr(expr) => self.eval_contract_expr(vm_state, Some(checkpoint), expr),
            _ => None,
        }
    }

    /// Whether the element-count argument (defaulting to `args[2]`, the
    /// `[Target, Ty, Expr]` layout) evaluates to the constant `0`, making any
    /// InBound/Allocated byte-range check trivially satisfied.  `count_arg`
    /// overrides the index for two-argument forms like `Init(self, n)`.
    pub(super) fn count_is_zero<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        count_arg: usize,
    ) -> bool {
        property
            .args()
            .get(count_arg)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            .and_then(|ct| ct.as_u64())
            == Some(0)
    }

    pub(super) fn access_bytes<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        property: &Property<'tcx>,
        ty_arg: usize,
        count_arg: usize,
        checkpoint: &Checkpoint<'tcx>,
        value: &VmValue<'z3, 'tcx>,
    ) -> Int<'z3> {
        let required_ty = property.ty_arg(ty_arg);
        let count = property
            .args()
            .get(count_arg)
            .and_then(|arg| self.resolve_arg_term(vm_state, checkpoint, arg))
            .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
        vm_state.access_bytes(value, required_ty, count)
    }

    pub(super) fn zst_guard<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let required_ty = property.ty_arg(1);
        self.is_zst_type(vm_state, checkpoint, required_ty)
    }

    pub(super) fn is_zst_type<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Option<Ty<'tcx>>,
    ) -> bool {
        let ty = match ty {
            Some(t) => t,
            None => return false,
        };
        if self.is_concrete_zst(vm_state, ty) {
            return true;
        }
        let resolved = vm_state.instantiate_callsite_ty(checkpoint, ty);
        if resolved != ty {
            return self.is_concrete_zst(vm_state, resolved);
        }
        false
    }

    pub(super) fn is_concrete_zst<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        !self.is_generic_ty(ty) && vm_state.size_of_ty(ty) == 0
    }

    pub(super) fn is_generic_ty<'tcx>(&self, ty: Ty<'tcx>) -> bool {
        matches!(
            ty.kind(),
            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_)
        )
    }

    pub(super) fn resolve_ty_params<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Param(_) => vm_state.instantiate_callsite_ty(checkpoint, ty),
            TyKind::Adt(adt_def, substs) => {
                let mut changed = false;
                let resolved_substs: Vec<_> = substs
                    .iter()
                    .map(|arg| match arg.kind() {
                        GenericArgKind::Type(t) => {
                            let resolved = self.resolve_ty_params(vm_state, checkpoint, t);
                            if resolved != t {
                                changed = true;
                                GenericArg::from(resolved)
                            } else {
                                arg
                            }
                        }
                        _ => arg,
                    })
                    .collect();
                if changed {
                    Ty::new_adt(
                        vm_state.tcx,
                        *adt_def,
                        vm_state.tcx.mk_args(&resolved_substs),
                    )
                } else {
                    ty
                }
            }
            _ => ty,
        }
    }

    pub(super) fn eval_contract_expr<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        vm_state.eval_contract_tree(expr, ContractEvalContext::Check(checkpoint))
    }

    pub(super) fn trace_value<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        op: &Operand<'tcx>,
    ) -> VmValue<'z3, 'tcx> {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return vm_state.value_of_operand(op),
        };
        if !place.projection.is_empty() {
            return vm_state.value_of_operand(op);
        }
        let local = place.local;
        if local.as_usize() <= vm_state.body().arg_count {
            return vm_state.value_of_operand(op);
        }
        for block in vm_state.body().basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local
                        && dest.projection.is_empty()
                        && let Rvalue::Use(src_op, ..) = rvalue
                    {
                        return self.trace_value(vm_state, src_op);
                    }
                }
            }
        }
        vm_state.value_of_operand(op)
    }
}

/// Unwrap `MaybeUninit<T>` to `T` (or `None` for any other type).  `MaybeUninit`
/// is `#[repr(transparent)]` over a union, so `MaybeUninit<T>` and `T` share
/// size and alignment.
pub(super) fn maybe_uninit_inner(ty: Ty<'_>) -> Option<Ty<'_>> {
    if let TyKind::Adt(adt_def, substs) = ty.kind()
        && crate::verify::api_classify::is_maybe_uninit_type(adt_def.did())
        && let Some(inner) = substs.first().and_then(|s| s.as_type())
    {
        return Some(inner);
    }
    None
}

/// Peel one level of smart-pointer indirection to the pointee type:
/// `Box<T>`/`Vec<T>`/`NonNull<T>`/`Rc<T>`/`CString` (matched by `DefId`), plus
/// raw pointers and references.  Used by `check_allocated` to discharge
/// `Allocated(p, Box<T>, n)` after provenance resolution has already penetrated
/// `p` (e.g. a `&mut ManuallyDrop<Box<T>>`) down to the `T` allocation: the
/// box's *pointee* is what actually occupies the allocation.
pub(super) fn smart_pointer_pointee(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => Some(*e),
        TyKind::Adt(adt, args) => {
            let did = adt.did();
            if crate::verify::api_classify::is_std_box(did)
                || crate::verify::api_classify::is_std_vec(did)
                || crate::verify::api_classify::is_std_nonnull(did)
                || crate::verify::api_classify::is_std_cstring(did)
                || type_ids::rc_types().contains(&did)
            {
                args.types().next()
            } else {
                None
            }
        }
        _ => None,
    }
}
