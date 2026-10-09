//! Shared helpers for the property checkers.
//!
//! Argument/place resolution (`target_value`, `eval_contract_expr`), the
//! `smt_check` "negate and prove" primitive, and size/byte-width utilities used
//! by every checker family.

use crate::helpers::mir_utils;
use crate::def_id;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::{
    ContractExpr, ContractPlace, ContractProjection, NumericBinOp, PlaceBase, Property,
    PropertyArg, RelOp,
};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::{VmState, VmValue};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind};
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::ty::{GenericArg, GenericArgKind, Ty, TyKind};
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

/// Resolve a callee `Local(n)` to the corresponding checkpoint operand, using
/// the callee's real argument count. Returns `None` when the checkpoint has no
/// callee or `n` is not an argument local.
pub(super) fn local_param_operand<'a, 'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    ck: &'a Checkpoint<'tcx>,
    n: usize,
) -> Option<&'a Operand<'tcx>> {
    let callee = ck.callee?;
    let idx = mir_utils::callee_param_index_for_local(vm_state.tcx, callee, n)?;
    ck.args.get(idx)
}

impl PropertyChecker {
    pub(super) fn ty_arg<'tcx>(property: &Property<'tcx>, idx: usize) -> Option<Ty<'tcx>> {
        property.args().get(idx).and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        })
    }

    pub(super) fn target_value<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        self.target_value_raw(vm_state, checkpoint, property)
    }

    /// Resolve the target place to a `VmValue`, without pointer provenance
    /// penetration (see [`Self::resolve_pointer_provenance`]).
    fn target_value_raw<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Const(n)) => {
                let idx = usize::try_from(*n).ok()?;
                crate::verify::contract::ContractPlace {
                    base: PlaceBase::Arg(idx),
                    projections: vec![],
                }
            }
            PropertyArg::Predicates(_) | PropertyArg::Ty(_) | PropertyArg::Ident(_) => return None,
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(cp) => cp.clone(),
                _ => return None,
            },
            _ => return None,
        };
        if cp.projections.is_empty() {
            return match cp.base {
                PlaceBase::Return => vm_state.local_value(Local::from_usize(0)).cloned(),
                PlaceBase::Arg(n) => {
                    let operand = checkpoint.args.get(n)?;
                    Some(vm_state.value_of_operand(operand))
                }
                PlaceBase::Local(n) => vm_state.local_value(Local::from_usize(n)).cloned(),
            };
        }
        let base_local = match cp.base {
            PlaceBase::Return => Local::from_usize(0),
            PlaceBase::Arg(n) => {
                let operand = checkpoint.args.get(n)?;
                match operand {
                    Operand::Copy(place) | Operand::Move(place) => place.local,
                    _ => return None,
                }
            }
            PlaceBase::Local(n) => Local::from_usize(n),
        };
        let mut field_path: Vec<usize> = Vec::new();
        let mut last_field_ty: Option<Ty<'tcx>> = None;

        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index, ty } => {
                    field_path.push(*index);
                    last_field_ty = *ty;
                }
                ContractProjection::Downcast { variant_index } => {
                    let base_val = vm_state
                        .field_value(base_local, &field_path)
                        .cloned()
                        .or_else(|| vm_state.local_value(base_local).cloned());
                    let Some(base_val) = base_val else {
                        return None;
                    };

                    let enum_ty = last_field_ty.unwrap_or(base_val.ty);
                    let inner_ty = match enum_ty.kind() {
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum() {
                                let variant = &adt_def.variants()
                                    [rustc_abi::VariantIdx::from_usize(*variant_index)];
                                if !variant.fields.is_empty() {
                                    Some(mir_utils::field_ty(
                                        vm_state.tcx,
                                        &variant.fields[rustc_abi::FieldIdx::from_usize(0)],
                                        substs,
                                    ))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    let inner_ty = inner_ty.unwrap_or(base_val.ty);

                    return Some(VmValue {
                        z3_term: base_val.z3_term.clone(),
                        ty: inner_ty,
                        provenance: base_val.provenance.clone(),
                        facts: base_val.facts,
                        source: base_val.source.field_offset_only(),
                    });
                }
                ContractProjection::ForEach => {
                    // iter() projections: try to resolve the base field and
                    // return the base value (iterator elements handled elsewhere).
                    if let Some(val) = vm_state.field_value(base_local, &field_path) {
                        return Some(val.clone());
                    }
                    if let Some(base_val) = vm_state.local_value(base_local)
                        && base_val.is_pointer() {
                            return Some(VmValue {
                                z3_term: base_val.z3_term.clone(),
                                ty: base_val.ty,
                                provenance: base_val.provenance.clone(),
                                facts: base_val.facts.clone(),
                                source: base_val.source.field_offset_only(),
                            });
                        }
                    return None;
                }
            }
        }

        // All projections were Field (or no projections)
        if let Some(val) = vm_state.field_value(base_local, &field_path) {
            return Some(val.clone());
        }
        // Fallback: if the field value is not set (e.g. constructor return
        // value _0 whose Aggregate was not executed), resolve from MIR.
        if !field_path.is_empty() && base_local == Local::from_usize(0) {
            for bb in vm_state.body().basic_blocks.iter() {
                for stmt in &bb.statements {
                    if let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind {
                        let (ref place, ref rval) = **assign;
                        if let rustc_middle::mir::Rvalue::Aggregate(_, operands) = rval
                            && place.local == base_local
                                && let Some(operand) =
                                    operands.get(rustc_abi::FieldIdx::from_usize(field_path[0]))
                                {
                                    let val = vm_state.value_of_operand(operand);
                                    if field_path.len() == 1 {
                                        return Some(val);
                                    }
                                }
                    }
                }
            }
        }
        if let Some(base_val) = vm_state.local_value(base_local)
            && let Some(ref prov) = base_val.provenance {
                return Some(VmValue {
                    z3_term: base_val.z3_term.clone(),
                    ty: base_val.ty,
                    provenance: Some(prov.clone()),
                    facts: base_val.facts.clone(),
                    source: base_val.source.field_offset_only(),
                });
            }
        None
    }

    /// Penetrate a reference/raw-pointer target down to the owned heap behind
    /// it.  A target like `&mut ManuallyDrop<Box<T>>` or `*mut Box<T>` carries
    /// the *stack* provenance of the referent; the properties that matter
    /// (`Allocated`/`Owning`/`ValidPtr`) concern the heap object inside, so
    /// resolve through the referent local's owned heap field.
    pub(super) fn resolve_pointer_provenance<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        mut value: VmValue<'z3, 'tcx>,
    ) -> VmValue<'z3, 'tcx> {
        if matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Ref(..) | rustc_middle::ty::TyKind::RawPtr(..)
        )
            && let Some(owner) = vm_state.find_local_by_address(&value.z3_term)
                && let Some(heap_field) = vm_state.owner_ptr_field(owner)
                    && heap_field.is_pointer() {
                        value.z3_term = heap_field.z3_term.clone();
                        value.provenance = heap_field.provenance.clone();
                        value.facts = heap_field.facts.clone();
                    }
        value
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
        use crate::verify::def_use::{PlaceBaseKey, PlaceKey};
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
                    && term_zero == 0 {
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
            SatResult::Unknown => CheckResult::Unknown(UnknownReason::SmtTimeout),
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
        solver.pop(1);

        solver.push();
        vm_state.assert_all(&solver);
        solver.assert(&elem_size.ge(&one));
        solver.assert(goal_negated);
        let r_non_zst = solver.check();
        solver.pop(1);

        match (r_zst, r_non_zst) {
            (SatResult::Unsat, SatResult::Unsat) => CheckResult::ProvedBySmt,
            (SatResult::Sat, _) | (_, SatResult::Sat) => on_sat,
            _ => CheckResult::Unknown(UnknownReason::SmtTimeout),
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
                match cp.base {
                    PlaceBase::Arg(n) => {
                        let op = checkpoint.args.get(n)?;
                        Some(vm_state.value_of_operand(op).z3_term)
                    }
                    PlaceBase::Local(n) => {
                        // The Local(N) refers to the callee's parameter. Map to
                        // the callsite's corresponding Arg via the callee's real
                        // signature (falling back to the VM local when there is
                        // no callee — e.g. a synthetic checkpoint — or `n` is a
                        // temporary rather than a parameter).
                        if let Some(op) = local_param_operand(vm_state, checkpoint, n) {
                            Some(vm_state.value_of_operand(op).z3_term)
                        } else {
                            vm_state
                                .local_value(Local::from_usize(n))
                                .map(|v| v.z3_term.clone())
                        }
                    }
                    PlaceBase::Return => None,
                }
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
        // Element size as a symbolic term.  A concrete contract `T` uses its
        // constant byte size; a generic `T` falls back to the target pointer's
        // own pointee type (which may resolve to the call-site concrete type,
        // e.g. `from_raw_parts::<u32>`), and only then to the symbolic `sizeof_T`.
        let elem_ty = property
            .args()
            .get(ty_arg)
            .and_then(|a| {
                if let PropertyArg::Ty(ty) = a {
                    Some(*ty)
                } else {
                    None
                }
            })
            .filter(|ty| vm_state.size_of_ty(*ty) > 0)
            .or_else(|| {
                // Two-argument form (`Init(self, n)`, no `T`): derive the
                // element type from the target's pointee, peeling `[T]` /
                // `[T; N]` down to `T` so `n * sizeof(elem)` is computed.
                mir_utils::pointee_ty(value.ty).map(|ty| match ty.kind() {
                    rustc_middle::ty::TyKind::Slice(e) | rustc_middle::ty::TyKind::Array(e, _) => {
                        *e
                    }
                    _ => ty,
                })
            });
        let elem_size_term = elem_ty
            .map(|ty| vm_state.size_sym_read(ty))
            .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));

        let count_term = property
            .args()
            .get(count_arg)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
        // Simplify the multiplication for concrete count and elem_size
        if let (Some(elem), Some(count)) = (
            elem_size_term.simplify().as_u64(),
            count_term.simplify().as_u64(),
        ) {
            return Int::from_u64(vm_state.z3_ctx, elem.max(1) * count.max(1));
        }
        Int::mul(vm_state.z3_ctx, &[&elem_size_term, &count_term])
    }

    pub(super) fn zst_guard<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let required_ty = Self::ty_arg(property, 1);
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
        let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
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

    pub(super) fn instantiate_callsite_ty<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let TyKind::Param(param) = ty.kind() else {
            return ty;
        };
        // A synthetic checkpoint (raw-ptr-deref, static-mut, type-invariant) has
        // no callee: its property type args are already the caller's own types.
        // Resolving them through `checkpoint.block`'s terminator would pick up an
        // *unrelated* neighbouring call (e.g. the `same_bucket` closure call for a
        // `&mut *ptr_write` deref), mapping `T` to the closure type `F`.
        if checkpoint.callee.is_none() {
            return ty;
        };

        let body = vm_state.body();
        let terminator = body.basic_blocks[checkpoint.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return ty;
        };
        let Operand::Constant(func_constant) = func else {
            return ty;
        };
        let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
            return ty;
        };
        let Some(arg) = crate::compat::args_get(args, param.index as usize) else {
            return ty;
        };
        match arg.kind() {
            GenericArgKind::Type(actual_ty) => actual_ty,
            _ => ty,
        }
    }

    pub(super) fn instantiate_callsite_const<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        index: u32,
    ) -> Option<u128> {
        let body = vm_state.body();
        let terminator = body.basic_blocks[checkpoint.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return None;
        };
        let Operand::Constant(func_constant) = func else {
            return None;
        };
        let TyKind::FnDef(_, args) = func_constant.const_.ty().kind() else {
            return None;
        };
        let arg = crate::compat::args_get(args, index as usize)?;
        match arg.kind() {
            GenericArgKind::Const(actual_const) => actual_const
                .try_to_target_usize(vm_state.tcx)
                .map(|value| value as u128)
                .or_else(|| {
                    mir_utils::const_int_from_debug(&format!("{actual_const:?}"))
                        .map(|v| v as u128)
                }),
            _ => None,
        }
    }

    pub(super) fn resolve_ty_params<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Param(_) => self.instantiate_callsite_ty(vm_state, checkpoint, ty),
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
        match expr {
            ContractExpr::Const(n) => Some(Int::from_u64(vm_state.z3_ctx, *n as u64)),
            ContractExpr::SizeOf(ty) => {
                let mut size = vm_state.size_of_ty(*ty);
                if size == 0 && matches!(ty.kind(), rustc_middle::ty::TyKind::Param(_)) {
                    size = mir_utils::size_of_generic_param(
                        vm_state.tcx,
                        vm_state.current_frame.current_def_id,
                        *ty,
                    );
                    if size == 0
                        && let Some(ck) = checkpoint
                            && let Some(_callee) = ck.callee
                                && !self.is_caller_type_param(vm_state, *ty) {
                                    let resolved = self.instantiate_callsite_ty(vm_state, ck, *ty);
                                    if resolved != *ty {
                                        size = vm_state.size_of_ty(resolved);
                                    }
                                }
                }
                if size > 0 {
                    Some(Int::from_u64(vm_state.z3_ctx, size))
                } else {
                    Some(Int::from_u64(vm_state.z3_ctx, 0))
                }
            }
            ContractExpr::AlignOf(ty) => {
                let align = vm_state.align_of_ty(*ty);
                if align > 0 {
                    Some(Int::from_u64(vm_state.z3_ctx, align.max(1)))
                } else {
                    Some(Int::from_u64(vm_state.z3_ctx, 0))
                }
            }
            ContractExpr::Place(cp) => self.eval_contract_place(vm_state, checkpoint, cp),
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_contract_expr(vm_state, checkpoint, lhs)?;
                let r = self.eval_contract_expr(vm_state, checkpoint, rhs)?;
                match op {
                    NumericBinOp::Add => Some(Int::add(vm_state.z3_ctx, &[&l, &r])),
                    NumericBinOp::Sub => Some(Int::sub(vm_state.z3_ctx, &[&l, &r])),
                    NumericBinOp::Mul => Some(Int::mul(vm_state.z3_ctx, &[&l, &r])),
                    NumericBinOp::Div | NumericBinOp::Rem => {
                        // Z3 division by zero yields unconstrained results,
                        // leading to unsound proofs downstream. When the
                        // divisor is zero (e.g. size_of::<T>() for generic
                        // or ZST params), return zero so that subsequent
                        // access_bytes computes 0 * elem_size == 0.
                        if r.as_u64() == Some(0) {
                            Some(Int::from_u64(vm_state.z3_ctx, 0))
                        } else if matches!(op, NumericBinOp::Div) {
                            Some(l.div(&r))
                        } else {
                            let q = l.div(&r);
                            Some(Int::sub(
                                vm_state.z3_ctx,
                                &[&l, &Int::mul(vm_state.z3_ctx, &[&q, &r])],
                            ))
                        }
                    }
                    NumericBinOp::Min => Some(l.le(&r).ite(&l, &r)),
                    NumericBinOp::Max => Some(l.ge(&r).ite(&l, &r)),
                    _ => None,
                }
            }
            ContractExpr::Unary { op, expr: inner } => {
                let v = self.eval_contract_expr(vm_state, checkpoint, inner)?;
                match op {
                    crate::verify::contract::NumericUnaryOp::Not => {
                        Some(v._eq(&Int::from_u64(vm_state.z3_ctx, 0)).ite(
                            &Int::from_u64(vm_state.z3_ctx, 1),
                            &Int::from_u64(vm_state.z3_ctx, 0),
                        ))
                    }
                    crate::verify::contract::NumericUnaryOp::Neg => {
                        let zero = Int::from_u64(vm_state.z3_ctx, 0);
                        Some(Int::sub(vm_state.z3_ctx, &[&zero, &v]))
                    }
                }
            }
            ContractExpr::Len(inner) => {
                if let Some(ck) = checkpoint
                    && let Some(term) = self.try_iter_len_from_fields(vm_state, ck, inner) {
                        return Some(term);
                    }
                let val = self.eval_contract_expr_to_value(vm_state, checkpoint, inner)?;
                // A struct (e.g. `NodeRef`) whose `len()` reads `(*x.field).len`
                // through a `NonNull` field.
                if let crate::verify::contract::ContractExpr::Place(cp) = &**inner
                    && let Some(field_path) = cp.plain_field_path() {
                        let base_local =
                            match cp.base {
                                PlaceBase::Return => Some(Local::from_usize(0)),
                                PlaceBase::Local(n) => Some(Local::from_usize(n)),
                                PlaceBase::Arg(n) => checkpoint
                                    .and_then(|ck| ck.args.get(n))
                                    .and_then(|op| match op {
                                        Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                                        _ => None,
                                    }),
                            };
                        if let Some(local) = base_local
                            && let Some(len) =
                                vm_state.try_struct_nn_len_field(local, &field_path, val.ty)
                            {
                                return Some(len);
                            }
                    }
                vm_state.len_from_value(&val)
            }
            ContractExpr::ConstParam { index, name: _ } => self
                .instantiate_callsite_const(vm_state, checkpoint?, *index)
                .and_then(|v| u64::try_from(v).ok())
                .map(|v| Int::from_u64(vm_state.z3_ctx, v)),
            ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let l = self.eval_contract_expr(vm_state, checkpoint, &cond.lhs)?;
                let r = self.eval_contract_expr(vm_state, checkpoint, &cond.rhs)?;
                let cond_bool = match cond.op {
                    RelOp::Eq => l._eq(&r),
                    RelOp::Ne => l._eq(&r).not(),
                    RelOp::Le => l.le(&r),
                    RelOp::Lt => l.lt(&r),
                    RelOp::Ge => l.ge(&r),
                    RelOp::Gt => l.gt(&r),
                };
                // When the condition is concretely true/false, short-circuit to
                // the taken branch so the result is a concrete term (otherwise an
                // `ite(true, a, b)` stays symbolic and downstream `as_u64()`
                // checks fail, e.g. the `count == 0` fast-path in check_in_bound).
                match cond_bool.simplify().as_bool() {
                    Some(true) => self.eval_contract_expr(vm_state, checkpoint, then_expr),
                    Some(false) => self.eval_contract_expr(vm_state, checkpoint, else_expr),
                    _ => {
                        let t = self.eval_contract_expr(vm_state, checkpoint, then_expr)?;
                        let e = self.eval_contract_expr(vm_state, checkpoint, else_expr)?;
                        Some(cond_bool.ite(&t, &e))
                    }
                }
            }
            _ => None,
        }
    }

    pub(super) fn eval_contract_expr_to_value<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => {
                if cp.projections.is_empty() {
                    return match cp.base {
                        PlaceBase::Return => vm_state.local_value(Local::from_usize(0)).cloned(),
                        PlaceBase::Arg(n) => checkpoint?
                            .args
                            .get(n)
                            .map(|op| vm_state.value_of_operand(op)),
                        PlaceBase::Local(n) => {
                            let ck = checkpoint?;
                            if let Some(op) = local_param_operand(vm_state, ck, n) {
                                return Some(vm_state.value_of_operand(op));
                            }
                            vm_state.local_value(Local::from_usize(n)).cloned()
                        }
                    };
                }
                // Field projections: resolve the base local, then read the
                // materialized field value (mirrors `target_value`). This is
                // what lets `InBound(v, T, v.len())` resolve `Len(v)` for a
                // struct field `v` (e.g. a `*mut [T]` slice field on the
                // constructed return value).
                let base_local = match cp.base {
                    PlaceBase::Return => Local::from_usize(0),
                    PlaceBase::Arg(n) => {
                        let op = checkpoint?.args.get(n)?;
                        match op {
                            Operand::Copy(p) | Operand::Move(p) => p.local,
                            _ => return None,
                        }
                    }
                    PlaceBase::Local(n) => Local::from_usize(n),
                };
                let field_path = cp.plain_field_path()?;
                vm_state.field_value(base_local, &field_path).cloned()
            }
            _ => None,
        }
    }

    pub(super) fn eval_contract_place<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        cp: &crate::verify::contract::ContractPlace<'tcx>,
    ) -> Option<Int<'z3>> {
        // Collect numeric field projections.  Any non-field projection (e.g. a
        // `Downcast` or `ForEach`) cannot be resolved to a scalar, so the
        // place does not evaluate.
        let field_path = cp.plain_field_path()?;

        let base_local: Option<Local> = match cp.base {
            PlaceBase::Return => Some(Local::from_usize(0)),
            PlaceBase::Arg(n) => {
                if field_path.is_empty() {
                    return checkpoint.and_then(|ck| {
                        let op = ck.args.get(n)?;
                        self.eval_contract_operand(vm_state, op)
                    });
                }
                // A field projection of an argument: resolve the argument
                // operand to its underlying local so the field can be read.
                checkpoint
                    .and_then(|ck| ck.args.get(n))
                    .and_then(|op| match op {
                        Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                        _ => None,
                    })
            }
            PlaceBase::Local(n) => {
                if field_path.is_empty()
                    && let Some(ck) = checkpoint
                        && let Some(op) = local_param_operand(vm_state, ck, n)
                            && let Some(v) = self.eval_contract_operand(vm_state, op) {
                                return Some(v);
                            }
                Some(Local::from_usize(n))
            }
        };

        let local = base_local?;
        if field_path.is_empty() {
            vm_state.local_value(local).map(|v| v.z3_term.clone())
        } else {
            vm_state
                .field_value(local, &field_path)
                .map(|v| v.z3_term.clone())
        }
    }

    pub(super) fn eval_contract_operand<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Int<'z3>> {
        match op {
            Operand::Constant(c) => {
                let const_text = format!("{:?}", c.const_);
                let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
                if let Ok(val) = c
                    .const_
                    .eval(vm_state.tcx, typing_env, rustc_span::DUMMY_SP)
                    && let Some(scalar) = val.try_to_scalar_int() {
                        let v = scalar.to_bits(scalar.size()) as u64;
                        if v == 0
                            && (const_text.contains("AlignOf")
                                || const_text.contains("SizeOf")
                                || const_text.contains("min_align_of")
                                || const_text.contains("min_size_of"))
                        {
                            // Generic AlignOf/SizeOf may evaluate to 0 but
                            // are always >= 1 for non-ZST types. Fall through
                            // to the debug text path below.
                        } else {
                            return Some(Int::from_u64(vm_state.z3_ctx, v));
                        }
                    }
                mir_utils::const_int_from_debug(&const_text)
                    .map(|v| Int::from_u64(vm_state.z3_ctx, v))
            }
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                vm_state.local_value(p.local).map(|v| v.z3_term.clone())
            }
            _ => None,
        }
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
        // If this local is a parameter (arg), use it directly
        if local.as_usize() <= vm_state.body().arg_count {
            return vm_state.value_of_operand(op);
        }
        // Trace through simple Use assignments
        for block in vm_state.body().basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local && dest.projection.is_empty() {
                        #[cfg(rapx_rvalue_use_with_retag)]
                        if let Rvalue::Use(src_op, _) = rvalue {
                            return self.trace_value(vm_state, src_op);
                        }
                        #[cfg(not(rapx_rvalue_use_with_retag))]
                        if let Rvalue::Use(src_op) = rvalue {
                            return self.trace_value(vm_state, src_op);
                        }
                    }
                }
            }
        }
        vm_state.value_of_operand(op)
    }

    pub(super) fn alloc_elem_is_array_of<'tcx>(
        &self,
        alloc_elem_ty: Ty<'tcx>,
        required_ty: Ty<'tcx>,
    ) -> bool {
        match alloc_elem_ty.kind() {
            TyKind::Array(inner_ty, _) => {
                *inner_ty == required_ty
                    || matches!(
                        (inner_ty.kind(), required_ty.kind()),
                        (TyKind::Param(_), TyKind::Param(_))
                    )
            }
            TyKind::Slice(inner_ty) => {
                *inner_ty == required_ty
                    || matches!(
                        (inner_ty.kind(), required_ty.kind()),
                        (TyKind::Param(_), TyKind::Param(_))
                    )
            }
            _ => false,
        }
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
                || def_id::rc_types().contains(&did)
            {
                args.types().next()
            } else {
                None
            }
        }
        _ => None,
    }
}
