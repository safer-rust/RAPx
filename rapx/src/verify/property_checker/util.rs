//! Shared helpers for the property checkers.
//!
//! Argument/place resolution (`target_value`, `eval_contract_expr`), the
//! `smt_check` "negate and prove" primitive, and size/byte-width utilities used
//! by every checker family.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::{
    ContractExpr, ContractPlace, ContractProjection, NumericBinOp, PlaceBase, Property,
    PropertyArg, RelOp,
};
use crate::verify::report::CheckResult;
use crate::verify::vm::state::{VmState, VmValue};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{GenericArg, GenericArgKind, Ty, TyKind};
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

/// Resolve a callee `Local(n)` to the corresponding checkpoint operand, using
/// the callee's real argument count. Returns `None` when the checkpoint has no
/// callee or `n` is not an argument local.
fn local_param_operand<'a, 'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
    ck: &'a Checkpoint<'tcx>,
    n: usize,
) -> Option<&'a Operand<'tcx>> {
    let callee = ck.callee?;
    let idx = crate::helpers::mir_utils::callee_param_index_for_local(vm_state.tcx, callee, n)?;
    ck.args.get(idx)
}

impl PropertyChecker {
    pub(super) fn target_value<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'ctx, 'tcx>> {
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
                                    Some(crate::helpers::mir_utils::field_ty(
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
                        term: base_val.term.clone(),
                        ty: inner_ty,
                        provenance: base_val.provenance.clone(),
                        invariants: base_val.invariants,
                    });
                }
                ContractProjection::ForEach => {
                    // iter() projections: try to resolve the base field and
                    // return the base value (iterator elements handled elsewhere).
                    if let Some(val) = vm_state.field_value(base_local, &field_path) {
                        return Some(val.clone());
                    }
                    if let Some(base_val) = vm_state.local_value(base_local) {
                        if base_val.provenance.is_some() {
                            return Some(VmValue {
                                term: base_val.term.clone(),
                                ty: base_val.ty,
                                provenance: base_val.provenance.clone(),
                                invariants: base_val.invariants,
                            });
                        }
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
            for bb in vm_state.body.basic_blocks.iter() {
                for stmt in &bb.statements {
                    match &stmt.kind {
                        rustc_middle::mir::StatementKind::Assign(assign) => {
                            let (ref place, ref rval) = **assign;
                            if let rustc_middle::mir::Rvalue::Aggregate(_, operands) = rval {
                                if place.local == base_local {
                                    if let Some(operand) =
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
                        _ => {}
                    }
                }
            }
        }
        if let Some(base_val) = vm_state.local_value(base_local) {
            if let Some(ref prov) = base_val.provenance {
                return Some(VmValue {
                    term: base_val.term.clone(),
                    ty: base_val.ty,
                    provenance: Some(prov.clone()),
                    invariants: base_val.invariants,
                });
            }
        }
        None
    }

    /// Implicit vacuous truth for projected targets.
    ///
    /// A property over `x.unwrap_some()` / `x.iter()` talks about the contents
    /// of an `Option`/container; when that container resolves to no allocation
    /// (e.g. `Option::None`, an empty or unmodeled container) there is no
    /// element to check, so the property holds vacuously.  The explicit
    /// counterpart is the `Null(p)` guard ([`Self::is_null`]), which the user
    /// writes via `any(Null(p), …)`.
    pub(super) fn is_vacuously_true_for_nullable<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
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
    pub(super) fn is_null<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
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
                if v.provenance.is_none() && !v.invariants.non_null {
                    return true;
                }
                if let Some(term_zero) = v.term.simplify().as_u64() {
                    if term_zero == 0 {
                        return true;
                    }
                }
                false
            }
            None => true,
        }
    }

    pub(super) fn smt_check<'ctx>(
        &self,
        solver: &Solver<'ctx>,
        condition: &Bool<'ctx>,
    ) -> CheckResult {
        solver.push();
        solver.assert(condition);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat => CheckResult::Failed,
            SatResult::Unknown => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    pub(super) fn resolve_arg_term<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        arg: &PropertyArg<'tcx>,
    ) -> Option<Int<'ctx>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) if *n <= u64::MAX as u128 => {
                Some(Int::from_u64(vm_state.ctx, *n as u64))
            }
            PropertyArg::Expr(ContractExpr::Place(cp)) => {
                match cp.base {
                    PlaceBase::Arg(n) => {
                        let op = checkpoint.args.get(n)?;
                        Some(vm_state.value_of_operand(op).term)
                    }
                    PlaceBase::Local(n) => {
                        // The Local(N) refers to the callee's parameter.
                        // Map to the callsite's corresponding Arg(N-1).
                        let arg_idx = n.saturating_sub(1);
                        if arg_idx < checkpoint.args.len() {
                            let op = &checkpoint.args[arg_idx];
                            Some(vm_state.value_of_operand(op).term)
                        } else {
                            vm_state
                                .local_value(Local::from_usize(n))
                                .map(|v| v.term.clone())
                        }
                    }
                    PlaceBase::Return => None,
                }
            }
            PropertyArg::Expr(expr) => self.eval_contract_expr(vm_state, Some(checkpoint), expr),
            _ => None,
        }
    }

    /// Whether the element-count argument (`args[2]`) evaluates to the constant
    /// `0`, making any InBound/Allocated byte-range check trivially satisfied.
    pub(super) fn count_is_zero<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        property
            .args()
            .get(2)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            .and_then(|ct| ct.as_u64())
            == Some(0)
    }

    pub(super) fn access_bytes<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        property: &Property<'tcx>,
        ty_arg: usize,
        count_arg: usize,
        checkpoint: &Checkpoint<'tcx>,
        _value: &VmValue<'ctx, 'tcx>,
    ) -> Int<'ctx> {
        let elem_size = property
            .args()
            .get(ty_arg)
            .and_then(|a| {
                if let PropertyArg::Ty(ty) = a {
                    Some(vm_state.size_of_ty(*ty))
                } else {
                    None
                }
            })
            .unwrap_or(0);
        // When the contract uses a generic T (size_of returns 0), infer the
        // concrete element type from the checkpoint's target argument's pointee.
        let elem_size = if elem_size == 0 {
            checkpoint
                .args
                .first()
                .map(|op| {
                    let arg_val = vm_state.value_of_operand(op);
                    vm_state.pointee_elem_size(arg_val.ty)
                })
                .unwrap_or(0)
        } else {
            elem_size
        };
        let elem_size_term = Int::from_u64(vm_state.ctx, (elem_size as u64).max(1));

        let count_term = property
            .args()
            .get(count_arg)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            .unwrap_or_else(|| Int::from_u64(vm_state.ctx, 1));
        // Simplify the multiplication for concrete count and elem_size
        if let (Some(elem), Some(count)) = (Some(elem_size), count_term.simplify().as_u64()) {
            return Int::from_u64(vm_state.ctx, (elem as u64).max(1) * count.max(1));
        }
        Int::mul(vm_state.ctx, &[&elem_size_term, &count_term])
    }

    pub(super) fn zst_guard<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let required_ty = property.args().get(1).and_then(|a| {
            if let PropertyArg::Ty(ty) = a {
                Some(*ty)
            } else {
                None
            }
        });
        self.is_zst_type(vm_state, checkpoint, required_ty)
    }

    pub(super) fn is_zst_type<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
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

    pub(super) fn is_concrete_zst<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        match ty.kind() {
            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_) => false,
            _ => vm_state.size_of_ty(ty) == 0,
        }
    }

    pub(super) fn is_generic_ty<'tcx>(&self, ty: Ty<'tcx>) -> bool {
        matches!(
            ty.kind(),
            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_)
        )
    }

    pub(super) fn instantiate_callsite_ty<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let TyKind::Param(param) = ty.kind() else {
            return ty;
        };

        let body = vm_state.body;
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

    pub(super) fn instantiate_callsite_const<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        index: u32,
    ) -> Option<u128> {
        let body = vm_state.body;
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
                    crate::helpers::mir_utils::const_int_from_debug(&format!("{actual_const:?}"))
                        .map(|v| v as u128)
                }),
            _ => None,
        }
    }

    pub(super) fn resolve_ty_params<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
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
                                arg.clone()
                            }
                        }
                        _ => arg.clone(),
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

    pub(super) fn eval_contract_expr<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'ctx>> {
        match expr {
            ContractExpr::Const(n) => Some(Int::from_u64(vm_state.ctx, *n as u64)),
            ContractExpr::SizeOf(ty) => {
                let mut size = vm_state.size_of_ty(*ty);
                if size == 0 && matches!(ty.kind(), rustc_middle::ty::TyKind::Param(_)) {
                    size = crate::helpers::mir_utils::size_of_generic_param(
                        vm_state.tcx,
                        vm_state.caller_def_id,
                        *ty,
                    );
                    if size == 0 {
                        if let Some(ck) = checkpoint {
                            if let Some(_callee) = ck.callee {
                                if !self.is_caller_type_param(vm_state, *ty) {
                                    let resolved = self.instantiate_callsite_ty(vm_state, ck, *ty);
                                    if resolved != *ty {
                                        size = vm_state.size_of_ty(resolved);
                                    }
                                }
                            }
                        }
                    }
                }
                if size > 0 {
                    Some(Int::from_u64(vm_state.ctx, size as u64))
                } else {
                    Some(Int::from_u64(vm_state.ctx, 0))
                }
            }
            ContractExpr::AlignOf(ty) => {
                let align = vm_state.align_of_ty(*ty) as u64;
                if align > 0 {
                    Some(Int::from_u64(vm_state.ctx, align.max(1)))
                } else {
                    Some(Int::from_u64(vm_state.ctx, 0))
                }
            }
            ContractExpr::Place(cp) => self.eval_contract_place(vm_state, checkpoint, cp),
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_contract_expr(vm_state, checkpoint, lhs)?;
                let r = self.eval_contract_expr(vm_state, checkpoint, rhs)?;
                match op {
                    NumericBinOp::Add => Some(Int::add(vm_state.ctx, &[&l, &r])),
                    NumericBinOp::Sub => Some(Int::sub(vm_state.ctx, &[&l, &r])),
                    NumericBinOp::Mul => Some(Int::mul(vm_state.ctx, &[&l, &r])),
                    NumericBinOp::Div | NumericBinOp::Rem => {
                        // Z3 division by zero yields unconstrained results,
                        // leading to unsound proofs downstream. When the
                        // divisor is zero (e.g. size_of::<T>() for generic
                        // or ZST params), return zero so that subsequent
                        // access_bytes computes 0 * elem_size == 0.
                        if r.as_u64() == Some(0) {
                            Some(Int::from_u64(vm_state.ctx, 0))
                        } else if matches!(op, NumericBinOp::Div) {
                            Some(l.div(&r))
                        } else {
                            let q = l.div(&r);
                            Some(Int::sub(
                                vm_state.ctx,
                                &[&l, &Int::mul(vm_state.ctx, &[&q, &r])],
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
                        Some(v._eq(&Int::from_u64(vm_state.ctx, 0)).ite(
                            &Int::from_u64(vm_state.ctx, 1),
                            &Int::from_u64(vm_state.ctx, 0),
                        ))
                    }
                    crate::verify::contract::NumericUnaryOp::Neg => {
                        let zero = Int::from_u64(vm_state.ctx, 0);
                        Some(Int::sub(vm_state.ctx, &[&zero, &v]))
                    }
                }
            }
            ContractExpr::Len(inner) => {
                if let Some(ck) = checkpoint {
                    if let Some(term) = self.try_iter_len_from_fields(vm_state, ck, inner) {
                        return Some(term);
                    }
                }
                let val = self.eval_contract_expr_to_value(vm_state, checkpoint, inner)?;
                let alloc_id = val.provenance_alloc_id()?;
                let alloc = vm_state.alloc(alloc_id);
                let elem_ty = alloc.element_ty?;
                let elem_size = vm_state.size_of_ty(elem_ty).max(1) as u64;
                if elem_size == 1 {
                    return Some(alloc.size.clone());
                }
                let elem_term = Int::from_u64(vm_state.ctx, elem_size);
                Some(alloc.size.div(&elem_term))
            }
            ContractExpr::ConstParam { index, name: _ } => self
                .instantiate_callsite_const(vm_state, checkpoint?, *index)
                .and_then(|v| u64::try_from(v).ok())
                .map(|v| Int::from_u64(vm_state.ctx, v)),
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

    pub(super) fn eval_contract_expr_to_value<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'ctx, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
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
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn eval_contract_place<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        cp: &crate::verify::contract::ContractPlace<'tcx>,
    ) -> Option<Int<'ctx>> {
        // Collect numeric field projections.  Any non-field projection (e.g. a
        // `Downcast` or `ForEach`) cannot be resolved to a scalar, so the
        // place does not evaluate.
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index, .. } => field_path.push(*index),
                _ => return None,
            }
        }

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
                if field_path.is_empty() {
                    if let Some(ck) = checkpoint {
                        if let Some(op) = local_param_operand(vm_state, ck, n) {
                            if let Some(v) = self.eval_contract_operand(vm_state, op) {
                                return Some(v);
                            }
                        }
                    }
                }
                Some(Local::from_usize(n))
            }
        };

        let local = base_local?;
        if field_path.is_empty() {
            vm_state.local_value(local).map(|v| v.term.clone())
        } else {
            vm_state
                .field_value(local, &field_path)
                .map(|v| v.term.clone())
        }
    }

    pub(super) fn eval_contract_operand<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<Int<'ctx>> {
        match op {
            Operand::Constant(c) => {
                let const_text = format!("{:?}", c.const_);
                let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
                if let Ok(val) = c
                    .const_
                    .eval(vm_state.tcx, typing_env, rustc_span::DUMMY_SP)
                {
                    if let Some(scalar) = val.try_to_scalar_int() {
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
                            return Some(Int::from_u64(vm_state.ctx, v));
                        }
                    }
                }
                crate::helpers::mir_utils::const_int_from_debug(&const_text)
                    .map(|v| Int::from_u64(vm_state.ctx, v))
            }
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                vm_state.local_value(p.local).map(|v| v.term.clone())
            }
            _ => None,
        }
    }

    pub(super) fn trace_value<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>,
    ) -> VmValue<'ctx, 'tcx> {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return vm_state.value_of_operand(op),
        };
        if !place.projection.is_empty() {
            return vm_state.value_of_operand(op);
        }
        let local = place.local;
        // If this local is a parameter (arg), use it directly
        if local.as_usize() <= vm_state.body.arg_count {
            return vm_state.value_of_operand(op);
        }
        // Trace through simple Use assignments
        for block in vm_state.body.basic_blocks.iter() {
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
            _ => false,
        }
    }
}
