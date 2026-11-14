//! Contract expression evaluation over symbolic VM values.

use crate::helpers::mir_utils;
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::{ContractExpr, NumericBinOp, NumericUnaryOp, PlaceBase, RelOp};
use rustc_hir::def_id::DefId;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{
    mir::{Local, Operand, Place, TerminatorKind},
    ty::{GenericArgKind, Ty, TyKind},
};
use z3::ast::{Ast, Bool, Int};

use super::query::ContractTargetContext;
use super::state::{VmState, VmValue};

#[derive(Clone, Copy)]
pub(crate) enum ContractEvalContext<'a, 'tcx> {
    Facts,
    Check(Option<&'a Checkpoint<'tcx>>),
}

impl ContractEvalContext<'_, '_> {
    fn is_check(&self) -> bool {
        matches!(self, Self::Check(_))
    }
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn eval_contract_tree(
        &self,
        expr: &ContractExpr<'tcx>,
        context: ContractEvalContext<'_, 'tcx>,
    ) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::Const(value) => Some(self.u128_term(*value)),
            ContractExpr::Binary { op, lhs, rhs } => {
                let left = self.eval_contract_tree(lhs, context)?;
                let right = self.eval_contract_tree(rhs, context)?;
                match op {
                    NumericBinOp::Add | NumericBinOp::Sub | NumericBinOp::Mul => {
                        self.contract_binary_term(*op, &left, &right)
                    }
                    NumericBinOp::Div | NumericBinOp::Rem if !context.is_check() => {
                        Some(if matches!(op, NumericBinOp::Div) {
                            left.div(&right)
                        } else {
                            left.rem(&right)
                        })
                    }
                    NumericBinOp::Div | NumericBinOp::Rem => {
                        if right.as_u64() == Some(0) {
                            Some(Int::from_u64(self.z3_ctx, 0))
                        } else if matches!(op, NumericBinOp::Div) {
                            Some(left.div(&right))
                        } else {
                            let quotient = left.div(&right);
                            Some(Int::sub(
                                self.z3_ctx,
                                &[&left, &Int::mul(self.z3_ctx, &[&quotient, &right])],
                            ))
                        }
                    }
                    NumericBinOp::Min if context.is_check() => {
                        Some(left.le(&right).ite(&left, &right))
                    }
                    NumericBinOp::Max if context.is_check() => {
                        Some(left.ge(&right).ite(&left, &right))
                    }
                    _ => None,
                }
            }
            ContractExpr::Unary { op, expr } => {
                let value = self.eval_contract_tree(expr, context)?;
                Some(self.contract_unary_term(*op, &value))
            }
            ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } if context.is_check() => {
                let left = self.eval_contract_tree(&cond.lhs, context)?;
                let right = self.eval_contract_tree(&cond.rhs, context)?;
                let condition = self.contract_relop_bool(cond.op, &left, &right);
                match condition.simplify().as_bool() {
                    Some(true) => self.eval_contract_tree(then_expr, context),
                    Some(false) => self.eval_contract_tree(else_expr, context),
                    None => {
                        let then_value = self.eval_contract_tree(then_expr, context)?;
                        let else_value = self.eval_contract_tree(else_expr, context)?;
                        Some(condition.ite(&then_value, &else_value))
                    }
                }
            }
            _ => match context {
                ContractEvalContext::Facts => self.eval_contract_expr_simple_leaf(expr),
                ContractEvalContext::Check(checkpoint) => {
                    self.eval_contract_expr_check_leaf(checkpoint, expr)
                }
            },
        }
    }

    pub(crate) fn instantiate_callsite_ty(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        let TyKind::Param(param) = ty.kind() else {
            return ty;
        };
        if checkpoint.callee.is_none() {
            return ty;
        };

        let body = self.body();
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

    fn instantiate_callsite_const(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        index: u32,
    ) -> Option<Int<'z3>> {
        let body = self.body();
        let terminator = body.basic_blocks[checkpoint.block].terminator();
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return None;
        };
        let Operand::Constant(func_constant) = func else {
            return None;
        };
        let TyKind::FnDef(callee_def_id, args) = func_constant.const_.ty().kind() else {
            return None;
        };
        let arg = crate::compat::args_get(args, index as usize)?;
        match arg.kind() {
            GenericArgKind::Const(actual_const) => {
                let value = actual_const
                    .try_to_target_usize(self.tcx)
                    .or_else(|| mir_utils::const_int_from_debug(&format!("{actual_const:?}")));
                let param = self
                    .tcx
                    .generics_of(*callee_def_id)
                    .param_at(index as usize, self.tcx);
                let param_ty = self.tcx.type_of(param.def_id).instantiate_identity();
                let param_ty = param_ty.skip_norm_wip();
                Some(match value {
                    Some(value) => Int::from_u64(self.z3_ctx, value),
                    None => self
                        .symbolic_const_term(&rustc_middle::mir::Const::Ty(param_ty, actual_const)),
                })
            }
            _ => None,
        }
    }

    fn is_caller_type_param(&self, ty: Ty<'tcx>) -> bool {
        let rustc_middle::ty::TyKind::Param(param_ty) = ty.kind() else {
            return false;
        };
        let generics = self.tcx.generics_of(self.current_frame.current_def_id);
        generics.own_params.iter().any(|p| {
            matches!(p.kind, rustc_middle::ty::GenericParamDefKind::Type { .. })
                && p.name == param_ty.name
        })
    }

    fn is_local_adt_receiver(&self, value: &VmValue<'z3, 'tcx>) -> bool {
        let ty = mir_utils::pointee_ty(value.ty).unwrap_or(value.ty);
        matches!(ty.kind(), TyKind::Adt(adt, _) if adt.did().as_local().is_some())
    }

    fn eval_contract_method_call(
        &self,
        receiver: &ContractExpr<'tcx>,
        method: DefId,
        args: &[ContractExpr<'tcx>],
        context: ContractEvalContext<'_, 'tcx>,
    ) -> Option<Int<'z3>> {
        let value = match context {
            ContractEvalContext::Facts => self.eval_contract_expr_simple_value(receiver)?,
            ContractEvalContext::Check(checkpoint) => {
                self.eval_contract_expr_to_value(checkpoint, receiver)?
            }
        };
        let local = match (context, receiver) {
            (ContractEvalContext::Facts, ContractExpr::Place(cp)) => Some(cp.base.to_local()),
            (ContractEvalContext::Check(checkpoint), ContractExpr::Place(cp)) => match cp.base {
                PlaceBase::Arg(index) => checkpoint
                    .and_then(|ck| ck.args.get(index))
                    .and_then(|operand| operand.place())
                    .map(|place| place.local),
                PlaceBase::Local(index) => Some(Local::from_usize(index)),
                PlaceBase::Return => Some(Local::from_usize(0)),
            },
            _ => None,
        };
        let args = args
            .iter()
            .map(|arg| self.eval_contract_tree(arg, context))
            .collect::<Option<Vec<_>>>()?;
        self.eval_contract_method(method, value, local, args)
    }
    fn eval_contract_expr_check_leaf(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::SizeOf(ty) => {
                let mut size = self.size_of_ty(*ty);
                if size == 0 && matches!(ty.kind(), rustc_middle::ty::TyKind::Param(_)) {
                    size = mir_utils::size_of_generic_param(
                        self.tcx,
                        self.current_frame.current_def_id,
                        *ty,
                    );
                    if size == 0
                        && let Some(ck) = checkpoint
                        && let Some(_callee) = ck.callee
                        && !self.is_caller_type_param(*ty)
                    {
                        let resolved = self.instantiate_callsite_ty(ck, *ty);
                        if resolved != *ty {
                            size = self.size_of_ty(resolved);
                        }
                    }
                }
                if size > 0 {
                    Some(Int::from_u64(self.z3_ctx, size))
                } else {
                    Some(Int::from_u64(self.z3_ctx, 0))
                }
            }
            ContractExpr::AlignOf(ty) => {
                let align = self.align_of_ty(*ty);
                if align > 0 {
                    Some(Int::from_u64(self.z3_ctx, align.max(1)))
                } else {
                    Some(Int::from_u64(self.z3_ctx, 0))
                }
            }
            ContractExpr::Place(cp) => self.eval_contract_place(checkpoint, cp),
            ContractExpr::Len(inner, method) => {
                if let Some(method) = method
                    && let Some(receiver) = self.eval_contract_expr_to_value(checkpoint, inner)
                    && let Some(result) = self.cached_method_result(*method, &receiver)
                {
                    return Some(result);
                }
                if let Some(ck) = checkpoint
                    && let Some(term) = self.try_iter_len_from_fields(ck, inner)
                {
                    return Some(term);
                }
                let val = self.eval_contract_expr_to_value(checkpoint, inner)?;
                if self.is_local_adt_receiver(&val) {
                    return None;
                }
                if let crate::verify::contract::ContractExpr::Place(cp) = &**inner
                    && let Some(field_path) = cp.plain_field_path()
                {
                    let base_local = match cp.base {
                        PlaceBase::Return => Some(Local::from_usize(0)),
                        PlaceBase::Local(n) => Some(Local::from_usize(n)),
                        PlaceBase::Arg(n) => {
                            checkpoint
                                .and_then(|ck| ck.args.get(n))
                                .and_then(|op| match op {
                                    Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                                    _ => None,
                                })
                        }
                    };
                    if let Some(local) = base_local
                        && let Some(len) = self.try_struct_nn_len_field(local, &field_path, val.ty)
                    {
                        return Some(len);
                    }
                }
                self.len_from_value(&val)
            }
            ContractExpr::MethodCall {
                receiver,
                method,
                args,
            } => self.eval_contract_method_call(
                receiver,
                *method,
                args,
                ContractEvalContext::Check(checkpoint),
            ),
            ContractExpr::IsEmpty(inner, method) => {
                let method = (*method)?;
                let receiver = self.eval_contract_expr_to_value(checkpoint, inner)?;
                self.cached_method_result(method, &receiver)
            }
            ContractExpr::ConstParam { index, .. } => match checkpoint {
                Some(checkpoint) => self.instantiate_callsite_const(checkpoint, *index),
                None => self.const_param_term(*index),
            },
            _ => None,
        }
    }

    pub(crate) fn eval_contract_expr_to_value(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => {
                if cp.projections.is_empty() {
                    return match cp.base {
                        PlaceBase::Return => self.local_value(Local::from_usize(0)).cloned(),
                        PlaceBase::Arg(n) => {
                            checkpoint?.args.get(n).map(|op| self.value_of_operand(op))
                        }
                        PlaceBase::Local(n) => {
                            let ck = checkpoint?;
                            if let Some(op) = self.callsite_operand_for_local(ck, n) {
                                return Some(self.value_of_operand(op));
                            }
                            self.local_value(Local::from_usize(n)).cloned()
                        }
                    };
                }
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
                self.field_value(base_local, &field_path).cloned()
            }
            _ => None,
        }
    }

    fn eval_contract_place(
        &self,
        checkpoint: Option<&Checkpoint<'tcx>>,
        cp: &crate::verify::contract::ContractPlace<'tcx>,
    ) -> Option<Int<'z3>> {
        let field_path = cp.plain_field_path()?;

        let base_local: Option<Local> = match cp.base {
            PlaceBase::Return => Some(Local::from_usize(0)),
            PlaceBase::Arg(n) => {
                if field_path.is_empty() {
                    return checkpoint.and_then(|ck| {
                        let op = ck.args.get(n)?;
                        self.eval_contract_operand(op)
                    });
                }
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
                    && let Some(op) = self.callsite_operand_for_local(ck, n)
                    && let Some(v) = self.eval_contract_operand(op)
                {
                    return Some(v);
                }
                Some(Local::from_usize(n))
            }
        };

        let local = base_local?;
        if field_path.is_empty() {
            self.local_value(local).map(|v| v.z3_term.clone())
        } else {
            self.field_value(local, &field_path)
                .map(|v| v.z3_term.clone())
        }
    }

    fn eval_contract_operand(&self, op: &Operand<'tcx>) -> Option<Int<'z3>> {
        match op {
            Operand::Constant(c) => {
                let const_text = format!("{:?}", c.const_);
                let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
                if let Ok(val) = c.const_.eval(self.tcx, typing_env, rustc_span::DUMMY_SP)
                    && let Some(scalar) = val.try_to_scalar_int()
                {
                    let bits = scalar.to_bits(scalar.size());
                    if bits != 0
                        || !(const_text.contains("AlignOf")
                            || const_text.contains("SizeOf")
                            || const_text.contains("min_align_of")
                            || const_text.contains("min_size_of"))
                    {
                        return self.scalar_bits_term(c.const_.ty(), bits);
                    }
                }
                Some(
                    mir_utils::const_int_from_debug(&const_text)
                        .map(|v| Int::from_u64(self.z3_ctx, v))
                        .unwrap_or_else(|| self.symbolic_const_term(&c.const_)),
                )
            }
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                self.local_value(p.local).map(|v| v.z3_term.clone())
            }
            _ => None,
        }
    }

    fn try_iter_len_from_fields(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        let ContractExpr::Place(cp) = expr else {
            return None;
        };
        let op: &Operand<'tcx> = match cp.base {
            PlaceBase::Arg(n) => checkpoint.args.get(n)?,
            PlaceBase::Local(n) => {
                let callee = checkpoint.callee?;
                let idx = mir_utils::callee_param_index_for_local(self.tcx, callee, n)?;
                checkpoint.args.get(idx)?
            }
            _ => return None,
        };
        let place: &Place<'tcx> = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let local = place.local;
        let local_val = self.local_value(local)?;
        if !self.is_iter_ref(local_val) {
            return None;
        }
        if let (Some(ptr), Some(end)) =
            (self.field_value(local, &[0]), self.field_value(local, &[1]))
            && let Some(len) = self.iter_len_from_ptrs(ptr, end)
        {
            return Some(len);
        }
        let target_alloc = local_val.provenance_alloc_id()?;
        for (scan_local, scan_val) in self.all_local_values() {
            if scan_val.provenance_alloc_id() != Some(target_alloc) {
                continue;
            }
            if let (Some(ptr), Some(end)) = (
                self.field_value(scan_local, &[0]),
                self.field_value(scan_local, &[1]),
            ) && let Some(len) = self.iter_len_from_ptrs(ptr, end)
            {
                return Some(len);
            }
        }
        None
    }

    pub(crate) fn eval_contract_expr_simple(&self, expr: &ContractExpr<'tcx>) -> Option<Int<'z3>> {
        self.eval_contract_tree(expr, ContractEvalContext::Facts)
    }

    fn eval_contract_expr_simple_leaf(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::SizeOf(ty) => Some(self.size_sym_read(*ty)),
            ContractExpr::Place(cp) => {
                let path = cp.plain_field_path()?;
                if let Some(value) = self.contract_place_value_at(ContractTargetContext::Bound, cp)
                {
                    return Some(value.z3_term);
                }
                if path.is_empty() {
                    return None;
                }
                let local = cp.base.to_local();
                let base_val = self.local_value(local)?;
                let alloc_id = base_val.provenance_alloc_id()?;
                let view_ty = mir_utils::pointee_ty(base_val.ty).unwrap_or(base_val.ty);
                self.units[alloc_id.0]
                    .content
                    .values
                    .get(&(view_ty, path))
                    .map(|value| value.z3_term.clone())
            }
            ContractExpr::Len(inner, _) => {
                let val = self.eval_contract_expr_simple_value(inner)?;
                if self.is_local_adt_receiver(&val) {
                    return None;
                }
                if let Some(term) = self.try_simple_iter_len(&val) {
                    return Some(term);
                }
                if let ContractExpr::Place(cp) = &**inner
                    && let Some(path) = cp.plain_field_path()
                {
                    let local = cp.base.to_local();
                    if let Some(ty) = self.field_type_at(local, &path)
                        && let Some(term) = self.try_struct_nn_len_field(local, &path, ty)
                    {
                        return Some(term);
                    }
                }
                self.len_from_value(&val)
            }
            ContractExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                self.eval_contract_method_call(receiver, *method, args, ContractEvalContext::Facts)
            }
            ContractExpr::ConstParam { index, .. } => self.const_param_term(*index),
            _ => None,
        }
    }

    fn eval_contract_expr_simple_value(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
                PlaceBase::Local(n) => self.local_value(Local::from_usize(n)).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    fn try_simple_iter_len(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if !self.is_iter_ref(arg_val) {
            return None;
        }
        let local = Local::from_usize(1);
        let ptr = self.field_value(local, &[0])?;
        let end = self.field_value(local, &[1])?;
        self.iter_len_from_ptrs(ptr, end)
    }

    pub(crate) fn contract_binary_term(
        &self,
        op: NumericBinOp,
        left: &Int<'z3>,
        right: &Int<'z3>,
    ) -> Option<Int<'z3>> {
        match op {
            NumericBinOp::Add => Some(Int::add(self.z3_ctx, &[left, right])),
            NumericBinOp::Sub => Some(Int::sub(self.z3_ctx, &[left, right])),
            NumericBinOp::Mul => Some(Int::mul(self.z3_ctx, &[left, right])),
            _ => None,
        }
    }

    pub(crate) fn contract_unary_term(&self, op: NumericUnaryOp, value: &Int<'z3>) -> Int<'z3> {
        let zero = Int::from_u64(self.z3_ctx, 0);
        match op {
            NumericUnaryOp::Not => value._eq(&zero).ite(&Int::from_u64(self.z3_ctx, 1), &zero),
            NumericUnaryOp::Neg => Int::sub(self.z3_ctx, &[&zero, value]),
        }
    }

    pub(crate) fn contract_relop_bool(
        &self,
        op: RelOp,
        left: &Int<'z3>,
        right: &Int<'z3>,
    ) -> Bool<'z3> {
        match op {
            RelOp::Eq => left._eq(right),
            RelOp::Ne => left._eq(right).not(),
            RelOp::Le => left.le(right),
            RelOp::Lt => left.lt(right),
            RelOp::Ge => left.ge(right),
            RelOp::Gt => left.gt(right),
        }
    }
}
