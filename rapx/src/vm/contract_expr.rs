//! Contract-fact expressions and shared numeric operations.

use crate::contract::{BinOp, ContractExpr, ContractPlace, ContractProjection, PlaceBase, RelOp, UnaryOp};
use crate::util::mir_utils;
use crate::vm::state::VmValue;
use crate::vm::VmExecutor;
use rustc_middle::{mir::Local, ty::TyKind};
use z3::ast::{Ast, Bool, Int};

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// Resolve a contract place already bound to this frame's locals.
    pub(crate) fn bound_contract_place_value(&self, place: &ContractPlace) -> Option<VmValue<'z3, 'tcx>> {
        let local = place.base.to_local();
        if place.projections.is_empty() { return self.local_value(local).cloned() }
        let mut fields = Vec::new();
        for projection in &place.projections {
            match projection {
                ContractProjection::Field { index } => fields.push(*index),
                ContractProjection::Downcast { .. } | ContractProjection::ForEach => {
                    return if fields.is_empty() { self.local_value(local).cloned() } else { self.field_value(local, &fields).cloned() };
                }
            }
        }
        self.field_value(local, &fields).cloned()
    }

    fn eval_contract_fact_tree(&self, expr: &ContractExpr<'tcx>) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::Const(value) => Some(self.u128_term(*value)),
            ContractExpr::Binary { op, lhs, rhs } => {
                let left = self.eval_contract_fact_tree(lhs)?;
                let right = self.eval_contract_fact_tree(rhs)?;
                match op {
                    BinOp::Add | BinOp::Sub | BinOp::Mul => self.contract_binary_term(*op, &left, &right),
                    BinOp::Div => Some(left.div(&right)),
                    BinOp::Rem => Some(left.rem(&right)),
                    _ => None,
                }
            }
            ContractExpr::Unary { op, expr } => {
                let value = self.eval_contract_fact_tree(expr)?;
                Some(self.contract_unary_term(*op, &value))
            }
            _ => self.eval_contract_expr_simple_leaf(expr),
        }
    }

    pub(crate) fn eval_contract_expr_simple(&self, expr: &ContractExpr<'tcx>) -> Option<Int<'z3>> {
        self.eval_contract_fact_tree(expr)
    }

    fn eval_contract_expr_simple_leaf(&self, expr: &ContractExpr<'tcx>) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::SizeOf(ty) => Some(self.size_sym_read(*ty)),
            ContractExpr::Place(cp) => {
                let path = cp.plain_field_path()?;
                if let Some(value) = self.bound_contract_place_value(cp)
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
                self.content(alloc_id)
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
                let value = self.eval_contract_expr_simple_value(receiver)?;
                let local = match receiver.as_ref() {
                    ContractExpr::Place(cp) => Some(cp.base.to_local()),
                    _ => None,
                };
                let args = args.iter().map(|arg| self.eval_contract_fact_tree(arg)).collect::<Option<Vec<_>>>()?;
                self.eval_contract_method(*method, value, local, args)
            }
            ContractExpr::ConstParam { index, .. } => self.const_param_term(*index),
            _ => None,
        }
    }

    fn eval_contract_expr_simple_value(&self, expr: &ContractExpr<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
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

    pub(crate) fn is_local_adt_receiver(&self, value: &VmValue<'z3, 'tcx>) -> bool {
        let ty = mir_utils::pointee_ty(value.ty).unwrap_or(value.ty);
        matches!(ty.kind(), TyKind::Adt(adt, _) if adt.did().as_local().is_some())
    }

    pub(crate) fn contract_binary_term(
        &self,
        op: BinOp,
        left: &Int<'z3>,
        right: &Int<'z3>,
    ) -> Option<Int<'z3>> {
        match op {
            BinOp::Add => Some(Int::add(self.z3_ctx, &[left, right])),
            BinOp::Sub => Some(Int::sub(self.z3_ctx, &[left, right])),
            BinOp::Mul => Some(Int::mul(self.z3_ctx, &[left, right])),
            _ => None,
        }
    }

    pub(crate) fn contract_unary_term(&self, op: UnaryOp, value: &Int<'z3>) -> Int<'z3> {
        let zero = Int::from_u64(self.z3_ctx, 0);
        match op {
            UnaryOp::Not => value._eq(&zero).ite(&Int::from_u64(self.z3_ctx, 1), &zero),
            UnaryOp::Neg => Int::sub(self.z3_ctx, &[&zero, value]),
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
