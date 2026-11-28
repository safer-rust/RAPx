//! Contract-fact expressions and shared numeric operations.

use crate::contract::{BinOp, ContractExpr, ContractPlace, ContractProjection, PlaceBase, RelOp, UnaryOp};
use crate::def_ids::type_ids;
use crate::compat::FxHashSet;
use crate::util::mir_utils;
use crate::vm::integer::integer_eq;
use crate::vm::state::VmValue;
use crate::vm::VmExecutor;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::{Ty, TyKind}};
use z3::ast::{Ast, Bool, Int};

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// Read the actual strong counter in an `RcInner` or `ArcInner` allocation.
    /// An unmaterialized header is unknown; counting visible owners is not a
    /// substitute because other owners may exist outside this path.
    fn strong_ref_count_field(&self, pointer: &VmValue<'z3, 'tcx>, owner_ty: Ty<'tcx>)
        -> Option<(super::state::AllocId, Ty<'tcx>, Vec<usize>, Int<'z3>)> {
        let TyKind::Adt(owner, args) = owner_ty.peel_refs().kind() else { return None };
        let is_rc = type_ids::is_std_rc(owner.did());
        if !is_rc && !type_ids::is_std_arc(owner.did()) { return None; }
        let ptr_field = owner.non_enum_variant().fields.iter().next()?;
        let ptr_ty = mir_utils::field_ty(self.tcx, ptr_field, args);
        let inner_ty = self.find_nn_pointee(ptr_ty)?;
        let inner_adt = inner_ty.ty_adt_def()?;
        let strong_field = inner_adt.non_enum_variant().fields.iter()
            .position(|field| field.name.as_str() == "strong")?;
        let count_path = if is_rc { vec![strong_field, 0, 0] } else { vec![strong_field] };
        let alloc_id = self.root_alloc(pointer.provenance_alloc_id()?);
        if self.alloc(alloc_id).dead { return None; }
        let pointee_ty = mir_utils::pointee_ty(pointer.ty)?;
        let generic_pointee = matches!(pointee_ty.kind(), TyKind::Param(_))
            || matches!(pointee_ty.kind(), TyKind::Adt(_, args)
                if args.types().any(|ty| matches!(ty.kind(), TyKind::Param(_))));
        let mut counts = self.content(alloc_id).values.iter().filter_map(|((view_ty, path), value)| {
            let TyKind::Adt(view_adt, view_args) = view_ty.kind() else { return None; };
            (path == &count_path && view_adt.did() == inner_adt.did()
                && (if generic_pointee {
                    view_args.first().and_then(|arg| arg.as_type())
                        .is_some_and(|ty| !matches!(ty.kind(), TyKind::Param(_)))
                } else {
                    view_ty == &pointee_ty
                        || view_args.first().and_then(|arg| arg.as_type()) == Some(pointee_ty)
                }))
                .then_some((*view_ty, path.clone(), value.z3_term.clone()))
        });
        let count = counts.next()?;
        counts.next().is_none().then_some((alloc_id, count.0, count.1, count.2))
    }

    /// Resolve a named or numbered field path against a materialized header view.
    fn count_field_path(&self, mut ty: Ty<'tcx>, fields: &[String]) -> Option<Vec<usize>> {
        let mut path = Vec::with_capacity(fields.len());
        for field in fields {
            let TyKind::Adt(adt, args) = ty.kind() else { return None; };
            if adt.is_enum() { return None; }
            let index = field.parse::<usize>().ok().or_else(|| adt.non_enum_variant().fields.iter()
                .position(|candidate| candidate.name.as_str() == field))?;
            let field_def = adt.non_enum_variant().fields.iter().nth(index)?;
            path.push(index);
            ty = mir_utils::field_ty(self.tcx, field_def, args);
        }
        Some(path)
    }

    /// Locate the header type reached through an owner's raw pointer field.
    fn owner_header_ty(&self, mut ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        for index in self.container_ptr_field(ty)? {
            let TyKind::Adt(adt, args) = ty.kind() else { return None; };
            let field = adt.non_enum_variant().fields.iter().nth(index)?;
            ty = mir_utils::field_ty(self.tcx, field, args);
        }
        self.find_nn_pointee(ty).or_else(|| mir_utils::pointee_ty(ty))
    }

    /// Read the explicit count field from the pointer's backing allocation.
    pub(crate) fn strong_ref_count_at(&self, pointer: &VmValue<'z3, 'tcx>, owner_ty: Ty<'tcx>, fields: &[String]) -> Option<Int<'z3>> {
        if let Some(owner) = owner_ty.peel_refs().ty_adt_def()
            && (type_ids::is_std_rc(owner.did()) || type_ids::is_std_arc(owner.did()))
        {
            let (_, view_ty, path, count) = self.strong_ref_count_field(pointer, owner_ty)?;
            return (self.count_field_path(view_ty, fields)? == path).then_some(count);
        }
        let alloc_id = self.root_alloc(pointer.provenance_alloc_id()?);
        if self.alloc(alloc_id).dead { return None; }
        let header_ty = self.owner_header_ty(owner_ty)?;
        let header = header_ty.ty_adt_def()?;
        let mut counts = self.content(alloc_id).values.iter().filter_map(|((view_ty, path), value)| {
            (view_ty.ty_adt_def().is_some_and(|adt| adt.did() == header.did())
                && self.count_field_path(*view_ty, fields).as_deref() == Some(path.as_slice()))
                .then_some(value.z3_term.clone())
        });
        let count = counts.next()?;
        counts.next().is_none().then_some(count)
    }

    /// Locate owner pointer fields inside a local or a struct field of that local.
    fn owner_ptr_paths(&self, ty: Ty<'tcx>, owner: DefId, prefix: Vec<usize>, depth: usize, out: &mut Vec<Vec<usize>>) {
        if ty.ty_adt_def().is_some_and(|adt| adt.did() == owner) {
            if let Some(mut path) = self.container_ptr_field(ty) {
                let mut full = prefix;
                full.append(&mut path);
                out.push(full);
            }
            return;
        }
        if depth >= 4 { return; }
        match ty.kind() {
            TyKind::Adt(adt, args) if !adt.is_enum() => {
                for (index, field) in adt.non_enum_variant().fields.iter().enumerate() {
                    let mut path = prefix.clone();
                    path.push(index);
                    self.owner_ptr_paths(mir_utils::field_ty(self.tcx, field, args), owner, path, depth + 1, out);
                }
            }
            TyKind::Tuple(fields) => {
                for (index, field) in fields.iter().enumerate() {
                    let mut path = prefix.clone();
                    path.push(index);
                    self.owner_ptr_paths(field, owner, path, depth + 1, out);
                }
            }
            _ => {}
        }
    }

    /// Count materialized owner slots in the caller and its inlined frames.
    pub(crate) fn rc_owner_count(&self, pointer: &VmValue<'z3, 'tcx>, owner: DefId) -> Option<Int<'z3>> {
        let root = self.root_alloc(pointer.provenance_alloc_id()?);
        let mut slots = FxHashSet::default();
        let frames = std::iter::once(&self.path_state.current_frame)
            .chain(self.path_state.caller_frames.iter().map(|saved| &saved.frame));
        for frame in frames {
            for (&local, &slot) in &frame.local_alloc {
                if self.alloc(slot).dead { continue; }
                let ty = self.frame_local_ty(frame, local);
                let mut paths = Vec::new();
                self.owner_ptr_paths(ty, owner, Vec::new(), 0, &mut paths);
                for path in paths {
                    let Some(value) = self.load_value(slot, ty, &path) else { continue; };
                    if value.provenance_alloc_id().is_some_and(|id| self.root_alloc(id) == root) {
                        slots.insert((slot, path));
                    }
                }
            }
        }
        Some(Int::from_u64(self.z3_ctx, slots.len() as u64))
    }

    /// Update the materialized header when a shared owner is dropped.
    pub(crate) fn decrement_strong_ref_count(&mut self, pointer: &VmValue<'z3, 'tcx>, owner_ty: Ty<'tcx>) {
        let Some((alloc_id, view_ty, path, count)) = self.strong_ref_count_field(pointer, owner_ty) else { return; };
        let Some(mut value) = self.load_value(alloc_id, view_ty, &path).cloned() else { return; };
        value.z3_term = &count - Int::from_u64(self.z3_ctx, 1);
        self.store_value(alloc_id, view_ty, path, value);
    }

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
            ContractExpr::StrongRefCount { ptr, field_path } => {
                let ContractExpr::Place(place) = ptr.as_ref() else { return None; };
                let owner_ty = self.body().local_decls[place.base.to_local()].ty;
                let pointer = self.bound_contract_place_value(place)?;
                self.strong_ref_count_at(&pointer, owner_ty, field_path)
            }
            ContractExpr::RcOwnerCount { ptr, owner } => {
                let ContractExpr::Place(place) = ptr.as_ref() else { return None; };
                let pointer = self.bound_contract_place_value(place)?;
                self.rc_owner_count(&pointer, *owner)
            }
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
            ContractExpr::ConstParam { index, .. } => {
                self.const_param_input(*index).map(|(term, _)| term)
            }
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
            RelOp::Eq => integer_eq(left, right),
            RelOp::Ne => integer_eq(left, right).not(),
            RelOp::Le => left.le(right),
            RelOp::Lt => left.lt(right),
            RelOp::Ge => left.ge(right),
            RelOp::Gt => left.gt(right),
        }
    }
}
