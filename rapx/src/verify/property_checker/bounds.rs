//! Checkers for `InBound` and `NonOverlap`.
//!
//! Bounds are discharged from `has_checked_bounds`/`in_bounds` facts, layout
//! field-offset invariants, or an SMT coverage check over allocation base/size.
//! `NonOverlap` uses provenance-distinctness and range-overlap reasoning.

#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::api_classify;
use crate::verify::contract::{
    ContractExpr, NumericBinOp, PlaceBase, Property, PropertyArg, RelOp,
};
use crate::verify::report::CheckResult;
use crate::verify::vm::state::{VmState, VmValue};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyKind};
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_in_bound<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Fast-path: if a prior ChecksIndexBoundsDisjoint call already
        // validated bounds for this function, the InBound holds.
        if vm_state.contract_flags.has_checked_bounds {
            return CheckResult::Proved;
        }
        // Fast-path: contract with for_each guarantees all elements
        // of the index array are in bounds.
        if property.for_each().is_some() {
            return CheckResult::Proved;
        }

        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { index: _, .. })) =
            property.args().first()
        {
            return self.check_in_bound_slice(vm_state, solver, checkpoint, property);
        }

        let required_ty = property.args().get(1).and_then(|a| {
            if let PropertyArg::Ty(ty) = a {
                Some(*ty)
            } else {
                None
            }
        });
        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::Proved;
        }

        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        if matches!(value.ty.kind(), TyKind::Ref(..)) {
            return CheckResult::Proved;
        }
        if value.provenance.is_some() {
            if let TyKind::Adt(adt_def, _) = value.ty.kind() {
                if api_classify::is_std_nonnull(adt_def.did()) {
                    return CheckResult::Proved;
                }
            }
        }
        if value.invariants.in_bounds {
            return CheckResult::Proved;
        }
        // `byte_add(offset_of!(Container, field))` always keeps the pointer
        // within the container allocation, because the byte offset of a field
        // never exceeds `size_of::<Container>()`.  This covers patterns such
        // as `Option::as_slice`.
        if self.count_is_offset_of(vm_state, checkpoint, property, &value) {
            return CheckResult::Proved;
        }
        // When the contract expression for the element count evaluates to
        // zero (e.g. div-by-sizeof for ZST generic params), the byte-level
        // access is zero and limits checking is trivial.
        let count_term = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a));
        if let Some(ref ct) = count_term {
            if ct.as_u64() == Some(0) {
                return CheckResult::Proved;
            }
        }
        let access = self.access_bytes(vm_state, property, 1, 2, checkpoint, &value);
        let Some(alloc_id) = value.provenance_alloc_id() else {
            return CheckResult::Unknown;
        };
        let (Some(base), Some(size)) = (
            vm_state.allocation_base(alloc_id).cloned(),
            vm_state.allocation_size(alloc_id).cloned(),
        ) else {
            return CheckResult::Unknown;
        };

        let alloc = vm_state.alloc(alloc_id);
        if let (Some(alloc_elem_ty), Some(req_ty)) = (alloc.element_ty, required_ty) {
            if self.alloc_elem_is_array_of(alloc_elem_ty, req_ty) {
                return CheckResult::Proved;
            }
        }

        // External allocations have unbounded size.
        if vm_state.alloc(alloc_id).is_external {
            return CheckResult::Proved;
        }

        let alloc_elem_is_generic = vm_state
            .alloc(alloc_id)
            .element_ty
            .map_or(false, |ty| matches!(ty.kind(), TyKind::Param(_)));
        let fallback_for_generic =
            alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some();

        solver.push();
        let bound = Int::add(vm_state.ctx, &[&base, &size]);
        let covered = Int::add(vm_state.ctx, &[&value.term, &access]);
        // A field-offset provenance (`offset_of!`) is always within the
        // container together with the accessed range: the field plus its own
        // size fits inside the container.  Assert this layout fact so the
        // in-bounds check below can be discharged.
        if value
            .provenance
            .as_ref()
            .is_some_and(|prov| prov.is_field_offset)
        {
            let prov = value.provenance.as_ref().unwrap();
            let zero = Int::from_u64(vm_state.ctx, 0);
            solver.assert(&prov.offset.ge(&zero));
            solver.assert(&Int::add(vm_state.ctx, &[&prov.offset, &access]).le(&size));
        }
        // Upper bound: value + access > base + size
        let above_negated = covered.le(&bound).not();
        // Lower bound: value < base (pointer below allocation start)
        let below_negated = value.term.lt(&base);
        solver.assert(&z3::ast::Bool::or(
            vm_state.ctx,
            &[&above_negated, &below_negated],
        ));
        let sat_result = solver.check();
        let r = match sat_result {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat if fallback_for_generic => CheckResult::Unknown,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    pub(super) fn count_is_offset_of<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        value: &VmValue<'ctx, 'tcx>,
    ) -> bool {
        let Some(count_arg) = property.args().get(2) else {
            return false;
        };
        let PropertyArg::Expr(ContractExpr::Place(cp)) = count_arg else {
            return false;
        };
        let PlaceBase::Arg(n) = cp.base else {
            return false;
        };
        let Some(operand) = checkpoint.args.get(n) else {
            return false;
        };
        let Operand::Constant(c) = operand else {
            return false;
        };
        let Some(container) =
            crate::helpers::mir_utils::offset_of_container(vm_state.tcx, &c.const_)
        else {
            return false;
        };
        // The pointer must be the base of its allocation (offset 0), otherwise
        // adding the field offset could overflow the container end.
        let at_base = value
            .provenance
            .as_ref()
            .is_some_and(|p| p.offset.as_u64() == Some(0));
        if !at_base {
            return false;
        }
        // The allocation must be the same container the offset was computed on.
        crate::helpers::mir_utils::pointee_ty(value.ty).is_some_and(|pointee| pointee == container)
    }

    pub(super) fn resolve_index_access_args(
        property: &Property<'_>,
    ) -> (Option<usize>, Option<usize>) {
        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args().first()
        {
            let slice_idx = Self::extract_place_arg_index(slice);
            let index_idx = Self::extract_place_arg_index(index);
            (slice_idx, index_idx)
        } else {
            (Some(0), Some(1))
        }
    }

    pub(super) fn extract_place_arg_index(expr: &ContractExpr<'_>) -> Option<usize> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
                PlaceBase::Arg(n) => Some(n),
                _ => None,
            },
            _ => None,
        }
    }

    pub(super) fn check_in_bound_slice<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let (slice_arg_idx, index_arg_idx) = Self::resolve_index_access_args(property);

        let slice_val = match slice_arg_idx.and_then(|idx| checkpoint.args.get(idx)) {
            Some(op) => vm_state.value_of_operand(op),
            None => return CheckResult::Unknown,
        };
        if slice_val.invariants.in_bounds {
            return CheckResult::Proved;
        }

        let (index_val, is_range) = match index_arg_idx.and_then(|idx| checkpoint.args.get(idx)) {
            Some(op) => {
                if let Some(end_val) = self.extract_range_end(vm_state, op, checkpoint) {
                    (end_val, true)
                } else {
                    (vm_state.value_of_operand(op), false)
                }
            }
            None => return CheckResult::Unknown,
        };

        let data_alloc_id = slice_val.provenance_alloc_id();
        let Some(data_alloc_id) = data_alloc_id else {
            return CheckResult::Unknown;
        };

        let Some(size) = vm_state.allocation_size(data_alloc_id).cloned() else {
            return CheckResult::Unknown;
        };

        let elem_size = vm_state
            .alloc(data_alloc_id)
            .element_ty
            .map(|ty| vm_state.size_of_ty(ty) as u64)
            .unwrap_or(1)
            .max(1);

        let elem_sz = Int::from_u64(vm_state.ctx, elem_size);
        let len = size.div(&elem_sz);

        solver.push();
        // Assert accumulated path conditions (e.g. the loop-carried
        // `initialized < N` guard that makes `idx < N` hold at this call site)
        // so the bound check below can be discharged symbolically.
        for cond in &vm_state.path_conditions {
            solver.assert(cond);
        }
        let negated = if is_range {
            // For range-based InBound (start..end), check end <= len
            index_val.term.le(&len).not()
        } else {
            // For single-element InBound (index), check index + 1 <= len
            let one = Int::from_u64(vm_state.ctx, 1);
            let index_plus_one = Int::add(vm_state.ctx, &[&index_val.term, &one]);
            index_plus_one.le(&len).not()
        };
        solver.assert(&negated);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    pub(super) fn extract_range_end<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>,
        _checkpoint: &Checkpoint<'tcx>,
    ) -> Option<VmValue<'ctx, 'tcx>> {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let range_local = place.local;
        let ty = vm_state.body.local_decls[range_local].ty;
        let is_range = format!("{:?}", ty.kind()).contains("Range");
        if !is_range {
            return None;
        }
        for block in vm_state.body.basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == range_local && dest.projection.is_empty() {
                        if let Rvalue::Aggregate(_kind, operands) = rvalue {
                            let end_idx = rustc_abi::FieldIdx::from_usize(1);
                            if let Some(end_op) = operands.get(end_idx) {
                                return Some(self.trace_value(vm_state, end_op));
                            }
                        }
                    }
                }
            }
        }
        None
    }

    pub(super) fn check_non_overlap<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(v1) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        // Get the second pointer from the property args (not from checkpoint directly).
        // The property may reference the two pointers in any order (e.g. dst at args[0]).
        let v2 = property
            .args()
            .get(1)
            .and_then(|a| {
                let cp = match a {
                    PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
                    _ => return None,
                };
                match cp.base {
                    PlaceBase::Arg(n) => checkpoint
                        .args
                        .get(n)
                        .map(|op| vm_state.value_of_operand(op)),
                    PlaceBase::Local(n) => vm_state.local_value(Local::from_usize(n)).cloned(),
                    _ => None,
                }
            })
            .or_else(|| {
                checkpoint
                    .args
                    .get(1)
                    .map(|op| vm_state.value_of_operand(op))
            });
        let Some(v2) = v2 else {
            // Without a second pointer we cannot prove non-overlap.
            return CheckResult::Unknown;
        };
        // Only discharge non-overlap when both pointers carry provenance into
        // distinct allocations. `Option` comparison here is unsound: a `None`
        // (unknown) provenance would compare unequal to any concrete `AllocId`
        // and spuriously report the pointers as non-overlapping.
        if let (Some(a), Some(b)) = (v1.provenance_alloc_id(), v2.provenance_alloc_id()) {
            if a != b {
                return CheckResult::Proved;
            }
        }

        // Try range-based overlap detection when count and element size are available.
        if let Some(count_term) = checkpoint
            .args
            .get(2)
            .map(|op| vm_state.value_of_operand(op).term)
        {
            // Use the pointee element size from either pointer type.
            let elem_size = vm_state
                .pointee_elem_size(v1.ty)
                .max(vm_state.pointee_elem_size(v2.ty))
                .max(1) as u64;
            let _elem_size_term = Int::from_u64(vm_state.ctx, elem_size);
            if let Some(count) = count_term.simplify().as_u64() {
                let range = Int::from_u64(vm_state.ctx, elem_size * count.max(1));
                let src_end = Int::add(vm_state.ctx, &[&v1.term, &range]);
                let dst_end = Int::add(vm_state.ctx, &[&v2.term, &range]);
                solver.push();
                let overlap = Bool::and(
                    vm_state.ctx,
                    &[&v1.term.lt(&dst_end), &v2.term.lt(&src_end)],
                );
                solver.assert(&overlap);
                let r = match solver.check() {
                    SatResult::Unsat => CheckResult::Proved,
                    SatResult::Sat => CheckResult::Failed,
                    _ => CheckResult::Unknown,
                };
                solver.pop(1);
                return r;
            }
        }

        // Fallback: check pointer-distinctness.
        solver.push();
        let ne = v1.term._eq(&v2.term).not();
        solver.assert(&ne);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    pub(super) fn all_predicates_are_slice_size_invariant<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        predicates: &[crate::verify::contract::NumericPredicate<'tcx>],
    ) -> bool {
        !predicates.is_empty()
            && predicates
                .iter()
                .all(|p| self.predicate_is_slice_size_invariant(vm_state, checkpoint, p))
    }

    pub(super) fn predicate_is_slice_size_invariant<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> bool {
        if !matches!(pred.op, RelOp::Le | RelOp::Lt) {
            return false;
        }
        // rhs must be >= isize::MAX (the language invaraint bound)
        let ContractExpr::Const(bound) = &pred.rhs else {
            return false;
        };
        if *bound < i64::MAX as u128 {
            return false;
        }
        // lhs must be size_of(T) * count
        let ContractExpr::Binary {
            op: NumericBinOp::Mul,
            lhs,
            rhs,
        } = &pred.lhs
        else {
            return false;
        };
        let (size_ty, count_expr) = match (lhs.as_ref(), rhs.as_ref()) {
            (ContractExpr::SizeOf(ty), count) => (*ty, count),
            (count, ContractExpr::SizeOf(ty)) => (*ty, count),
            _ => return false,
        };
        // Resolve SizeOf type via callsite substitutions
        let resolved_ty = self.instantiate_callsite_ty(vm_state, checkpoint, size_ty);
        // count must be a Place referencing a callsite arg
        self.count_derives_from_slice_param(vm_state, checkpoint, count_expr, resolved_ty)
    }

    pub(super) fn count_derives_from_slice_param<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        count_expr: &ContractExpr<'tcx>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
        // Must be a Place, not a constant literal
        let ContractExpr::Place(cp) = count_expr else {
            return false;
        };
        if !cp.projections.is_empty() {
            return false;
        }
        let Some(local) = cp.local_base() else {
            return false;
        };
        if local == 0 {
            return false;
        }
        let Some(callee) = checkpoint.callee else {
            return false;
        };
        let Some(arg_idx) =
            crate::helpers::mir_utils::callee_param_index_for_local(vm_state.tcx, callee, local)
        else {
            return false;
        };
        // Reject constant literal arguments (like usize::MAX)
        if matches!(checkpoint.args.get(arg_idx), Some(Operand::Constant(_))) {
            return false;
        }
        // Check caller has a matching slice reference parameter.
        let body = vm_state.body;
        let has_slice_param = (1..=body.arg_count).any(|i| {
            let param_ty = body.local_decls[Local::from_usize(i)].ty;
            self.is_slice_ref_with_elem(param_ty, elem_ty, vm_state, checkpoint)
        });
        if has_slice_param {
            return true;
        }
        // No direct slice param — check if the pointer has provenance from
        // an external allocation (raw pointer params get this in init_parameters).
        if let Some(op) = checkpoint.args.first() {
            let target_val = vm_state.value_of_operand(op);
            if target_val.provenance.is_some() {
                return true;
            }
        }
        false
    }

    pub(super) fn is_slice_ref_with_elem<'ctx, 'tcx>(
        &self,
        ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() else {
            return false;
        };
        match inner.kind() {
            rustc_middle::ty::TyKind::Slice(slice_elem) => {
                let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, *slice_elem);
                self.same_erased_ty(vm_state, resolved, elem_ty)
            }
            _ => false,
        }
    }

    pub(super) fn same_erased_ty<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        a: Ty<'tcx>,
        b: Ty<'tcx>,
    ) -> bool {
        vm_state.size_of_ty(a) > 0
            && vm_state.size_of_ty(b) > 0
            && vm_state.size_of_ty(a) == vm_state.size_of_ty(b)
    }

    pub(super) fn is_caller_type_param<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Param(param_ty) = ty.kind() else {
            return false;
        };
        let generics = vm_state.tcx.generics_of(vm_state.caller_def_id);
        generics.own_params.iter().any(|p| {
            matches!(p.kind, rustc_middle::ty::GenericParamDefKind::Type { .. })
                && p.name == param_ty.name
        })
    }
}
