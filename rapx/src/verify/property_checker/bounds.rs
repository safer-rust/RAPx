//! Checkers for `InBound` and `NonOverlap`.
//!
//! Bounds are discharged from `has_checked_bounds` facts, layout field-offset
//! invariants, or an SMT coverage check over allocation base/size.
//! `NonOverlap` uses provenance-distinctness and range-overlap reasoning.

use crate::verify::checkpoint::Checkpoint;
use crate::helpers::mir_utils;
use crate::verify::api_classify;
use crate::verify::contract::{
    ContractExpr, ContractKind, NumericBinOp, PlaceBase, Property, PropertyArg, RelOp,
};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::{OffsetKind, VmState, VmValue};
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyKind};
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_slice_offset<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        _checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let locals: Option<Vec<Local>> = property.args().iter().map(|arg| {
            let PropertyArg::Expr(ContractExpr::Place(place)) = arg else { return None };
            place.projections.is_empty().then(|| place.base.to_local())
        }).collect();
        let Some(locals) = locals else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let [dest, base_local, index_local] = locals.as_slice() else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let (Some(actual), Some(base), Some(index)) = (
            vm_state.local_value(*dest),
            vm_state.local_value(*base_local),
            vm_state.local_value(*index_local),
        ) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let exact_start = vm_state.slice_index_start(index, *index_local).is_some();
        let mut state = vm_state.clone();
        if !state.apply_slice_offset(*dest, base, index, *index_local) {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        let Some(expected) = state.local_value(*dest) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        match (actual.provenance_alloc_id(), expected.provenance_alloc_id()) {
            (Some(left), Some(right)) if left != right => {
                return CheckResult::Unknown(UnknownReason::Unimplemented);
            }
            (Some(_), Some(_)) => {}
            _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
        }
        if !exact_start {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        let solver = Solver::new(vm_state.z3_ctx);
        state.assert_all(&solver);
        let address_wrong = actual.z3_term._eq(&expected.z3_term).not();
        let output_is_slice = mir_utils::pointee_ty(actual.ty)
            .is_some_and(|ty| matches!(ty.kind(), TyKind::Slice(_) | TyKind::Str));
        let wrong = if output_is_slice {
            let (Some(actual_len), Some(expected_len)) = (
                vm_state.field_value(*dest, &[1]),
                vm_state.slice_index_output_len(base, index, *index_local),
            ) else {
                return CheckResult::Unknown(UnknownReason::Unimplemented);
            };
            Bool::or(
                vm_state.z3_ctx,
                &[&address_wrong, &actual_len.z3_term._eq(&expected_len).not()],
            )
        } else {
            address_wrong
        };
        solver.assert(&wrong);
        match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat
                if actual.z3_term == base.z3_term
                    && matches!(index.ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::Usize)) =>
            {
                CheckResult::Failed
            }
            SatResult::Sat => CheckResult::Unknown(UnknownReason::Unimplemented),
            SatResult::Unknown => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        }
    }

    pub(super) fn check_in_bound<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        if property.for_each().is_some() {
            return CheckResult::ProvedByRule;
        }

        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { .. })) =
            property.args().first()
        {
            return self.check_in_bound_slice(vm_state, &solver, checkpoint, property);
        }

        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }

        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if property.contract_kind() == ContractKind::Postcond
            && let Some(PropertyArg::Ty(ty)) = property.args().get(1)
            && matches!(ty.kind(), TyKind::Alias(..) | TyKind::Slice(..) | TyKind::Str)
        {
            let concrete_ty = if matches!(ty.kind(), TyKind::Alias(..)) {
                mir_utils::pointee_ty(value.ty).unwrap_or(*ty)
            } else {
                *ty
            };
            if let Some(alloc_id) = value.provenance_alloc_id()
                && vm_state.has_bounded_object_span(alloc_id, &value.z3_term, concrete_ty)
            {
                return CheckResult::ProvedByRule;
            }
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        // `in_bounds` records "points at a valid element" (established by a
        // single-element deref/contract), so it only discharges a single-element
        // InBound.  A `count > 1` check still needs the byte-range proof below.
        if value.facts.in_bounds {
            let count_one = property
                .args()
                .get(2)
                .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
                .is_none_or(|c| c.simplify().as_u64() == Some(1));
            if count_one {
                return CheckResult::ProvedByRule;
            }
        }
        // `byte_add(offset_of!(Container, field))` always keeps the pointer
        // within the container allocation, because the byte offset of a field
        // never exceeds `size_of::<Container>()`.  This covers patterns such
        // as `Option::as_slice`.
        if self.count_is_offset_of(vm_state, checkpoint, property, &value) {
            return CheckResult::ProvedByRule;
        }
        if self.count_is_zero(vm_state, checkpoint, property, 2) {
            return CheckResult::ProvedByRule;
        }
        let access = self.access_bytes(vm_state, property, 1, 2, checkpoint, &value);
        let Some(alloc_id) = value.provenance_alloc_id() else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let base = vm_state.allocation_base(alloc_id).clone();
        let size = vm_state.allocation_size(alloc_id).clone();

        let alloc = vm_state.alloc(alloc_id);
        // An external allocation whose size is the `i64::MAX` "unbounded"
        // sentinel (a Vec/slice buffer, or a materialized `Allocated` fact)
        // auto-passes any `InBound` access.  A *raw-pointer target* carries a
        // symbolic "unknown" size instead, so its access falls through and must
        // be proved (and otherwise fails).
        if alloc.is_external() && size.simplify().as_u64() == Some(i64::MAX as u64) {
            return CheckResult::ProvedByRule;
        }

        // Element-level bounds fast-path: when the allocation materializes a
        // slice length and the pointer was derived by element-strided arithmetic
        // (its `element_offset` is tracked), check `k + count <= len` linearly.
        // This avoids the non-linear `(k + count)·S <= len·S` byte form for a
        // generic element size `S`, which Z3's NIA solver cannot decide.
        // `sub` walks *backwards* (`[value - access, value)`), so this forward
        // form would mis-classify `end.sub(n)` as out of bounds; the `sub`-aware
        // byte-range proof below handles that direction.
        let matching_element_ty = property
            .args()
            .get(1)
            .and_then(|arg| match arg {
                PropertyArg::Ty(ty) => Some(vm_state.instantiate_callsite_ty(checkpoint, *ty)),
                _ => None,
            })
            .is_none_or(|ty| Some(ty) == alloc.element_ty.as_ty());
        if !api_classify::is_pointer_sub(checkpoint.callee)
            && matching_element_ty
            && let (Some(len), Some(k)) = (
                alloc.slice_len().cloned(),
                value
                    .provenance
                    .as_ref()
                    .and_then(|p| match &p.offset_kind {
                        Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
                        _ => None,
                    }),
            ) {
                let count_term = property
                    .args()
                    .get(2)
                    .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
                    .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
                let zero = Int::from_u64(vm_state.z3_ctx, 0);
                let covered = Int::add(vm_state.z3_ctx, &[&k, &count_term]);
                solver.push();
                solver.assert(&z3::ast::Bool::or(
                    vm_state.z3_ctx,
                    &[&covered.gt(&len), &k.lt(&zero)],
                ));
                let r = match solver.check() {
                    SatResult::Unsat => CheckResult::ProvedBySmt,
                    SatResult::Sat => CheckResult::Failed,
                    _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
                };
                solver.pop(1);
                return r;
            }

        let alloc_elem_is_generic = vm_state
            .alloc(alloc_id)
            .element_ty
            .as_ty()
            .is_some_and(|ty| matches!(ty.kind(), TyKind::Param(_)));
        let fallback_for_generic =
            alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some();

        solver.push();
        // A field-offset pointer (`byte_add(offset_of!())`) is valid within the
        // *field* it addresses: the accessed range must fit in the field's own
        // size.  "The field lies inside its container" is a layout invariant
        // that needs no proof here, so skip the container-coverage check below
        // (whose container layout may be unknown, e.g. `Option<T>`).
        if value
            .provenance
            .as_ref()
            .is_some_and(|prov| matches!(prov.offset_kind, Some(OffsetKind::Field)))
        {
            let field_size = mir_utils::pointee_ty(value.ty)
                .map(|ty| vm_state.size_sym_read(ty))
                .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
            solver.assert(&access.le(&field_size).not());
            let r = match solver.check() {
                SatResult::Unsat => CheckResult::ProvedBySmt,
                SatResult::Sat => CheckResult::Failed,
                _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
            };
            solver.pop(1);
            return r;
        }

        let bound = Int::add(vm_state.z3_ctx, &[&base, &size]);
        // `sub` walks *backwards*: the accessed range is `[value - access, value)`,
        // so the lower bound is `value - access >= base` and the upper bound is
        // `value <= base + size`.  `add` (and everything else) walks forwards.
        let (above_negated, below_negated) = if api_classify::is_pointer_sub(checkpoint.callee) {
            let walked = Int::sub(vm_state.z3_ctx, &[&value.z3_term, &access]);
            (value.z3_term.gt(&bound), walked.lt(&base))
        } else {
            let covered = Int::add(vm_state.z3_ctx, &[&value.z3_term, &access]);
            (covered.gt(&bound), value.z3_term.lt(&base))
        };
        let negated = z3::ast::Bool::or(vm_state.z3_ctx, &[&above_negated, &below_negated]);

        // Generic element size: discharge by a case split on `S = 0` (ZST) vs
        // `S ≥ 1` (non-ZST) rather than a single nonlinear query.
        if let Some(s) = vm_state.generic_elem_size(alloc_id) {
            solver.pop(1);
            let on_sat = if fallback_for_generic {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            } else {
                CheckResult::Failed
            };
            return Self::smt_check_size_split(vm_state, &s, &negated, on_sat);
        }

        solver.assert(&negated);
        let sat_result = solver.check();
        let r = match sat_result {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat if fallback_for_generic => {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            }
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        };
        solver.pop(1);
        r
    }

    pub(super) fn count_is_offset_of<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        value: &VmValue<'z3, 'tcx>,
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
            mir_utils::offset_of_container(vm_state.tcx, &c.const_)
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
        mir_utils::pointee_ty(value.ty).is_some_and(|pointee| pointee == container)
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

    pub(super) fn check_in_bound_slice<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        solver: &Solver<'z3>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let (slice_arg_idx, index_arg_idx) = Self::resolve_index_access_args(property);

        let slice_val = match slice_arg_idx.and_then(|idx| checkpoint.args.get(idx)) {
            Some(op) => vm_state.value_of_operand(op),
            None => return CheckResult::Unknown(UnknownReason::Unimplemented),
        };
        if let Some(index_op) = index_arg_idx.and_then(|idx| checkpoint.args.get(idx)) {
            let index_val = vm_state.value_of_operand(index_op);
            if vm_state.index_access_facts.iter().any(|(slice, index, _, _)| {
                slice.to_string() == slice_val.z3_term.to_string()
                    && index.to_string() == index_val.z3_term.to_string()
            }) {
                return CheckResult::ProvedByRule;
            }
        }
        let (index_val, range_start, is_range, inclusive) = match index_arg_idx.and_then(|idx| checkpoint.args.get(idx)) {
            Some(op) => {
                if let Some(end_val) = self.extract_range_end(vm_state, op) {
                    let index_ty = vm_state.value_of_operand(op).ty;
                    let (needs_start, inclusive) = match index_ty.kind() {
                        TyKind::Adt(def, _) => {
                            let kind = mir_utils::range_kind(vm_state.tcx, def.did());
                            (
                                matches!(kind, mir_utils::RangeKind::Range | mir_utils::RangeKind::RangeInclusive)
                                    || api_classify::is_index_range(def.did()),
                                matches!(kind, mir_utils::RangeKind::RangeInclusive),
                            )
                        }
                        _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
                    };
                    let start = if needs_start {
                        match self.extract_range_field(vm_state, op, 0) {
                            Some(value) => Some(value.z3_term),
                            None => return CheckResult::Unknown(UnknownReason::Unimplemented),
                        }
                    } else {
                        None
                    };
                    (end_val, start, true, inclusive)
                } else {
                    let value = vm_state.value_of_operand(op);
                    match value.ty.kind() {
                        TyKind::Uint(rustc_middle::ty::UintTy::Usize) => {
                            (value, None, false, false)
                        }
                        TyKind::Adt(def, _) => {
                            let did = def.did();
                            let kind = mir_utils::range_kind(vm_state.tcx, did);
                            if matches!(kind, mir_utils::RangeKind::RangeFrom)
                                || crate::def_ids::lang_api::matches(
                                    vm_state.tcx,
                                    did,
                                    crate::def_ids::lang_api::LangItem::RangeToInclusive,
                                )
                            {
                                let Some(field) = self.extract_range_field(vm_state, op, 0) else {
                                    return CheckResult::Unknown(UnknownReason::Unimplemented);
                                };
                                let inclusive = !matches!(kind, mir_utils::RangeKind::RangeFrom);
                                (field, None, true, inclusive)
                            } else if crate::def_ids::lang_api::matches(
                                vm_state.tcx,
                                did,
                                crate::def_ids::lang_api::LangItem::RangeFull,
                            ) {
                                (
                                    VmValue::new(Int::from_u64(vm_state.z3_ctx, 0), vm_state.tcx.types.usize),
                                    None,
                                    true,
                                    false,
                                )
                            } else {
                                return CheckResult::Unknown(UnknownReason::Unimplemented);
                            }
                        }
                        _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
                    }
                }
            }
            None => return CheckResult::Unknown(UnknownReason::Unimplemented),
        };

        let data_alloc_id = slice_val.provenance_alloc_id();
        let Some(data_alloc_id) = data_alloc_id else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };

        let len = vm_state
            .slice_len_from_value(&slice_val)
            .unwrap_or_else(|| {
                let size = vm_state.allocation_size(data_alloc_id).clone();
                let elem_sz = vm_state
                    .alloc(data_alloc_id)
                    .element_ty
                    .as_ty()
                    .map(|ty| vm_state.size_sym_read(ty))
                    .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
                size.div(&elem_sz)
            });

        solver.push();
        let valid = if let Some(start) = range_start {
            let end_valid = if inclusive {
                index_val.z3_term.lt(&len)
            } else {
                index_val.z3_term.le(&len)
            };
            Bool::and(vm_state.z3_ctx, &[&start.le(&index_val.z3_term), &end_valid])
        } else if is_range {
            if inclusive {
                index_val.z3_term.lt(&len)
            } else {
                index_val.z3_term.le(&len)
            }
        } else {
            index_val.z3_term.lt(&len)
        };
        solver.assert(&valid.not());
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        };
        solver.pop(1);
        r
    }

    pub(super) fn extract_range_end<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        op: &Operand<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        if !place.projection.is_empty() {
            return None;
        }
        let range_local = place.local;
        let ty = vm_state.body().local_decls[range_local].ty;
        let adt_def = match ty.kind() {
            TyKind::Adt(adt_def, _) => *adt_def,
            _ => return None,
        };
        // The `end` field index depends on the range kind: `Range`/`RangeInclusive`
        // store `(start, end)` (end at field 1), while `RangeTo` stores just `end`
        // (field 0). `RangeFrom`/`RangeFull`/`RangeToInclusive` have no usable end
        // field here and fall back to the single-index path.
        let end_idx = match mir_utils::range_kind(vm_state.tcx, adt_def.did()) {
            mir_utils::RangeKind::RangeTo => {
                Some(rustc_abi::FieldIdx::from_usize(0))
            }
            mir_utils::RangeKind::Range
            | mir_utils::RangeKind::RangeInclusive => {
                Some(rustc_abi::FieldIdx::from_usize(1))
            }
            mir_utils::RangeKind::Other => {
                // `core::ops::IndexRange` is a private `{ start, end }` struct
                // (no lang item); its `end` lives at field 1 like `Range`.
                if api_classify::is_index_range(adt_def.did()) {
                    Some(rustc_abi::FieldIdx::from_usize(1))
                } else {
                    None
                }
            }
            _ => None,
        };
        self.extract_range_field(vm_state, op, end_idx?.as_usize())
    }

    fn extract_range_field<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        op: &Operand<'tcx>,
        field_idx: usize,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p,
            _ => return None,
        };
        let range_local = place.local;
        if let Some(value) = vm_state.field_value(range_local, &[field_idx]) {
            return Some(value.clone());
        }
        for block in vm_state.body().basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == range_local && dest.projection.is_empty()
                        && let Rvalue::Aggregate(_kind, operands) = rvalue
                            && let Some(field_op) = operands.get(rustc_abi::FieldIdx::from_usize(field_idx)) {
                                return Some(self.trace_value(vm_state, field_op));
                            }
                }
            }
        }
        None
    }

    pub(super) fn check_non_overlap<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        if property.args().len() == 1 {
            return self.check_non_overlap_indices(vm_state, checkpoint, property);
        }
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        let Some(v1) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
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
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        // Only discharge non-overlap when both pointers carry provenance into
        // distinct allocations. `Option` comparison here is unsound: a `None`
        // (unknown) provenance would compare unequal to any concrete `AllocId`
        // and spuriously report the pointers as non-overlapping.
        if let (Some(a), Some(b)) = (v1.provenance_alloc_id(), v2.provenance_alloc_id())
            && a != b {
                return CheckResult::ProvedByRule;
            }

        let Some(count_term) = checkpoint
            .args
            .get(2)
            .map(|op| vm_state.value_of_operand(op).z3_term)
        else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let elem_size = vm_state
            .pointee_elem_size(v1.ty)
            .max(vm_state.pointee_elem_size(v2.ty));
        if count_term.simplify().as_u64() == Some(0) {
            return CheckResult::ProvedByRule;
        }
        if elem_size == 0 {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        let range = Int::mul(
            vm_state.z3_ctx,
            &[&Int::from_u64(vm_state.z3_ctx, elem_size), &count_term],
        );
        let src_end = Int::add(vm_state.z3_ctx, &[&v1.z3_term, &range]);
        let dst_end = Int::add(vm_state.z3_ctx, &[&v2.z3_term, &range]);
        solver.push();
        let overlap = Bool::and(
            vm_state.z3_ctx,
            &[
                &range.gt(&Int::from_u64(vm_state.z3_ctx, 0)),
                &v1.z3_term.lt(&dst_end),
                &v2.z3_term.lt(&src_end),
            ],
        );
        solver.assert(&overlap);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        };
        solver.pop(1);
        r
    }

    fn check_non_overlap_indices<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(array) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let TyKind::Array(elem_ty, len) = array.ty.kind() else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let Some(n) = mir_utils::eval_array_len(vm_state.tcx, len)
            .and_then(|n| usize::try_from(n).ok())
        else {
            let solver = Solver::new(vm_state.z3_ctx);
            vm_state.assert_all(&solver);
            match solver.check() {
                SatResult::Unsat => return CheckResult::ProvedBySmt,
                SatResult::Unknown => {
                    return CheckResult::Unknown(UnknownReason::from_solver(&solver));
                }
                SatResult::Sat => {}
            }
            let n = vm_state.const_len_term(len);
            solver.assert(&n.ge(&Int::from_u64(vm_state.z3_ctx, 2)));
            return match solver.check() {
                SatResult::Unsat => CheckResult::ProvedBySmt,
                SatResult::Sat => CheckResult::Unknown(UnknownReason::Unimplemented),
                SatResult::Unknown => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
            };
        };
        if n < 2 {
            return CheckResult::ProvedByRule;
        }
        let range_inclusive = if *elem_ty == vm_state.tcx.types.usize {
            None
        } else if let TyKind::Adt(def, args) = elem_ty.kind()
            && args.types().next() == Some(vm_state.tcx.types.usize)
        {
            match vm_state.tcx.def_path_str(def.did()).as_str() {
                "core::ops::range::Range" | "core::ops::Range" | "core::range::Range"
                | "std::ops::Range" => Some(false),
                "core::ops::range::RangeInclusive" | "core::ops::RangeInclusive"
                | "core::range::RangeInclusive" | "std::ops::RangeInclusive" => Some(true),
                _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
            }
        } else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let Some(place) = property.target_place() else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if !place.projections.is_empty() {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        }
        let local = match place.base {
            PlaceBase::Arg(index) => checkpoint
                .args
                .get(index)
                .and_then(Operand::place)
                .map(|p| p.local),
            PlaceBase::Local(index) => Some(Local::from_usize(index)),
            PlaceBase::Return => Some(Local::from_usize(0)),
        };
        let Some(local) = local else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let Some(elements) = (0..n)
            .map(|i| {
                let start_path = if range_inclusive.is_some() {
                    vec![i, 0]
                } else {
                    vec![i]
                };
                let start = vm_state.field_value(local, &start_path)?.z3_term.clone();
                let end = if range_inclusive.is_some() {
                    Some(vm_state.field_value(local, &[i, 1])?.z3_term.clone())
                } else {
                    None
                };
                Some((start, end))
            })
            .collect::<Option<Vec<_>>>()
        else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let solver = Solver::new(vm_state.z3_ctx);
        vm_state.assert_all(&solver);
        match solver.check() {
            SatResult::Unsat => return CheckResult::ProvedBySmt,
            SatResult::Unknown => {
                return CheckResult::Unknown(UnknownReason::from_solver(&solver));
            }
            SatResult::Sat => {}
        }
        for (i, (left_start, left_end)) in elements.iter().enumerate() {
            for (right_start, right_end) in elements.iter().skip(i + 1) {
                let overlap = match (left_end, right_end, range_inclusive) {
                    (Some(left_end), Some(right_end), Some(true)) => Bool::and(
                        vm_state.z3_ctx,
                        &[&left_start.le(right_end), &right_start.le(left_end)],
                    ),
                    (Some(left_end), Some(right_end), Some(false)) => Bool::and(
                        vm_state.z3_ctx,
                        &[&left_start.lt(right_end), &right_start.lt(left_end)],
                    ),
                    (None, None, None) => left_start._eq(right_start),
                    _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
                };
                solver.push();
                solver.assert(&overlap);
                let result = solver.check();
                solver.pop(1);
                match result {
                    SatResult::Unsat => {}
                    SatResult::Sat => return CheckResult::Failed,
                    SatResult::Unknown => {
                        return CheckResult::Unknown(UnknownReason::from_solver(&solver));
                    }
                }
            }
        }
        CheckResult::ProvedBySmt
    }

    pub(super) fn all_predicates_are_slice_size_invariant<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        predicates: &[crate::verify::contract::NumericPredicate<'tcx>],
    ) -> bool {
        !predicates.is_empty()
            && predicates
                .iter()
                .all(|p| self.predicate_is_slice_size_invariant(vm_state, checkpoint, p))
    }

    pub(super) fn predicate_is_slice_size_invariant<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> bool {
        if !matches!(pred.op, RelOp::Le | RelOp::Lt) {
            return false;
        }
        let ContractExpr::Const(bound) = &pred.rhs else {
            return false;
        };
        if *bound < i64::MAX as u128 {
            return false;
        }
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
        let resolved_ty = vm_state.instantiate_callsite_ty(checkpoint, size_ty);
        self.count_derives_from_slice_param(vm_state, checkpoint, count_expr, resolved_ty)
    }

    pub(super) fn count_derives_from_slice_param<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        count_expr: &ContractExpr<'tcx>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
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
            mir_utils::callee_param_index_for_local(vm_state.tcx, callee, local)
        else {
            return false;
        };
        if matches!(checkpoint.args.get(arg_idx), Some(Operand::Constant(_))) {
            return false;
        }
        let body = vm_state.body();
        let has_slice_param = (1..=body.arg_count).any(|i| {
            let param_ty = body.local_decls[Local::from_usize(i)].ty;
            self.is_slice_ref_with_elem(param_ty, elem_ty, vm_state, checkpoint)
        });
        if has_slice_param {
            return true;
        }
        if let Some(op) = checkpoint.args.first() {
            let target_val = vm_state.value_of_operand(op);
            if target_val.is_pointer() {
                return true;
            }
        }
        false
    }

    pub(super) fn is_slice_ref_with_elem<'z3, 'tcx>(
        &self,
        ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() else {
            return false;
        };
        match inner.kind() {
            rustc_middle::ty::TyKind::Slice(slice_elem) => {
                let resolved = vm_state.instantiate_callsite_ty(checkpoint, *slice_elem);
                self.same_erased_ty(vm_state, resolved, elem_ty)
            }
            _ => false,
        }
    }

    pub(super) fn same_erased_ty<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        a: Ty<'tcx>,
        b: Ty<'tcx>,
    ) -> bool {
        vm_state.size_of_ty(a) > 0
            && vm_state.size_of_ty(b) > 0
            && vm_state.size_of_ty(a) == vm_state.size_of_ty(b)
    }


}
