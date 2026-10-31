//! Checkers for memory-shape properties: `Align`, `NonNull`, `Allocated`,
//! `Init`, and `Alive`.
//!
//! These consume the VM's provenance/invariant facts (e.g. `align_n`,
//! `in_bounds`, `non_null`) with fast paths, falling back to SMT over
//! `value.z3_term` and allocation base/size.

use crate::helpers::mir_utils;
use crate::verify::checkpoint::Checkpoint;
use crate::verify::api_classify;
use crate::verify::contract::{ContractExpr, Property, PropertyArg, is_static_lifetime_ident};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::{AllocId, OffsetKind, VmState, VmValue};
use rustc_hash::FxHashSet;
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::TyKind;
use z3::{
    DeclKind, SatResult, Solver,
    ast::{Ast, Int},
};

use super::PropertyChecker;
use super::util::maybe_uninit_inner;

/// Prove divisibility from the expression tree of a pointer offset.
/// Unknown forms return false, so they continue to the SMT check.
fn multiple_of(term: &Int<'_>, divisor: u64, depth: usize) -> bool {
    if divisor == 0 {
        return false;
    }
    if let Some(n) = term.as_u64() {
        return n % divisor == 0;
    }
    if depth == 0 {
        return false;
    }
    let child = |index| term.nth_child(index).and_then(|ast| ast.as_int());
    match term.decl().kind() {
        DeclKind::ADD | DeclKind::SUB => (0..term.num_children())
            .all(|i| child(i).is_some_and(|c| multiple_of(&c, divisor, depth - 1))),
        DeclKind::MUL => (0..term.num_children())
            .any(|i| child(i).is_some_and(|c| multiple_of(&c, divisor, depth - 1))),
        DeclKind::UMINUS => child(0).is_some_and(|c| multiple_of(&c, divisor, depth - 1)),
        DeclKind::ITE => {
            child(1).is_some_and(|c| multiple_of(&c, divisor, depth - 1))
                && child(2).is_some_and(|c| multiple_of(&c, divisor, depth - 1))
        }
        _ => false,
    }
}

impl PropertyChecker {
    pub(super) fn check_align<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };

        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        if self.is_concrete_zst(vm_state, value.ty) {
            return CheckResult::ProvedByRule;
        }
        let ty_arg = property.ty_arg(1);
        let align = match ty_arg {
            Some(ty) => {
                let resolved = vm_state.instantiate_callsite_ty(checkpoint, ty);
                vm_state.align_sym_read(resolved)
            }
            None => Int::from_u64(vm_state.z3_ctx, 1),
        };
        if align.simplify().as_u64() == Some(1) {
            return CheckResult::ProvedByRule;
        }
        // A pointer whose term is a known local's *stack address* is aligned to
        // that local's own type alignment, regardless of the value's provenance.
        // A borrow of a `Box`/`Vec` local (`&mut _1` / `&raw mut (*&mut _1)`)
        // carries the pointee's *heap* provenance, so the provenance-based
        // alignment below would compare against the pointee's alignment; the
        // pointer itself, however, is aligned to the stack slot's type
        // (`align_of::<Box<i32>>() = 8`).  Require a provenance so a pointer
        // local whose value fell back to its own stack-address default (and is
        // really some unaligned offset) is not mistaken for a stack borrow.
        if value.is_pointer()
            && let Some(local) = vm_state.find_local_by_address(&value.z3_term) {
                let local_ty = vm_state.body().local_decls[local].ty;
                let local_align = vm_state.align_sym_read(local_ty);
                if let Some(local_align_u64) = local_align.simplify().as_u64()
                    && local_align_u64 != 1
                        && let Some(align_u64) = align.simplify().as_u64()
                            && local_align_u64 >= align_u64 {
                                return CheckResult::ProvedByRule;
                            }
            }
        // Symbolic fast-path: if the value is known to be at least `align`-aligned
        // (its effective alignment satisfies `align_n >= align`, both powers of
        // two), the check holds without a modulo query — Z3 cannot discharge
        // `% align_T == 0` for a symbolic divisor, but `align_n >= align` is a
        // linear inequality it *can* decide given the tracked bounds.
        //
        // For a field-offset pointer (`base + offset_of!(Container, field)`) the
        // effective alignment is the *field's* own type alignment, not the
        // container's.
        let effective_align_n = if value
            .provenance
            .as_ref()
            .is_some_and(|prov| matches!(prov.offset_kind, Some(OffsetKind::Field)))
        {
            mir_utils::pointee_ty(value.ty).map(|ty| vm_state.align_sym_read(ty))
        } else {
            value.facts.align_n.clone()
        };
        if let Some(known_align) = effective_align_n {
            if let (Some(known_u64), Some(align_u64)) =
                (known_align.simplify().as_u64(), align.simplify().as_u64())
                && known_u64 >= align_u64 {
                    return CheckResult::ProvedByRule;
                }
            let solver = Solver::new(vm_state.z3_ctx);
            solver.push();
            vm_state.assert_all(&solver);
            solver.assert(&known_align.lt(&align));
            let r = solver.check();
            solver.pop(1);
            // `align_n` is only a *lower bound* on the value's alignment: even
            // when `align_n >= align` is satisfiable (not implied), the pointer
            // may still be `align`-aligned through a separate path condition
            // (e.g. `ptr.align_offset(align)` guarantees
            // `(ptr + off*elem) % align == 0`).  Fall through to the full
            // modulo query rather than reporting `Failed` prematurely.
            if matches!(r, SatResult::Unsat) {
                return CheckResult::ProvedBySmt;
            }
        }
        if let Some(prov) = &value.provenance
            && let Some(aligned_ty) = vm_state.alloc(prov.alloc_id).facts.for_each.aligned_ty {
                let fa = vm_state.align_sym_read(aligned_ty);
                if let (Some(fa_u64), Some(align_u64)) =
                    (fa.simplify().as_u64(), align.simplify().as_u64())
                    && fa_u64 >= align_u64 {
                        return CheckResult::ProvedByRule;
                    }
            }
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            // `MaybeUninit<T>` and T share alignment; an array has its
            // element's alignment. A live stack local carries that guarantee
            // even when the full generic layout is symbolic.
            if !alloc.is_external()
                && let Some(required) = align.simplify().as_u64()
                && let Some(local) = vm_state.current_frame.local_alloc.iter().find_map(|(local, id)| {
                    (*id == prov.alloc_id).then_some(*local)
                })
            {
                let mut local_ty = vm_state.body().local_decls[local].ty;
                let mut peeled = false;
                loop {
                    if let Some(inner) = maybe_uninit_inner(local_ty) {
                        local_ty = inner;
                    } else if let TyKind::Array(elem, _) = local_ty.kind() {
                        local_ty = *elem;
                    } else {
                        break;
                    }
                    peeled = true;
                }
                if peeled
                    && vm_state.align_of_ty(local_ty) >= required
                    && multiple_of(&prov.offset, required, 24)
                {
                    return CheckResult::ProvedByRule;
                }
            }
            let off_u64 = prov
                .offset
                .as_u64()
                .or_else(|| prov.offset.simplify().as_u64());
            if let (Some(off), Some(align_u64), Some(alloc_align_u64)) = (
                off_u64,
                align.simplify().as_u64(),
                alloc.align.simplify().as_u64(),
            )
                && alloc_align_u64 >= align_u64 {
                    return if off % align_u64 == 0 {
                        CheckResult::ProvedByRule
                    } else {
                        CheckResult::Failed
                    };
                }
        }
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            if let (Some(alloc_align_u64), Some(align_u64)) =
                (alloc.align.simplify().as_u64(), align.simplify().as_u64())
                && alloc_align_u64 < align_u64
                    && let Some(off) = prov.offset.as_u64()
                        && off % align_u64 != 0 {
                            return CheckResult::Failed;
                        }
        }
        let align_term = align;
        let zero = Int::from_u64(vm_state.z3_ctx, 0);
        let local = Solver::new(vm_state.z3_ctx);
        local.push();
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            local.assert(
                &value
                    .z3_term
                    ._eq(&Int::add(vm_state.z3_ctx, &[&alloc.base, &prov.offset])),
            );
            local.assert(&alloc.base._eq(&zero).not());
            local.assert(&alloc.base.ge(&zero));
            if alloc.align.simplify().as_u64() != Some(1) {
                local.assert(&alloc.base.rem(&alloc.align)._eq(&zero));
            }
        }
        if let Some(known_align) = value.facts.align_n.as_ref() {
            local.assert(&value.z3_term.rem(known_align)._eq(&zero));
        }
        vm_state.assert_path_constraints(&local);
        let negated = value.z3_term.rem(&align_term)._eq(&zero).not();
        local.assert(&negated);
        let r = match local.check() {
            z3::SatResult::Sat
                if value.provenance.is_none()
                    && value.facts.align_n.is_none()
                    && value.z3_term.simplify().as_u64().is_none() =>
            {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            }
            z3::SatResult::Sat => CheckResult::Failed,
            z3::SatResult::Unsat => CheckResult::ProvedBySmt,
            z3::SatResult::Unknown => CheckResult::Unknown(UnknownReason::from_solver(&local)),
        };
        local.pop(1);
        if matches!(r, CheckResult::Failed) {
            rap_debug!(
                "align=Failed vterm={} align_n={:?} off={}",
                value.z3_term.to_string(),
                value.facts.align_n,
                value
                    .provenance
                    .as_ref()
                    .map(|p| p.offset.to_string())
                    .unwrap_or_default()
            );
        }
        r
    }

    pub(super) fn value_aligned_to<'z3, 'tcx>(
        vm_state: &VmState<'z3, 'tcx>,
        value: &VmValue<'z3, 'tcx>,
        align: u64,
    ) -> bool {
        if align <= 1 {
            return true;
        }
        if let Some(n) = value
            .facts
            .align_n
            .as_ref()
            .and_then(|n| n.simplify().as_u64())
            && n >= align && n % align == 0 {
                return true;
            }
        let solver = Solver::new(vm_state.z3_ctx);
        solver.push();
        let zero = Int::from_u64(vm_state.z3_ctx, 0);
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            solver.assert(
                &value
                    .z3_term
                    ._eq(&Int::add(vm_state.z3_ctx, &[&alloc.base, &prov.offset])),
            );
            solver.assert(&alloc.base.ge(&zero));
            if alloc.align.simplify().as_u64() != Some(1) {
                solver.assert(&alloc.base.rem(&alloc.align)._eq(&zero));
            }
        }
        vm_state.assert_path_constraints(&solver);
        let align_term = Int::from_u64(vm_state.z3_ctx, align);
        solver.assert(&value.z3_term.rem(&align_term)._eq(&zero).not());
        let r = solver.check() == SatResult::Unsat;
        solver.pop(1);
        r
    }

    pub(super) fn check_non_null<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if value.facts.non_null || value.facts.in_bounds {
            return CheckResult::ProvedByRule;
        }
        if let Some(ref prov) = value.provenance
            && !vm_state.alloc(prov.alloc_id).is_external() {
                return CheckResult::ProvedByRule;
            }
        // For an external pointer, check nullability against the *path
        // conditions* only.  `assert_all` also asserts every live value's
        // derived `non_null` flag, but the `&T` produced by this very deref
        // shares the source pointer's term and is marked non-null — using it
        // would circularly "prove" `NonNull` on the pointer being dereferenced.
        let zero = Int::from_u64(vm_state.z3_ctx, 0);
        let local = Solver::new(vm_state.z3_ctx);
        vm_state.assert_path_constraints(&local);
        self.smt_check(&local, &value.z3_term._eq(&zero))
    }

    pub(super) fn check_null<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // `Null(p)` is the guard branch of `any(Null(p), ...)`.  It is Proved
        // when `p` is null (or carries no allocation, i.e. not known non-null),
        // making the guarded obligation vacuous; otherwise Failed, so the other
        // disjunct decides the outcome.
        let Some(place) = (match property.args().first() {
            Some(PropertyArg::Expr(ContractExpr::Place(p))) => Some(p),
            _ => None,
        }) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if self.is_null(vm_state, checkpoint, place) {
            CheckResult::ProvedByRule
        } else {
            CheckResult::Failed
        }
    }

    pub(super) fn check_allocated<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let value = vm_state.resolve_pointer_provenance(value);

        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        if self.is_concrete_zst(vm_state, value.ty) {
            return CheckResult::ProvedByRule;
        }

        if self.count_is_zero(vm_state, checkpoint, property, 2) {
            return CheckResult::ProvedByRule;
        }

        let Some(alloc_id) = value.provenance_alloc_id() else {
            if value.facts.dangling {
                return CheckResult::Failed;
            }
            if crate::verify::api_classify::is_manually_drop_drop(checkpoint.callee) {
                return CheckResult::ProvedByRule;
            }
            if value.z3_term.simplify().as_u64() == Some(0) {
                return CheckResult::Failed;
            }
            if value.z3_term.to_string().contains("const_") {
                return CheckResult::Failed;
            }
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };

        if vm_state.alloc(alloc_id).facts.dead {
            if !vm_state.is_maybe_uninit_ptr(&value, alloc_id) {
                let is_param_ref = vm_state.resolve_origin(&value).is_some_and(|origin| {
                    origin.local.as_usize() <= vm_state.body().arg_count
                        && origin.local != Local::from_usize(0)
                });
                if !is_param_ref {
                    return CheckResult::Failed;
                }
            }
        }

        let required_ty = property
            .args()
            .get(1)
            .and_then(|a| {
                if let PropertyArg::Ty(ty) = a {
                    Some(*ty)
                } else {
                    None
                }
            })
            .map(|ty| vm_state.instantiate_callsite_ty(checkpoint, ty));

        if let Some(required_ty) = required_ty.map(|ty| {
            if matches!(ty.kind(), TyKind::Alias(..)) {
                mir_utils::pointee_ty(value.ty).unwrap_or(ty)
            } else {
                ty
            }
        })
            && property
                .args()
                .get(2)
                .and_then(|arg| self.resolve_arg_term(vm_state, checkpoint, arg))
                .is_none_or(|count| count.simplify().as_u64() == Some(1))
            && vm_state.has_bounded_object_span(alloc_id, &value.z3_term, required_ty)
        {
            return CheckResult::ProvedByRule;
        }

        // `Allocated(container.iter(), T, n)` for_each: every element pointer
        // backs `>= n` `T` elements, so a pointer loaded from the container
        // (whose provenance names the container allocation) satisfies
        // `Allocated(cur, T, n)`.
        if let Some((t, n)) = &vm_state.alloc(alloc_id).facts.for_each.allocated {
            let resolved_t = vm_state.instantiate_callsite_ty(checkpoint, *t);
            if Some(resolved_t) == required_ty {
                let req_count = property
                    .args()
                    .get(2)
                    .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a));
                let count_ok = match (
                    n.simplify().as_u64(),
                    req_count.as_ref().and_then(|c| c.simplify().as_u64()),
                ) {
                    (Some(fact_n), Some(req_n)) => fact_n >= req_n,
                    _ => false,
                };
                if count_ok {
                    return CheckResult::ProvedByRule;
                }
            }
        }

        let alloc = vm_state.alloc(alloc_id);
        if let (Some(alloc_elem_ty), Some(req_ty)) = (alloc.element_ty.as_ty(), required_ty) {
            // `MaybeUninit<T>` is `#[repr(transparent)]` over a union, so it has
            // exactly the size/alignment of `T`.  An allocation of
            // `MaybeUninit<T>` is therefore a valid allocation of `T` (and vice
            // versa).  This lets `assume_init_ref`/`assume_init_mut`
            // (`&[MaybeUninit<T>]` → `&[T]`) and `assume_init_drop` discharge
            // `Allocated(p, T, n)` against the `MaybeUninit<T>` allocation whose
            // symbolic size would otherwise be a distinct constant.
            if maybe_uninit_inner(alloc_elem_ty) == Some(req_ty)
                || maybe_uninit_inner(req_ty) == Some(alloc_elem_ty)
            {
                return CheckResult::ProvedByRule;
            }
            // Cross-type generic fast-path: when allocation element type
            // and required type are both generic params (e.g. T vs U),
            // sizes are opaque. If the pointer is derived from the same
            // function's slice parameter, the byte-level layout is
            // compatible by Rust's type system.
            if matches!(
                (alloc_elem_ty.kind(), req_ty.kind()),
                (TyKind::Param(_), TyKind::Param(_))
            ) {
                return CheckResult::ProvedByRule;
            }
            // Smart-pointer indirection: `Allocated(slot, Box<T>, n)` after
            // provenance penetration (`&mut ManuallyDrop<Box<T>>` → the `T`
            // allocation) declares the wrapper type while the allocation holds
            // its pointee. Peeling the wrapper down to `T` discharges the check
            // (only when the declared type *wraps* the allocation element, so a
            // plain type mismatch still falls through to the size check).
            if req_ty != alloc_elem_ty {
                let mut peeled = req_ty;
                loop {
                    match super::util::smart_pointer_pointee(peeled) {
                        Some(inner) if inner != peeled => {
                            if inner == alloc_elem_ty {
                                return CheckResult::ProvedByRule;
                            }
                            peeled = inner;
                        }
                        _ => break,
                    }
                }
            }
        }

        // A live `&mut MaybeUninit<T>` (or `&MaybeUninit<T>`) reference points at
        // a `MaybeUninit<T>` whose size/alignment equal `T`'s (`#[repr(transparent)]`
        // over a union), so `Allocated(p, T, n)` holds regardless of the provenance
        // the VM recorded for an iterator-deref pointer (`array_try_from_fn_ext`).
        if let Some(req_ty) = required_ty {
            let val_pointee = mir_utils::pointee_ty(value.ty);
            if val_pointee.and_then(maybe_uninit_inner) == Some(req_ty)
                || maybe_uninit_inner(req_ty) == val_pointee
            {
                return CheckResult::ProvedByRule;
            }
        }

        let base = vm_state.allocation_base(alloc_id).clone();
        let size = vm_state.allocation_size(alloc_id).clone();

        // An external allocation whose size is the `i64::MAX` "unbounded"
        // sentinel (a Vec/slice buffer, or a materialized `Allocated` fact)
        // auto-passes any `Allocated` access.  A *raw-pointer target* carries a
        // symbolic "unknown" size instead, so its access falls through and must
        // be proved (and otherwise fails).
        if vm_state.alloc(alloc_id).is_external() && size.simplify().as_u64() == Some(i64::MAX as u64)
        {
            return CheckResult::ProvedByRule;
        }

        let access = self.access_bytes(vm_state, property, 1, 2, checkpoint, &value);

        // A field-offset pointer (`byte_add(offset_of!())`) is allocated within
        // the *field* it addresses: the accessed range must fit in the field's
        // own size.  "The field lies inside its container" is a layout
        // invariant that needs no proof here (and the container's generic
        // layout may be unknown, e.g. `Option<T>`).
        if value
            .provenance
            .as_ref()
            .is_some_and(|prov| matches!(prov.offset_kind, Some(OffsetKind::Field)))
        {
            let field_size = mir_utils::pointee_ty(value.ty)
                .map(|ty| vm_state.size_sym_read(ty))
                .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
            let solver = Solver::new(vm_state.z3_ctx);
            solver.push();
            vm_state.assert_all(&solver);
            solver.assert(&access.le(&field_size).not());
            let r = match solver.check() {
                SatResult::Unsat => CheckResult::ProvedBySmt,
                SatResult::Sat => CheckResult::Failed,
                _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
            };
            solver.pop(1);
            return r;
        }

        if let (Some(off), Some(size_val), Some(access_val)) = (
            value
                .provenance
                .as_ref()
                .and_then(|p| p.offset.simplify().as_u64()),
            size.as_u64(),
            access.as_u64(),
        ) {
            if off.saturating_add(access_val) > size_val {
                return CheckResult::Failed;
            }
            return CheckResult::ProvedByRule;
        }

        // Generic element type: both size and access use max(1) fallback,
        // making the check about element counts. When the pointer's offset
        // cannot be determined concretely, the byte-level inequality
        // "offset + count <= total_len" relies on facts (split_at, etc.)
        // that may not be in path conditions. Fall back to Unknown rather
        // than Failed for generic-element allocations.
        let alloc_elem_is_generic = vm_state
            .alloc(alloc_id)
            .element_ty
            .as_ty()
            .is_some_and(|ty| matches!(ty.kind(), TyKind::Param(_)));
        let elem_size = vm_state.generic_elem_size(alloc_id);
        if alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some() {
            return Self::allocation_covers_access(
                vm_state,
                &value,
                &access,
                &base,
                &size,
                CheckResult::Unknown(UnknownReason::Unimplemented),
                elem_size.as_ref(),
            );
        }

        Self::allocation_covers_access(
            vm_state,
            &value,
            &access,
            &base,
            &size,
            CheckResult::Failed,
            elem_size.as_ref(),
        )
    }

    /// Prove that `value + access` fits within `[base, base + size)`.
    ///
    /// `on_sat` is the result when the overflow is satisfiable: `Failed` for
    /// concrete sizes, `Unknown` for generic-element allocations whose byte
    /// layout cannot be resolved.  `elem_size`, when present, is the *generic*
    /// element-size term: the check is then discharged by a case split on `S = 0`
    /// (ZST) vs `S ≥ 1` (non-ZST) rather than a single nonlinear query.
    fn allocation_covers_access<'z3, 'tcx>(
        vm_state: &VmState<'z3, 'tcx>,
        value: &VmValue<'z3, 'tcx>,
        access: &Int<'z3>,
        base: &Int<'z3>,
        size: &Int<'z3>,
        on_sat: CheckResult,
        elem_size: Option<&Int<'z3>>,
    ) -> CheckResult {
        let bound = Int::add(vm_state.z3_ctx, &[base, size]);
        let covered = Int::add(vm_state.z3_ctx, &[&value.z3_term, access]);
        let negated = covered.le(&bound).not();

        if let Some(s) = elem_size {
            return Self::smt_check_size_split(vm_state, s, &negated, on_sat);
        }

        let solver = Solver::new(vm_state.z3_ctx);
        solver.push();
        vm_state.assert_all(&solver);
        solver.assert(&negated);
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::ProvedBySmt,
            SatResult::Sat => on_sat,
            _ => CheckResult::Unknown(UnknownReason::from_solver(&solver)),
        };
        solver.pop(1);
        r
    }

    pub(super) fn check_init<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        if self.is_concrete_zst(vm_state, value.ty) {
            return CheckResult::ProvedByRule;
        }

        if self.count_is_zero(vm_state, checkpoint, property, 2) {
            return CheckResult::ProvedByRule;
        }

        // `Init(p, MaybeUninit<T>, n)` reduces to `Typed(p, MaybeUninit<T>)`:
        // `MaybeUninit<T>` carries no validity invariant (any bit pattern is a
        // valid `MaybeUninit<T>`), so there is nothing to "initialize" — the
        // content need only be of type `MaybeUninit<T>`.  Mirrors the
        // `ty_is_maybe_uninit` fast-path in `check_typed`; this is what lets a
        // `&[MaybeUninit<T>]` slice satisfy `Init` without its contents being
        // initialized.
        if let Some(required_ty) = property.ty_arg(1)
            && Self::ty_is_maybe_uninit(required_ty) {
                return CheckResult::ProvedByRule;
            }

        let access = self.access_bytes(vm_state, property, 1, 2, checkpoint, &value);
        let requested_ty = property.ty_arg(1).and_then(|ty| {
            if !matches!(ty.kind(), TyKind::Param(_)) {
                return Some(ty);
            }
            mir_utils::pointee_ty(value.ty).and_then(|pointee| {
                match pointee.kind() {
                    TyKind::Adt(def, args)
                        if crate::verify::api_classify::is_maybe_uninit_type(def.did()) => {
                        args.first().and_then(|arg| arg.as_type())
                    }
                    _ => Some(pointee),
                }
            }).or(Some(ty))
        });

        if let Some(id) = value.provenance_alloc_id() {
            rap_debug!(
                "check_init: alloc={} init_set={} access={:?}",
                id.0,
                vm_state.content(id).facts.initialized,
                access.as_u64()
            );
            if vm_state.alloc(id).facts.dead {
                // `assume_init_drop` (and other MaybeUninit drop/read ops)
                // legitimately consume an initialized element from storage that
                // may be going out of scope; the `Init` requirement concerns
                // whether the element was written, not whether the allocation is
                // still live. Mirror the `check_allocated` exception.
                if !vm_state.is_maybe_uninit_ptr(&value, id) {
                    return CheckResult::Failed;
                }
            }
            if let Some(prov) = &value.provenance
                && prov.offset.simplify().as_u64() == Some(0)
                && let Some((copied_ty, copied_count)) = &vm_state.content(id).copied_prefix
                && requested_ty == Some(*copied_ty)
                && property.args().get(2)
                    .and_then(|arg| self.resolve_arg_term(vm_state, checkpoint, arg))
                    .is_some_and(|count| vm_state.path_implies(&count.le(copied_count)))
            {
                return CheckResult::ProvedByRule;
            }
            let backing_maybe_uninit = vm_state.alloc(id)
                .element_ty
                .as_ty()
                .is_some_and(Self::ty_is_maybe_uninit);
            if backing_maybe_uninit
                && let Some(prov) = &value.provenance
                && prov.offset.simplify().as_u64() == Some(0)
                && vm_state.content(id).facts.written_pointee_ty.is_some()
                && vm_state.content(id).facts.written_pointee_ty
                    == requested_ty.or_else(|| mir_utils::pointee_ty(value.ty))
            {
                let one = Int::from_u64(vm_state.z3_ctx, 1);
                let count = property.args().get(2)
                    .and_then(|arg| self.resolve_arg_term(vm_state, checkpoint, arg))
                    .unwrap_or_else(|| one.clone());
                if vm_state.path_implies(&count.le(&one)) {
                    return CheckResult::ProvedByRule;
                }
            }
            if let Some(access_val) = access.as_u64()
                && let Some(prov) = &value.provenance
                    && let Some(prov_off) = prov.offset.as_u64() {
                        let end = prov_off + access_val;
                        let all_init = (prov_off as usize..end as usize)
                            .all(|off| vm_state.is_byte_init(id, off));
                        if all_init && access_val > 0 {
                            return CheckResult::ProvedByRule;
                        }
                    }
            if vm_state.content(id).facts.initialized && !backing_maybe_uninit {
                let size = vm_state.allocation_size(id);
                if let (Some(access_val), Some(size_val)) = (access.as_u64(), size.as_u64()) {
                    // `size_val == 0` means the element type is generic
                    // (size unknown), so the required access can't exceed a
                    // meaningful allocation size; skip the bound check.
                    if size_val > 0 && access_val > size_val {
                        return CheckResult::Failed;
                    }
                }
                return CheckResult::ProvedByRule;
            }
            if value.facts.init
                && !backing_maybe_uninit
                && value.facts.non_null
                && vm_state.is_value_aligned(&value)
                && matches!(value.ty.kind(), TyKind::RawPtr(..))
                && !vm_state.alloc(id).facts.dead
                && crate::verify::api_classify::is_mem_copy_or_write(checkpoint.callee) {
                    return CheckResult::ProvedByRule;
                }
            let size = vm_state.allocation_size(id).clone();
            if let Some(size_val) = size.as_u64() {
                let size_usize = (size_val as usize).min(4096);
                let all_init = (0..size_usize).all(|off| vm_state.is_byte_init(id, off));
                if all_init && size_val > 0 && vm_state.path_implies(&access.le(&size)) {
                    return CheckResult::ProvedByRule;
                }
            }
            return CheckResult::Failed;
        }
        if let Some(origin_op) = checkpoint.args.first() {
            let origin_val = vm_state.value_of_operand(origin_op);
            if let Some(prov) = &origin_val.provenance
                && vm_state.content(prov.alloc_id).facts.initialized {
                    let size = vm_state.allocation_size(prov.alloc_id);
                    if let (Some(access_val), Some(size_val)) = (access.as_u64(), size.as_u64()) {
                        if access_val <= size_val {
                            return CheckResult::ProvedByRule;
                        }
                    } else {
                        return CheckResult::ProvedByRule;
                    }
                }
            if let Operand::Copy(place) | Operand::Move(place) = origin_op {
                for alloc_id in self.trace_alloc_ids(vm_state, place.local) {
                    if vm_state.content(alloc_id).facts.initialized {
                        let size = vm_state.allocation_size(alloc_id);
                        if let (Some(access_val), Some(size_val)) = (access.as_u64(), size.as_u64()) {
                            if access_val <= size_val {
                                return CheckResult::ProvedByRule;
                            }
                        } else {
                            return CheckResult::ProvedByRule;
                        }
                    }
                }
            }
            if let Operand::Copy(place) | Operand::Move(place) = origin_op {
                let allocs = self.trace_alloc_ids(vm_state, place.local);
                if !allocs.is_empty() && allocs.iter().all(|id| !vm_state.content(*id).facts.initialized) {
                    return CheckResult::Failed;
                }
            }
        }
        CheckResult::Unknown(UnknownReason::Unimplemented)
    }

    pub(super) fn trace_alloc_ids<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        local: Local,
    ) -> Vec<AllocId> {
        let mut result = Vec::new();
        if let Some(id) = vm_state.current_frame.local_alloc.get(&local) {
            result.push(*id);
        }
        let mut worklist = vec![local];
        let mut visited = FxHashSet::default();
        visited.insert(local);
        while let Some(cur) = worklist.pop() {
            for block in vm_state.body().basic_blocks.iter() {
                for stmt in &block.statements {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        let (dest, rvalue) = &**assign;
                        if dest.local != cur || !dest.projection.is_empty() {
                            continue;
                        }
                        let src_local = match rvalue {
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                                if p.projection.is_empty() =>
                            {
                                Some(p.local)
                            }
                            Rvalue::CopyForDeref(p) if p.projection.is_empty() => Some(p.local),
                            Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                                if p.projection.is_empty() =>
                            {
                                Some(p.local)
                            }
                            Rvalue::RawPtr(_, p) if p.projection.is_empty() => Some(p.local),
                            _ => None,
                        };
                        if let Some(src) = src_local
                            && visited.insert(src)
                        {
                            if let Some(id) = vm_state.current_frame.local_alloc.get(&src) {
                                result.push(*id);
                            }
                            worklist.push(src);
                        }
                    }
                }
            }
        }
        result
    }

    pub(super) fn check_alive<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };
        let Some(id) = value.provenance_alloc_id() else {
            return if value.facts.non_null || value.facts.init {
                CheckResult::ProvedByRule
            } else {
                CheckResult::Unknown(UnknownReason::Unimplemented)
            };
        };

        if vm_state.alloc(id).facts.dead {
            if let Some(origin) = vm_state.resolve_origin(&value) {
                let is_param = origin.local.as_usize() <= vm_state.body().arg_count
                    && origin.local != Local::from_usize(0);
                if is_param {
                    return CheckResult::ProvedByRule;
                }
            }
            return CheckResult::Failed;
        }

        // Classify by the *value's own type*, not `resolve_origin`'s kind: a raw
        // pointer field can be misclassified when a derived temp (`&mut T` from a
        // call) shares the allocation's provenance and reads back as `MutRef`.
        // A raw pointer / `NonNull` carries no liveness guarantee, so `Alive`
        // must be justified by an explicit assumption (an `Alive` precondition /
        // struct invariant, materialized as `liveness`) or by provenance
        // shared with a live reference parameter.
        let is_raw_ptr = matches!(value.ty.kind(), TyKind::RawPtr(..))
            || matches!(value.ty.kind(), TyKind::Adt(adt_def, _)
                if mir_utils::is_raw_ptr_wrapper(vm_state.tcx, adt_def.did()));
        let check_region = property.args().get(1).and_then(|arg| match arg {
            PropertyArg::Region(region) => Some(*region),
            PropertyArg::Ident(name) if is_static_lifetime_ident(name) => {
                Some(vm_state.tcx.lifetimes.re_static)
            }
            PropertyArg::Ident(_) => crate::verify::vm::region::fn_return_region(
                vm_state.tcx,
                checkpoint.caller,
            ),
            _ => None,
        });

        if is_raw_ptr {
            let mut root_id = id;
            while let Some(parent_id) = vm_state.alloc(root_id).parent {
                root_id = parent_id;
            }
            if vm_state.alloc(root_id).facts.locally_allocated
                && !vm_state.alloc(root_id).facts.dead
            {
                if check_region == Some(vm_state.tcx.lifetimes.re_static) {
                    let owned_here = vm_state.current_frame.local_alloc.iter().any(|(local, &id)| {
                        !vm_state.alloc(id).facts.dead
                            && vm_state.container_data_alloc(id, vm_state.body().local_decls[*local].ty)
                                == Some(root_id)
                    });
                    return if owned_here {
                        CheckResult::Failed
                    } else {
                        CheckResult::Unknown(UnknownReason::Unimplemented)
                    };
                }
                if value.facts.non_null
                    && value.provenance.as_ref().is_some_and(|p| p.offset.as_u64() == Some(0))
                    && value.z3_term == vm_state.alloc(root_id).base
                {
                    return CheckResult::ProvedByRule;
                }
                let solver = Solver::new(vm_state.z3_ctx);
                vm_state.assert_path_constraints(&solver);
                let zero = Int::from_u64(vm_state.z3_ctx, 0);
                return self.smt_check(&solver, &vm_state.alloc(root_id).base._eq(&zero));
            }
            if !vm_state.alloc(root_id).is_external() && !vm_state.alloc(root_id).facts.dead {
                return CheckResult::ProvedByRule;
            }
            if !vm_state.alloc(root_id).facts.dead
                && let Some(src_region) = &vm_state.alloc(root_id).facts.liveness {
                    if let Some(r) = check_region {
                        let outlives = crate::verify::vm::region::region_outlives(
                            vm_state.tcx,
                            checkpoint.caller,
                            *src_region,
                            r,
                        );
                        let implied = crate::verify::vm::region::fn_arg_ty(
                            vm_state.tcx,
                            checkpoint.caller,
                            0,
                        )
                        .is_some_and(|self_ty| {
                            crate::verify::vm::region::region_outlives_implied(
                                vm_state.tcx,
                                *src_region,
                                self_ty,
                                r,
                            )
                        });
                        if !outlives && !implied {
                            return CheckResult::Failed;
                        }
                    }
                    return CheckResult::ProvedByRule;
                }
            // A raw pointer derived from a live reference or owned (Box/Vec)
            // parameter is alive: the reference / ownership guarantees liveness.
            let body = vm_state.body();
            let matches_live_param = (1..=body.arg_count).any(|i| {
                let param_local = Local::from_usize(i);
                let param_ty = body.local_decls[param_local].ty;
                let guarantees = matches!(param_ty.kind(), TyKind::Ref(..))
                    || matches!(param_ty.kind(), TyKind::Adt(adt_def, _)
                        if api_classify::is_std_box(adt_def.did())
                            || api_classify::is_std_vec(adt_def.did()));
                if !guarantees {
                    return false;
                }
                vm_state
                    .local_value(param_local)
                    .and_then(|v| v.provenance_alloc_id())
                    .is_some_and(|pid| pid == root_id)
            });
            if matches_live_param {
                return CheckResult::ProvedByRule;
            }
            if vm_state.resolve_origin(&value).is_none() {
                return CheckResult::ProvedByRule;
            }
            return CheckResult::Failed;
        }

        CheckResult::ProvedByRule
    }
}
