//! Checkers for memory-shape properties: `Align`, `NonNull`, `Allocated`,
//! `Init`, and `Alive`.
//!
//! These consume the VM's provenance/invariant facts (e.g. `align_n`,
//! `in_bounds`, `non_null`) with fast paths, falling back to SMT over
//! `value.z3_term` and allocation base/size.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::api_classify;
use crate::verify::contract::{ContractExpr, Property, PropertyArg};
use crate::verify::report::{CheckResult, UnknownReason};
use crate::verify::vm::state::{AllocId, OffsetKind, VmState, VmValue};
use rustc_hash::FxHashSet;
use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::TyKind;
use z3::{
    SatResult, Solver,
    ast::{Ast, Int},
};

use super::PropertyChecker;
use super::util::maybe_uninit_inner;

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
        let ty_arg = Self::ty_arg(property, 1);
        // Alignment term: the *symbolic* `align_T` for a generic `T` (bounded by
        // the trait bounds' min/max), the concrete constant alignment for a
        // concrete type, or `1` when the property carries no type.
        let align = match ty_arg {
            Some(ty) => {
                let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
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
        if value.is_pointer() {
            if let Some(local) = vm_state.find_local_by_address(&value.z3_term) {
                let local_ty = vm_state.body().local_decls[local].ty;
                let local_align = vm_state.align_sym_read(local_ty);
                if let Some(local_align_u64) = local_align.simplify().as_u64() {
                    if local_align_u64 != 1 {
                        if let Some(align_u64) = align.simplify().as_u64() {
                            if local_align_u64 >= align_u64 {
                                return CheckResult::ProvedByRule;
                            }
                        }
                    }
                }
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
            crate::helpers::mir_utils::pointee_ty(value.ty).map(|ty| vm_state.align_sym_read(ty))
        } else {
            value.facts.align_n.clone()
        };
        if let Some(known_align) = effective_align_n {
            // Concrete fast-path: both alignments are powers of two, so
            // `align_n >= align` is a plain integer comparison — decide
            // structurally, no solver query.
            if let (Some(known_u64), Some(align_u64)) =
                (known_align.simplify().as_u64(), align.simplify().as_u64())
            {
                if known_u64 >= align_u64 {
                    return CheckResult::ProvedByRule;
                }
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
        // `Align(container.iter(), T)` for_each: every element pointer is
        // aligned to `align_of(T)`, so a pointer loaded from the container
        // (whose provenance names the container allocation) is T-aligned.
        if let Some(prov) = &value.provenance {
            if let Some(aligned_ty) = vm_state.alloc(prov.alloc_id).facts.for_each.aligned_ty {
                let fa = vm_state.align_sym_read(aligned_ty);
                if let (Some(fa_u64), Some(align_u64)) =
                    (fa.simplify().as_u64(), align.simplify().as_u64())
                {
                    if fa_u64 >= align_u64 {
                        return CheckResult::ProvedByRule;
                    }
                }
            }
        }
        // Check allocation base alignment with concrete offset
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            let off_u64 = prov
                .offset
                .as_u64()
                .or_else(|| prov.offset.simplify().as_u64());
            if let (Some(off), Some(align_u64), Some(alloc_align_u64)) = (
                off_u64,
                align.simplify().as_u64(),
                alloc.align.simplify().as_u64(),
            ) {
                if alloc_align_u64 >= align_u64 {
                    if off % align_u64 == 0 {
                        return CheckResult::ProvedByRule;
                    }
                    if off % align_u64 != 0 {
                        return CheckResult::Failed;
                    }
                }
            }
        }
        // Packed-struct fast-path: if the allocation is less aligned than
        // required, the concrete offset alone determines alignment.
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            if let (Some(alloc_align_u64), Some(align_u64)) =
                (alloc.align.simplify().as_u64(), align.simplify().as_u64())
            {
                if alloc_align_u64 < align_u64 {
                    if let Some(off) = prov.offset.as_u64() {
                        if off % align_u64 != 0 {
                            return CheckResult::Failed;
                        }
                    }
                }
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
        for cond in &vm_state.constraints.assertions {
            local.assert(cond);
        }
        let negated = value.z3_term.rem(&align_term)._eq(&zero).not();
        local.assert(&negated);
        let r = match local.check() {
            z3::SatResult::Sat => CheckResult::Failed,
            z3::SatResult::Unsat => CheckResult::ProvedBySmt,
            z3::SatResult::Unknown => CheckResult::Unknown(UnknownReason::SmtTimeout),
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
        {
            if n >= align && n % align == 0 {
                return true;
            }
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
        for cond in &vm_state.constraints.assertions {
            solver.assert(cond);
        }
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
        if value.facts.non_null {
            return CheckResult::ProvedByRule;
        }
        if value.facts.in_bounds {
            return CheckResult::ProvedByRule;
        }
        // Pointers with non-external provenance point into known stack/heap
        // allocations whose base addresses are never zero.  Raw-pointer
        // parameters get external provenance which may be null.
        if let Some(ref prov) = value.provenance {
            if !vm_state.alloc(prov.alloc_id).is_external() {
                return CheckResult::ProvedByRule;
            }
        }
        // For an external pointer, check nullability against the *path
        // conditions* only.  `assert_all` also asserts every live value's
        // derived `non_null` flag, but the `&T` produced by this very deref
        // shares the source pointer's term and is marked non-null — using it
        // would circularly "prove" `NonNull` on the pointer being dereferenced.
        let zero = Int::from_u64(vm_state.z3_ctx, 0);
        let local = Solver::new(vm_state.z3_ctx);
        for cond in &vm_state.constraints.assertions {
            local.assert(cond);
        }
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

    /// Whether `value` is known to be aligned: either `align_n` carries a
    /// concrete alignment, or the value sits at the base of an allocation whose
    /// `align` is not 1.
    fn is_value_aligned<'z3, 'tcx>(
        vm_state: &VmState<'z3, 'tcx>,
        value: &VmValue<'z3, 'tcx>,
    ) -> bool {
        value.facts.align_n.is_some()
            || value.provenance.as_ref().is_some_and(|p| {
                p.offset_kind.is_none()
                    && vm_state.alloc(p.alloc_id).align.simplify().as_u64() != Some(1)
            })
    }

    /// Whether `value` is a `MaybeUninit`-typed pointer access into `alloc_id`.
    ///
    /// `assume_init_drop` / `as_mut_ptr` (and friends) legitimately consume an
    /// initialized element from storage that may be going out of scope, so the
    /// `Init`/`Allocated` requirement concerns the write, not the allocation's
    /// live/dead flag.
    fn is_maybe_uninit_ptr<'z3, 'tcx>(
        vm_state: &VmState<'z3, 'tcx>,
        value: &VmValue<'z3, 'tcx>,
        alloc_id: AllocId,
    ) -> bool {
        value.facts.init
            && value.facts.non_null
            && Self::is_value_aligned(vm_state, value)
            && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                || matches!(value.ty.kind(), TyKind::Ref(_, inner, _)
                    if matches!(inner.kind(), TyKind::Adt(adt, _)
                        if api_classify::is_maybe_uninit_type(adt.did()))))
            && {
                let a = vm_state.alloc(alloc_id);
                !a.is_external()
                    && a.element_ty.as_ty().is_some_and(|ty| {
                        if let TyKind::Adt(adt, _) = ty.kind() {
                            api_classify::is_maybe_uninit_type(adt.did())
                        } else {
                            false
                        }
                    })
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
        let value = self.resolve_pointer_provenance(vm_state, value);

        if self.zst_guard(vm_state, checkpoint, property) {
            return CheckResult::ProvedByRule;
        }
        if self.is_concrete_zst(vm_state, value.ty) {
            return CheckResult::ProvedByRule;
        }

        // Zero-element access (`Allocated(p, T, 0)`) is trivially satisfied:
        // any pointer is valid for its 0-byte prefix, so this holds even when
        // provenance has been lost through a cast.  Mirrors the `count == 0`
        // fast-path in `check_in_bound` and covers `from_raw_parts(ptr, 0)`
        // (e.g. `Option::as_slice` on `None`).
        if self.count_is_zero(vm_state, checkpoint, property, 2) {
            return CheckResult::ProvedByRule;
        }

        let Some(alloc_id) = value.provenance_alloc_id() else {
            // `ManuallyDrop::drop(&mut slot)` on an *empty* container (`Vec::new`
            // / `String::new`) has no heap allocation behind the reference: the
            // container value is valid and there is nothing to free, so its
            // `ValidPtr`/`Allocated` precondition holds vacuously.
            if crate::verify::api_classify::is_manually_drop_drop(checkpoint.callee) {
                return CheckResult::ProvedByRule;
            }
            // A null pointer (address term 0) is definitely not backed by any
            // allocation — a confirmed violation, not an incomplete proof.
            if value.z3_term.simplify().as_u64() == Some(0) {
                return CheckResult::Failed;
            }
            // A pointer whose address is a compile-time constant (e.g.
            // `NonNull::dangling`'s `align_of::<T>()`, an unevaluated `const_…`
            // term) is likewise not backed by any allocation.
            if value.z3_term.to_string().contains("const_") {
                return CheckResult::Failed;
            }
            return CheckResult::Unknown(UnknownReason::Unimplemented);
        };

        if vm_state.alloc(alloc_id).facts.dead {
            let reenter = vm_state.path_facts.reenter;
            // A `ManuallyDrop::drop` frees the slot's allocation at *this*
            // checkpoint, so its `ValidPtr`/`Allocated` precondition concerns
            // the pre-drop (still-live) state.  A double free — an
            // already-dead allocation reaching a *second* drop — must still
            // fail, so the exemption is lifted (unless the repeated block is
            // only a loop-unrolled iteration).
            let dropped_here =
                crate::verify::api_classify::is_manually_drop_drop(checkpoint.callee) && reenter;
            if !dropped_here && !Self::is_maybe_uninit_ptr(vm_state, &value, alloc_id) {
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
            .map(|ty| self.instantiate_callsite_ty(vm_state, checkpoint, ty));

        // `Allocated(container.iter(), T, n)` for_each: every element pointer
        // backs `>= n` `T` elements, so a pointer loaded from the container
        // (whose provenance names the container allocation) satisfies
        // `Allocated(cur, T, n)`.
        if let Some((t, n)) = &vm_state.alloc(alloc_id).facts.for_each.allocated {
            let resolved_t = self.instantiate_callsite_ty(vm_state, checkpoint, *t);
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
            if self.alloc_elem_is_array_of(alloc_elem_ty, req_ty) {
                return CheckResult::ProvedByRule;
            }
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
            let val_pointee = crate::helpers::mir_utils::pointee_ty(value.ty);
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
            let field_size = crate::helpers::mir_utils::pointee_ty(value.ty)
                .map(|ty| vm_state.size_sym_read(ty))
                .unwrap_or_else(|| Int::from_u64(vm_state.z3_ctx, 1));
            let solver = Solver::new(vm_state.z3_ctx);
            solver.push();
            vm_state.assert_all(&solver);
            solver.assert(&access.le(&field_size).not());
            let r = match solver.check() {
                SatResult::Unsat => CheckResult::ProvedBySmt,
                SatResult::Sat => CheckResult::Failed,
                _ => CheckResult::Unknown(UnknownReason::SmtTimeout),
            };
            solver.pop(1);
            return r;
        }

        // Concrete sizes and offset: direct byte-range comparison, no solver.
        // The accessed range is `[offset, offset + access)`, which must fit in
        // `[0, size)`.  The offset is a non-negative byte offset by provenance
        // construction, so only the upper bound needs checking.
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
            _ => CheckResult::Unknown(UnknownReason::SmtTimeout),
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

        // Zero elements: `Init(p, T, 0)` is vacuously satisfied (the empty
        // range is trivially initialized, regardless of whether `p` is a
        // dangling pointer), mirroring `check_allocated`'s fast-path.
        let count_arg = if property.args().len() >= 3 { 2 } else { 1 };
        if self.count_is_zero(vm_state, checkpoint, property, count_arg) {
            return CheckResult::ProvedByRule;
        }

        // `Init(p, MaybeUninit<T>, n)` reduces to `Typed(p, MaybeUninit<T>)`:
        // `MaybeUninit<T>` carries no validity invariant (any bit pattern is a
        // valid `MaybeUninit<T>`), so there is nothing to "initialize" — the
        // content need only be of type `MaybeUninit<T>`.  Mirrors the
        // `ty_is_maybe_uninit` fast-path in `check_typed`; this is what lets a
        // `&[MaybeUninit<T>]` slice satisfy `Init` without its contents being
        // initialized.
        if let Some(required_ty) = Self::ty_arg(property, 1) {
            if Self::ty_is_maybe_uninit(required_ty) {
                return CheckResult::ProvedByRule;
            }
        }

        // Compute the required init range: count * sizeof(T) bytes.  The
        // two-argument form `Init(self, n)` carries no `T`; `access_bytes`
        // falls back to the target's pointee element type.
        let access = if property.args().len() >= 3 {
            Some(self.access_bytes(vm_state, property, 1, count_arg, checkpoint, &value))
        } else if property.args().len() == 2 {
            Some(self.access_bytes(vm_state, property, 0, count_arg, checkpoint, &value))
        } else {
            None
        };

        if let Some(id) = value.provenance_alloc_id() {
            rap_debug!(
                "check_init: alloc={} init_set={} access={:?}",
                id.0,
                vm_state.content(id).facts.initialized,
                access.as_ref().and_then(|a| a.as_u64())
            );
            if vm_state.alloc(id).facts.dead {
                // `assume_init_drop` (and other MaybeUninit drop/read ops)
                // legitimately consume an initialized element from storage that
                // may be going out of scope; the `Init` requirement concerns
                // whether the element was written, not whether the allocation is
                // still live. Mirror the `check_allocated` exception.
                if !Self::is_maybe_uninit_ptr(vm_state, &value, id) {
                    return CheckResult::Failed;
                }
            }
            // Verify the entire access range is covered
            if let Some(ref access_term) = access {
                if let (Some(access_val), Some(prov)) = (access_term.as_u64(), &value.provenance) {
                    if let Some(prov_off) = prov.offset.as_u64() {
                        let end = prov_off + access_val;
                        let all_init = (prov_off as usize..end as usize)
                            .all(|off| vm_state.is_byte_init(id, off));
                        if all_init && access_val > 0 {
                            return CheckResult::ProvedByRule;
                        }
                    }
                }
            }
            if vm_state.content(id).facts.initialized {
                if let Some(ref access_term) = access {
                    let size = vm_state.allocation_size(id);
                    if let (Some(access_val), Some(size_val)) =
                        (access_term.as_u64(), size.as_u64())
                    {
                        // `size_val == 0` means the element type is generic
                        // (size unknown), so the required access can't exceed a
                        // meaningful allocation size; skip the bound check.
                        if size_val > 0 && access_val > size_val {
                            return CheckResult::Failed;
                        }
                    }
                }
                return CheckResult::ProvedByRule;
            }
            // as_ptr/as_mut_ptr on MaybeUninit → write operations don't need pre-init.
            if value.facts.init
                && value.facts.non_null
                && Self::is_value_aligned(vm_state, &value)
                && matches!(value.ty.kind(), TyKind::RawPtr(..))
                && !vm_state.alloc(id).facts.dead
            {
                if crate::verify::api_classify::is_mem_copy_or_write(checkpoint.callee) {
                    return CheckResult::ProvedByRule;
                }
            }
            // Check byte-level init: if all bytes in range are initialized
            let size = vm_state.allocation_size(id).clone();
            if let Some(size_val) = size.as_u64() {
                let size_usize = (size_val as usize).min(4096);
                let all_init = (0..size_usize).all(|off| vm_state.is_byte_init(id, off));
                if all_init && size_val > 0 {
                    return CheckResult::ProvedByRule;
                }
            }
            // The allocation's `initialized` flag stayed `false` (nothing wrote
            // it: `MaybeUninit::uninit` / `Box::new_uninit`), and this is not a
            // write operation — the access reads uninitialized memory, a
            // confirmed violation rather than an incomplete proof.
            return CheckResult::Failed;
        }
        // Check field-level init for aggregate types
        if let Some(origin_op) = checkpoint.args.first() {
            let origin_val = vm_state.value_of_operand(origin_op);
            if let Some(prov) = &origin_val.provenance {
                if vm_state.content(prov.alloc_id).facts.initialized {
                    if let Some(ref access_term) = access {
                        let size = vm_state.allocation_size(prov.alloc_id);
                        if let (Some(access_val), Some(size_val)) =
                            (access_term.as_u64(), size.as_u64())
                        {
                            if access_val <= size_val {
                                return CheckResult::ProvedByRule;
                            }
                            // Required bytes exceed allocation → not fully init
                        } else {
                            return CheckResult::ProvedByRule;
                        }
                    }
                    // access=None: can't verify size, fall through
                }
            }
            if let Operand::Copy(place) | Operand::Move(place) = origin_op {
                for alloc_id in self.trace_alloc_ids(vm_state, place.local) {
                    if vm_state.content(alloc_id).facts.initialized {
                        if let Some(ref access_term) = access {
                            let size = vm_state.allocation_size(alloc_id);
                            if let (Some(access_val), Some(size_val)) =
                                (access_term.as_u64(), size.as_u64())
                            {
                                if access_val <= size_val {
                                    return CheckResult::ProvedByRule;
                                }
                            } else {
                                return CheckResult::ProvedByRule;
                            }
                        }
                    }
                }
            }
            // No path proved init.  If the value traces to a known allocation
            // that was never written (its `initialized` flag stayed `false`),
            // reading it is a confirmed violation rather than an incomplete
            // proof.
            if let Operand::Copy(place) | Operand::Move(place) = origin_op {
                let allocs = self.trace_alloc_ids(vm_state, place.local);
                if !allocs.is_empty() && allocs.iter().all(|id| !vm_state.content(*id).facts.initialized) {
                    return CheckResult::Failed;
                }
            }
        }
        // A path that evaluated an `Iterator::next` discriminant may be
        // infeasible when the iterator was empty (e.g. `assume_init_drop` on the
        // `Some` branch of `next()` that returned `None`). Check feasibility
        // only for such paths so unrelated over-constrained paths aren't
        // spuriously marked sound.
        if vm_state.path_facts.saw_next_discriminant {
            let local = Solver::new(vm_state.z3_ctx);
            local.push();
            for cond in &vm_state.constraints.assertions {
                local.assert(cond);
            }
            if local.check() == SatResult::Unsat {
                local.pop(1);
                return CheckResult::ProvedByRule;
            }
            local.pop(1);
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
                            #[cfg(rapx_rvalue_use_with_retag)]
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _)
                                if p.projection.is_empty() =>
                            {
                                Some(p.local)
                            }
                            #[cfg(not(rapx_rvalue_use_with_retag))]
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
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
                        if let Some(src) = src_local {
                            if visited.insert(src) {
                                if let Some(id) = vm_state.current_frame.local_alloc.get(&src) {
                                    result.push(*id);
                                }
                                worklist.push(src);
                            }
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
                if crate::helpers::mir_utils::is_raw_ptr_wrapper(vm_state.tcx, adt_def.did()));

        if is_raw_ptr {
            let mut root_id = id;
            while let Some(parent_id) = vm_state.alloc(root_id).parent {
                root_id = parent_id;
            }
            // A non-external allocation (stack local, owned heap, or const
            // materialization) is a real allocation whose liveness is tracked by
            // `dead`, so "not dead" means alive.
            if !vm_state.alloc(root_id).is_external() && !vm_state.alloc(root_id).facts.dead {
                return CheckResult::ProvedByRule;
            }
            // An external allocation is a placeholder for arbitrary external
            // memory (raw-pointer params/fields) and carries no liveness
            // guarantee; it is alive only if explicitly assumed (`Alive`
            // precondition / struct invariant), or grounded in a live reference.
            if !vm_state.alloc(root_id).facts.dead {
                match &vm_state.alloc(root_id).facts.liveness {
                    Some(src_region) => {
                        // The `Alive(p, 'r)` check demands the memory alive for
                        // `'r`, while the assumption only guarantees `'a`; the
                        // assumption covers the demand only when `'a: 'r`.
                        //
                        // A struct invariant / function `requires` binds its
                        // region at parse time (`PropertyArg::Region`); a callee
                        // contract carries either `'static` (concrete) or the
                        // callee's *generic* return lifetime (`Ident`), which is
                        // instantiated from the caller's return reference region.
                        let check_region = property.args().get(1).and_then(|a| match a {
                            PropertyArg::Region(r) => Some(*r),
                            PropertyArg::Ident(name)
                                if name == "static" || name == "static_lifetime" =>
                            {
                                Some(vm_state.tcx.lifetimes.re_static)
                            }
                            PropertyArg::Ident(_) => crate::verify::vm::region::fn_return_region(
                                vm_state.tcx,
                                checkpoint.caller,
                            ),
                            _ => None,
                        });
                        if let Some(r) = check_region {
                            let outlives = crate::verify::vm::region::region_outlives(
                                vm_state.tcx,
                                checkpoint.caller,
                                *src_region,
                                r,
                            );
                            // A reference parameter `&'r Self<'a>` implies
                            // `'a: 'r` through its type (not a where-clause).
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
                                )
                            });
                            if !outlives && !implied {
                                return CheckResult::Failed;
                            }
                        }
                        return CheckResult::ProvedByRule;
                    }
                    None => {}
                }
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
            // No local origin: the allocation is not tied to any local, so it
            // outlives the function (e.g. `static` data not materialized as a
            // const byte array).
            if vm_state.resolve_origin(&value).is_none() {
                return CheckResult::ProvedByRule;
            }
            return CheckResult::Failed;
        }

        // A reference or owned value guarantees its pointee is live.
        CheckResult::ProvedByRule
    }
}
