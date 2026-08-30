//! Checkers for memory-shape properties: `Align`, `NonNull`, `Allocated`,
//! `Init`, and `Alive`.
//!
//! These consume the VM's provenance/invariant facts (e.g. `align_n`,
//! `in_bounds`, `non_null`) with fast paths, falling back to SMT over
//! `value.term` and allocation base/size.

use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{GenericArgKind, TyKind};
#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use rustc_hash::FxHashSet;
use z3::{SatResult, Solver, ast::{Ast, Int}};
use crate::verify::contract::{ContractExpr, Property, PropertyArg};
use crate::verify::report::CheckResult;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::{AllocId, VmState, VmValue};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_align<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };

        if self.zst_guard(vm_state, checkpoint, property) { return CheckResult::Proved; }
        if self.is_concrete_zst(vm_state, value.ty) { return CheckResult::Proved; }
        let ty_arg = property.args().get(1).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        let align = ty_arg.map(|ty| vm_state.align_of_ty(ty)).unwrap_or(1);
        let align = if align <= 1 {
            ty_arg.and_then(|ty| {
                let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
                let resolved_align = vm_state.align_of_ty(resolved);
                if resolved_align > 1 {
                    Some(resolved_align)
                } else {
                    let min_a = crate::helpers::mir_utils::min_align_of_generic_param(vm_state.tcx, vm_state.caller_def_id, resolved);
                    if min_a > 1 { Some(min_a) } else { None }
                }
            }).unwrap_or(align)
        } else {
            align
        };
        if align <= 1 { return CheckResult::Proved; }
        // Check allocation base alignment with concrete offset
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            let off_u64 = prov.offset.as_u64()
                .or_else(|| prov.offset.simplify().as_u64());
            if let Some(off) = off_u64 {
                if alloc.align >= align {
                    if off % align == 0 {
                        return CheckResult::Proved;
                    }
                    if off % align != 0 {
                        return CheckResult::Failed;
                    }
                }
            }
        }
        if let Some(known_align) = value.invariants.align_n {
            if known_align >= align && known_align % align == 0 {
                return CheckResult::Proved;
            }
        }
        // Packed-struct fast-path: if the allocation is less aligned than
        // required, the concrete offset alone determines alignment.
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            if alloc.align < align {
                if let Some(off) = prov.offset.as_u64() {
                    if off % align != 0 {
                        return CheckResult::Failed;
                    }
                }
            }
        }
        let align_term = Int::from_u64(vm_state.ctx, align);
        let zero = Int::from_u64(vm_state.ctx, 0);
        let local = Solver::new(vm_state.ctx);
        local.push();
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            local.assert(&value.term._eq(&Int::add(vm_state.ctx, &[&alloc.base, &prov.offset])));
            local.assert(&alloc.base._eq(&zero).not());
            local.assert(&alloc.base.ge(&zero));
            if alloc.align > 1 {
                let a = Int::from_u64(vm_state.ctx, alloc.align);
                local.assert(&alloc.base.rem(&a)._eq(&zero));
            }
        }
        if let Some(known_align) = value.invariants.align_n {
            let n = Int::from_u64(vm_state.ctx, known_align);
            local.assert(&value.term.rem(&n)._eq(&zero));
        }
        for cond in &vm_state.path_conditions {
            local.assert(cond);
        }
        let negated = value.term.rem(&align_term)._eq(&zero).not();
        local.assert(&negated);
        let r = match local.check() {
            z3::SatResult::Sat => CheckResult::Failed,
            z3::SatResult::Unsat => CheckResult::Proved,
            z3::SatResult::Unknown => CheckResult::Unknown,
        };
        local.pop(1);
        if matches!(r, CheckResult::Failed) {
            rap_debug!("align=Failed vterm={} align_n={:?} aligned={} off={}",
                value.term.to_string(), value.invariants.align_n, value.invariants.aligned,
                value.provenance.as_ref().map(|p| p.offset.to_string()).unwrap_or_default());
        }
        r
    }

    pub(super) fn value_aligned_to<'ctx, 'tcx>(
        vm_state: &VmState<'ctx, 'tcx>,
        value: &VmValue<'ctx, 'tcx>,
        align: u64,
    ) -> bool {
        if align <= 1 {
            return true;
        }
        if let Some(n) = value.invariants.align_n {
            if n >= align && n % align == 0 {
                return true;
            }
        }
        let solver = Solver::new(vm_state.ctx);
        solver.push();
        let zero = Int::from_u64(vm_state.ctx, 0);
        if let Some(ref prov) = value.provenance {
            let alloc = vm_state.alloc(prov.alloc_id);
            solver.assert(&value.term._eq(&Int::add(vm_state.ctx, &[&alloc.base, &prov.offset])));
            solver.assert(&alloc.base.ge(&zero));
            if alloc.align > 1 {
                let a = Int::from_u64(vm_state.ctx, alloc.align);
                solver.assert(&alloc.base.rem(&a)._eq(&zero));
            }
        }
        for cond in &vm_state.path_conditions {
            solver.assert(cond);
        }
        let align_term = Int::from_u64(vm_state.ctx, align);
        solver.assert(&value.term.rem(&align_term)._eq(&zero).not());
        let r = solver.check() == SatResult::Unsat;
        solver.pop(1);
        r
    }

    pub(super) fn check_non_null<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if value.invariants.non_null { return CheckResult::Proved; }
        if value.invariants.in_bounds { return CheckResult::Proved; }
        // Pointers with non-external provenance point into known stack/heap
        // allocations whose base addresses are never zero.  Raw-pointer
        // parameters get external provenance which may be null.
        if let Some(ref prov) = value.provenance {
            if !vm_state.alloc(prov.alloc_id).is_external {
                return CheckResult::Proved;
            }
        }
        let zero = Int::from_u64(vm_state.ctx, 0);
        self.smt_check(solver, &value.term._eq(&zero))
    }

    pub(super) fn check_null<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        // `Null(p)` is the guard branch of `any(Null(p), ...)`.  It is Proved
        // when `p` is null (or carries no allocation, i.e. not known non-null),
        // making the guarded obligation vacuous; otherwise Failed, so the other
        // disjunct decides the outcome.
        let Some(place) = (match property.args().first() {
            Some(PropertyArg::Expr(ContractExpr::Place(p))) => Some(p),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        if self.is_null(vm_state, checkpoint, place) {
            CheckResult::Proved
        } else {
            CheckResult::Failed
        }
    }

    /// Whether `value` is a `MaybeUninit`-typed pointer access into `alloc_id`.
    ///
    /// `assume_init_drop` / `as_mut_ptr` (and friends) legitimately consume an
    /// initialized element from storage that may be going out of scope, so the
    /// `Init`/`Allocated` requirement concerns the write, not the allocation's
    /// live/dead flag.
    fn is_maybe_uninit_ptr<'ctx, 'tcx>(
        vm_state: &VmState<'ctx, 'tcx>,
        value: &VmValue<'ctx, 'tcx>,
        alloc_id: AllocId,
    ) -> bool {
        value.invariants.init && value.invariants.non_null && value.invariants.aligned
            && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                || matches!(value.ty.kind(), TyKind::Ref(_, inner, _)
                    if matches!(inner.kind(), TyKind::Adt(adt, _)
                        if vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit"))))
            && {
                let a = vm_state.alloc(alloc_id);
                !a.is_external && a.element_ty.map_or(false, |ty| {
                    if let TyKind::Adt(adt, _) = ty.kind() {
                        vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit")
                    } else { false }
                })
            }
    }

    pub(super) fn check_allocated<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };

        if self.zst_guard(vm_state, checkpoint, property) { return CheckResult::Proved; }
        if self.is_concrete_zst(vm_state, value.ty) { return CheckResult::Proved; }

        // Zero-element access (`Allocated(p, T, 0)`) is trivially satisfied:
        // any pointer is valid for its 0-byte prefix, so this holds even when
        // provenance has been lost through a cast.  Mirrors the `count == 0`
        // fast-path in `check_in_bound` and covers `from_raw_parts(ptr, 0)`
        // (e.g. `Option::as_slice` on `None`).
        let count_term = property.args().get(2)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a));
        if count_term.as_ref().is_some_and(|ct| ct.as_u64() == Some(0)) {
            return CheckResult::Proved;
        }

        let Some(alloc_id) = value.provenance_alloc_id() else { return CheckResult::Unknown };

        if vm_state.alloc(alloc_id).dead {
            if !Self::is_maybe_uninit_ptr(vm_state, &value, alloc_id) {
                let is_param_ref = vm_state.resolve_origin(&value)
                    .map_or(false, |origin| {
                        origin.local.as_usize() <= vm_state.body.arg_count
                            && origin.local != Local::from_usize(0)
                    });
                if !is_param_ref {
                    return CheckResult::Failed;
                }
            }
        }

        let required_ty = property.args().get(1)
            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });

        let alloc = vm_state.alloc(alloc_id);
        if let (Some(alloc_elem_ty), Some(req_ty)) = (alloc.element_ty, required_ty) {
            if self.alloc_elem_is_array_of(alloc_elem_ty, req_ty) {
                return CheckResult::Proved;
            }
            // Cross-type generic fast-path: when allocation element type
            // and required type are both generic params (e.g. T vs U),
            // sizes are opaque. If the pointer is derived from the same
            // function's slice parameter, the byte-level layout is
            // compatible by Rust's type system.
            if matches!((alloc_elem_ty.kind(), req_ty.kind()),
                (TyKind::Param(_), TyKind::Param(_))) {
                return CheckResult::Proved;
            }
        }

        let (Some(base), Some(size)) = (vm_state.allocation_base(alloc_id).cloned(), vm_state.allocation_size(alloc_id).cloned()) else {
            return CheckResult::Unknown;
        };

        if vm_state.alloc(alloc_id).is_external {
            return CheckResult::Proved;
        }

        let access = self.access_bytes(vm_state, property, 1, 2, checkpoint, &value);

        // Concrete sizes: direct comparison.
        if let (Some(size_val), Some(access_val)) = (size.as_u64(), access.as_u64()) {
            if size_val < access_val {
                return CheckResult::Failed;
            }
            return CheckResult::Proved;
        }

        // Generic element type: both size and access use max(1) fallback,
        // making the check about element counts. When the pointer's offset
        // cannot be determined concretely, the byte-level inequality
        // "offset + count <= total_len" relies on facts (split_at, etc.)
        // that may not be in path conditions. Fall back to Unknown rather
        // than Failed for generic-element allocations.
        let alloc_elem_is_generic = vm_state.alloc(alloc_id)
            .element_ty.map_or(false, |ty| matches!(ty.kind(), TyKind::Param(_)));
        if alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some() {
            return Self::allocation_covers_access(vm_state, &value, &access, &base, &size, CheckResult::Unknown);
        }

        Self::allocation_covers_access(vm_state, &value, &access, &base, &size, CheckResult::Failed)
    }

    /// Prove that `value + access` fits within `[base, base + size)`.
    ///
    /// `on_sat` is the result when the overflow is satisfiable: `Failed` for
    /// concrete sizes, `Unknown` for generic-element allocations whose byte
    /// layout cannot be resolved.
    fn allocation_covers_access<'ctx, 'tcx>(
        vm_state: &VmState<'ctx, 'tcx>,
        value: &VmValue<'ctx, 'tcx>,
        access: &Int<'ctx>,
        base: &Int<'ctx>,
        size: &Int<'ctx>,
        on_sat: CheckResult,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.ctx);
        solver.push();
        vm_state.assert_all(&solver);
        let bound = Int::add(vm_state.ctx, &[base, size]);
        let covered = Int::add(vm_state.ctx, &[&value.term, access]);
        solver.assert(&covered.le(&bound).not());
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat => on_sat,
            _ => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    pub(super) fn check_init<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        if self.zst_guard(vm_state, checkpoint, property) { return CheckResult::Proved; }
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if self.is_concrete_zst(vm_state, value.ty) { return CheckResult::Proved; }

        // Compute the required init range: count * sizeof(T) bytes
        let access = if property.args().len() >= 3 {
            Some(self.access_bytes(vm_state, property, 1, 2, checkpoint, &value))
        } else {
            None
        };

        if let Some(id) = value.provenance_alloc_id() {
            rap_debug!("check_init: alloc={} init_set={} access={:?}",
                id.0, vm_state.alloc(id).initialized,
                access.as_ref().and_then(|a| a.as_u64()));
            if vm_state.alloc(id).dead {
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
                        let all_init = (prov_off as usize..end as usize).all(|off| vm_state.is_byte_init(id, off));
                        if all_init && access_val > 0 {
                            return CheckResult::Proved;
                        }
                    }
                }
            }
            if vm_state.alloc(id).initialized {
                if let (Some(ref access_term), Some(ref size)) = (access, vm_state.allocation_size(id)) {
                    if let (Some(access_val), Some(size_val)) = (access_term.as_u64(), size.as_u64()) {
                        // `size_val == 0` means the element type is generic
                        // (size unknown), so the required access can't exceed a
                        // meaningful allocation size; skip the bound check.
                        if size_val > 0 && access_val > size_val {
                            return CheckResult::Failed;
                        }
                    }
                    if access_term.as_u64().is_some() && size.as_u64().is_some() {
                        return CheckResult::Proved;
                    }
                }
                return CheckResult::Proved;
            }
            // as_ptr/as_mut_ptr on MaybeUninit → write operations don't need pre-init.
            if value.invariants.init && value.invariants.non_null && value.invariants.aligned
                && matches!(value.ty.kind(), TyKind::RawPtr(..))
                && !vm_state.alloc(id).dead
            {
                if crate::verify::api_classify::is_mem_copy_or_write(checkpoint.callee) {
                    return CheckResult::Proved;
                }
            }
            // Check byte-level init: if all bytes in range are initialized
            if let Some(size) = vm_state.allocation_size(id).cloned() {
                if let Some(size_val) = size.as_u64() {
                    let size_usize = (size_val as usize).min(4096);
                    let all_init = (0..size_usize).all(|off| vm_state.is_byte_init(id, off));
                    if all_init && size_val > 0 {
                        return CheckResult::Proved;
                    }
                }
            }
        }
        // Check field-level init for aggregate types
        if let Some(origin_op) = checkpoint.args.first() {
            let origin_val = vm_state.value_of_operand(origin_op);
            if let Some(prov) = &origin_val.provenance {
                if vm_state.alloc(prov.alloc_id).initialized {
                    if let Some(ref access_term) = access {
                        if let Some(size) = vm_state.allocation_size(prov.alloc_id) {
                            if let (Some(access_val), Some(size_val)) = (access_term.as_u64(), size.as_u64()) {
                                if access_val <= size_val {
                                    return CheckResult::Proved;
                                }
                                // Required bytes exceed allocation → not fully init
                            } else {
                                return CheckResult::Proved;
                            }
                        } else {
                            return CheckResult::Proved;
                        }
                    }
                    // access=None: can't verify size, fall through
                }
            }
            if let Operand::Copy(place) | Operand::Move(place) = origin_op {
                for alloc_id in self.trace_alloc_ids(vm_state, place.local) {
                    if vm_state.alloc(alloc_id).initialized {
                        if let Some(ref access_term) = access {
                            if let Some(size) = vm_state.allocation_size(alloc_id) {
                                if let (Some(access_val), Some(size_val)) = (access_term.as_u64(), size.as_u64()) {
                                    if access_val <= size_val {
                                        return CheckResult::Proved;
                                    }
                                } else {
                                    return CheckResult::Proved;
                                }
                            } else {
                                return CheckResult::Proved;
                            }
                         }
                    }
                }
            }
        }
        // A path that evaluated an `Iterator::next` discriminant may be
        // infeasible when the iterator was empty (e.g. `assume_init_drop` on the
        // `Some` branch of `next()` that returned `None`). Check feasibility
        // only for such paths so unrelated over-constrained paths aren't
        // spuriously marked sound.
        if vm_state.contract_flags.saw_next_discriminant {
            let local = Solver::new(vm_state.ctx);
            local.push();
            for cond in &vm_state.path_conditions {
                local.assert(cond);
            }
            if local.check() == SatResult::Unsat {
                local.pop(1);
                return CheckResult::Proved;
            }
            local.pop(1);
        }
        CheckResult::Unknown
    }

    pub(super) fn trace_alloc_ids<'ctx, 'tcx>(
        &self, vm_state: &VmState<'ctx, 'tcx>, local: Local,
    ) -> Vec<AllocId> {
        let mut result = Vec::new();
        if let Some(id) = vm_state.local_alloc_ids.get(&local) {
            result.push(*id);
        }
        let mut worklist = vec![local];
        let mut visited = FxHashSet::default();
        visited.insert(local);
        while let Some(cur) = worklist.pop() {
            for block in vm_state.body.basic_blocks.iter() {
                for stmt in &block.statements {
                    if let StatementKind::Assign(assign) = &stmt.kind {
                        let (dest, rvalue) = &**assign;
                        if dest.local != cur || !dest.projection.is_empty() {
                            continue;
                        }
                        let src_local = match rvalue {
                            #[cfg(rapx_rvalue_use_with_retag)]
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _)
                                if p.projection.is_empty() => Some(p.local),
                            #[cfg(not(rapx_rvalue_use_with_retag))]
                            Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                                if p.projection.is_empty() => Some(p.local),
                            Rvalue::CopyForDeref(p) if p.projection.is_empty() => Some(p.local),
                            Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _)
                                if p.projection.is_empty() => Some(p.local),
                            Rvalue::RawPtr(_, p) if p.projection.is_empty() => Some(p.local),
                            _ => None,
                        };
                        if let Some(src) = src_local {
                            if visited.insert(src) {
                                if let Some(id) = vm_state.local_alloc_ids.get(&src) {
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

    pub(super) fn check_alive<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if let Some(id) = value.provenance_alloc_id() {
            if vm_state.alloc(id).dead {
                if let Some(origin) = vm_state.resolve_origin(&value) {
                    let is_param = origin.local.as_usize() <= vm_state.body.arg_count
                        && origin.local != Local::from_usize(0);
                    if is_param {
                        return CheckResult::Proved;
                    }
                }
                return CheckResult::Failed;
            }
            if let Some(origin) = vm_state.resolve_origin(&value) {
                let is_raw_ptr = matches!(origin.kind,
                    crate::verify::vm::alias::VmOriginKind::RawMutPtr
                    | crate::verify::vm::alias::VmOriginKind::RawConstPtr);
                if is_raw_ptr {
                    let is_field = origin.local.as_usize() > vm_state.body.arg_count;
                    if is_field {
                        let mut root_id = id;
                        while let Some(parent_id) = vm_state.alloc(root_id).parent {
                            root_id = parent_id;
                        }
                        if root_id != id
                            && vm_state.alloc(root_id).alive_assumed
                            && !vm_state.alloc(root_id).dead
                        {
                            return CheckResult::Proved;
                        }
                        if vm_state.allocations.iter().any(|a| a.alive_assumed) {
                            let root_is_external = vm_state.alloc(root_id).is_external;
                            if root_is_external {
                                return CheckResult::Proved;
                            }
                        }
                        // Only fail for raw pointer struct fields when the
                        // return type has an explicit named lifetime (from
                        // struct generics) that is not grounded in &self.
                        let ret_ty = &vm_state.body.local_decls[Local::from_usize(0)].ty;
                        let is_named = match ret_ty.kind() {
                            rustc_middle::ty::TyKind::Ref(r, _, _) => {
                                !matches!(r.kind(), rustc_middle::ty::RegionKind::ReErased)
                            }
                            _ => false,
                        };
                        if is_named || super::signature_return_has_lifetime(
                            vm_state.tcx, vm_state.caller_def_id)
                            .map_or(false, |(_, t)| t.contains('\''))
                        {
                            // Named/explicit return lifetime: check whether
                            // a reference parameter pointee is an ADT that
                            // carries NO lifetime parameters.  When the
                            // struct has no lifetimes of its own, the
                            // returned view's lifetime is guaranteed to be
                            // caller-chosen and tied to the borrow (e.g.
                            // &self).  In that case the pointer field's
                            // provenance is grounded in a live reference.
                            let body = vm_state.body;
                            let adt_no_lifetime = (1..=body.arg_count).any(|i| {
                                let param_ty = body.local_decls[Local::from_usize(i)].ty;
                                if let rustc_middle::ty::TyKind::Ref(_, pointee, _) = param_ty.kind() {
                                    if let rustc_middle::ty::TyKind::Adt(_adt_def, substs) = pointee.kind() {
                                        return !substs.types().any(|t| {
                                            matches!(t.kind(), rustc_middle::ty::TyKind::Param(_))
                                        })
                                        && !substs.iter().any(|g| matches!(g.kind(),
                                            GenericArgKind::Lifetime(_)));
                                    }
                                }
                                false
                            });
                            if !adt_no_lifetime {
                                return CheckResult::Failed;
                            }
                        }
                        return CheckResult::Proved;
                    }
                    // Raw pointer param: check if any ref param shares provenance.
                    let body = vm_state.body;
                    let matches_ref_param = (1..=body.arg_count).any(|i| {
                        let param_local = Local::from_usize(i);
                        let param_ty = body.local_decls[param_local].ty;
                        if !matches!(param_ty.kind(), rustc_middle::ty::TyKind::Ref(..)) {
                            return false;
                        }
                        vm_state.local_value(param_local)
                            .and_then(|v| v.provenance_alloc_id())
                            .is_some_and(|pid| pid == id)
                    });
                    if !matches_ref_param && !vm_state.alloc(id).alive_assumed {
                        return CheckResult::Failed;
                    }
                }
                return CheckResult::Proved;
            }
            return CheckResult::Proved;
        }
        if value.invariants.non_null || value.invariants.init { return CheckResult::Proved; }
        CheckResult::Unknown
    }
}
