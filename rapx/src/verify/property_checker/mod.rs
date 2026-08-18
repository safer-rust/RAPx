//! Unified property checker for the symbolic VM.

use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_middle::ty::{GenericArg, GenericArgKind, Ty, TyKind};
#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use rustc_hash::FxHashSet;
use z3::{
    SatResult, Solver,
    ast::{Ast, Bool, Int},
};

use crate::verify::{
    contract::{
        ContractExpr, ContractProjection, NumericOp, PlaceBase, Property, PropertyArg, PropertyKind,
        RelOp,
    },
    def_use::PlaceKey,
    report::CheckResult,
};

use crate::helpers::mir_scan::Checkpoint;

use super::vm::state::{AllocId, VmState, VmValue};

mod cstr;
mod transmute;

pub struct PropertyChecker;

impl PropertyChecker {
    pub fn check<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let solver = Solver::new(vm_state.ctx);
        vm_state.assert_all(&solver);
        self.check_inner(vm_state, &solver, checkpoint, property)
    }

    fn check_inner<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        // Null guard: property is vacuously true when the guarded place is null.
        if let Some(guard_key) = property.null_guard() {
            if self.is_guard_null(vm_state, checkpoint, guard_key) {
                return CheckResult::Proved;
            }
        }
        // Vacuous truth: properties with unwrap_some() / iter() projections
        // are trivially true when the container value cannot be resolved to
        // a meaningful pointer (e.g. Option::None has no provenance).
        if self.is_vacuously_true_for_nullable(vm_state, checkpoint, property) {
            return CheckResult::Proved;
        }
        match property {
            Property::Or(_) => self.check_or(vm_state, solver, checkpoint, property),
            Property::Leaf(leaf) => match leaf.kind {
                PropertyKind::Align => self.check_align(vm_state, solver, checkpoint, property),
                PropertyKind::NonNull => self.check_non_null(vm_state, solver, checkpoint, property),
                PropertyKind::Allocated => self.check_allocated(vm_state, solver, checkpoint, property),
                PropertyKind::InBound => self.check_in_bound(vm_state, solver, checkpoint, property),
                PropertyKind::Init => self.check_init(vm_state, solver, checkpoint, property),
                PropertyKind::Typed => self.check_typed(vm_state, solver, checkpoint, property),
                PropertyKind::Alias => self.check_alias(vm_state, solver, checkpoint, property),
                PropertyKind::Owning => self.check_owning(vm_state, solver, checkpoint, property),
                PropertyKind::Alive => self.check_alive(vm_state, solver, checkpoint, property),
                PropertyKind::NonOverlap => self.check_non_overlap(vm_state, solver, checkpoint, property),
                PropertyKind::NonVolatile => CheckResult::Proved,
                PropertyKind::ValidNum => self.check_valid_num(vm_state, solver, checkpoint, property),
                PropertyKind::ValidCStr => self.check_valid_cstr(vm_state, solver, checkpoint, property),
                PropertyKind::ValidTransmute => {
                    self.check_valid_transmute(vm_state, solver, checkpoint, property)
                }
                PropertyKind::SplitTransmute => {
                    self.check_split_transmute(vm_state, solver, checkpoint, property)
                }
                PropertyKind::Trait => self.check_trait(vm_state, solver, checkpoint, property),
                PropertyKind::Size => self.check_size(vm_state, property),

                _ => CheckResult::Unknown,
            },
        }
    }

    fn check_or<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        // OR semantics: proved if any group is fully proved; failed only if
        // *every* group is definitely violated; unknown otherwise.
        let mut overall: Option<CheckResult> = None;
        for group in property.groups() {
            let mut group_acc: Option<CheckResult> = None;
            for p in group {
                let result = self.check_inner(vm_state, solver, checkpoint, p);
                group_acc = Some(match group_acc {
                    Some(prev) => prev.and(result),
                    None => result,
                });
            }
            // An empty group is vacuously proved.
            let group_result = group_acc.unwrap_or(CheckResult::Proved);
            overall = Some(match overall {
                Some(prev) => prev.or(group_result),
                None => group_result,
            });
        }
        overall.unwrap_or(CheckResult::Failed)
    }

    // ── Resolve target place through checkpoint args ────────────

    pub(super) fn target_value<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> Option<VmValue<'ctx, 'tcx>>
    {
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
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => cp.clone(),
                    _ => return None,
                }
            }
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
                    let base_val = vm_state.field_value(base_local, &field_path)
                        .cloned()
                        .or_else(|| vm_state.local_value(base_local).cloned());
                    let Some(base_val) = base_val else { return None };

                    let enum_ty = last_field_ty.unwrap_or(base_val.ty);
                    let inner_ty = match enum_ty.kind() {
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum() {
                                let variant = &adt_def.variants()[rustc_abi::VariantIdx::from_usize(*variant_index)];
                                if !variant.fields.is_empty() {
                                    Some(variant.fields[rustc_abi::FieldIdx::from_usize(0)].ty(vm_state.tcx, substs).skip_norm_wip())
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
                ContractProjection::IterElements => {
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
                                    if let Some(operand) = operands.get(rustc_abi::FieldIdx::from_usize(field_path[0])) {
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

    /// Check whether a property is vacuously true because its target place
    /// uses a nullable projection (Downcast/IterElements) on a container
    /// that has no meaningful provenance (e.g. Option::None).
    fn is_vacuously_true_for_nullable<'ctx, 'tcx>(
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
            matches!(p, ContractProjection::Downcast { .. } | ContractProjection::IterElements)
        });
        if !has_nullable_proj {
            return false;
        }
        match self.target_value(vm_state, checkpoint, property) {
            Some(val) => val.provenance.is_none(),
            None => true,
        }
    }

    /// Check whether a null-guard place (from `any(Null(p), ...)`) is null.
    fn is_guard_null<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        guard_key: &crate::verify::def_use::PlaceKey,
    ) -> bool {
        use crate::verify::def_use::PlaceBaseKey;
        let local = match guard_key.base {
            PlaceBaseKey::Local(n) => Local::from_usize(n),
            PlaceBaseKey::Arg(n) => {
                checkpoint.args.get(n)
                    .and_then(|op| match op {
                        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                        _ => None,
                    })
                    .unwrap_or(Local::from_usize(n + 1))
            }
            PlaceBaseKey::Return => Local::from_usize(0),
        };
        let val = if guard_key.fields.is_empty() {
            vm_state.local_value(local).cloned()
        } else {
            vm_state.field_value(local, &guard_key.fields).cloned()
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

    // ── SMT helper ─────────────────────────────────────────────

    fn smt_check<'ctx>(&self, solver: &Solver<'ctx>, condition: &Bool<'ctx>) -> CheckResult {
        solver.push();
        solver.assert(condition);
        let r = match solver.check() { SatResult::Unsat => CheckResult::Proved, SatResult::Sat => CheckResult::Failed, SatResult::Unknown => CheckResult::Unknown };
        solver.pop(1);
        r
    }

    /// Resolve a property arg into a Z3 Int term suitable as an element count.
    /// Maps Local/Arg bases in ContractExpr::Place wrappers to checkpoint operands or VM locals.
    fn resolve_arg_term<'ctx, 'tcx>(
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
                            vm_state.local_value(Local::from_usize(n)).map(|v| v.term.clone())
                        }
                    }
                    PlaceBase::Return => None,
                }
            }
            PropertyArg::Expr(expr) => self.eval_contract_expr(vm_state, Some(checkpoint), expr),
            _ => None,
        }
    }

    /// Access size in bytes for `ty_arg`-typed elements × `count_arg` elements.
    /// Falls back to the target value's type size when the type arg can't be resolved.
    /// Resolves symbolic count args from the checkpoint's actual operands.
    fn access_bytes<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        property: &Property<'tcx>, ty_arg: usize, count_arg: usize,
        checkpoint: &Checkpoint<'tcx>, _value: &VmValue<'ctx, 'tcx>) -> Int<'ctx>
    {
        let elem_size = property.args().get(ty_arg)
            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(vm_state.size_of_ty(*ty)) } else { None })
            .unwrap_or(0);
        // When the contract uses a generic T (size_of returns 0), infer the
        // concrete element type from the checkpoint's target argument's pointee.
        let elem_size = if elem_size == 0 {
            checkpoint.args.first()
                .map(|op| {
                    let arg_val = vm_state.value_of_operand(op);
                    vm_state.pointee_elem_size(arg_val.ty)
                })
                .unwrap_or(0)
        } else {
            elem_size
        };
        let elem_size_term = Int::from_u64(vm_state.ctx, (elem_size as u64).max(1));

        let count_term = property.args().get(count_arg)
            .and_then(|a| self.resolve_arg_term(vm_state, checkpoint, a))
            .unwrap_or_else(|| Int::from_u64(vm_state.ctx, 1));
        // Simplify the multiplication for concrete count and elem_size
        if let (Some(elem), Some(count)) = (Some(elem_size), count_term.simplify().as_u64()) {
            return Int::from_u64(vm_state.ctx, (elem as u64).max(1) * count.max(1));
        }
        Int::mul(vm_state.ctx, &[&elem_size_term, &count_term])
    }

    // ── check_align ────────────────────────────────────────────

    fn check_align<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
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
                    let min_a = vm_state.min_align_of_generic_param(resolved);
                    if min_a > 1 { Some(min_a) } else { None }
                }
            }).unwrap_or(align)
        } else {
            align
        };
        if align <= 1 { return CheckResult::Proved; }
        // Check allocation base alignment with concrete offset
        if let Some(ref prov) = value.provenance {
            if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == prov.alloc_id) {
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
        }
        if value.invariants.aligned {
            if let Some(known_align) = value.invariants.align_n {
                if known_align >= align && known_align % align == 0 {
                    return CheckResult::Proved;
                }
            }
        } else if let Some(known_align) = value.invariants.align_n {
            if known_align >= align && known_align % align == 0 {
                return CheckResult::Proved;
            }
        }
        // Packed-struct fast-path: if the allocation is less aligned than
        // required, the concrete offset alone determines alignment.
        if let Some(ref prov) = value.provenance {
            if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == prov.alloc_id) {
                if alloc.align < align {
                    if let Some(off) = prov.offset.as_u64() {
                        if off % align != 0 {
                            return CheckResult::Failed;
                        }
                    }
                }
            }
        }
        let align_term = Int::from_u64(vm_state.ctx, align);
        let zero = Int::from_u64(vm_state.ctx, 0);
        let local = Solver::new(vm_state.ctx);
        local.push();
        if let Some(ref prov) = value.provenance {
            if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == prov.alloc_id) {
                local.assert(&value.term._eq(&Int::add(vm_state.ctx, &[&alloc.base, &prov.offset])));
                local.assert(&alloc.base._eq(&zero).not());
                local.assert(&alloc.base.ge(&zero));
                if alloc.align > 1 {
                    let a = Int::from_u64(vm_state.ctx, alloc.align);
                    local.assert(&alloc.base.rem(&a)._eq(&zero));
                }
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

    // ── check_non_null ─────────────────────────────────────────

    /// Whether pointer `value` is provably aligned to `align` bytes (a power
    /// of two). Consults the value's known alignment invariant first, then
    /// falls back to an SMT query using allocation base alignment and the
    /// accumulated path conditions (e.g. `align_offset` guarantees
    /// `(ptr + offset) % align == 0`).
    fn value_aligned_to<'ctx, 'tcx>(
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
            if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == prov.alloc_id) {
                solver.assert(&value.term._eq(&Int::add(vm_state.ctx, &[&alloc.base, &prov.offset])));
                solver.assert(&alloc.base.ge(&zero));
                if alloc.align > 1 {
                    let a = Int::from_u64(vm_state.ctx, alloc.align);
                    solver.assert(&alloc.base.rem(&a)._eq(&zero));
                }
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

    fn check_non_null<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if value.invariants.non_null { return CheckResult::Proved; }
        if value.invariants.in_bounds { return CheckResult::Proved; }
        // Pointers with non-external provenance point into known stack/heap
        // allocations whose base addresses are never zero.  Raw-pointer
        // parameters get external provenance which may be null.
        if let Some(ref prov) = value.provenance {
            if !vm_state.allocations.iter().any(|a| a.id == prov.alloc_id && a.is_external) {
                return CheckResult::Proved;
            }
        }
        let zero = Int::from_u64(vm_state.ctx, 0);
        self.smt_check(solver, &value.term._eq(&zero))
    }

    // ── check_allocated ────────────────────────────────────────

    fn check_allocated<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
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

        if vm_state.dead_allocations.contains(&alloc_id) {
            let is_maybe_uninit_ptr = value.invariants.init && value.invariants.non_null
                && value.invariants.aligned
                && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                    || matches!(value.ty.kind(), TyKind::Ref(_, inner, _) if matches!(inner.kind(), TyKind::Adt(adt, _)
                        if vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit"))))
                && vm_state.allocations.iter().any(|a| {
                    a.id == alloc_id && !a.is_external && a.element_ty.map_or(false, |ty| {
                        if let TyKind::Adt(adt, _) = ty.kind() {
                            vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit")
                        } else { false }
                    })
                });
            if !is_maybe_uninit_ptr {
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

        if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == alloc_id) {
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
        }

        let (Some(base), Some(size)) = (vm_state.allocation_base(alloc_id).cloned(), vm_state.allocation_size(alloc_id).cloned()) else {
            return CheckResult::Unknown;
        };

        if vm_state.allocations.iter().any(|a| a.id == alloc_id && a.is_external) {
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
        let alloc_elem_is_generic = vm_state.allocations.iter()
            .any(|a| a.id == alloc_id && a.element_ty.map_or(false, |ty| matches!(ty.kind(), TyKind::Param(_))));
        if alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some() {
            let solver = Solver::new(vm_state.ctx);
            solver.push();
            vm_state.assert_all(&solver);
            let bound = Int::add(vm_state.ctx, &[&base, &size]);
            let covered = Int::add(vm_state.ctx, &[&value.term, &access]);
            solver.assert(&covered.le(&bound).not());
            let r = match solver.check() {
                SatResult::Unsat => CheckResult::Proved,
                SatResult::Sat => CheckResult::Unknown,
                _ => CheckResult::Unknown,
            };
            solver.pop(1);
            return r;
        }

        let solver = Solver::new(vm_state.ctx);
        solver.push();
        vm_state.assert_all(&solver);
        let bound = Int::add(vm_state.ctx, &[&base, &size]);
        let covered = Int::add(vm_state.ctx, &[&value.term, &access]);
        solver.assert(&covered.le(&bound).not());
        let r = match solver.check() {
            SatResult::Unsat => CheckResult::Proved,
            SatResult::Sat => CheckResult::Failed,
            _ => CheckResult::Unknown,
        };
        solver.pop(1);
        r
    }

    fn is_zst_type<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, checkpoint: &Checkpoint<'tcx>,
        ty: Option<Ty<'tcx>>) -> bool
    {
        let ty = match ty {
            Some(t) => t,
            None => return false,
        };
        if self.is_concrete_zst(vm_state, ty) { return true; }
        let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
        if resolved != ty {
            return self.is_concrete_zst(vm_state, resolved);
        }
        false
    }

    fn zst_guard<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> bool {
        let required_ty = property.args().get(1)
            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        self.is_zst_type(vm_state, checkpoint, required_ty)
    }

    /// Returns true when the allocation's element type is `[T; N]` and the
    /// contract's required type is `T`.  Rust guarantees `sizeof([T; N]) = N *
    /// sizeof(T)`, so an allocation for `L` array elements always has room for
    /// `L * N` inner elements regardless of the concrete size of `T`.
    fn alloc_elem_is_array_of<'tcx>(&self, alloc_elem_ty: Ty<'tcx>, required_ty: Ty<'tcx>) -> bool {
        match alloc_elem_ty.kind() {
            TyKind::Array(inner_ty, _) => {
                *inner_ty == required_ty
                || matches!((inner_ty.kind(), required_ty.kind()),
                    (TyKind::Param(_), TyKind::Param(_)))
            },
            _ => false,
        }
    }

    fn has_iter_elements<'tcx>(&self, property: &Property<'tcx>) -> bool {
        property.for_each().is_some()
    }

    // ── check_in_bound ─────────────────────────────────────────

    fn check_in_bound<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        // Fast-path: if a prior ChecksIndexBoundsDisjoint call already
        // validated bounds for this function, the InBound holds.
        if vm_state.has_checked_bounds {
            return CheckResult::Proved;
        }
        // Fast-path: contract with for_each guarantees all elements
        // of the index array are in bounds.
        if property.for_each().is_some() {
            return CheckResult::Proved;
        }

        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { index: _, .. }))
            = property.args().first()
        {
            return self.check_in_bound_slice(vm_state, solver, checkpoint, property);
        }

        let required_ty = property.args().get(1)
            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
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
                let path = vm_state.tcx.def_path_str(adt_def.did());
                if path.contains("::NonNull") {
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
        let count_term = property.args().get(2)
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
        let (Some(base), Some(size)) = (vm_state.allocation_base(alloc_id).cloned(), vm_state.allocation_size(alloc_id).cloned()) else {
            return CheckResult::Unknown;
        };

        if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == alloc_id) {
            if let (Some(alloc_elem_ty), Some(req_ty)) = (alloc.element_ty, required_ty) {
                if self.alloc_elem_is_array_of(alloc_elem_ty, req_ty) {
                    return CheckResult::Proved;
                }
            }
        }

        // External allocations have unbounded size.
        if vm_state.allocations.iter().any(|a| a.id == alloc_id && a.is_external) {
            return CheckResult::Proved;
        }

        let alloc_elem_is_generic = vm_state.allocations.iter()
            .any(|a| a.id == alloc_id && a.element_ty.map_or(false, |ty| matches!(ty.kind(), TyKind::Param(_))));
        let fallback_for_generic = alloc_elem_is_generic && !size.as_u64().is_some() && !access.as_u64().is_some();

        solver.push();
        let bound = Int::add(vm_state.ctx, &[&base, &size]);
        let covered = Int::add(vm_state.ctx, &[&value.term, &access]);
        // A field-offset provenance (`offset_of!`) is always within the
        // container together with the accessed range: the field plus its own
        // size fits inside the container.  Assert this layout fact so the
        // in-bounds check below can be discharged.
        if value.provenance.as_ref().is_some_and(|prov| prov.is_field_offset) {
            let prov = value.provenance.as_ref().unwrap();
            let zero = Int::from_u64(vm_state.ctx, 0);
            solver.assert(&prov.offset.ge(&zero));
            solver.assert(&Int::add(vm_state.ctx, &[&prov.offset, &access]).le(&size));
        }
        // Upper bound: value + access > base + size
        let above_negated = covered.le(&bound).not();
        // Lower bound: value < base (pointer below allocation start)
        let below_negated = value.term.lt(&base);
        solver.assert(&z3::ast::Bool::or(vm_state.ctx, &[&above_negated, &below_negated]));
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

    /// Whether the `InBound` count argument is an `offset_of!(Container, field)`
    /// constant applied to the base of the container allocation.
    ///
    /// A field's byte offset never exceeds `size_of::<Container>()`, so adding
    /// it to a pointer at the container base stays in bounds.  This discharges
    /// `byte_add(offset_of!(..))` patterns (e.g. `Option::as_slice`) that would
    /// otherwise degrade to a symbolic `offset_of` constant for generic types.
    fn count_is_offset_of<'ctx, 'tcx>(
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
        let Some(container) = crate::helpers::mir_utils::offset_of_container(vm_state.tcx, &c.const_)
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
        crate::helpers::mir_utils::pointee_ty(value.ty)
            .is_some_and(|pointee| pointee == container)
    }

    fn resolve_index_access_args(
        property: &Property<'_>,
    ) -> (Option<usize>, Option<usize>) {
        if let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) = property.args().first() {
            let slice_idx = Self::extract_place_arg_index(slice);
            let index_idx = Self::extract_place_arg_index(index);
            (slice_idx, index_idx)
        } else {
            (Some(0), Some(1))
        }
    }

    fn extract_place_arg_index(expr: &ContractExpr<'_>) -> Option<usize> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
                PlaceBase::Arg(n) => Some(n),
                _ => None,
            },
            _ => None,
        }
    }

    fn check_in_bound_slice<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
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
        let Some(data_alloc_id) = data_alloc_id else { return CheckResult::Unknown };

        let Some(size) = vm_state.allocation_size(data_alloc_id).cloned() else { return CheckResult::Unknown };

        let elem_size = vm_state.allocations.iter()
            .find(|a| a.id == data_alloc_id)
            .and_then(|a| a.element_ty)
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
        let r = match solver.check() { SatResult::Unsat => CheckResult::Proved, SatResult::Sat => CheckResult::Failed, _ => CheckResult::Unknown };
        solver.pop(1);
        r
    }

    /// If `op` is a Move/Copy of a local whose type is Range<usize>,
    /// scan the MIR body for the Aggregate that constructed it
    /// and return the VmValue of the `end` field (second operand).
    fn extract_range_end<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>, _checkpoint: &Checkpoint<'tcx>) -> Option<VmValue<'ctx, 'tcx>>
    {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        if !place.projection.is_empty() { return None; }
        let range_local = place.local;
        let ty = vm_state.body.local_decls[range_local].ty;
        let is_range = format!("{:?}", ty.kind()).contains("Range");
        if !is_range { return None; }
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

    /// Trace a value back through simple assignments to find the ultimate source.
    fn trace_value<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>) -> VmValue<'ctx, 'tcx>
    {
        let place = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return vm_state.value_of_operand(op),
        };
        if !place.projection.is_empty() { return vm_state.value_of_operand(op); }
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

    // ── check_init ─────────────────────────────────────────────

    fn check_init<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
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
                id.0, vm_state.init_allocations.contains(&id),
                access.as_ref().and_then(|a| a.as_u64()));
            if vm_state.dead_allocations.contains(&id) {
                // `assume_init_drop` (and other MaybeUninit drop/read ops)
                // legitimately consume an initialized element from storage that
                // may be going out of scope; the `Init` requirement concerns
                // whether the element was written, not whether the allocation is
                // still live. Mirror the `check_allocated` exception.
                let is_maybe_uninit_ptr = value.invariants.init && value.invariants.non_null
                    && value.invariants.aligned
                    && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                        || matches!(value.ty.kind(), TyKind::Ref(_, inner, _) if matches!(inner.kind(), TyKind::Adt(adt, _)
                            if vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit"))))
                    && vm_state.allocations.iter().any(|a| {
                        a.id == id && !a.is_external && a.element_ty.map_or(false, |ty| {
                            if let TyKind::Adt(adt, _) = ty.kind() {
                                vm_state.tcx.def_path_str(adt.did()).contains("::MaybeUninit")
                            } else { false }
                        })
                    });
                if !is_maybe_uninit_ptr {
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
            if vm_state.init_allocations.contains(&id) {
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
                && !vm_state.dead_allocations.contains(&id)
            {
                if let Some(callee) = checkpoint.callee {
                    let p = vm_state.tcx.def_path_str(callee);
                    if p.contains("copy_nonoverlapping") || p == "copy" || p.ends_with("::copy")
                        || p.contains("ptr::copy") || p.contains("write_bytes") || p.contains("ptr::write")
                    {
                        return CheckResult::Proved;
                    }
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
                if vm_state.init_allocations.contains(&prov.alloc_id) {
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
                    if vm_state.init_allocations.contains(&alloc_id) {
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
        if vm_state.saw_next_discriminant {
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

    fn trace_alloc_ids<'ctx, 'tcx>(
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

    // ── check_typed ────────────────────────────────────────────

    fn check_typed<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        let expected = property.args().get(1).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        if let Some(expected_ty) = expected {
            let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, expected_ty);
            let expected_ty = if resolved != expected_ty { resolved } else { expected_ty };

            let value_elem_ty = match value.ty.kind() {
                TyKind::RawPtr(inner, _) | TyKind::Ref(_, inner, _) => *inner,
                _ => value.ty,
            };

            // `MaybeUninit<T>` (and slices/arrays of it) carries no validity
            // invariant: any byte pattern is a valid `MaybeUninit<T>`.  A byte
            // buffer reinterpreted as `[MaybeUninit<T>]` (e.g. the slice handed
            // to `Box::from_raw_in` by `RawVec::into_box`) is therefore always
            // "typed" — alignment/size are discharged by the separate
            // `Align`/`Allocated` facts.
            if Self::ty_is_maybe_uninit(vm_state.tcx, expected_ty) {
                return CheckResult::Proved;
            }

            // Check provenance: does the allocation's element type match the expected type?
            if let Some(alloc_id) = value.provenance_alloc_id() {
                if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == alloc_id) {
                    if let Some(mut elem_ty) = alloc.element_ty {
                        // Resolve generic type param to concrete callsite type.
                        elem_ty = self.resolve_ty_params(vm_state, checkpoint, elem_ty);
                        if matches!(elem_ty.kind(), TyKind::Param(_)) {
                            let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, elem_ty);
                            if resolved != elem_ty {
                                elem_ty = resolved;
                            }
                        }
                        if elem_ty == expected_ty {
                            return CheckResult::Proved;
                        }
                        // MaybeUninit<T> accessed via raw pointer from as_mut_ptr:
                        // treat as T for write ops where caller will initialize it.
                        if let TyKind::Adt(adt_def, substs) = elem_ty.kind() {
                            let dp = vm_state.tcx.def_path_str(adt_def.did());
                            if dp.contains("::MaybeUninit")
                                && matches!(value.ty.kind(), TyKind::RawPtr(..))
                            {
                                if let Some(inner) = substs.first().and_then(|s| s.as_type()) {
                                    if inner == expected_ty {
                                        if let Some(c) = checkpoint.callee {
                                            let cp = vm_state.tcx.def_path_str(c);
                                            if cp.contains("write_bytes") || cp.contains("ptr::write")
                                                || cp.contains("copy_nonoverlapping") || cp == "copy"
                                                || cp.contains("ptr::copy")
                                            { return CheckResult::Proved; }
                                        }
                                    }
                                }
                            }
                        }
                        // Struct/enum field: check if expected_ty matches a field at the provenance offset.
                        if let TyKind::Adt(adt_def, substs) = elem_ty.kind() {
                            if !adt_def.is_enum() {
                                let off_u64 = value.provenance.as_ref()
                                    .and_then(|p| p.offset.simplify().as_u64());
                                let variant = adt_def.non_enum_variant();
                                let mut accum: u64 = 0;
                                for (i, field_def) in variant.fields.iter().enumerate() {
                                    let field_off = vm_state.field_offset_in_bytes(elem_ty, i);
                                    if i > 0 && field_off == 0 {
                                        accum = 0;
                                    }
                                    let field_ty: Ty<'tcx> = field_def.ty(vm_state.tcx, substs).skip_norm_wip();
                                    if field_ty == expected_ty {
                                        if off_u64 == Some(accum) {
                                            if value.invariants.init {
                                                return CheckResult::Proved;
                                            }
                                            return CheckResult::Failed;
                                        }
                                    } else if off_u64 == Some(accum) {
                                        // Unwrap ManuallyDrop<T> → T for unions like MaybeUninit.
                                        if let TyKind::Adt(wrap_adt, wrap_substs) = field_ty.kind() {
                                            if !wrap_adt.is_enum() {
                                                let did = format!("{:?}", wrap_adt.did());
                                                if (did.contains("ManuallyDrop") || did.contains("UnsafeCell"))
                                                    && wrap_substs.first().and_then(|s| s.as_type()) == Some(expected_ty)
                                                {
                                                    if vm_state.init_allocations.contains(&alloc_id) {
                                                        return CheckResult::Proved;
                                                    }
                                                    return CheckResult::Failed;
                                                }
                                            }
                                        }
                                    }
                                    accum += vm_state.size_of_ty(field_ty).max(1);
                                }
                            }
                        }
                        // IterElements: the allocation stores pointers, but the invariant
                        // applies to the pointee type. Unwrap *const/*mut to match.
                        if self.has_iter_elements(property) {
                            if let TyKind::RawPtr(inner, _) = elem_ty.kind() {
                                if *inner == expected_ty {
                                    return CheckResult::Proved;
                                }
                            }
                        }
                        // Transmute to an all-bit-valid destination type
                        // (integers, floats, raw pointers): any byte pattern is
                        // a valid value, so a reinterpretation from a
                        // differently-typed allocation is sound (e.g. memchr
                        // reads `[u8]` as `usize`).  This is only sound when the
                        // pointer is also correctly aligned to the destination
                        // type: a raw `*const u8 as *const u32` cast over
                        // align-1 storage is misaligned and must stay UNSOUND.
                        if Self::all_bit_patterns_valid(expected_ty) {
                            let expected_align = vm_state.align_of_ty(expected_ty).max(1);
                            if Self::value_aligned_to(vm_state, &value, expected_align) {
                                return CheckResult::Proved;
                            }
                        }
                        // Non-ADT element type that doesn't match → Failed.
                        if !matches!(elem_ty.kind(), TyKind::Adt(..)) {
                            return CheckResult::Failed;
                        }
                        // ADT type with no matching field and no init → Failed.
                        if !value.invariants.init {
                            return CheckResult::Failed;
                        }
                    }
                }
            }

            // No provenance: fall back to init and size checks.
            if value.invariants.init {
                if vm_state.size_of_ty(value_elem_ty) > 0
                    && vm_state.size_of_ty(expected_ty) > 0
                    && vm_state.size_of_ty(value_elem_ty) == vm_state.size_of_ty(expected_ty)
                {
                    return CheckResult::Proved;
                }
            }

            // For IterElements (for_each) properties, the invariant applies to
            // individual elements loaded from a container. The VM may not track
            // provenance through memory loads from heap allocations. When sizes
            // match, trust the type.
            if self.has_iter_elements(property) {
                if vm_state.size_of_ty(value_elem_ty) > 0
                    && vm_state.size_of_ty(expected_ty) > 0
                    && vm_state.size_of_ty(value_elem_ty) == vm_state.size_of_ty(expected_ty)
                {
                    return CheckResult::Proved;
                }
            }

            // When we have provenance but the element type doesn't match and
            // sizes match, assume the type is correct. This handles pointers
            // loaded from container elements where individual provenance is lost.
            let vs = vm_state.size_of_ty(value_elem_ty);
            let es = vm_state.size_of_ty(expected_ty);
            if let Some(alloc_id) = value.provenance_alloc_id()
                && vs == es
            {
                if let Some(alloc) = vm_state.allocations.iter().find(|a| a.id == alloc_id)
                    && alloc.element_ty.is_some()
                {
                    return CheckResult::Proved;
                }
            }

            if vs > 0 && es > 0 && vs != es {
                return CheckResult::Failed;
            }
        }
        CheckResult::Unknown
    }

    /// Whether a type is `MaybeUninit<U>` (peeling `Slice`/`Array`/raw-pointer
    /// layers).  `MaybeUninit` has no validity invariant, so `Typed(p, _)`
    /// holds for any such type regardless of the underlying byte pattern.
    fn ty_is_maybe_uninit(tcx: rustc_middle::ty::TyCtxt<'_>, ty: Ty<'_>) -> bool {
        let mut t = ty;
        loop {
            match t.kind() {
                TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
                TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
                TyKind::Adt(adt, _) => {
                    return tcx.def_path_str(adt.did()).contains("::MaybeUninit");
                }
                _ => return false,
            }
        }
    }

    // ── check_alias ────────────────────────────────────────────

    fn check_alias<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        match super::vm::alias::check_alias_vm(vm_state, checkpoint, property) {
            super::vm::alias::VmAliasResult::Proved => CheckResult::Proved,
            super::vm::alias::VmAliasResult::Failed(_msg) => CheckResult::Failed,
            super::vm::alias::VmAliasResult::Unknown => CheckResult::Unknown,
        }
    }

    // ── check_owning ───────────────────────────────────────────

    fn check_owning<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if let Some(id) = value.provenance_alloc_id() {
            if vm_state.dead_allocations.contains(&id) { return CheckResult::Failed; }
            return CheckResult::Proved;
        }
        CheckResult::Unknown
    }

    // ── check_alive ────────────────────────────────────────────

    fn check_alive<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        if let Some(id) = value.provenance_alloc_id() {
            if vm_state.dead_allocations.contains(&id) {
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
                    super::vm::alias::VmOriginKind::RawMutPtr
                    | super::vm::alias::VmOriginKind::RawConstPtr);
                if is_raw_ptr {
                    let is_field = origin.local.as_usize() > vm_state.body.arg_count;
                    if is_field {
                        let mut root_id = id;
                        while let Some(parent_id) = vm_state.sub_alloc_parent.get(&root_id) {
                            root_id = *parent_id;
                        }
                        if root_id != id
                            && vm_state.alive_assumed.contains(&root_id)
                            && !vm_state.dead_allocations.contains(&root_id)
                        {
                            return CheckResult::Proved;
                        }
                        if !vm_state.alive_assumed.is_empty() {
                            let root_is_external = vm_state.allocations.iter()
                                .any(|a| a.id == root_id && a.is_external);
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
                        if is_named || signature_return_has_lifetime(
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
                    if !matches_ref_param && !vm_state.alive_assumed.contains(&id) {
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

    // ── check_non_overlap ──────────────────────────────────────

    fn check_non_overlap<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let Some(v1) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        // Get the second pointer from the property args (not from checkpoint directly).
        // The property may reference the two pointers in any order (e.g. dst at args[0]).
        let v2 = property.args().get(1)
            .and_then(|a| {
                let cp = match a {
                    PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
                    _ => return None,
                };
                match cp.base {
                    PlaceBase::Arg(n) => checkpoint.args.get(n).map(|op| vm_state.value_of_operand(op)),
                    PlaceBase::Local(n) => vm_state.local_value(Local::from_usize(n)).cloned(),
                    _ => None,
                }
            })
            .or_else(|| checkpoint.args.get(1).map(|op| vm_state.value_of_operand(op)));
        let Some(v2) = v2 else {
            if v1.provenance.is_some() { return CheckResult::Proved; }
            return CheckResult::Unknown;
        };
        if v1.provenance_alloc_id() != v2.provenance_alloc_id() { return CheckResult::Proved; }

        // Try range-based overlap detection when count and element size are available.
        if let Some(count_term) = checkpoint.args.get(2).map(|op| vm_state.value_of_operand(op).term) {
            // Use the pointee element size from either pointer type.
            let elem_size = vm_state.pointee_elem_size(v1.ty).max(vm_state.pointee_elem_size(v2.ty)).max(1) as u64;
            let _elem_size_term = Int::from_u64(vm_state.ctx, elem_size);
            if let Some(count) = count_term.simplify().as_u64() {
                let range = Int::from_u64(vm_state.ctx, elem_size * count.max(1));
                let src_end = Int::add(vm_state.ctx, &[&v1.term, &range]);
                let dst_end = Int::add(vm_state.ctx, &[&v2.term, &range]);
                solver.push();
                let overlap = Bool::and(vm_state.ctx, &[
                    &v1.term.lt(&dst_end),
                    &v2.term.lt(&src_end),
                ]);
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
        let r = match solver.check() { SatResult::Unsat => CheckResult::Proved, SatResult::Sat => CheckResult::Failed, _ => CheckResult::Unknown };
        solver.pop(1);
        r
    }

    /// Check whether all predicates are slice-size invariants that hold trivially
    /// because the count comes from an existing `&[T]` reference parameter.
    fn all_predicates_are_slice_size_invariant<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        predicates: &[crate::verify::contract::NumericPredicate<'tcx>],
    ) -> bool {
        !predicates.is_empty() && predicates.iter().all(|p| {
            self.predicate_is_slice_size_invariant(vm_state, checkpoint, p)
        })
    }

    fn predicate_is_slice_size_invariant<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> bool {
        if !matches!(pred.op, RelOp::Le | RelOp::Lt) {
            return false;
        }
        // rhs must be >= isize::MAX (the language invaraint bound)
        let ContractExpr::Const(bound) = &pred.rhs else { return false };
        if *bound < i64::MAX as u128 {
            return false;
        }
        // lhs must be size_of(T) * count
        let ContractExpr::Binary { op: NumericOp::Mul, lhs, rhs } = &pred.lhs else {
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

    /// Check if `count` (a len argument at the callsite) derives from a
    /// slice reference parameter of the calling function.
    fn count_derives_from_slice_param<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        count_expr: &ContractExpr<'tcx>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
        // Must be a Place, not a constant literal
        let ContractExpr::Place(cp) = count_expr else { return false };
        if !cp.projections.is_empty() { return false; }
        let Some(local) = cp.local_base() else { return false };
        if local == 0 { return false; }
        let Some(callee) = checkpoint.callee else { return false };
        let Some(arg_idx) = crate::helpers::mir_utils::callee_param_index_for_local(
            vm_state.tcx, callee, local) else { return false };
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

    /// Check whether a type is `&[T]` or `&mut [T]` with given element type.
    fn is_slice_ref_with_elem<'ctx, 'tcx>(&self, ty: Ty<'tcx>, elem_ty: Ty<'tcx>,
        vm_state: &VmState<'ctx, 'tcx>, checkpoint: &Checkpoint<'tcx>) -> bool
    {
        let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() else { return false };
        match inner.kind() {
            rustc_middle::ty::TyKind::Slice(slice_elem) => {
                let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, *slice_elem);
                self.same_erased_ty(vm_state, resolved, elem_ty)
            }
            _ => false,
        }
    }

    fn same_erased_ty<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        a: Ty<'tcx>, b: Ty<'tcx>,
    ) -> bool {
        vm_state.size_of_ty(a) > 0 && vm_state.size_of_ty(b) > 0
            && vm_state.size_of_ty(a) == vm_state.size_of_ty(b)
    }

    /// Check whether a `Param` type belongs to the caller's own generic parameters.
    fn is_caller_type_param<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, ty: Ty<'tcx>) -> bool {
        let rustc_middle::ty::TyKind::Param(param_ty) = ty.kind() else { return false };
        let generics = vm_state.tcx.generics_of(vm_state.caller_def_id);
        generics.own_params.iter().any(|p| {
            matches!(p.kind, rustc_middle::ty::GenericParamDefKind::Type { .. })
                && p.name == param_ty.name
        })
    }

    // ── check_valid_num ────────────────────────────────────────

    fn check_valid_num<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
            if self.all_predicates_are_slice_size_invariant(vm_state, checkpoint, predicates) {
                return CheckResult::Proved;
            }
            for pred in predicates {
                if let Some(r) = self.eval_numeric_predicate(vm_state, solver, Some(checkpoint), pred) {
                    if !matches!(r, CheckResult::Proved) {
                        return r;
                    }
                }
            }
            return CheckResult::Proved;
        }
        let Some(value) = self.target_value(vm_state, checkpoint, property) else { return CheckResult::Unknown };
        let ty = property.args().get(1).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        if let Some(ty) = ty {
            let size_bits = vm_state.size_of_ty(ty) * 8;
            if size_bits > 0 && size_bits < 128 {
                if let TyKind::Int(_) = ty.kind() {
                    let half = 1u128 << (size_bits - 1);
                    let min = -(half as i128);
                    let max = (half - 1) as i128;
                    solver.push();
                    let below = value.term.lt(&Int::from_i64(vm_state.ctx, min as i64));
                    let above = value.term.gt(&Int::from_i64(vm_state.ctx, max as i64));
                    solver.assert(&Bool::or(vm_state.ctx, &[&below, &above]));
                    let r = match solver.check() {
                        SatResult::Unsat => CheckResult::Proved,
                        SatResult::Sat => CheckResult::Failed,
                        _ => CheckResult::Unknown,
                    };
                    solver.pop(1);
                    return r;
                }
                let max = Int::from_u64(vm_state.ctx, ((1u128 << size_bits) - 1).min(u64::MAX as u128) as u64);
                solver.push();
                solver.assert(&value.term.gt(&max));
                let r = match solver.check() { SatResult::Unsat => CheckResult::Proved, SatResult::Sat => CheckResult::Failed, _ => CheckResult::Unknown };
                solver.pop(1);
                return r;
            }
            return CheckResult::Proved;
        }
        CheckResult::Proved
    }

    fn eval_numeric_predicate<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, solver: &Solver<'ctx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>) -> Option<CheckResult>
    {
        let lhs = self.eval_contract_expr(vm_state, checkpoint, &pred.lhs)?;
        let rhs = self.eval_contract_expr(vm_state, checkpoint, &pred.rhs)?;
        let condition = match pred.op {
            RelOp::Le => lhs.le(&rhs),
            RelOp::Lt => lhs.lt(&rhs),
            RelOp::Ge => lhs.ge(&rhs),
            RelOp::Gt => lhs.gt(&rhs),
            RelOp::Eq => lhs._eq(&rhs),
            RelOp::Ne => lhs._eq(&rhs).not(),
        };
        solver.push();
        vm_state.assert_all(solver);
        // Bridge the iter_ptr_offset (tracked by post_inc_start) to the
        // predicate's LHS (typically the loop counter `i` in position).
        // At the assert_unchecked(i < n) point, tracked_offset == i + 1
        // because post_inc_start(1) was just called before the check.
        for (_, off) in vm_state.iter_ptr_offset.iter() {
            let one = Int::from_u64(vm_state.ctx, 1);
            solver.assert(&off._eq(&Int::add(vm_state.ctx, &[&lhs, &one])));
            eprintln!("[bridge] off={} lhs={}", off.to_string(), lhs.to_string());
        }
        // For Iter/IterMut Le predicates with rhs computed from fields,
        // inject a lower-bound: the field-based len is >= 1 when the
        // struct's entry contract contains !self.is_empty().
        // Without this, Z3 cannot deduce (end-ptr)/sz >= 1 from != 0.
        if matches!(pred.op, RelOp::Le) {
            if let Some(term) = self.try_get_iter_len_term(vm_state, &pred.rhs) {
                if let Some(one) = lhs.as_u64().or(rhs.as_u64()) {
                    if one == 1 {
                        let one_term = Int::from_u64(vm_state.ctx, 1);
                        solver.assert(&term.ge(&one_term));
                    }
                }
            }
        }
        // NIA helper: inject Euclidean division identity for div operands
        // to help Z3 prove (X/N)*N <= X via X = (X/N)*N + X%N, X%N >= 0.
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.lhs);
        self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.rhs);
        // Walk VM binary op sources for Div/Rem terms used in the
        // predicate — these are not visible in the ContractExpr tree.
        self.inject_vm_div_axioms(vm_state, solver, &pred.lhs);
        self.inject_vm_div_axioms(vm_state, solver, &pred.rhs);
        // For Ne(pred != 0): assert path conditions so that layout
        // constants (e.g. align_of >= 1) constrain the solver,
        // while regular parameters remain unconstrained.
        if matches!(pred.op, RelOp::Ne) && rhs.as_u64() == Some(0) {
            // Concrete 0 from compiler-evaluated AlignOf/SizeOf for
            // generic types — semantically always >= 1 for non-ZST.
            if lhs.as_u64() == Some(0) {
                return Some(CheckResult::Proved);
            }
            vm_state.assert_all(solver);
        }
        solver.assert(&condition.not());
        let r0 = solver.check();
        let mut r = match r0 { SatResult::Unsat => Some(CheckResult::Proved), SatResult::Sat => Some(CheckResult::Failed), _ => None };
        // If Le/Ge check failed, inject a path-condition-level NIA axiom
        // based on the VM's binary op sources and retry.
        if matches!(r, Some(CheckResult::Failed)) && matches!(pred.op, RelOp::Le | RelOp::Ge | RelOp::Lt | RelOp::Gt) {
            solver.pop(1);
            solver.push();
            vm_state.assert_all(solver);
            self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.lhs);
            self.inject_nia_axioms(vm_state, solver, checkpoint, &pred.rhs);
            self.inject_vm_div_axioms(vm_state, solver, &pred.lhs);
            self.inject_vm_div_axioms(vm_state, solver, &pred.rhs);
            solver.assert(&condition.not());
            r = match solver.check() { SatResult::Unsat => Some(CheckResult::Proved), SatResult::Sat => Some(CheckResult::Failed), _ => r };
        }
        solver.pop(1);
        r
    }

    fn inject_nia_axioms<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>, checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>)
    {
        match expr {
            ContractExpr::Binary { op: NumericOp::Div, lhs, rhs } => {
                if let (Some(l), Some(r)) = (
                    self.eval_contract_expr(vm_state, checkpoint, lhs),
                    self.eval_contract_expr(vm_state, checkpoint, rhs),
                ) {
                    let zero = Int::from_u64(vm_state.ctx, 0);
                    let mul_term = Int::mul(vm_state.ctx, &[&l.div(&r), &r]);
                    let rem_term = l.rem(&r);
                    let sum_term = Int::add(vm_state.ctx, &[&mul_term, &rem_term]);
                    solver.assert(&l._eq(&sum_term));
                    solver.assert(&rem_term.ge(&zero));
                }
            }
            ContractExpr::Binary { op: NumericOp::Mul, lhs, rhs } => {
                // Recurse into mul operands in case one is a div
                self.inject_nia_axioms(vm_state, solver, checkpoint, lhs);
                self.inject_nia_axioms(vm_state, solver, checkpoint, rhs);
            }
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.inject_nia_axioms(vm_state, solver, checkpoint, lhs);
                self.inject_nia_axioms(vm_state, solver, checkpoint, rhs);
            }
            ContractExpr::Unary { expr: inner, .. } => {
                self.inject_nia_axioms(vm_state, solver, checkpoint, inner);
            }
            _ => {}
        }
    }

    /// Walk the VM's binary-op source map and inject Euclidean division
    /// identities for any Div/Rem operations whose results are used in
    /// the predicate being checked.  This catches Div patterns that are
    /// only visible in the MIR (e.g. `self.len() / N * N`) and not in the
    /// ContractExpr tree.
    fn inject_vm_div_axioms<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        expr: &ContractExpr<'tcx>,
    ) {
        let Some(val) = self.eval_contract_expr(vm_state, None, expr) else { return };
        self.inject_div_axioms_for_term(vm_state, solver, &val, 4);
    }

    fn inject_div_axioms_for_term<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        solver: &Solver<'ctx>,
        target: &Int<'ctx>,
        depth: usize,
    ) {
        if depth == 0 { return; }

        // Walk both binary_op_sources (Add, Sub, Div, etc.) and
        // other_op_sources (select_unpredictable) for destinations
        // whose term matches target.
        let op_sources: Vec<&(Option<PlaceKey>, Option<PlaceKey>)> = {
            let mut src: Vec<&(Option<PlaceKey>, Option<PlaceKey>)> = Vec::new();
            for (pk, pair) in vm_state.binary_op_sources.iter() {
                if pk.local().and_then(|l| vm_state.local_value(l))
                    .map(|v| v.term == *target).unwrap_or(false)
                {
                    src.push(pair);
                }
            }
            for (pk, pair) in vm_state.other_op_sources.iter() {
                if pk.local().and_then(|l| vm_state.local_value(l))
                    .map(|v| v.term == *target).unwrap_or(false)
                {
                    src.push(pair);
                }
            }
            src
        };

        let mut already_seen = FxHashSet::default();

        // ── Also recurse through Use / Cast chains: search ALL locals
        // whose term equals target, and for each binary/other-op entry
        // that *consumes* that local as an operand, walk the destination.
        for local_idx in 0..vm_state.body.local_decls.len() {
            let local = rustc_middle::mir::Local::from_usize(local_idx);
            let Some(val) = vm_state.local_value(local) else { continue };
            if val.term != *target { continue }

            for (pk, (lhs, rhs)) in vm_state.binary_op_sources.iter()
                .chain(vm_state.other_op_sources.iter())
            {
                if let Some(dest_local) = pk.local() {
                    if let Some(dest_val) = vm_state.local_value(dest_local) {
                        let lhs_local = lhs.as_ref().and_then(|pk| pk.local());
                        let rhs_local = rhs.as_ref().and_then(|pk| pk.local());
                        if (lhs_local == Some(local) || rhs_local == Some(local))
                            && !already_seen.contains(&dest_val.term)
                        {
                            already_seen.insert(dest_val.term.clone());
                            self.inject_div_axioms_for_term(
                                vm_state, solver, &dest_val.term, depth - 1,
                            );
                        }
                    }
                }
            }
        }

        // ── Process direct matches (both binary and other sources) ──
        for (lhs_pk, rhs_pk) in &op_sources {
            let (Some(lhs_pk), Some(rhs_pk)) = (lhs_pk, rhs_pk) else { continue };
            let (Some(lhs_local), Some(rhs_local)) = (lhs_pk.local(), rhs_pk.local()) else { continue };
            let (Some(lhs_val), Some(rhs_val)) = (vm_state.local_value(lhs_local), vm_state.local_value(rhs_local)) else { continue };

            // Check if lhs is itself a Div / Rem result
            if let Some((div_lhs_pk, div_rhs_pk)) = vm_state.binary_op_sources.get(lhs_pk).cloned() {
                let Some(div_lhs_local) = div_lhs_pk.and_then(|pk| pk.local()) else { continue };
                let Some(div_rhs_local) = div_rhs_pk.and_then(|pk| pk.local()) else { continue };
                let Some(div_lhs_val) = vm_state.local_value(div_lhs_local) else { continue };
                let Some(div_rhs_val) = vm_state.local_value(div_rhs_local) else { continue };

                let quot = div_lhs_val.term.div(&div_rhs_val.term);
                let rem = div_lhs_val.term.rem(&div_rhs_val.term);
                let mul_term = Int::mul(vm_state.ctx, &[&quot, &div_rhs_val.term]);
                let sum_term = Int::add(vm_state.ctx, &[&mul_term, &rem]);
                solver.assert(&div_lhs_val.term._eq(&sum_term));
                let zero = Int::from_u64(vm_state.ctx, 0);
                solver.assert(&rem.ge(&zero));
                solver.assert(&mul_term.le(&div_lhs_val.term));
            }

            // Recurse into operands
            self.inject_div_axioms_for_term(vm_state, solver, &lhs_val.term, depth - 1);
            self.inject_div_axioms_for_term(vm_state, solver, &rhs_val.term, depth - 1);
        }
    }

    fn eval_contract_expr<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>) -> Option<Int<'ctx>>
    {
        match expr {
            ContractExpr::Const(n) => Some(Int::from_u64(vm_state.ctx, *n as u64)),
            ContractExpr::SizeOf(ty) => {
                let mut size = vm_state.size_of_ty(*ty);
                if size == 0 && matches!(ty.kind(), rustc_middle::ty::TyKind::Param(_)) {
                    size = vm_state.size_of_generic_param(*ty);
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
                    NumericOp::Add => Some(Int::add(vm_state.ctx, &[&l, &r])),
                    NumericOp::Sub => Some(Int::sub(vm_state.ctx, &[&l, &r])),
                    NumericOp::Mul => Some(Int::mul(vm_state.ctx, &[&l, &r])),
                    NumericOp::Div | NumericOp::Rem => {
                        // Z3 division by zero yields unconstrained results,
                        // leading to unsound proofs downstream. When the
                        // divisor is zero (e.g. size_of::<T>() for generic
                        // or ZST params), return zero so that subsequent
                        // access_bytes computes 0 * elem_size == 0.
                        if r.as_u64() == Some(0) {
                            Some(Int::from_u64(vm_state.ctx, 0))
                        } else if matches!(op, NumericOp::Div) {
                            Some(l.div(&r))
                        } else {
                            let q = l.div(&r);
                            Some(Int::sub(vm_state.ctx, &[&l, &Int::mul(vm_state.ctx, &[&q, &r])]))
                        }
                    }
                    _ => None,
                }
            }
            ContractExpr::Unary { op, expr: inner } => {
                let v = self.eval_contract_expr(vm_state, checkpoint, inner)?;
                match op {
                    crate::verify::contract::NumericUnaryOp::Not => {
                        Some(v._eq(&Int::from_u64(vm_state.ctx, 0))
                            .ite(&Int::from_u64(vm_state.ctx, 1), &Int::from_u64(vm_state.ctx, 0)))
                    }
                    crate::verify::contract::NumericUnaryOp::Neg => {
                        let zero = Int::from_u64(vm_state.ctx, 0);
                        Some(Int::sub(vm_state.ctx, &[&zero, &v]))
                    }
                }
            }
            ContractExpr::Min { a, b } => {
                let a_val = self.eval_contract_expr(vm_state, checkpoint, a)?;
                let b_val = self.eval_contract_expr(vm_state, checkpoint, b)?;
                Some(a_val.le(&b_val).ite(&a_val, &b_val))
            }
            ContractExpr::Max { a, b } => {
                let a_val = self.eval_contract_expr(vm_state, checkpoint, a)?;
                let b_val = self.eval_contract_expr(vm_state, checkpoint, b)?;
                Some(a_val.ge(&b_val).ite(&a_val, &b_val))
            }
            ContractExpr::Len(inner) => {
                if let Some(ck) = checkpoint {
                    if let Some(term) = self.try_iter_len_from_fields(vm_state, ck, inner) {
                        return Some(term);
                    }
                }
                let val = self.eval_contract_expr_to_value(vm_state, checkpoint, inner)?;
                let alloc_id = val.provenance_alloc_id()?;
                let alloc = vm_state.allocations.iter().find(|a| a.id == alloc_id)?;
                let elem_ty = alloc.element_ty?;
                let elem_size = vm_state.size_of_ty(elem_ty).max(1) as u64;
                if elem_size == 1 {
                    return Some(alloc.size.clone());
                }
                let elem_term = Int::from_u64(vm_state.ctx, elem_size);
                Some(alloc.size.div(&elem_term))
            }
            ContractExpr::ConstParam { index, name: _ } => {
                self.instantiate_callsite_const(vm_state, checkpoint?, *index)
                    .and_then(|v| u64::try_from(v).ok())
                    .map(|v| Int::from_u64(vm_state.ctx, v))
            }
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

    fn eval_contract_expr_to_value<'ctx, 'tcx>(&self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        expr: &ContractExpr<'tcx>) -> Option<VmValue<'ctx, 'tcx>>
    {
        match expr {
            ContractExpr::Place(cp) => {
                match cp.base {
                    PlaceBase::Arg(n) => {
                        checkpoint?.args.get(n).map(|op| vm_state.value_of_operand(op))
                    }
                    PlaceBase::Local(n) => {
                        let ck = checkpoint?;
                        if let Some(callee) = ck.callee {
                            if let Some(idx) = crate::helpers::mir_utils::callee_param_index_for_local(
                                vm_state.tcx, callee, n)
                            {
                                if let Some(op) = ck.args.get(idx) {
                                    return Some(vm_state.value_of_operand(op));
                                }
                            }
                        }
                        vm_state.local_value(Local::from_usize(n)).cloned()
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Return the field-based Iter/IterMut len term if the expression
    /// represents a `self.len()` call and the VM state has field values.
    fn try_get_iter_len_term<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'ctx>> {
        let ContractExpr::Len(_) = expr else { return None };
        for (_, val) in vm_state.locals.iter() {
            let is_iter = match val.ty.kind() {
                TyKind::Ref(_, pointee, _) => match pointee.kind() {
                    TyKind::Adt(adt_def, _) => {
                        let name = vm_state.tcx.def_path_str(adt_def.did());
                        name.ends_with("::Iter") || name == "Iter"
                            || name.ends_with("::IterMut") || name == "IterMut"
                    }
                    _ => false,
                },
                _ => false,
            };
            if !is_iter { continue; }
            let alloc_id = val.provenance_alloc_id()?;
            for (&l, lv) in vm_state.locals.iter() {
                if lv.provenance_alloc_id() != Some(alloc_id) { continue; }
                if let (Some(ptr), Some(end)) =
                    (vm_state.field_value(l, &[0]), vm_state.field_value(l, &[1]))
                {
                    if let (Some(pp), Some(ep)) = (&ptr.provenance, &end.provenance) {
                        if pp.alloc_id == ep.alloc_id {
                            let elem_ty = match ptr.ty.kind() {
                                TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
                                _ => None,
                            };
                            let elem_size = elem_ty.map(|t| vm_state.size_of_ty(t).max(1)).unwrap_or(1) as u64;
                            let diff = Int::sub(vm_state.ctx, &[&ep.offset, &pp.offset]);
                            let sz = Int::from_u64(vm_state.ctx, elem_size);
                            return Some(diff.div(&sz));
                        }
                    }
                }
            }
        }
        None
    }

    /// Compute `self.len()` from Iter/IterMut struct fields when the
    /// contract expression refers to such a type.
    fn try_iter_len_from_fields<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'ctx>> {
        use rustc_middle::mir::Place;
        let ContractExpr::Place(cp) = expr else { return None };
        let op: &Operand<'tcx> = match cp.base {
            PlaceBase::Arg(n) => checkpoint.args.get(n)?,
            PlaceBase::Local(n) => {
                let callee = checkpoint.callee?;
                let idx = crate::helpers::mir_utils::callee_param_index_for_local(
                    vm_state.tcx, callee, n)?;
                checkpoint.args.get(idx)?
            }
            _ => return None,
        };
        let place: &Place<'tcx> = match op {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let local = place.local;
        let local_val = vm_state.locals.get(&local)?;
        let is_iter = match local_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => {
                    let name = vm_state.tcx.def_path_str(adt_def.did());
                    name.ends_with("::Iter") || name == "Iter"
                        || name.ends_with("::IterMut") || name == "IterMut"
                }
                _ => false,
            },
            _ => false,
        };
        if !is_iter { return None; }
        // Direct lookup first, then scan by alloc_id for temp copies.
        if let (Some(ptr), Some(end)) =
            (vm_state.field_value(local, &[0]), vm_state.field_value(local, &[1]))
        {
            if let (Some(pp), Some(ep)) = (&ptr.provenance, &end.provenance) {
                if pp.alloc_id == ep.alloc_id {
                    let diff = Int::sub(vm_state.ctx, &[&ep.offset, &pp.offset]);
                    let sz = Int::from_u64(vm_state.ctx, vm_state.iter_elem_size(ptr));
                    return Some(diff.div(&sz));
                }
            }
        }
        // Fallback: scan all locals for one with same struct alloc.
        let target_alloc = local_val.provenance_alloc_id()?;
        for (&scan_local, scan_val) in vm_state.locals.iter() {
            if scan_val.provenance_alloc_id() != Some(target_alloc) { continue; }
            if let (Some(ptr), Some(end)) =
                (vm_state.field_value(scan_local, &[0]), vm_state.field_value(scan_local, &[1]))
            {
                if let (Some(pp), Some(ep)) = (&ptr.provenance, &end.provenance) {
                    if pp.alloc_id == ep.alloc_id {
                        let diff = Int::sub(vm_state.ctx, &[&ep.offset, &pp.offset]);
                        let sz = Int::from_u64(vm_state.ctx, vm_state.iter_elem_size(ptr));
                        return Some(diff.div(&sz));
                    }
                }
            }
        }
        None
    }

    /// Resolve a contract `Place` expression against the VM state and checkpoint.
    fn eval_contract_place<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: Option<&Checkpoint<'tcx>>,
        cp: &crate::verify::contract::ContractPlace<'tcx>) -> Option<Int<'ctx>>
    {
        // Collect numeric field projections.  Any non-field projection (e.g. a
        // `Downcast` or `IterElements`) cannot be resolved to a scalar, so the
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
                checkpoint.and_then(|ck| ck.args.get(n)).and_then(|op| match op {
                    Operand::Copy(p) | Operand::Move(p) => Some(p.local),
                    _ => None,
                })
            }
            PlaceBase::Local(n) => {
                if field_path.is_empty() {
                    if let Some(ck) = checkpoint {
                        if let Some(callee) = ck.callee {
                            if let Some(idx) =
                                crate::helpers::mir_utils::callee_param_index_for_local(
                                    vm_state.tcx, callee, n)
                            {
                                if let Some(op) = ck.args.get(idx) {
                                    if let Some(v) = self.eval_contract_operand(vm_state, op) {
                                        return Some(v);
                                    }
                                }
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
            vm_state.field_value(local, &field_path).map(|v| v.term.clone())
        }
    }

    /// Evaluate a checkpoint operand to a Z3 term.
    fn eval_contract_operand<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>,
        op: &Operand<'tcx>) -> Option<Int<'ctx>>
    {
        match op {
            Operand::Constant(c) => {
                let const_text = format!("{:?}", c.const_);
                let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
                if let Ok(val) = c.const_.eval(vm_state.tcx, typing_env, rustc_span::DUMMY_SP) {
                    if let Some(scalar) = val.try_to_scalar_int() {
                        let v = scalar.to_bits(scalar.size()) as u64;
                        if v == 0 && (const_text.contains("AlignOf") || const_text.contains("SizeOf") || const_text.contains("min_align_of") || const_text.contains("min_size_of")) {
                            // Generic AlignOf/SizeOf may evaluate to 0 but
                            // are always >= 1 for non-ZST types. Fall through
                            // to the debug text path below.
                        } else {
                            return Some(Int::from_u64(vm_state.ctx, v));
                        }
                    }
                }
                super::vm::state::const_int_from_debug(&const_text)
                    .map(|v| Int::from_u64(vm_state.ctx, v))
            }
            Operand::Copy(p) | Operand::Move(p)
                if p.projection.is_empty()
            => {
                vm_state.local_value(p.local).map(|v| v.term.clone())
            }
            _ => None,
        }
    }

    /// Try to resolve a generic type param to its concrete type at the callsite.
    /// Uses the FnDef's type arguments from the call terminator to substitute
    /// generic parameters.
    /// Recursively resolve generic type parameters inside a type.
    /// E.g. `Node<Param(T)>` → `Node<ConcreteType>` by resolving T at the callsite.
    fn resolve_ty_params<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        ty: Ty<'tcx>,
    ) -> Ty<'tcx> {
        match ty.kind() {
            TyKind::Param(_) => self.instantiate_callsite_ty(vm_state, checkpoint, ty),
            TyKind::Adt(adt_def, substs) => {
                let mut changed = false;
                let resolved_substs: Vec<_> = substs.iter().map(|arg| {
                    match arg.kind() {
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
                    }
                }).collect();
                if changed {
                    Ty::new_adt(vm_state.tcx, *adt_def, vm_state.tcx.mk_args(&resolved_substs))
                } else {
                    ty
                }
            }
            _ => ty,
        }
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

    fn instantiate_callsite_const<'ctx, 'tcx>(
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
                .or_else(|| crate::verify::vm::state::const_int_from_debug(
                    &format!("{actual_const:?}")
                ).map(|v| v as u128)),
            _ => None,
        }
    }

    /// Check if a type is a concrete (non-generic) ZST.
    fn is_concrete_zst<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_) => false,
            _ => vm_state.size_of_ty(ty) == 0,
        }
    }

    /// Whether a type's layout is not statically known (generic/alias/error).
    fn is_generic_ty<'tcx>(&self, ty: Ty<'tcx>) -> bool {
        matches!(ty.kind(), TyKind::Param(_) | TyKind::Alias(..) | TyKind::Error(_))
    }

    // ── check_size ─────────────────────────────────────────────

    /// `Size(T, c)` / `Size(T, sized)` / `Size(T, unsized)`.
    ///
    /// - `Size(T, c)`: `sizeof(T) == c` (e.g. `Size(T, 0)` for ZST).
    /// - `Size(T, sized)`: `T: Sized` and non-ZST.
    /// - `Size(T, unsized)`: `!Sized`.
    fn check_size<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let ty = match property.args().iter().find_map(|a| match a {
            PropertyArg::Ty(t) => Some(*t),
            _ => None,
        }) {
            Some(t) => t,
            None => return CheckResult::Unknown,
        };

        match property.args().last() {
            Some(PropertyArg::Ident(id)) if id == "sized" => {
                // For a generic type parameter (`T: Sized`) the concrete size is
                // unknown, but the `non-ZST` constraint is a caller obligation
                // (mirroring the `inject_layout_constraints` convention that a
                // generic `SizeOf(T)` term is `>= 1`).  Functions that panic on
                // ZST — `offset_from`, `size_of_val`, ... — are sound for every
                // `T`, so treating the constraint as satisfied is safe.
                if self.is_generic_ty(ty) {
                    return CheckResult::Proved;
                }
                if vm_state.size_of_ty(ty) == 0 {
                    CheckResult::Failed
                } else {
                    CheckResult::Proved
                }
            }
            Some(PropertyArg::Ident(id)) if id == "unsized" => {
                match ty.kind() {
                    TyKind::Slice(_) | TyKind::Str | TyKind::Dynamic(..) => CheckResult::Proved,
                    _ => CheckResult::Unknown,
                }
            }
            Some(PropertyArg::Expr(ContractExpr::Const(c))) => {
                if self.is_generic_ty(ty) {
                    return CheckResult::Unknown;
                }
                if vm_state.size_of_ty(ty) as u128 == *c {
                    CheckResult::Proved
                } else {
                    CheckResult::Failed
                }
            }
            _ => CheckResult::Unknown,
        }
    }
}

/// Check if the source-level function signature has a named lifetime in return type.
fn signature_return_has_lifetime(tcx: rustc_middle::ty::TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> Option<(String, String)> {
    let local = def_id.as_local()?;
    let hir_id = tcx.local_def_id_to_hir_id(local);
    let span = tcx.hir_span(hir_id);
    let snippet = tcx.sess.source_map().span_to_snippet(span).ok()?;
    let start = snippet.find("fn ")?;
    let rest = &snippet[start..];
    let end = rest.find('{').unwrap_or(rest.len());
    let sig = &rest[..end];
    // Extract return type after "->"
    let ret = sig.split("->").nth(1)?;
    let ret = ret.split("where").next()?.trim();
    Some((sig.to_string(), ret.to_string()))
}
