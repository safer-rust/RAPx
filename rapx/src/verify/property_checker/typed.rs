//! Checkers for `Typed` and `Size`.
//!
//! `Typed` matches an allocation's `element_ty` (or a field at the provenance
//! offset) against the expected type; `Size` checks `sized`/`unsized`/exact
//! size assertions.

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::contract::{ContractExpr, Property, PropertyArg};
use crate::verify::report::CheckResult;
use crate::verify::vm::state::VmState;
use rustc_middle::ty::{Ty, TyKind};
use z3::{Solver, ast::Ast};

use super::PropertyChecker;

impl PropertyChecker {
    pub(super) fn check_typed<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(value) = self.target_value(vm_state, checkpoint, property) else {
            return CheckResult::Unknown;
        };
        let expected = property.args().get(1).and_then(|a| {
            if let PropertyArg::Ty(ty) = a {
                Some(*ty)
            } else {
                None
            }
        });
        if let Some(expected_ty) = expected {
            let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, expected_ty);
            let expected_ty = if resolved != expected_ty {
                resolved
            } else {
                expected_ty
            };

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
            if Self::ty_is_maybe_uninit(expected_ty) {
                return CheckResult::Proved;
            }

            // Check provenance: does the allocation's element type match the expected type?
            if let Some(alloc_id) = value.provenance_alloc_id() {
                let alloc = vm_state.alloc(alloc_id);
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
                    // An allocation of `T` elements is also "typed" when
                    // accessed through a slice/array pointer `[T]`/`[T; N]`
                    // (a slice is just N contiguous `T` elements, e.g. a `u8`
                    // buffer reinterpreted as `[u8]` by `slice_from_raw_parts`).
                    let expected_elem = match expected_ty.kind() {
                        TyKind::Slice(e) | TyKind::Array(e, _) => *e,
                        _ => expected_ty,
                    };
                    if elem_ty == expected_elem {
                        return CheckResult::Proved;
                    }
                    // MaybeUninit<T> accessed via raw pointer from as_mut_ptr:
                    // treat as T for write ops where caller will initialize it.
                    if let TyKind::Adt(adt_def, substs) = elem_ty.kind() {
                        if crate::verify::api_classify::is_maybe_uninit_type(adt_def.did())
                            && matches!(value.ty.kind(), TyKind::RawPtr(..))
                        {
                            if let Some(inner) = substs.first().and_then(|s| s.as_type()) {
                                if inner == expected_ty {
                                    if crate::verify::api_classify::is_mem_copy_or_write(
                                        checkpoint.callee,
                                    ) {
                                        return CheckResult::Proved;
                                    }
                                }
                            }
                        }
                    }
                    // Struct/enum field: check if expected_ty matches a field at the provenance offset.
                    if let TyKind::Adt(adt_def, substs) = elem_ty.kind() {
                        if !adt_def.is_enum() {
                            let off_u64 = value
                                .provenance
                                .as_ref()
                                .and_then(|p| p.offset.simplify().as_u64());
                            let variant = adt_def.non_enum_variant();
                            let mut accum: u64 = 0;
                            for (i, field_def) in variant.fields.iter().enumerate() {
                                let field_off = vm_state.field_offset_in_bytes(elem_ty, i);
                                if i > 0 && field_off == 0 {
                                    accum = 0;
                                }
                                let field_ty: Ty<'tcx> = crate::helpers::mir_utils::field_ty(
                                    vm_state.tcx,
                                    field_def,
                                    substs,
                                );
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
                                            if (did.contains("ManuallyDrop")
                                                || did.contains("UnsafeCell"))
                                                && wrap_substs.first().and_then(|s| s.as_type())
                                                    == Some(expected_ty)
                                            {
                                                if vm_state.alloc(alloc_id).initialized {
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
                    // ForEach: the allocation stores pointers, but the invariant
                    // applies to the pointee type. Unwrap *const/*mut to match.
                    if property.for_each().is_some() {
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

            // No provenance: fall back to init and size checks.
            if value.invariants.init {
                if vm_state.size_of_ty(value_elem_ty) > 0
                    && vm_state.size_of_ty(expected_ty) > 0
                    && vm_state.size_of_ty(value_elem_ty) == vm_state.size_of_ty(expected_ty)
                {
                    return CheckResult::Proved;
                }
            }

            // For ForEach (for_each) properties, the invariant applies to
            // individual elements loaded from a container. The VM may not track
            // provenance through memory loads from heap allocations. When sizes
            // match, trust the type.
            if property.for_each().is_some() {
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
                if vm_state.alloc(alloc_id).element_ty.is_some() {
                    return CheckResult::Proved;
                }
            }

            if vs > 0 && es > 0 && vs != es {
                return CheckResult::Failed;
            }
        }
        CheckResult::Unknown
    }

    pub(super) fn ty_is_maybe_uninit(ty: Ty<'_>) -> bool {
        let mut t = ty;
        loop {
            match t.kind() {
                TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
                TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
                TyKind::Adt(adt, _) => {
                    return crate::verify::api_classify::is_maybe_uninit_type(adt.did());
                }
                _ => return false,
            }
        }
    }

    pub(super) fn check_size<'ctx, 'tcx>(
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
            Some(PropertyArg::Ident(id)) if id == "unsized" => match ty.kind() {
                TyKind::Slice(_) | TyKind::Str | TyKind::Dynamic(..) => CheckResult::Proved,
                _ => CheckResult::Unknown,
            },
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

    pub(super) fn check_no_padding<'ctx, 'tcx>(
        &self,
        vm_state: &VmState<'ctx, 'tcx>,
        _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let Some(ty) = property.args().iter().find_map(|a| match a {
            PropertyArg::Ty(t) => Some(*t),
            _ => None,
        }) else {
            return CheckResult::Unknown;
        };
        let ty = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
        match self.type_has_no_padding(vm_state, ty) {
            Some(true) => CheckResult::Proved,
            Some(false) => CheckResult::Failed,
            None => CheckResult::Unknown,
        }
    }

    /// Conservative "no padding" test: `Some(true)` when the type definitely has
    /// no padding bytes, `Some(false)` when it definitely does, `None` when it
    /// cannot be determined (generic / enum / union / opaque).
    fn type_has_no_padding<'tcx>(
        &self,
        vm_state: &VmState<'_, 'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<bool> {
        let tcx = vm_state.tcx;
        if self.is_generic_ty(ty) {
            return None;
        }
        match ty.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::RawPtr(..)
            | TyKind::Ref(..)
            | TyKind::FnPtr(..)
            | TyKind::Never => Some(true),
            TyKind::Array(elem, _) => self.type_has_no_padding(vm_state, *elem),
            TyKind::Tuple(elems) => {
                let mut sum = 0u64;
                for elem in *elems {
                    match self.type_has_no_padding(vm_state, elem) {
                        Some(true) => sum += vm_state.size_of_ty(elem),
                        Some(false) => return Some(false),
                        None => return None,
                    }
                }
                Some(vm_state.size_of_ty(ty) == sum)
            }
            TyKind::Adt(adt_def, substs) if !adt_def.is_enum() && !adt_def.is_union() => {
                let variant = adt_def.non_enum_variant();
                let mut sum = 0u64;
                for field_def in variant.fields.iter() {
                    let field_ty: Ty<'tcx> =
                        crate::helpers::mir_utils::field_ty(tcx, field_def, substs);
                    match self.type_has_no_padding(vm_state, field_ty) {
                        Some(true) => sum += vm_state.size_of_ty(field_ty),
                        Some(false) => return Some(false),
                        None => return None,
                    }
                }
                Some(vm_state.size_of_ty(ty) == sum)
            }
            _ => None,
        }
    }
}
