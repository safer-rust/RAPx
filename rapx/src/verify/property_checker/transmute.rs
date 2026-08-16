//! Transmute / trait / size property checking for the symbolic VM.

use rustc_middle::ty::{GenericArgKind, Ty, TyKind};
use z3::Solver;

use crate::verify::{
    contract::{Property, PropertyArg},
    report::CheckResult,
};
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::VmState;

use super::PropertyChecker;

impl PropertyChecker {
    // ── check_valid_transmute ──────────────────────────────────

    pub(super) fn check_valid_transmute<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        _checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let src = property.args().get(0).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        let dst = property.args().get(1).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        match (src, dst) {
            (Some(s), Some(d)) if vm_state.size_of_ty(s) == vm_state.size_of_ty(d) => CheckResult::Proved,
            (Some(s), Some(d)) => {
                let ss = vm_state.size_of_ty(s);
                let ds = vm_state.size_of_ty(d);
                if ss == 0 || ds == 0 {
                    // One or both types are generic; sizes are opaque.
                    // Trust the type system: the call compiles, so
                    // the transmute is compatible.
                    CheckResult::Proved
                } else if ss == ds {
                    CheckResult::Proved
                } else {
                    CheckResult::Failed
                }
            }
            _ => CheckResult::Proved,
        }
    }

    // ── check_trait ────────────────────────────────────────────

    pub(super) fn check_trait<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        let ty = match property.args().first() {
            Some(PropertyArg::Ty(ty)) => *ty,
            _ => return CheckResult::Unknown,
        };
        let trait_name = match property.args().get(1) {
            Some(PropertyArg::Ident(name)) => name.as_str(),
            _ => return CheckResult::Unknown,
        };

        let tcx = vm_state.tcx;

        if trait_name == "Copy" {
            let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, checkpoint.caller);
            if tcx.type_is_copy_modulo_regions(typing_env, ty) {
                return CheckResult::Proved;
            }
            // Resolve generic param to concrete type via FnDef args
            let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
            if resolved != ty && tcx.type_is_copy_modulo_regions(typing_env, resolved) {
                return CheckResult::Proved;
            }
        }

        if trait_name == "Sized" {
            if !ty.is_sized(tcx, rustc_middle::ty::TypingEnv::post_analysis(tcx, checkpoint.caller)) {
                return CheckResult::Failed;
            }
            return CheckResult::Proved;
        }

        let predicates = crate::compat::predicates_of(tcx, checkpoint.caller);
        #[cfg(not(rapx_rustc_ge_199))]
        let pred_iter = predicates.predicates.iter();
        #[cfg(rapx_rustc_ge_199)]
        let pred_iter = predicates.clauses.iter();
        for (predicate, _span) in pred_iter {
            if let rustc_middle::ty::ClauseKind::Trait(trait_ref) = predicate.kind().skip_binder() {
                if trait_ref.self_ty() == ty {
                    let def_path = tcx.def_path_str(trait_ref.def_id());
                    let short_name = def_path.rsplit("::").next().unwrap_or(&def_path);
                    if short_name == trait_name {
                        return CheckResult::Proved;
                    }
                }
            }
        }

        CheckResult::Unknown
    }

    // ── check_split_transmute ──────────────────────────────────

    pub(super) fn check_split_transmute<'ctx, 'tcx>(&self, vm_state: &VmState<'ctx, 'tcx>, _solver: &Solver<'ctx>,
        checkpoint: &Checkpoint<'tcx>, property: &Property<'tcx>) -> CheckResult
    {
        if vm_state.split_transmute_asserted {
            return CheckResult::Proved;
        }
        let src = property.args().get(0).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        let dst = property.args().get(1).and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
        let src = src.map(|ty| self.instantiate_callsite_ty(vm_state, checkpoint, ty));
        let dst = dst.map(|ty| self.instantiate_callsite_ty(vm_state, checkpoint, ty));
        match (src, dst) {
            (Some(mut s), Some(mut d)) => {
                // If the type is a slice (e.g. `[T]` from contract parsing), unwrap
                // to the element type.  `unwrap_array_expr` strips the array expr
                // in the parser, but some paths (e.g. `parse_type` fallback) may
                // keep the slice wrapper.
                if let TyKind::Slice(elem) = s.kind() {
                    s = *elem;
                }
                if let TyKind::Slice(elem) = d.kind() {
                    d = *elem;
                }

                // If the source and destination element types are the same,
                // transmute is trivially valid.
                if s == d {
                    return CheckResult::Proved;
                }

                // If the destination is a SIMD vector with a matching lane type,
                // the transmute is valid by the standard library contract.
                if Self::is_simd_vector(vm_state, d) {
                    if let TyKind::Adt(_, args) = d.kind() {
                        if args.iter().any(|a| matches!(a.kind(), GenericArgKind::Type(t) if t == s)) {
                            return CheckResult::Proved;
                        }
                    }
                }

                let src_sz = Self::ty_size(vm_state, s);
                let dst_sz = Self::ty_size(vm_state, d);
                if src_sz == 0 || dst_sz == 0 { return CheckResult::Failed; }
                // A split transmute is sound whenever the destination element
                // type accepts all bit patterns (integers, floats, raw pointers):
                // any contiguous `size_of::<U>()`-byte chunk of the source is
                // then a valid destination value. This holds for both narrowing
                // (`[usize]` -> `[u8]`, src_sz >= dst_sz) and widening
                // (`[u8]` -> `[usize]`, src_sz < dst_sz) transmutes.
                if Self::all_bit_patterns_valid(d) {
                    return CheckResult::Proved;
                }
                CheckResult::Failed
            }
            _ => CheckResult::Failed,
        }
    }

    /// Return true if `ty` is `core::simd::Simd<T, N>`.
    fn is_simd_vector<'ctx, 'tcx>(vm_state: &VmState<'ctx, 'tcx>, ty: Ty<'tcx>) -> bool {
        if let TyKind::Adt(adt_def, _) = ty.kind() {
            let name = vm_state.tcx.item_name(adt_def.did());
            if name.as_str() == "Simd" {
                let path = vm_state.tcx.def_path_str(adt_def.did());
                return path.contains("::simd::");
            }
        }
        false
    }

    /// Compute type size, trying different typing environments.
    fn ty_size<'ctx, 'tcx>(vm_state: &VmState<'ctx, 'tcx>, ty: Ty<'tcx>) -> u64 {
        let sz = vm_state.size_of_ty(ty);
        if sz > 0 { return sz; }
        // Fallback 1: try with the monomorphized environment.
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(
            vm_state.tcx, vm_state.caller_def_id);
        let sz = crate::helpers::mir_utils::catch_panic(|| {
            vm_state.tcx.layout_of(
                rustc_middle::ty::PseudoCanonicalInput { typing_env, value: ty }
            )
        }).ok().and_then(|r| r.ok()).map(|l| l.size.bytes()).unwrap_or(0);
        if sz > 0 { return sz; }
        // Fallback 2: for generic type params, enumerate impl sizes.
        let generic_sz = vm_state.size_of_generic_param(ty);
        if generic_sz > 0 { return generic_sz; }
        0
    }

    /// Returns true for integer and float types that accept all possible bit patterns
    /// as valid values.  Types like bool, char, and enums have restricted validity.
    /// Tuples and arrays are all-bit-patterns-valid iff every component is, so a
    /// widening `SplitTransmute` such as `[u8] -> [(usize, usize)]` (used by
    /// `memrchr`) is recognised.
    pub(super) fn all_bit_patterns_valid(ty: Ty<'_>) -> bool {
        match ty.kind() {
            rustc_middle::ty::TyKind::Uint(_) => true,
            rustc_middle::ty::TyKind::Int(_) => true,
            rustc_middle::ty::TyKind::Float(_) => true,
            rustc_middle::ty::TyKind::RawPtr(..) => true,
            rustc_middle::ty::TyKind::Tuple(elems) => {
                elems.iter().all(|e| Self::all_bit_patterns_valid(e))
            }
            rustc_middle::ty::TyKind::Array(elem, _) => Self::all_bit_patterns_valid(*elem),
            _ => false,
        }
    }
}
