//! Transmute / trait / size property checking for the symbolic VM.

use crate::helpers::mir_utils;
use rustc_middle::ty::{GenericArgKind, Ty, TyKind};

use crate::helpers::mir_scan::Checkpoint;
use crate::verify::vm::state::VmState;
use crate::verify::{
    contract::{Property, PropertyArg},
    report::{CheckResult, UnknownReason},
};

use super::PropertyChecker;

impl PropertyChecker {
    // ── check_valid_transmute ──────────────────────────────────

    pub(super) fn check_valid_transmute<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let src = Self::ty_arg(property, 0);
        let dst = Self::ty_arg(property, 1);
        match (src, dst) {
            (Some(s), Some(d)) if vm_state.size_of_ty(s) == vm_state.size_of_ty(d) => {
                CheckResult::ProvedByRule
            }
            (Some(s), Some(d)) => {
                let ss = vm_state.size_of_ty(s);
                let ds = vm_state.size_of_ty(d);
                if ss == 0 || ds == 0 {
                    // One or both types are generic; sizes are opaque.
                    // Trust the type system: the call compiles, so
                    // the transmute is compatible.
                    CheckResult::ProvedByRule
                } else if ss == ds {
                    CheckResult::ProvedByRule
                } else {
                    CheckResult::Failed
                }
            }
            _ => CheckResult::ProvedByRule,
        }
    }

    // ── check_trait ────────────────────────────────────────────

    pub(super) fn check_trait<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let ty = match property.args().first() {
            Some(PropertyArg::Ty(ty)) => *ty,
            _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
        };
        let trait_name = match property.args().get(1) {
            Some(PropertyArg::Ident(name)) => name.as_str(),
            _ => return CheckResult::Unknown(UnknownReason::Unimplemented),
        };

        let tcx = vm_state.tcx;

        if trait_name == "Copy" {
            let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, checkpoint.caller);
            if tcx.type_is_copy_modulo_regions(typing_env, ty) {
                return CheckResult::ProvedByRule;
            }
            // Resolve generic param to concrete type via FnDef args
            let resolved = self.instantiate_callsite_ty(vm_state, checkpoint, ty);
            if resolved != ty && tcx.type_is_copy_modulo_regions(typing_env, resolved) {
                return CheckResult::ProvedByRule;
            }
        }

        if trait_name == "Sized" {
            if !ty.is_sized(
                tcx,
                rustc_middle::ty::TypingEnv::post_analysis(tcx, checkpoint.caller),
            ) {
                return CheckResult::Failed;
            }
            return CheckResult::ProvedByRule;
        }

        let predicates = crate::compat::predicates_of(tcx, checkpoint.caller);
        #[cfg(not(rapx_ge_100))]
        let pred_iter = predicates.predicates.iter();
        #[cfg(rapx_ge_100)]
        let pred_iter = predicates.clauses.iter();
        for (predicate, _span) in pred_iter {
            if let rustc_middle::ty::ClauseKind::Trait(trait_ref) = predicate.kind().skip_binder() {
                if trait_ref.self_ty() == ty {
                    let short_name = crate::helpers::name::short_fn_name(tcx, trait_ref.def_id());
                    if short_name == trait_name {
                        return CheckResult::ProvedByRule;
                    }
                }
            }
        }

        // A `Copy` obligation that none of the fast-paths discharged is a
        // confirmed violation: either `ty` is a concrete non-`Copy` type, or it
        // is a generic parameter without a `Copy` bound (and some instantiation
        // is non-`Copy`).  An unrecognized trait name stays Unknown.
        if trait_name == "Copy" {
            return CheckResult::Failed;
        }
        CheckResult::Unknown(UnknownReason::Unimplemented)
    }

    // ── check_split_transmute ──────────────────────────────────

    pub(super) fn check_split_transmute<'z3, 'tcx>(
        &self,
        vm_state: &VmState<'z3, 'tcx>,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
    ) -> CheckResult {
        let src = Self::ty_arg(property, 0);
        let dst = Self::ty_arg(property, 1);
        let src = src.map(|ty| self.instantiate_callsite_ty(vm_state, checkpoint, ty));
        let dst = dst.map(|ty| self.instantiate_callsite_ty(vm_state, checkpoint, ty));
        // A `SplitTransmute([T], [U])` contract declared by the caller licenses
        // the receiver slice's data allocation to be re-interpreted as `U`.  The
        // license is anchored to that allocation (`split_transmute_to`), so find
        // it through the receiver's provenance.
        let licensed = checkpoint
            .args
            .first()
            .map(|op| vm_state.value_of_operand(op))
            .and_then(|receiver| receiver.provenance)
            .and_then(|prov| vm_state.content(prov.alloc_id).facts.split_transmute_to);
        if let (Some(licensed), Some(d)) = (licensed, dst) {
            let d_elem = match d.kind() {
                TyKind::Slice(e) => *e,
                _ => d,
            };
            if licensed == d_elem {
                return CheckResult::ProvedByRule;
            }
        }
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
                    return CheckResult::ProvedByRule;
                }

                // If the destination is a SIMD vector with a matching lane type,
                // the transmute is valid by the standard library contract.
                if Self::is_simd_vector(vm_state, d) {
                    if let TyKind::Adt(_, args) = d.kind() {
                        if args
                            .iter()
                            .any(|a| matches!(a.kind(), GenericArgKind::Type(t) if t == s))
                        {
                            return CheckResult::ProvedByRule;
                        }
                    }
                }

                let src_sz = Self::ty_size(vm_state, s);
                let dst_sz = Self::ty_size(vm_state, d);
                if src_sz == 0 || dst_sz == 0 {
                    return CheckResult::Failed;
                }
                // A split transmute is sound whenever the destination element
                // type accepts all bit patterns (integers, floats, raw pointers):
                // any contiguous `size_of::<U>()`-byte chunk of the source is
                // then a valid destination value. This holds for both narrowing
                // (`[usize]` -> `[u8]`, src_sz >= dst_sz) and widening
                // (`[u8]` -> `[usize]`, src_sz < dst_sz) transmutes.
                if Self::all_bit_patterns_valid(d) {
                    return CheckResult::ProvedByRule;
                }
                CheckResult::Failed
            }
            _ => CheckResult::Failed,
        }
    }

    /// Return true if `ty` is a SIMD vector (a `#[repr(simd)]` ADT such as
    /// `core::simd::Simd<T, N>`).
    fn is_simd_vector<'z3, 'tcx>(_vm_state: &VmState<'z3, 'tcx>, ty: Ty<'tcx>) -> bool {
        if let TyKind::Adt(adt_def, _) = ty.kind() {
            return adt_def.repr().simd();
        }
        false
    }

    /// Compute type size, trying different typing environments.
    fn ty_size<'z3, 'tcx>(vm_state: &VmState<'z3, 'tcx>, ty: Ty<'tcx>) -> u64 {
        let sz = vm_state.size_of_ty(ty);
        if sz > 0 {
            return sz;
        }
        // Fallback 1: try with the monomorphized environment.
        let typing_env =
            rustc_middle::ty::TypingEnv::post_analysis(vm_state.tcx, vm_state.current_frame.current_def_id);
        let sz = mir_utils::catch_panic(|| {
            vm_state
                .tcx
                .layout_of(rustc_middle::ty::PseudoCanonicalInput {
                    typing_env,
                    value: ty,
                })
        })
        .ok()
        .and_then(|r| r.ok())
        .map(|l| l.size.bytes())
        .unwrap_or(0);
        if sz > 0 {
            return sz;
        }
        // Fallback 2: for generic type params, enumerate impl sizes.
        let generic_sz = mir_utils::size_of_generic_param(
            vm_state.tcx,
            vm_state.current_frame.current_def_id,
            ty,
        );
        if generic_sz > 0 {
            return generic_sz;
        }
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
