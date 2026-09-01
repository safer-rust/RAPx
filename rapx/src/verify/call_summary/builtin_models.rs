//! Builtin call models: API behaviour modelling when MIR is unavailable.
//!
//! Each recognised standard-library API is described by a single table
//! row: a **matcher** (from [`crate::verify::api_classify`]) and an
//! **effect builder**.  [`lookup_effect`] scans the table linearly (first match
//! wins) and converts the matched row into the effect summary consumed by the
//! VM; [`is_modeled`] reports whether a call is in the table (used by the path
//! graph to keep modelled calls opaque instead of inlining their branchy CFG).
//!
//! Two layers:
//! 1. **Matchers** — [`crate::verify::api_classify`] `DefId` classifiers.
//! 2. **Effect functions** — produce the `Vec<CallEffect>` for a single API.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_middle::ty::{Ty, TyCtxt};

use super::from_raw_parts_elem_size;
use super::{CallEffect, CallEffectSummary};
use crate::helpers::mir_utils::{destination_stride, pointee_alignment, pointee_ty, type_layout};
use crate::verify::api_classify;

// ── Context for effect builders ────────────────────────────────────────

pub(crate) struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub func: &'a Operand<'tcx>,
    pub dest: Option<rustc_middle::mir::Local>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(Option<DefId>) -> bool,
    effects: fn(&EffCtx<'_, '_>) -> Vec<CallEffect>,
}

/// `DefId`-based matcher row (`fn(Option<DefId>) -> bool`).
macro_rules! ED {
    ($m:expr, $e:ident) => {
        Entry {
            matches: $m,
            effects: $e,
        }
    };
}

static REGISTRY: &[Entry] = &[
    // ── Intrinsics — no MIR body ────────────────────────────────────
    // Compiler intrinsics (`core::intrinsics::*`) have no MIR to inline, so the
    // hand-written effect is the *only* model. `mem::size_of`/`align_of` are
    // `#[inline]` wrappers around the intrinsic and are matched for the same
    // reason.
    ED!(api_classify::is_layout_constant, eff_layout_const),
    // ── MIR unavailable — non-#[inline] cross-crate ─────────────────
    // These std functions are not `#[inline]`, so precompiled std ships no MIR
    // for them (`tcx.is_mir_available` is false) and the effect is the only
    // model. (`Vec::push` itself is `#[inline]` but is grouped with
    // `reserve`/`reserve_exact` — which are not — for the shared
    // write-to-buffer model.)
    ED!(api_classify::is_vec_alloc_constructor, eff_new_allocation),
    // `into_vec` / `box_assume_init_into_vec_unsafe`: needed on older
    // toolchains where `vec![…]` literals lower to `into_vec` (not `from_elem`).
    ED!(api_classify::is_vec_from_box, eff_vec_from_box),
    ED!(
        api_classify::is_vec_with_capacity,
        eff_new_allocation_from_cap
    ),
    ED!(api_classify::is_into_boxed_slice, eff_box_from_vec),
    ED!(api_classify::is_vec_push_or_reserve, eff_write_mem),
    // ── MIR available — precise symbolic summary ────────────────────
    // The following have MIR available (`#[inline]` or local), but a symbolic
    // summary is more precise than inlining their branchy / bit-twiddling
    // bodies.

    // Non-zero-preserving integer ops are modelled as a precise expression over
    // their operands (ite / arithmetic) so a downstream `!= 0` obligation
    // discharges *conditionally* — only when the operands are actually
    // non-zero — rather than unconditionally.
    ED!(api_classify::is_max, eff_return_max),
    ED!(api_classify::is_clamp, eff_return_clamp),
    ED!(api_classify::is_abs, eff_return_abs),
    ED!(api_classify::is_neg, eff_return_neg),
    ED!(api_classify::is_sat_unchecked_add, eff_return_add),
    ED!(api_classify::is_sat_unchecked_mul, eff_return_mul),
    ED!(api_classify::is_checked_add, eff_return_option_some_add),
    ED!(api_classify::is_checked_mul, eff_return_option_some_mul),
    ED!(api_classify::is_overflowing_abs_neg, eff_overflowing_nz),
    ED!(api_classify::is_unwrap, eff_alias_arg0),
    // Pointer arithmetic: direction and granularity are orthogonal; each entry
    // picks a fixed-stride `ReturnPointerAdd`/`ReturnPointerSub`.
    ED!(api_classify::is_element_ptr_add, eff_ptr_add),
    ED!(api_classify::is_element_ptr_sub, eff_ptr_sub),
    ED!(api_classify::is_byte_ptr_add, eff_ptr_add_byte),
    ED!(api_classify::is_byte_ptr_sub, eff_ptr_sub_byte),
    // Pointer extraction / cast: `as_ptr`/`into_raw` return a non-null, aligned,
    // initialized alias of their argument (`ReturnPointerFromArg` derives those
    // from the source). Raw-pointer `cast` is excluded (`is_as_ptr_valid`)
    // because it only reinterprets the address and is left to MIR inlining.
    ED!(api_classify::is_as_ptr_valid, eff_alias_ptr),
    // Slice / collection queries.
    ED!(api_classify::is_len, eff_len),
    ED!(api_classify::is_capacity, eff_len),
    ED!(api_classify::is_min_like, eff_cmp_min),
    ED!(api_classify::is_bit_preserving_nz, eff_return_nonzero_iff),
    ED!(
        api_classify::is_checked_nonzero_iff,
        eff_return_option_some_nonzero_iff
    ),
    ED!(
        api_classify::is_checked_next_pow2,
        eff_return_option_some_nonzero
    ),
    // SliceIndex::get_unchecked / get_unchecked_mut.
    ED!(api_classify::is_slice_get_unchecked, eff_alias_ptr),
    // `SliceIndex::get_unchecked(self, slice)` returns `slice + self` (the
    // receiver is the *index*, the slice pointer is argument 1), so model it as
    // element-strided pointer arithmetic off argument 1 rather than an alias of
    // argument 0.
    ED!(
        api_classify::is_sliceindex_get_unchecked,
        eff_sliceindex_get_unchecked
    ),
    // Ownership reconstruction (`Box::from_raw` / `CString::from_raw` / …).
    ED!(
        api_classify::is_ownership_reconstruction,
        eff_ownership_recon
    ),
    // Slice helpers.
    ED!(api_classify::is_split_at, eff_split_at),
    ED!(api_classify::is_from_raw_parts, eff_from_raw_parts),
    ED!(api_classify::is_align_offset, eff_align_offset),
    ED!(api_classify::is_cstr_from_ptr, eff_alias_arg0),
    // Layout accessor (`align_of`): returns a power of two.
    ED!(api_classify::is_layout_align, eff_layout_align),
    // Local re-implementations (std-challenge suites' `_ext` fns): matched by
    // name-scanning `fn_defs()`. Their MIR is local, but the re-implemented
    // algorithm is modelled with the same effect as the std original.
    // (`iter`/`into_iter`/`iter_mut` are *not* here — they are derived from
    // the return type by `try_iter_constructor_effect`.)
    ED!(api_classify::is_align_to_local, eff_align_to),
    ED!(api_classify::is_iter_position, eff_option_scan_index),
    ED!(api_classify::is_strlen, eff_scan_length),
    // ── MIR available — deliberately opaque ─────────────────────────
    // `eff_none` stubs: no symbolic effect, but staying registered keeps
    // `is_modeled` true so the path graph does not inline their branchy bodies
    // (`NonNull::new`'s `is_null`, `MaybeUninit::uninit`/`assume_init`).
    // `MaybeUninit::write` marks the slot initialized (`WriteMemory`).
    ED!(api_classify::is_nonnull_checked_new, eff_none),
    ED!(api_classify::is_maybe_uninit_uninit, eff_none),
    ED!(api_classify::is_maybe_uninit_assume_init, eff_none),
    ED!(api_classify::is_maybe_uninit_write, eff_write_mem),
];

/// True when `callee` matches a hand-modelled API in the registry. The path
/// graph uses this to keep such calls opaque (it must not inline their branchy
/// CFG when the VM models their semantics more precisely).
pub(crate) fn is_modeled(callee: Option<DefId>) -> bool {
    REGISTRY.iter().any(|e| (e.matches)(callee))
}

pub(crate) fn lookup_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    name: &str,
    func: &Operand<'tcx>,
    destination: rustc_middle::mir::Local,
) -> Option<CallEffectSummary> {
    let dest = Some(destination);
    for e in REGISTRY {
        if (e.matches)(callee) {
            let ctx = EffCtx {
                tcx,
                caller,
                func,
                dest,
            };
            return Some(CallEffectSummary {
                name: name.to_string(),
                effects: (e.effects)(&ctx),
                unsupported: false,
            });
        }
    }
    None
}

// ── Effect builders — one small function per API semantic ──────────────

fn eff_none(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    Vec::new()
}

fn eff_alias_ptr(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let mut eff = vec![CallEffect::ReturnPointerFromArg { arg: 0 }];
    if pointee_alignment(ctx.tcx, ctx.caller, ctx.dest).is_some() {
        eff.push(CallEffect::ReturnAligned);
    }
    eff
}

/// `SliceIndex::get_unchecked(self, slice)` / `get_unchecked_mut`: returns an
/// element pointer at `slice + self` (receiver is the index, slice pointer is
/// argument 1). Element-strided add off argument 1, inheriting non-nullness
/// from the slice.
fn eff_sliceindex_get_unchecked(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    vec![CallEffect::ReturnPointerAdd {
        base_arg: 1,
        offset_arg: 0,
        stride: destination_stride(ctx.tcx, ctx.caller, ctx.dest),
    }]
}

fn eff_alias_arg0(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAliasArg { arg: 0 }]
}

fn eff_ptr_add(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Add, PtrGranularity::Element)
}

fn eff_ptr_sub(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Sub, PtrGranularity::Element)
}

fn eff_ptr_add_byte(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Add, PtrGranularity::Byte)
}

fn eff_ptr_sub_byte(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    eff_ptr_arith(ctx, PtrDirection::Sub, PtrGranularity::Byte)
}

enum PtrDirection {
    Add,
    Sub,
}

enum PtrGranularity {
    Element,
    Byte,
}

/// Shared model for `ReturnPointerAdd`/`ReturnPointerSub`.
///
/// `wrapping_add`/`wrapping_sub` are shared between integers and raw pointers.
/// When the destination is not a pointer type the call is an integer
/// `wrapping_add`, whose result may wrap to zero, so it is left unconstrained
/// rather than modelled as pointer arithmetic.
fn eff_ptr_arith(
    ctx: &EffCtx<'_, '_>,
    dir: PtrDirection,
    granularity: PtrGranularity,
) -> Vec<CallEffect> {
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    let stride = match granularity {
        PtrGranularity::Byte => Some(1),
        PtrGranularity::Element => destination_stride(ctx.tcx, ctx.caller, ctx.dest),
    };
    let effect = match dir {
        PtrDirection::Sub => CallEffect::ReturnPointerSub {
            base_arg: 0,
            offset_arg: 1,
            stride,
        },
        PtrDirection::Add => CallEffect::ReturnPointerAdd {
            base_arg: 0,
            offset_arg: 1,
            stride,
        },
    };
    vec![effect]
}

fn eff_write_mem(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::WriteMemory { pointer_arg: 0 }]
}

fn eff_len(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnLengthOfArg { arg: 0 }]
}

fn eff_cmp_min(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMin {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_nonzero_iff(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNonZeroIff { arg: 0 }]
}

fn eff_return_option_some_nonzero_iff(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeNonZeroIff { arg: 0 }]
}

fn eff_return_option_some_nonzero(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeNonZero]
}

fn eff_return_max(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMax {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_clamp(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnClamp {
        value_arg: 0,
        min_arg: 1,
        max_arg: 2,
    }]
}

fn eff_return_abs(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAbs { arg: 0 }]
}

fn eff_return_neg(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNeg { arg: 0 }]
}

fn eff_return_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAdd {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMul {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_option_some_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeAdd {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_return_option_some_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeMul {
        lhs_arg: 0,
        rhs_arg: 1,
    }]
}

fn eff_overflowing_nz(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnTupleFieldNonZero { field: 0 }]
}

fn eff_ownership_recon(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnNonZero,
        CallEffect::OwnsInitMemory { arg: 0 },
    ]
}

fn eff_align_to(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignTo { receiver_arg: 0 }]
}

fn eff_option_scan_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeScanIndex { self_arg: 0 }]
}

fn eff_scan_length(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnScanLength]
}

fn eff_align_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOffset {
        ptr_arg: 0,
        align_arg: 1,
    }]
}

fn eff_split_at(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnTupleFieldLength {
            field: 0,
            from_arg: 1,
        },
    ]
}

fn eff_from_raw_parts(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    let mut eff = vec![
        // ReturnAliasArg keeps the legacy PointsTo chain intact so the
        // legacy SMT Align checker can trace through as_ptr() → reference
        // provenance.  Without it, place_is_reference_aligned cannot
        // prove alignment for the pointer argument.
        CallEffect::ReturnAliasArg { arg: 0 },
        // ReturnFreshAllocation provides the allocation-tracking hint
        // used by the VM backend's memory model.
        CallEffect::ReturnFreshAllocation {
            pointer_arg: 0,
            size_arg: 1,
            elem_size: elem,
        },
        CallEffect::ReturnNonZero,
    ];
    if pointee_alignment(ctx.tcx, ctx.caller, ctx.dest).is_some() {
        eff.push(CallEffect::ReturnAligned);
    }
    eff
}

fn eff_new_allocation(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![CallEffect::ReturnNewAllocation {
        size_arg: 1,
        elem_size: elem,
    }]
}

fn eff_new_allocation_from_cap(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = from_raw_parts_elem_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![CallEffect::ReturnNewAllocationFromCap {
        cap_arg: 0,
        elem_size: elem,
    }]
}

fn eff_vec_from_box(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNewAllocationFromBox]
}

fn eff_layout_align(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPowerOfTwo]
}

fn eff_layout_const(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    layout_constant_effect(ctx.tcx, ctx.caller, ctx.func)
        .into_iter()
        .collect()
}

// ── Layout helpers (used by effect builders) ─────────────────────────

fn dest_is_pointer(tcx: TyCtxt<'_>, caller: DefId, dest: Option<rustc_middle::mir::Local>) -> bool {
    let Some(d) = dest else { return false };
    pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty).is_some()
}

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    crate::helpers::mir_utils::fn_def_first_type_arg(func)
}

fn layout_constant_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<CallEffect> {
    let ty = layout_call_ty(func)?;
    let (align, size) = type_layout(tcx, caller, ty)?;
    let Some(callee) = crate::helpers::mir_utils::dep_callee_def_id(func) else {
        return None;
    };
    if crate::def_id::contains(
        &[
            crate::def_id::mem_align_of(),
            crate::def_id::intrinsics_align_of(),
        ],
        callee,
    ) {
        Some(CallEffect::ReturnConst { value: align })
    } else if crate::def_id::contains(
        &[
            crate::def_id::mem_size_of(),
            crate::def_id::intrinsics_size_of(),
        ],
        callee,
    ) {
        Some(CallEffect::ReturnConst { value: size })
    } else {
        None
    }
}

fn eff_box_from_vec(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoxFromVec { arg: 0 }]
}
