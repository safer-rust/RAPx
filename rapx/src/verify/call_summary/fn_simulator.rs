//! Function simulation: API behaviour modelling when MIR is unavailable.
//!
//! Each recognised standard-library API is described by a single table
//! row: a **name matcher**, **argument dependency**, and **effect
//! builder**.  The public entry points [`lookup_dependency`] and
//! [`lookup_effect`] scan the table linearly (first match wins) and
//! convert the matched row into the concrete summaries consumed by the
//! backward/forward visitors.
//!
//! Two layers, both visible in one place:
//! 1. **Matcher functions** — cheap name-pattern checks (hot-path `is_*`
//!    helpers for classification queries).
//! 2. **Effect functions** — produce the `Vec<CallEffect>` for a single
//!    API.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::Operand;
use rustc_middle::ty::{GenericArgKind, Ty, TyCtxt, TyKind};

use super::{CallDependencySummary, CallEffect, CallEffectSummary};
use crate::helpers::api_classify;
use crate::helpers::mir_utils::{
    type_layout, destination_stride, pointee_ty, pointee_alignment,
    slice_element_size, vec_element_size,
};

// ── Context for effect builders ────────────────────────────────────────

pub struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub name: &'a str,
    pub func: &'a Operand<'tcx>,
    pub dest: Option<rustc_middle::mir::Local>,
}

// ── Registry table ─────────────────────────────────────────────────────

struct Entry {
    matches: fn(&str) -> bool,
    dep_on: &'static [usize],
    dep_on_all: bool,
    writes: &'static [usize],
    effects: fn(&EffCtx<'_, '_>) -> Vec<CallEffect>,
}

macro_rules! no_args { () => { &[] } }
macro_rules! arg0    { () => { &[0usize] } }
macro_rules! arg01   { () => { &[0usize, 1] } }

macro_rules! E {
    ($m:expr, $d:expr, $all:expr, $w:expr, $e:ident) => {
        Entry { matches: $m, dep_on: $d, dep_on_all: $all, writes: $w, effects: $e }
    };
}

/// Placeholder for `dep_on` when `dep_on_all` is true: in that case
/// `lookup_dependency` ignores `dep_on` and collects `0..arg_count`, so the
/// field is only present to satisfy the `E!` macro shape.
const ALL: &[usize] = &[];

static REGISTRY: &[Entry] = &[
    // ── Drop / forget ──────────────────────────────────────────────
    E!(mem_forget,           arg0!(),  false,  no_args!(),  eff_forget),

    // ── Pass-through / no-effect calls ──────────────────────────────
    E!(api_classify::is_maybe_uninit_uninit,no_args!(), false, no_args!(), eff_none),
    E!(api_classify::is_maybe_uninit_assume_init,arg0!(), false, no_args!(), eff_none),
    // Non-zero-preserving integer operations are each modelled with a precise
    // expression over its operands (ite / arithmetic) so the solver can
    // discharge a downstream `!= 0` obligation *conditionally* — only when the
    // operands are actually non-zero — rather than asserting the result is
    // unconditionally non-zero.
    E!(int_max,               ALL,      true,   no_args!(),  eff_return_max),
    E!(int_clamp,             ALL,      true,   no_args!(),  eff_return_clamp),
    E!(int_abs,               ALL,      true,   no_args!(),  eff_return_abs),
    E!(int_neg,               ALL,      true,   no_args!(),  eff_return_neg),
    E!(int_add,               ALL,      true,   no_args!(),  eff_return_add),
    E!(int_mul,               ALL,      true,   no_args!(),  eff_return_mul),
    E!(int_checked_add,       ALL,      true,   no_args!(),  eff_return_option_some_add),
    E!(int_checked_mul,       ALL,      true,   no_args!(),  eff_return_option_some_mul),
    E!(overflowing_nz,        ALL,      true,   no_args!(),  eff_overflowing_nz),
    E!(saturating_sub,        ALL,      true,   no_args!(),  eff_return_sub),
    E!(api_classify::is_offset_from_unsigned, arg01!(), false, no_args!(), eff_offset_from_unsigned),
    E!(api_classify::is_option_unwrap, arg0!(),  false,  no_args!(),  eff_alias_arg0),

    // ── Pointer extraction / cast ───────────────────────────────────
    // `NonNull::new` returns `Option<NonNull<T>>`; its `ReturnNonZero` +
    // `ReturnPointerFromArg` summary is more precise than inlining the
    // `is_null` branch, which the solver cannot discharge for a symbolic
    // buffer pointer (breaks the allocator cases).
    E!(nonnull_new,           arg0!(),  false,  no_args!(),  eff_alias_ptr),
    E!(api_classify::is_as_ptr, arg0!(), false,  no_args!(),  eff_alias_ptr),
    E!(api_classify::is_as_ptr_range, arg0!(), false, no_args!(), eff_alias_arg0),
    E!(api_classify::is_as_mut_ptr_range, arg0!(), false, no_args!(), eff_alias_arg0),

    // ── Pointer arithmetic ──────────────────────────────────────────
    E!(|n| api_classify::is_pointer_add(n) && !api_classify::is_byte_ptr_arith(n), arg01!(), false, no_args!(), eff_ptr_add),
    E!(|n| api_classify::is_pointer_sub(n) && !api_classify::is_byte_ptr_arith(n), arg01!(), false, no_args!(), eff_ptr_sub),
    E!(|n| api_classify::is_pointer_add(n) && api_classify::is_byte_ptr_arith(n), arg01!(), false, no_args!(), eff_ptr_add),
    E!(|n| api_classify::is_pointer_sub(n) && api_classify::is_byte_ptr_arith(n), arg01!(), false, no_args!(), eff_ptr_sub),

    // ── Memory read / write ─────────────────────────────────────────
    E!(ptr_read,              arg0!(),  false,  no_args!(),  eff_read_mem),
    E!(api_classify::is_ptr_write, no_args!(), false,  arg0!(),  eff_write_mem),
    E!(api_classify::is_maybe_uninit_write, no_args!(), false, arg0!(), eff_write_mem),

    // ── Slice / collection queries ──────────────────────────────────
    E!(api_classify::is_len,  arg0!(),  false,  no_args!(),  eff_len),
    E!(api_classify::is_capacity, arg0!(), false, no_args!(), eff_len),
    E!(is_empty,              arg0!(),  false,  no_args!(),  eff_is_empty),
    E!(cmp_min,               ALL,      true,   no_args!(),  eff_cmp_min),
    E!(midpoint,              ALL,      true,   no_args!(),  eff_cmp_min),
    E!(bit_preserving_nz,     ALL,      true,   no_args!(),  eff_return_nonzero_iff),
    E!(checked_pow_nz,        ALL,      true,   no_args!(),  eff_return_option_some_nonzero_iff),
    E!(checked_abs_nz,        ALL,      true,   no_args!(),  eff_return_option_some_nonzero_iff),
    E!(checked_neg_nz,        ALL,      true,   no_args!(),  eff_return_option_some_nonzero_iff),
    E!(checked_next_pow2_nz,  ALL,      true,   no_args!(),  eff_return_option_some_nonzero),

    // ── SliceIndex::get_unchecked / get_unchecked_mut ───────────────
    E!(is_slice_get_unchecked, arg0!(), false,  no_args!(),  eff_alias_ptr),

    // ── Ownership reconstruction ────────────────────────────────────
    E!(api_classify::is_ownership_reconstruction, arg0!(), false, no_args!(), eff_ownership_recon),

    // ── Slice helpers ───────────────────────────────────────────────
    E!(slice_index,           arg01!(), false,  no_args!(),  eff_alias_arg0),
    E!(align_to_local,        arg0!(),  false,  no_args!(),  eff_align_to),
    E!(into_iter_local,       arg0!(),  false,  no_args!(),  eff_return_iter),
    E!(iter_position,         arg0!(),  false,  no_args!(),  eff_option_scan_index),
    E!(is_strlen,             arg0!(),  false,  no_args!(),  eff_scan_length),
    E!(split_at,              arg01!(), false,  no_args!(),  eff_split_at),
    E!(api_classify::is_from_raw_parts, arg01!(), false, no_args!(), eff_from_raw_parts),
    E!(api_classify::is_align_offset, arg01!(), false, no_args!(), eff_align_offset),

    // ── Vec / collection constructors ────────────────────────────────
    E!(api_classify::is_vec_alloc_constructor, arg01!(), false, no_args!(), eff_new_allocation),
    E!(api_classify::is_vec_from_box,          arg0!(),  false, no_args!(), eff_vec_from_box),
    E!(api_classify::is_vec_with_capacity,     arg0!(),  false, no_args!(), eff_new_allocation_from_cap),
    E!(api_classify::is_into_boxed_slice,      arg0!(),  false, no_args!(), eff_box_from_vec),

    // ── Allocator::allocate / allocate_zeroed / grow / shrink ────────
    E!(allocator_allocate,    arg01!(), false,  no_args!(),  eff_allocator_allocate),

    // ── Layout accessors ────────────────────────────────────────────
    E!(layout_align,          no_args!(),  false,  no_args!(),  eff_layout_align),

    // ── Layout constants ────────────────────────────────────────────
    E!(api_classify::is_layout_constant, no_args!(), false,  no_args!(),  eff_layout_const),

    // ── CStr / CString helpers ──────────────────────────────────────
    E!(api_classify::is_cstr_from_ptr, arg0!(), false,  no_args!(),  eff_alias_arg0),
    E!(api_classify::is_cstr_from_bytes_with_nul_unchecked, arg0!(), false, no_args!(), eff_alias_arg0),
    E!(api_classify::is_vec_push, no_args!(), false,  arg0!(),  eff_write_mem),
];

pub fn lookup_dependency(
    callee: Option<DefId>,
    name: &str,
    arg_count: usize,
) -> Option<CallDependencySummary> {
    for e in REGISTRY {
        if (e.matches)(name) {
            let args = if e.dep_on_all { (0..arg_count).collect() } else { e.dep_on.to_vec() };
            return Some(CallDependencySummary {
                callee,
                name: name.to_string(),
                return_depends_on_args: args,
                may_write_args: e.writes.to_vec(),
                unsupported: false,
            });
        }
    }
    None
}

pub fn lookup_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    name: &str,
    func: &Operand<'tcx>,
    destination: rustc_middle::mir::Local,
) -> Option<CallEffectSummary> {
    let dest = Some(destination);
    for e in REGISTRY {
        if (e.matches)(name) {
            let ctx = EffCtx { tcx, caller, name, func, dest };
            return Some(CallEffectSummary {
                callee,
                name: name.to_string(),
                destination: dest,
                effects: (e.effects)(&ctx),
                unsupported: false,
            });
        }
    }
    None
}

// ── Effect builders — one small function per API semantic ──────────────

fn eff_none(_: &EffCtx<'_, '_>) -> Vec<CallEffect> { Vec::new() }

fn eff_alias_ptr(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let mut eff = vec![
        CallEffect::ReturnPointerFromArg { arg: 0 },
        CallEffect::ReturnNonZero,
    ];
    if let Some((a, n)) = pointee_alignment(ctx.tcx, ctx.caller, ctx.dest) {
        eff.push(CallEffect::ReturnAligned { align: a, ty_name: n });
    }
    eff
}

fn eff_alias_arg0(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAliasArg { arg: 0 }]
}

fn eff_ptr_add(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    // `wrapping_add`/`wrapping_sub` are shared between integers and raw
    // pointers. When the destination is not a pointer type the call is an
    // integer `wrapping_add`, whose result may wrap to zero, so it is left
    // unconstrained rather than modelled as pointer arithmetic.
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    let stride = if api_classify::is_byte_ptr_arith(ctx.name) {
        Some(1)
    } else {
        destination_stride(ctx.tcx, ctx.caller, ctx.dest)
    };
    vec![CallEffect::ReturnPointerAdd { base_arg: 0, offset_arg: 1, stride }]
}

fn eff_ptr_sub(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    if !dest_is_pointer(ctx.tcx, ctx.caller, ctx.dest) {
        return Vec::new();
    }
    let stride = if api_classify::is_byte_ptr_arith(ctx.name) {
        Some(1)
    } else {
        destination_stride(ctx.tcx, ctx.caller, ctx.dest)
    };
    vec![CallEffect::ReturnPointerSub { base_arg: 0, offset_arg: 1, stride }]
}

fn eff_offset_from_unsigned(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOffsetFromUnsigned { self_arg: 0, origin_arg: 1 }]
}

fn eff_read_mem(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReadMemory { arg: 0 }]
}

fn eff_write_mem(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::WriteMemory { pointer_arg: 0 }]
}

fn eff_len(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnLengthOfArg { arg: 0 }]
}

fn eff_is_empty(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIsEmptyOfArg { arg: 0 }]
}

fn eff_cmp_min(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMin { lhs_arg: 0, rhs_arg: 1 }]
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
    vec![CallEffect::ReturnMax { lhs_arg: 0, rhs_arg: 1 }]
}

fn eff_return_clamp(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnClamp { value_arg: 0, min_arg: 1, max_arg: 2 }]
}

fn eff_return_abs(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAbs { arg: 0 }]
}

fn eff_return_neg(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnNeg { arg: 0 }]
}

fn eff_return_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAdd { lhs_arg: 0, rhs_arg: 1 }]
}

fn eff_return_sub(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnSub { lhs_arg: 0, rhs_arg: 1 }]
}

fn eff_return_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnMul { lhs_arg: 0, rhs_arg: 1 }]
}

fn eff_return_option_some_add(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeAdd { lhs_arg: 0, rhs_arg: 1 }]
}

fn eff_return_option_some_mul(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeMul { lhs_arg: 0, rhs_arg: 1 }]
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

fn eff_return_iter(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIter { receiver_arg: 0 }]
}

fn eff_option_scan_index(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnOptionSomeScanIndex { self_arg: 0 }]
}

fn eff_scan_length(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnScanLength { ptr_arg: 0 }]
}

fn eff_align_offset(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignOffset { ptr_arg: 0, align_arg: 1 }]
}

fn eff_split_at(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnTupleFieldLength { field: 0, from_arg: 1 },
    ]
}

fn eff_from_raw_parts(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = slice_element_size(ctx.tcx, ctx.caller, ctx.dest);
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
    if let Some((a, n)) = pointee_alignment(ctx.tcx, ctx.caller, ctx.dest) {
        eff.push(CallEffect::ReturnAligned { align: a, ty_name: n });
    }
    eff
}

fn eff_new_allocation(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = vec_element_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![
        CallEffect::ReturnNewAllocation {
            size_arg: 1,
            elem_size: elem,
        },
    ]
}

fn eff_new_allocation_from_cap(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let elem = vec_element_size(ctx.tcx, ctx.caller, ctx.dest);
    vec![
        CallEffect::ReturnNewAllocation {
            size_arg: 0,
            elem_size: elem,
        },
    ]
}

fn eff_vec_from_box(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnNewAllocationFromBox { box_arg: 0 },
    ]
}

fn eff_allocator_allocate(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAllocBuffer]
}

fn eff_layout_align(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnPowerOfTwo]
}

fn eff_forget(_ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::CleanSliceDataLinks { arg: 0 },
    ]
}

fn eff_layout_const(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    layout_constant_effect(ctx.tcx, ctx.caller, ctx.func, ctx.name)
        .into_iter()
        .collect()
}

// ── Matcher functions (one per API pattern) ────────────────────────────

fn mem_forget(n: &str) -> bool             { n.ends_with("mem::forget") }
fn slice_index(n: &str) -> bool             { n.ends_with("::Index::index") || n.ends_with("::IndexMut::index_mut") }
fn align_to_local(n: &str) -> bool           {
    n.ends_with("align_to_ext") || n.ends_with("align_to_mut_ext")
}
fn into_iter_local(n: &str) -> bool          {
    (n.contains("into_iter") && (n.contains("IntoIterator") || n.contains("slice::into_iter")))
        || n.contains("slice::<impl [T]>::iter")
}
fn iter_position(n: &str) -> bool            { n.contains("Iterator::position") || n.contains("Iterator::find") || n.contains("Iterator::rposition") }
fn is_strlen(n: &str) -> bool                { n == "strlen" || n.ends_with("::strlen") }
fn nonnull_new(n: &str) -> bool             { n.ends_with("::new") && api_classify::is_nonnull_api(n) && !n.ends_with("::new_unchecked") }
fn ptr_read(n: &str) -> bool                { n.ends_with("::read") && n.contains("::ptr::") }
fn is_empty(n: &str) -> bool                { n.ends_with("::is_empty") }
fn cmp_min(n: &str) -> bool                 { (n.contains("::cmp::min") || n.contains("::Ord::min") || n.starts_with("core::cmp::min")) && !n.contains("min_by") }

/// `u32::midpoint`/`usize::midpoint`: `midpoint(a, b) >= min(a, b)`, so it is
/// non-zero whenever both arguments are non-zero. Modelled with `ReturnMin`
/// (a conservative lower bound that still discharges `ValidNum` obligations).
fn midpoint(n: &str) -> bool { n.ends_with("::midpoint") }

/// Bit-preserving integer operations: rotations, byte/bit reversals,
/// endianness conversions, popcount and integer square root all map `0` to
/// `0` and non-zero to non-zero, so the result is non-zero *iff* the operand
/// is (`ReturnNonZeroIff`). `saturating_pow` is grouped here too: a non-zero
/// base yields a non-zero result for any exponent, so the `base != 0 =>
/// result != 0` direction holds. The converse is only approximate — `x.pow(0)`
/// is `1` even when `x == 0` — so a zero base is not modelled as forcing a
/// zero result.
fn bit_preserving_nz(n: &str) -> bool {
    n.contains("::rotate_left")
        || n.contains("::rotate_right")
        || n.contains("::swap_bytes")
        || n.contains("::reverse_bits")
        || n.contains("::from_be")
        || n.contains("::from_le")
        || n.contains("::to_be")
        || n.contains("::to_le")
        || n.contains("::count_ones")
        || n.contains("::isqrt")
        || n.contains("::saturating_pow")
}

/// `checked_pow` returns `Option<T>` whose `Some` payload is non-zero when the
/// base is non-zero (`ReturnOptionSomeNonZeroIff`). As with `saturating_pow`,
/// the converse is approximate: `x.checked_pow(0) == Some(1)` even for `x == 0`.
fn checked_pow_nz(n: &str) -> bool {
    n.ends_with("::checked_pow")
}

/// `checked_abs`/`checked_neg` return `Option<T>`; `Some(x)` is `|x|` / `-x`,
/// which is non-zero iff the operand is non-zero (`MIN` yields `None`, not a
/// zero payload). Modelled with `ReturnOptionSomeNonZeroIff`.
fn checked_abs_nz(n: &str) -> bool {
    n.ends_with("::checked_abs")
}

fn checked_neg_nz(n: &str) -> bool {
    n.ends_with("::checked_neg")
}

/// `checked_next_power_of_two` returns `Option<T>` whose `Some` payload is the
/// next power of two, which is always positive regardless of the argument
/// (`0.next_power_of_two() == 1`). Modelled with the unconditional
/// `ReturnOptionSomeNonZero`.
fn checked_next_pow2_nz(n: &str) -> bool {
    n.ends_with("::checked_next_power_of_two")
}

/// Comparison / absolute-value / negation / saturating & unchecked arithmetic
/// operations. Each is modelled with a precise expression over its operands
/// (see the `eff_return_*` builders) so non-zero-ness is discharged
/// *conditionally* — only when the operands are actually non-zero.
fn int_max(n: &str) -> bool {
    (n.contains("::cmp::max") || n.contains("::Ord::max") || n.starts_with("core::cmp::max"))
        && !n.contains("max_by")
}
fn int_clamp(n: &str) -> bool { n.ends_with("::clamp") }
fn int_abs(n: &str) -> bool {
    n.ends_with("::abs")
        || n.ends_with("::saturating_abs")
        || n.ends_with("::wrapping_abs")
        || n.ends_with("::unsigned_abs")
}
fn int_neg(n: &str) -> bool {
    n.ends_with("::neg")
        || n.ends_with("::wrapping_neg")
        || n.ends_with("::saturating_neg")
}
fn int_add(n: &str) -> bool {
    n.ends_with("::saturating_add") || n.ends_with("::unchecked_add")
}
fn int_mul(n: &str) -> bool {
    n.ends_with("::saturating_mul") || n.ends_with("::unchecked_mul")
}
fn int_checked_add(n: &str) -> bool { n.ends_with("::checked_add") }
fn int_checked_mul(n: &str) -> bool { n.ends_with("::checked_mul") }

/// `overflowing_abs` / `overflowing_neg` return `(result, overflow)` where the
/// `result` field (0) is non-zero whenever the operand is non-zero.  Model the
/// field 0 as non-zero (`ReturnTupleFieldNonZero { field: 0 }`).
fn overflowing_nz(n: &str) -> bool {
    n.ends_with("::overflowing_abs") || n.ends_with("::overflowing_neg")
}
fn allocator_allocate(n: &str) -> bool      {
    n.ends_with("::Allocator::allocate")
        || n.ends_with("::Allocator::allocate_zeroed")
        || n.ends_with("::Allocator::grow")
        || n.ends_with("::Allocator::shrink")
}
fn layout_align(n: &str) -> bool            { n.ends_with("Layout::align") }
fn saturating_sub(n: &str) -> bool          { n.contains("::saturating_sub") }
fn split_at(n: &str) -> bool                { n.contains("::split_at") }
fn is_slice_get_unchecked(n: &str) -> bool   { 
    (n.contains("::get_unchecked") || n.contains("::get_unchecked_mut"))
        && (n.contains("::SliceIndex")
            || n.contains("::<impl [T]>::get_unchecked")
            || n.contains("::mut_ptr::get_unchecked")
            || n.contains("::const_ptr::get_unchecked"))
}

// ── Layout helpers (used by effect builders) ─────────────────────────

fn dest_is_pointer(tcx: TyCtxt<'_>, caller: DefId, dest: Option<rustc_middle::mir::Local>) -> bool {
    let Some(d) = dest else { return false };
    pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty).is_some()
}

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else { return None };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else { return None };
    args.iter().find_map(|a| {
        #[cfg(rapx_ge_99)] let a = a.skip_binder();
        match a.kind() { GenericArgKind::Type(t) => Some(t), _ => None }
    })
}

fn layout_constant_effect<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, func: &Operand<'tcx>, name: &str,
) -> Option<CallEffect> {
    let ty = layout_call_ty(func)?;
    let (align, size) = type_layout(tcx, caller, ty)?;
    if name.contains("align_of") {
        Some(CallEffect::ReturnConst { value: align, label: format!("align_of::<{ty:?}>()") })
    } else if name.contains("size_of") {
        Some(CallEffect::ReturnConst { value: size, label: format!("size_of::<{ty:?}>()") })
    } else {
        None
    }
}

fn eff_box_from_vec(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoxFromVec { arg: 0 }]
}
