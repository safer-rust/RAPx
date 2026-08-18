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
    type_layout, destination_stride, pointee_alignment,
    nonnull_inner_ty, slice_element_size, vec_element_size,
};

// ── Context for effect builders ────────────────────────────────────────

pub struct EffCtx<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub caller: DefId,
    pub callee: Option<DefId>,
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

macro_rules! none { () => { &[] } }
macro_rules! dep0  { () => { &[0usize] } }
macro_rules! dep01 { () => { &[0usize, 1] } }

macro_rules! E {
    ($m:expr, $d:expr, $all:expr, $w:expr, $e:ident) => {
        Entry { matches: $m, dep_on: $d, dep_on_all: $all, writes: $w, effects: $e }
    };
}

const ALL: &[usize] = &[];

static REGISTRY: &[Entry] = &[
    // ── Pass-through / no-effect calls ──────────────────────────────
    E!(mem_forget_capacity,   dep0!(),  false,  none!(),  eff_forget),
    E!(transmute,             dep0!(),  false,  none!(),  eff_none),
    E!(api_classify::is_maybe_uninit_uninit,none!(), false, none!(), eff_none),
    E!(api_classify::is_maybe_uninit_assume_init,dep0!(), false, none!(), eff_none),
    E!(api_classify::is_numeric_arith, ALL,      true,   none!(),  eff_none),
    E!(saturating_sub,        ALL,      true,   none!(),  eff_none),
    E!(api_classify::is_offset_from_unsigned, dep01!(), false, none!(), eff_offset_from_unsigned),
    E!(api_classify::is_option_unwrap, dep0!(),  false,  none!(),  eff_alias_arg0),
    E!(from_trait_call,       dep0!(),  false,  none!(),  eff_from_trait),

    // ── Pointer extraction / cast ───────────────────────────────────
    E!(nonnull_from,          dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_new_unchecked, dep0!(),  false,  none!(),  eff_none),
    E!(nonnull_new,           dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_as_ref,        dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_as_mut,        dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(api_classify::is_as_ptr, dep0!(), false,  none!(),  eff_alias_ptr),
    E!(api_classify::is_as_ptr_range, dep0!(), false, none!(), eff_alias_arg0),
    E!(api_classify::is_as_mut_ptr_range, dep0!(), false, none!(), eff_alias_arg0),

    // ── Pointer arithmetic ──────────────────────────────────────────
    E!(|n| api_classify::is_pointer_add(n) && !api_classify::is_byte_ptr_arith(n), dep01!(), false, none!(), eff_ptr_add),
    E!(|n| api_classify::is_pointer_sub(n) && !api_classify::is_byte_ptr_arith(n), dep01!(), false, none!(), eff_ptr_sub),
    E!(api_classify::is_byte_ptr_arith,    dep01!(), false,  none!(),  eff_ptr_add),
    E!(api_classify::is_byte_ptr_arith,    dep01!(), false,  none!(),  eff_ptr_sub),

    // ── Memory read / write ─────────────────────────────────────────
    E!(ptr_read,              dep0!(),  false,  none!(),  eff_read_mem),
    E!(api_classify::is_ptr_write, none!(), false,  dep0!(),  eff_write_mem),
    E!(api_classify::is_maybe_uninit_write, none!(), false, dep0!(), eff_write_mem),

    // ── Slice / collection queries ──────────────────────────────────
    E!(api_classify::is_len,  dep0!(),  false,  none!(),  eff_len),
    E!(is_empty,              dep0!(),  false,  none!(),  eff_is_empty),
    E!(cmp_min,               ALL,      true,   none!(),  eff_cmp_min),

    // ── SliceIndex::get_unchecked / get_unchecked_mut ───────────────
    E!(is_slice_get_unchecked, dep0!(), false,  none!(),  eff_alias_ptr),

    // ── Ownership reconstruction ────────────────────────────────────
    E!(api_classify::is_ownership_reconstruction, dep0!(), false, none!(), eff_ownership_recon),

    // ── Slice helpers ───────────────────────────────────────────────
    E!(slice_range,           dep01!(), false,  none!(),  eff_bounded_range),
    E!(slice_index,           dep01!(), false,  none!(),  eff_alias_arg0),
    E!(align_to_offsets,      ALL,      true,   none!(),  eff_lcm_split),
    E!(align_to_local,        dep0!(),  false,  none!(),  eff_align_to),
    E!(into_iter_local,       dep0!(),  false,  none!(),  eff_return_iter),
    E!(split_at,              dep01!(), false,  none!(),  eff_split_at),
    E!(api_classify::is_from_raw_parts, dep01!(), false, none!(), eff_from_raw_parts),
    E!(api_classify::is_align_offset, dep01!(), false, none!(), eff_align_offset),

    // ── Vec / collection constructors ────────────────────────────────
    E!(api_classify::is_vec_alloc_constructor, dep01!(), false, none!(), eff_new_allocation),
    E!(api_classify::is_vec_from_box,          dep0!(),  false, none!(), eff_vec_from_box),
    E!(api_classify::is_vec_with_capacity,     dep0!(),  false, none!(), eff_new_allocation_from_cap),
    E!(api_classify::is_into_boxed_slice,      dep0!(),  false, none!(), eff_box_from_vec),

    // ── Allocator::allocate / allocate_zeroed / grow / shrink ────────
    E!(allocator_allocate,    dep01!(), false,  none!(),  eff_allocator_allocate),

    // ── Layout accessors ────────────────────────────────────────────
    E!(layout_align,          none!(),  false,  none!(),  eff_layout_align),

    // ── Layout constants ────────────────────────────────────────────
    E!(api_classify::is_layout_constant, none!(), false,  none!(),  eff_layout_const),

    // ── CStr / CString helpers ──────────────────────────────────────
    E!(api_classify::is_cstr_from_ptr, dep0!(), false,  none!(),  eff_alias_arg0),
    E!(api_classify::is_cstr_from_bytes_with_nul_unchecked, dep0!(), false, none!(), eff_alias_arg0),
    E!(api_classify::is_vec_push, none!(), false,  dep0!(),  eff_write_mem),
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
            let ctx = EffCtx { tcx, caller, callee, name, func, dest };
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

fn eff_alias_nonnull(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let mut eff = vec![
        CallEffect::ReturnPointerFromArg { arg: 0 },
        CallEffect::ReturnNonZero,
    ];
    if let Some((a, n)) = nonnull_pointee_alignment(ctx.tcx, ctx.caller, ctx.dest) {
        eff.push(CallEffect::ReturnAligned { align: a, ty_name: n });
    }
    eff
}

fn eff_from_trait(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    if is_nonnull_dest(ctx.tcx, ctx.caller, ctx.dest) {
        eff_alias_nonnull(ctx)
    } else {
        Vec::new()
    }
}

fn eff_alias_arg0(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAliasArg { arg: 0 }]
}

fn eff_ptr_add(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let stride = if api_classify::is_byte_ptr_arith(ctx.name) {
        Some(1)
    } else {
        destination_stride(ctx.tcx, ctx.caller, ctx.dest)
    };
    vec![CallEffect::ReturnPointerAdd { base_arg: 0, offset_arg: 1, stride }]
}

fn eff_ptr_sub(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
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

fn eff_ownership_recon(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnNonZero,
        CallEffect::OwnsInitMemory { arg: 0 },
    ]
}

fn eff_bounded_range(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnBoundedRange { bounds_arg: 1 }]
}

fn eff_lcm_split(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnLcmSplit { receiver_arg: 0 }]
}

fn eff_align_to(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnAlignTo { receiver_arg: 0 }]
}

fn eff_return_iter(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![CallEffect::ReturnIter { receiver_arg: 0 }]
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
    let elem = slice_element_size(ctx.tcx, ctx.caller, ctx.func, ctx.dest);
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

fn mem_forget_capacity(n: &str) -> bool     { n.ends_with("mem::forget") || n.ends_with("::capacity") }
fn transmute(n: &str) -> bool               { n.contains("::transmute") || n.contains("intrinsics::transmute") }
fn slice_range(n: &str) -> bool             { let b = n.split('<').next().unwrap_or(n); b.ends_with("slice::range") || b.contains("slice::index::range") }
fn slice_index(n: &str) -> bool             { n.ends_with("::Index::index") || n.ends_with("::IndexMut::index_mut") }
fn align_to_offsets(n: &str) -> bool        { n.contains("::align_to_offsets") }
fn align_to_local(n: &str) -> bool           {
    n.ends_with("align_to_ext") || n.ends_with("align_to_mut_ext")
}
fn into_iter_local(n: &str) -> bool          {
    n.contains("into_iter") && (n.contains("IntoIterator") || n.contains("slice::into_iter"))
}
fn from_trait_call(n: &str) -> bool         { n == "std::convert::From::from" || n == "core::convert::From::from" }
fn nonnull_from(n: &str) -> bool            { n.ends_with("::from") && api_classify::is_nonnull_api(n) }
fn nonnull_new_unchecked(n: &str) -> bool   { n.ends_with("::new_unchecked") && api_classify::is_nonnull_api(n) }
fn nonnull_new(n: &str) -> bool             { n.ends_with("::new") && api_classify::is_nonnull_api(n) && !n.ends_with("::new_unchecked") }
fn nonnull_as_ref(n: &str) -> bool          { n.ends_with("::as_ref") && api_classify::is_nonnull_api(n) }
fn nonnull_as_mut(n: &str) -> bool          { n.ends_with("::as_mut") && api_classify::is_nonnull_api(n) }
fn ptr_read(n: &str) -> bool                { n.ends_with("::read") && n.contains("::ptr::") }
fn is_empty(n: &str) -> bool                { n.ends_with("::is_empty") }
fn cmp_min(n: &str) -> bool                 { (n.contains("::cmp::min") || n.contains("::Ord::min") || n.starts_with("core::cmp::min")) && !n.contains("min_by") }
fn allocator_allocate(n: &str) -> bool      {
    n.ends_with("::Allocator::allocate")
        || n.ends_with("::Allocator::allocate_zeroed")
        || n.ends_with("::Allocator::grow")
        || n.ends_with("::Allocator::shrink")
}
fn layout_align(n: &str) -> bool            { n.ends_with("Layout::align") && !n.ends_with("Layout::alignment") }
fn saturating_sub(n: &str) -> bool          { n.contains("::saturating_sub") }
fn split_at(n: &str) -> bool                { n.contains("::split_at") }
fn is_slice_get_unchecked(n: &str) -> bool   { 
    (n.contains("::get_unchecked") || n.contains("::get_unchecked_mut"))
        && (n.contains("::SliceIndex")
            || n.contains("::<impl [T]>::get_unchecked")
            || n.contains("::impl [T]>::get_unchecked")
            || n.contains("::mut_ptr::get_unchecked")
            || n.contains("::const_ptr::get_unchecked"))
}

// ── Layout helpers (used by effect builders) ─────────────────────────

fn nonnull_pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, dest: Option<rustc_middle::mir::Local>,
) -> Option<(u64, String)> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let pointee = nonnull_inner_ty(tcx, ty)?;
    type_layout(tcx, caller, pointee).map(|(a, _)| (a, format!("{pointee:?}")))
}

fn is_nonnull_dest(tcx: TyCtxt<'_>, caller: DefId, dest: Option<rustc_middle::mir::Local>) -> bool {
    let Some(d) = dest else { return false };
    nonnull_inner_ty(tcx, tcx.optimized_mir(caller).local_decls[d].ty).is_some()
}

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else { return None };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else { return None };
    args.iter().find_map(|a| {
        #[cfg(rapx_rustc_ge_199)] let a = a.skip_binder();
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
