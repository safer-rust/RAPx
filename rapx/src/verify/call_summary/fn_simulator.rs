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
use rustc_middle::ty::{GenericArgKind, PseudoCanonicalInput, Ty, TyCtxt, TyKind};

use super::{CallDependencySummary, CallEffect, CallEffectSummary};
use crate::helpers::mir_utils::ty_has_param_const;
use crate::verify::{
    smt_check::common::pointee_ty,
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
    ($m:ident, $d:expr, $all:expr, $w:expr, $e:ident) => {
        Entry { matches: $m, dep_on: $d, dep_on_all: $all, writes: $w, effects: $e }
    };
}

const ALL: &[usize] = &[];

static REGISTRY: &[Entry] = &[
    // ── Pass-through / no-effect calls ──────────────────────────────
    E!(mem_forget_capacity,   dep0!(),  false,  none!(),  eff_none),
    E!(transmute,             dep0!(),  false,  none!(),  eff_none),
    E!(is_maybe_uninit_uninit,none!(),  false,  none!(),  eff_none),
    E!(is_numeric_arith,      ALL,      true,   none!(),  eff_none),
    E!(saturating_sub,        ALL,      true,   none!(),  eff_none),
    E!(is_option_unwrap,      dep0!(),  false,  none!(),  eff_none),
    E!(from_trait_call,       dep0!(),  false,  none!(),  eff_from_trait),

    // ── Pointer extraction / cast ───────────────────────────────────
    E!(nonnull_from,          dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_new_unchecked, dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_as_ref,        dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(nonnull_as_mut,        dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(is_as_ptr,             dep0!(),  false,  none!(),  eff_alias_ptr),
    E!(is_as_ptr_range,       dep0!(),  false,  none!(),  eff_alias_arg0),
    E!(is_as_mut_ptr_range,   dep0!(),  false,  none!(),  eff_alias_arg0),

    // ── Pointer arithmetic ──────────────────────────────────────────
    E!(ptr_add,               dep01!(), false,  none!(),  eff_ptr_add),
    E!(ptr_sub,               dep01!(), false,  none!(),  eff_ptr_sub),
    E!(byte_ptr_add,          dep01!(), false,  none!(),  eff_ptr_add),
    E!(byte_ptr_sub,          dep01!(), false,  none!(),  eff_ptr_sub),

    // ── Memory read / write ─────────────────────────────────────────
    E!(ptr_read,              dep0!(),  false,  none!(),  eff_read_mem),
    E!(is_ptr_write,          none!(),  false,  dep0!(),  eff_write_mem),

    // ── Slice / collection queries ──────────────────────────────────
    E!(is_len,                dep0!(),  false,  none!(),  eff_len),
    E!(is_empty,              dep0!(),  false,  none!(),  eff_is_empty),
    E!(cmp_min,               ALL,      true,   none!(),  eff_cmp_min),

    // ── Ownership reconstruction ────────────────────────────────────
    E!(is_ownership_reconstruction, dep0!(), false, none!(), eff_ownership_recon),

    // ── Slice helpers ───────────────────────────────────────────────
    E!(slice_range,           dep01!(), false,  none!(),  eff_bounded_range),
    E!(align_to_offsets,      ALL,      true,   none!(),  eff_lcm_split),
    E!(split_at,              dep01!(), false,  none!(),  eff_split_at),
    E!(is_from_raw_parts,     dep01!(), false,  none!(),  eff_from_raw_parts),

    // ── Layout constants ────────────────────────────────────────────
    E!(is_layout_constant,    none!(),  false,  none!(),  eff_layout_const),
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
    let stride = if is_byte_ptr_arith(ctx.name) {
        Some(1)
    } else {
        destination_stride(ctx.tcx, ctx.caller, ctx.dest)
    };
    vec![CallEffect::ReturnPointerAdd { base_arg: 0, offset_arg: 1, stride }]
}

fn eff_ptr_sub(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let stride = if is_byte_ptr_arith(ctx.name) {
        Some(1)
    } else {
        destination_stride(ctx.tcx, ctx.caller, ctx.dest)
    };
    vec![CallEffect::ReturnPointerSub { base_arg: 0, offset_arg: 1, stride }]
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

fn eff_split_at(_: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnTupleFieldLength { field: 0, from_arg: 1 },
    ]
}

fn eff_from_raw_parts(ctx: &EffCtx<'_, '_>) -> Vec<CallEffect> {
    let mut eff = vec![
        CallEffect::ReturnAliasArg { arg: 0 },
        CallEffect::ReturnNonZero,
    ];
    if let Some((a, n)) = pointee_alignment(ctx.tcx, ctx.caller, ctx.dest) {
        eff.push(CallEffect::ReturnAligned { align: a, ty_name: n });
    }
    eff
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
fn align_to_offsets(n: &str) -> bool        { n.contains("::align_to_offsets") }
fn from_trait_call(n: &str) -> bool         { n == "std::convert::From::from" || n == "core::convert::From::from" }
fn nonnull_from(n: &str) -> bool            { n.ends_with("::from") && n.contains("ptr::non_null") }
fn nonnull_new_unchecked(n: &str) -> bool   { n.ends_with("::new_unchecked") && n.contains("ptr::non_null") }
fn nonnull_as_ref(n: &str) -> bool          { n.ends_with("::as_ref") && n.contains("ptr::non_null") }
fn nonnull_as_mut(n: &str) -> bool          { n.ends_with("::as_mut") && n.contains("ptr::non_null") }
fn ptr_add(n: &str) -> bool                 { is_pointer_add(n) && !is_byte_ptr_arith(n) }
fn ptr_sub(n: &str) -> bool                 { is_pointer_sub(n) && !is_byte_ptr_arith(n) }
fn byte_ptr_add(n: &str) -> bool            { is_byte_ptr_arith(n) }
fn byte_ptr_sub(n: &str) -> bool            { is_byte_ptr_arith(n) }
fn ptr_read(n: &str) -> bool                { n.ends_with("::read") && n.contains("::ptr::") }
fn is_empty(n: &str) -> bool                { n.ends_with("::is_empty") }
fn cmp_min(n: &str) -> bool                 { (n.contains("::cmp::min") || n.starts_with("core::cmp::min")) && !n.contains("min_by") }
fn saturating_sub(n: &str) -> bool          { n.contains("::saturating_sub") }
fn split_at(n: &str) -> bool                { n.contains("::split_at") }

// ── is_* helpers (hot path — direct string matching) ─────────────────

pub fn is_ownership_reconstruction(name: &str) -> bool {
    name.contains("from_raw") && !name.contains("from_raw_parts")
        && (name.contains("boxed") || name.contains("Box")
            || name.contains("CString") || name.contains("ffi::c_str"))
}

pub fn is_as_ptr(name: &str) -> bool {
    name.contains("::as_ptr") && !name.ends_with("::as_ptr_range")
        || name.ends_with("::into_raw")
        || name.contains("::as_mut_ptr") && !name.ends_with("::as_mut_ptr_range")
        || name.ends_with("::into_raw_mut")
        || name.contains("::cast") || name.contains("cast_array")
        || name.contains("cast_const") || name.contains("cast_mut")
        || name.ends_with("::from") && name.contains("ptr::non_null")
        || name.ends_with("::new_unchecked") && name.contains("ptr::non_null")
        || name.ends_with("::as_ref") && name.contains("ptr::non_null")
        || name.ends_with("::as_mut") && name.contains("ptr::non_null")
}

pub fn is_pointer_arithmetic(name: &str) -> bool { is_pointer_add(name) || is_pointer_sub(name) }

pub fn is_pointer_add(name: &str) -> bool {
    name.ends_with("::add") || name.ends_with("::wrapping_add")
        || name.contains("::offset") || name.contains("::wrapping_offset")
        || name.contains("::byte_add") || name.contains("::wrapping_byte_add")
        || name.contains("::byte_offset") || name.contains("::wrapping_byte_offset")
}

pub fn is_pointer_sub(name: &str) -> bool {
    name.ends_with("::sub") || name.ends_with("::wrapping_sub")
        || name.contains("::byte_sub") || name.contains("::wrapping_byte_sub")
}

pub fn is_element_ptr_arith(name: &str) -> bool {
    name.ends_with("::add") || name.ends_with("::wrapping_add")
        || name.ends_with("::sub") || name.ends_with("::wrapping_sub")
        || name.contains("::offset") || name.contains("::wrapping_offset")
}

pub fn is_byte_ptr_arith(name: &str) -> bool {
    name.contains("::byte_add") || name.contains("::wrapping_byte_add")
        || name.contains("::byte_sub") || name.contains("::wrapping_byte_sub")
        || name.contains("::byte_offset") || name.contains("::wrapping_byte_offset")
}

pub fn is_signed_ptr_arith(name: &str) -> bool {
    name.contains("::offset") || name.contains("::wrapping_offset")
        || name.contains("::byte_offset") || name.contains("::wrapping_byte_offset")
}

pub fn is_layout_constant(name: &str) -> bool { name.contains("align_of") || name.contains("size_of") }
pub fn is_align_of(name: &str) -> bool { name.contains("align_of") }
pub fn is_ptr_cast(name: &str) -> bool {
    name.contains("::cast") || name.contains("cast_array")
        || name.contains("cast_const") || name.contains("cast_mut")
}
pub fn is_as_ptr_range(name: &str) -> bool { name.ends_with("::as_ptr_range") }
pub fn is_as_mut_ptr_range(name: &str) -> bool { name.ends_with("::as_mut_ptr_range") }
pub fn is_ptr_write(name: &str) -> bool {
    (name.contains("::write") || name.ends_with("write"))
        && !name.contains("write_bytes") && !name.contains("write_unaligned")
        && !name.contains("write_volatile")
}
pub fn is_len(name: &str) -> bool { name.contains("::len") }
pub fn is_numeric_arith(name: &str) -> bool {
    name.contains("::unchecked_mul") || name.contains("::unchecked_add")
        || name.contains("::unchecked_sub") || name.contains("::unchecked_div")
        || name.contains("::unchecked_rem") || name.contains("::exact_div")
        || name.contains("::checked_mul") || name.contains("::checked_add")
        || name.contains("::checked_sub")
}
pub fn is_option_unwrap(name: &str) -> bool {
    (name.contains("Option") || name.contains("Result"))
        && (name.contains("::expect") || name.contains("::unwrap")
            || name.contains("::unwrap_unchecked"))
}
pub fn is_maybe_uninit_uninit(name: &str) -> bool {
    name.contains("MaybeUninit") && name.ends_with("::uninit")
}
pub fn is_from_raw_parts(name: &str) -> bool { name.contains("::from_raw_parts") }

// ── Layout helpers (used by effect builders) ─────────────────────────

fn layout_call_ty<'tcx>(func: &Operand<'tcx>) -> Option<Ty<'tcx>> {
    let Operand::Constant(c) = func else { return None };
    let TyKind::FnDef(_, args) = c.const_.ty().kind() else { return None };
    args.iter().find_map(|a| {
        #[cfg(rapx_rustc_ge_199)] let a = a.skip_binder();
        match a.kind() { GenericArgKind::Type(t) => Some(t), _ => None }
    })
}

fn type_layout<'tcx>(tcx: TyCtxt<'tcx>, caller: DefId, ty: Ty<'tcx>) -> Option<(u64, u64)> {
    if ty_has_param_const(ty) { return None }
    let env = rustc_middle::ty::TypingEnv::post_analysis(tcx, caller);
    match tcx.layout_of(PseudoCanonicalInput { typing_env: env, value: ty }) {
        Ok(l) => Some((l.align.abi.bytes(), l.size.bytes())),
        Err(_) if matches!(ty.kind(), TyKind::Param(_)) => Some((0, 0)),
        Err(_) => None,
    }
}

pub(crate) fn destination_stride<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, dest: Option<rustc_middle::mir::Local>,
) -> Option<u64> {
    let d = dest?;
    let pointee = pointee_ty(tcx.optimized_mir(caller).local_decls[d].ty)?;
    type_layout(tcx, caller, pointee).map(|(_, s)| s)
}

fn pointee_alignment<'tcx>(
    tcx: TyCtxt<'tcx>, caller: DefId, dest: Option<rustc_middle::mir::Local>,
) -> Option<(u64, String)> {
    let d = dest?;
    let ty = tcx.optimized_mir(caller).local_decls[d].ty;
    let pointee = pointee_ty(ty).or(Some(ty))?;
    if let Some((a, _)) = type_layout(tcx, caller, pointee) {
        return Some((a, format!("{pointee:?}")));
    }
    if let TyKind::Array(e, _) = pointee.kind()
        && let Some((a, _)) = type_layout(tcx, caller, *e)
    {
        return Some((a, format!("{pointee:?}")));
    }
    Some((0, format!("{pointee:?}")))
}

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

fn nonnull_inner_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    let TyKind::Adt(def, args) = ty.kind() else { return None };
    if !tcx.def_path_str(def.did()).contains("ptr::non_null::NonNull") { return None }
    args.iter().find_map(|a| match a.kind() { GenericArgKind::Type(t) => Some(t), _ => None })
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
