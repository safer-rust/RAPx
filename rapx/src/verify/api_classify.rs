//! API call and type classification helpers.
//!
//! Each classifier answers "what kind of operation is this call?" (pointer
//! arithmetic, raw memory access, ownership transfer, …). Callers — the path
//! graph, VM, alias/hazard scanner, and call-summary registry — use these to pick
//! a modelling strategy or discharge a safety obligation.
//!
//! # Matching mechanism
//!
//! Most classifiers match callees or ADT types by `DefId`, using identities
//! from [`crate::def_ids::intrinsic_api`],
//! [`crate::def_ids::other_api`] and [`crate::def_ids::type_ids`].

use crate::def_ids::{intrinsic_api, other_api, type_ids};
use crate::verify::call_summary::pointer_flow;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};

/// Whether `callee` is an intrinsic with one of the given names.
fn is_intrinsic(tcx: TyCtxt<'_>, callee: Option<DefId>, names: &[&str]) -> bool {
    intrinsic_api::intrinsic_name(tcx, callee).is_some_and(|name| names.contains(&name.as_str()))
}

/// Whether `callee` explicitly drops the value stored in `ManuallyDrop<T>`.
pub fn is_manually_drop_drop(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|c| other_api::is_manually_drop(tcx, c))
}

// ── Pointer extraction / cast ─────────────────────────────────────

/// Whether MIR traces the returned pointer to the first argument.
pub fn is_as_ptr(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|id| {
        crate::verify::call_summary::pointer_flow::return_source_arg(tcx, id) == Some(0)
            || crate::verify::call_summary::pointer_flow::is_nonnull_view(tcx, id)
    })
}

fn is_intrinsic_copy(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic(tcx, callee, &["copy", "copy_nonoverlapping"])
}

pub fn is_intrinsic_ptr_offset_from(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic(tcx, callee, &["ptr_offset_from", "ptr_offset_from_unsigned"])
}

// ── Raw pointer read / write ──────────────────────────────────────

/// Whether `callee` writes through a raw pointer to its first argument
/// (`ptr::write`, `write_bytes`, `write_unaligned`, `write_volatile`).
pub fn is_ptr_write(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| other_api::is_ptr_write(tcx, did))
}

pub fn is_ptr_copy(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic_copy(tcx, callee)
        || callee.is_some_and(|did| other_api::is_ptr_copy(tcx, did))
}

/// Whether `callee` reads through a raw pointer or copies memory
/// (`ptr::read`/`read_unaligned`/`read_volatile`, pointer-copy wrappers,
/// `MaybeUninit::assume_init_read`, and intrinsics `copy`/`copy_nonoverlapping`).
pub fn is_ptr_read(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic_copy(tcx, callee)
        || callee.is_some_and(|did| crate::helpers::mir_utils::is_ptr_copy_wrapper(tcx, did))
        || callee.is_some_and(|did| other_api::is_ptr_read(tcx, did))
        || callee.is_some_and(|did| other_api::is_assume_init_read(tcx, did))
}

/// Copy/write operations that do not require initialized destination bytes:
/// Intrinsic copies, pointer-copy wrappers, `write`, and `write_bytes` do not
/// require initialized destination bytes for `Init`/`Typed` obligations.
pub fn is_mem_copy_or_write(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    is_intrinsic_copy(tcx, callee)
        || callee.is_some_and(|did| crate::helpers::mir_utils::is_ptr_copy_wrapper(tcx, did))
        || callee.is_some_and(|did| other_api::is_ptr_write_to_uninit(tcx, did))
}

// ── Alias-hazard classification ───────────────────────────────────
// Ref-counted reconstruction retains a dedicated rule until the alias model
// accounts for shared ownership and clone counts.
/// Mutability of a reference returned from a `NonNull<T>` receiver.
pub fn nonnull_ref_return(tcx: TyCtxt<'_>, callee: DefId) -> Option<rustc_middle::mir::Mutability> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn)
        || !tcx.is_mir_available(callee)
    {
        return None;
    }
    let sig = tcx.fn_sig(callee).skip_binder();
    let [receiver] = sig.inputs().skip_binder() else {
        return None;
    };
    let TyKind::Ref(_, inner, _) = receiver.kind() else {
        return None;
    };
    let TyKind::Adt(adt, args) = inner.kind() else {
        return None;
    };
    if !is_std_nonnull(adt.did()) {
        return None;
    }
    let pointee = args.first().and_then(|arg| arg.as_type())?;
    let output = sig.output().skip_binder();
    let TyKind::Ref(_, returned, mutability) = output.kind() else {
        return None;
    };
    (*returned == pointee && pointer_flow::return_reference_source_arg(tcx, callee) == Some(0))
        .then_some(*mutability)
}

/// Whether MIR shows a read-only pointer view of the first argument.
pub fn is_benign_origin_use(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| {
        pointer_flow::is_read_only_return(tcx, did)
            || pointer_flow::is_read_only_nonnull_view(tcx, did)
    })
}

// ── ADT type-name classifiers ─────────────────────────────────────
// *Shape* recognizers used by the VM to model repr(transparent) wrappers and
// fixed field layouts (`Vec` = ptr/cap/len, `slice::Iter` = ptr/end, …).
// Matched by `DefId` (resolved in [`crate::def_ids::type_ids`]).

pub fn is_std_vec(def_id: DefId) -> bool {
    type_ids::vec_types().contains(&def_id)
}
pub fn is_std_string(def_id: DefId) -> bool {
    type_ids::string_types().contains(&def_id)
}
pub fn is_std_box(def_id: DefId) -> bool {
    type_ids::box_types().contains(&def_id)
}
pub fn is_std_cstring(def_id: DefId) -> bool {
    type_ids::cstring_types().contains(&def_id)
}
pub fn is_std_nonnull(def_id: DefId) -> bool {
    type_ids::nonnull_types().contains(&def_id)
}
pub fn is_maybe_uninit_type(def_id: DefId) -> bool {
    type_ids::maybe_uninit_types().contains(&def_id)
}

/// Whether `ty` (peeling through `&` / `*mut` / `*const` / `[T]` / `[T; N]`) is
/// `MaybeUninit<...>`, i.e. carries no validity invariant (any bit pattern is a
/// valid value).  Shared by the VM (`init_parameters`) and the `Typed` checker.
pub fn is_maybe_uninit_ty(ty: Ty<'_>) -> bool {
    let mut t = ty;
    loop {
        match t.kind() {
            TyKind::Slice(e) | TyKind::Array(e, _) => t = *e,
            TyKind::RawPtr(e, _) | TyKind::Ref(_, e, _) => t = *e,
            TyKind::Adt(adt, _) => return is_maybe_uninit_type(adt.did()),
            _ => return false,
        }
    }
}
pub fn is_std_iter_or_itermut(def_id: DefId) -> bool {
    type_ids::iter_types().contains(&def_id)
}

pub fn is_std_ordering(def_id: DefId) -> bool {
    type_ids::ordering_types().contains(&def_id)
}

/// Whether `def_id` is `core::ops::index_range::IndexRange`.
pub fn is_index_range(def_id: DefId) -> bool {
    type_ids::index_range_types().contains(&def_id)
}
