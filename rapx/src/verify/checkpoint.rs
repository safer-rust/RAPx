//! Verification checkpoint types and their MIR collection.
//!
//! A [`Checkpoint`] is a point in a function body that must be verified: an
//! unsafe call, a MIR intrinsic, a raw-pointer dereference, or a `static mut` access.  The
//! `collect_*` functions scan MIR for them; the rest of the verifier consumes
//! the resulting records.

#[cfg(not(rapx_box_deref_transmute))]
use crate::def_ids::lang_api::{self, LangItem};
use rustc_hir::{Safety, def_id::DefId};
#[cfg(rapx_box_deref_transmute)]
use rustc_middle::mir::CastKind;
#[cfg(not(rapx_box_deref_transmute))]
use rustc_middle::ty::TyKind;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, List, Ty, TyCtxt},
};
use std::collections::HashSet;

use crate::helpers::{
    mir_scan::{get_fn_safety, place_has_raw_deref},
    mir_utils::{dep_callee_def_id, pointee_ty, resolve_callee_impl},
    name::get_cleaned_def_path_name,
};
use super::contract::Property;

/// Stable MIR location for a call terminator inside one function body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct CheckpointLocation {
    /// Function containing the call terminator.
    pub caller: DefId,
    /// Basic block whose terminator is the call.
    pub block: BasicBlock,
}

/// Kind of an unsafe verification checkpoint inside a function body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CheckpointKind {
    /// A real unsafe function call.
    UnsafeCall,
    /// A MIR `CopyNonOverlapping` statement.
    CopyNonOverlapping,
    /// A raw pointer dereference.
    RawPtrDeref,
    /// A mutable static variable access.
    StaticMutAccess,
}

/// A verification checkpoint in one MIR body.
///
/// Unifies unsafe calls, MIR intrinsics, raw-pointer dereferences, and mutable static
/// accesses under a single type so they all flow through the same path
/// extraction and SMT verification pipeline.
#[derive(Clone, Debug)]
pub struct Checkpoint<'tcx> {
    pub caller: DefId,
    pub callee: Option<DefId>,
    pub block: BasicBlock,
    pub args: Vec<Operand<'tcx>>,
    pub kind: CheckpointKind,
    /// Requirements attached directly to this MIR operation.
    pub(crate) requires: Vec<Property<'tcx>>,
    pub destination: Option<Local>,
    /// For `RawPtrDeref` checkpoints: whether the deref produces a mutable
    /// reference (`&mut *ptr`) rather than a shared one (`&*ptr`).
    pub is_mut_ref: bool,
    /// Statement index within `block` for statement checkpoints; used to stop
    /// slicing at the operation and for reverse liveness at raw dereferences.
    pub statement_index: usize,
    /// Distinguishes multiple accesses at one MIR location (for example,
    /// separate static pointers passed as arguments to the same call).
    pub site_ordinal: usize,
}

impl<'tcx> Checkpoint<'tcx> {
    /// Return the MIR location that identifies this checkpoint inside the verifier.
    pub fn location(&self) -> CheckpointLocation {
        CheckpointLocation {
            caller: self.caller,
            block: self.block,
        }
    }

    /// Return a human-readable label for diagnostics.
    pub fn callee_name(&self, tcx: TyCtxt<'tcx>) -> String {
        if self.kind == CheckpointKind::CopyNonOverlapping {
            return "copy_nonoverlapping".to_string();
        }
        match self.callee {
            Some(def_id) => get_cleaned_def_path_name(tcx, def_id),
            None => match self.kind {
                CheckpointKind::RawPtrDeref => "raw-ptr-deref".to_string(),
                CheckpointKind::StaticMutAccess => "static-mut-access".to_string(),
                _ => "unknown-callee".to_string(),
            },
        }
    }
}

/// Detect whether a function writes through a raw pointer (`*ptr = ...`).
///
/// Used by the marker-trait (`Send`/`Sync`) checker to decide whether a type's
/// methods mutate through a raw-pointer field (interior mutation).
pub fn has_raw_ptr_write(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.iter().any(|bb| {
        bb.statements.iter().any(|stmt| {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (lhs, _) = &**assign;
                place_has_raw_deref(body, lhs)
            } else {
                false
            }
        })
    })
}

/// Detect whether a function performs an atomic update, either through a
/// compiler intrinsic (`atomic_store`/`atomic_xadd`/...) or through an
/// `Atomic*` method (`fetch_add`/`store`/...). Reads and fences do not count.
///
/// Used by the marker-trait (`Send`/`Sync`) checker to recognize raw-pointer
/// updates that are performed atomically rather than through a plain
/// `*ptr = ...` write.  `AtomicUsize::fetch_add` and friends lower to intrinsic
/// calls only when inlined; rapx disables inlining (`-Zmir-opt-level=0`), so the
/// `Atomic*` method-call form must be recognized too.
pub fn has_atomic_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if !tcx.is_mir_available(def_id) {
        return false;
    }
    let body = tcx.optimized_mir(def_id);
    body.basic_blocks.iter().any(|bb| {
        if let TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } =
            &bb.terminator().kind
        {
            let Some(callee) = dep_callee_def_id(func) else {
                return false;
            };
            if tcx
                .intrinsic(callee)
                .is_some_and(|i| {
                    i.name.as_str().strip_prefix("atomic_").is_some_and(|op| {
                        [
                            "store", "xchg", "cxchg", "xadd", "xsub", "and", "or", "xor",
                            "nand", "min", "max", "umin", "umax",
                        ]
                            .iter()
                            .any(|prefix| op.starts_with(prefix))
                    })
                })
            {
                return true;
            }
            let Some(impl_id) = tcx.inherent_impl_of_assoc(callee) else {
                return false;
            };
            let Some(adt) = tcx.type_of(impl_id).skip_binder().ty_adt_def() else {
                return false;
            };
            let owner = tcx.def_path_str(adt.did());
            (owner.starts_with("core::sync::atomic::Atomic")
                || owner.starts_with("std::sync::atomic::Atomic"))
                && matches!(
                    tcx.item_name(callee).as_str(),
                    "store" | "swap" | "compare_exchange" | "compare_exchange_weak"
                        | "fetch_add" | "fetch_sub" | "fetch_and" | "fetch_nand"
                        | "fetch_or" | "fetch_xor" | "fetch_not" | "fetch_update"
                        | "fetch_max" | "fetch_min" | "fetch_ptr_add" | "fetch_ptr_sub"
                        | "fetch_byte_add" | "fetch_byte_sub"
                )
        } else {
            false
        }
    })
}

/// Collect all unsafe MIR checkpoints in `def_id` with full per-checkpoint metadata.
pub fn collect_unsafe_callsites<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Checkpoint<'tcx>> {
    let mut checkpoints = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return checkpoints;
    }

    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Intrinsic(intrinsic) = &statement.kind {
                let (kind, callee, args) = match &**intrinsic {
                    NonDivergingIntrinsic::CopyNonOverlapping(copy) => (
                        CheckpointKind::CopyNonOverlapping,
                        tcx.get_diagnostic_item(rustc_span::sym::ptr_copy_nonoverlapping),
                        vec![copy.src.clone(), copy.dst.clone(), copy.count.clone()],
                    ),
                    _ => (CheckpointKind::UnsafeCall, None, Vec::new()),
                };
                checkpoints.push(Checkpoint {
                    caller: def_id,
                    callee,
                    block: bb,
                    args,
                    kind,
                    requires: Vec::new(),
                    destination: None,
                    is_mut_ref: false,
                    statement_index,
                    site_ordinal: 0,
                });
            }
        }

        let (func, args, destination) = match &data.terminator().kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => (func, args, Some(destination.local)),
            TerminatorKind::TailCall { func, args, .. } => (func, args, None),
            _ => continue,
        };

        let func_ty = match func {
            Operand::Constant(func_constant) => func_constant.const_.ty(),
            Operand::Copy(place) | Operand::Move(place) => place.ty(body, tcx).ty,
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => continue,
        };
        let ty::FnDef(callee_def_id, callee_args) = func_ty.kind() else {
            if let ty::FnPtr(_, header) = func_ty.kind()
                && header.safety() == Safety::Unsafe
            {
                checkpoints.push(Checkpoint {
                    caller: def_id,
                    callee: None,
                    block: bb,
                    args: args.iter().map(|arg| arg.node.clone()).collect(),
                    kind: CheckpointKind::UnsafeCall,
                    requires: Vec::new(),
                    destination,
                    is_mut_ref: false,
                    statement_index: 0,
                    site_ordinal: 0,
                });
            }
            continue;
        };
        #[cfg(rapx_ge_99)]
        let callee_args = callee_args.skip_binder();

        if get_fn_safety(tcx, *callee_def_id) != Safety::Unsafe {
            continue;
        }

        // Normalize a trait-method callee to the concrete impl method so that
        // inline `#[rapx::requires]` contracts (which live on the impl, not the
        // trait declaration) are found during contract lookup.
        let resolved_callee =
            resolve_callee_impl(tcx, def_id, *callee_def_id, callee_args).unwrap_or(*callee_def_id);

        checkpoints.push(Checkpoint {
            caller: def_id,
            callee: Some(resolved_callee),
            block: bb,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
            kind: CheckpointKind::UnsafeCall,
            requires: Vec::new(),
            destination,
            is_mut_ref: false,
            statement_index: 0,
            site_ordinal: 0,
        });
    }

    checkpoints
}

/// Metadata for a single raw pointer dereference operation found in MIR.
#[derive(Clone, Debug)]
pub struct RawPtrDerefInfo<'tcx> {
    pub block: BasicBlock,
    pub ptr_operand: Operand<'tcx>,
    pub pointee_ty: Ty<'tcx>,
    pub is_read: bool,
    /// Whether the statement is a reference creation from a raw pointer
    /// (`&*raw_ptr` / `&mut *raw_ptr`), i.e. an `Rvalue::Ref` whose place has a
    /// raw-pointer deref projection. This is the `Ptr2Ref` operation.
    pub is_ptr2ref: bool,
    /// Whether the Ptr2Ref produces a mutable reference (`&mut *raw_ptr`).
    pub is_mut_ref: bool,
    pub destination: Local,
    /// Statement index within `block` (for reverse liveness at the deref point).
    pub statement_index: usize,
}

/// Locals that hold the result of the compiler's safe `*box` deref lowering
/// (directly, or through copies and pointer casts). The compiler lowers `*box`
/// to a raw-pointer deref of a pointer produced by casting the box's inner
/// field to a raw pointer, and that deref is safe by the `Box` invariant, so it
/// is not a raw-pointer-deref checkpoint.
fn box_deref_transmute_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut result = HashSet::new();
    let mut changed = true;
    while changed {
        changed = false;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (target, rhs) = &**assign;
                if !target.projection.is_empty() {
                    continue;
                }
                let from_box = if is_box_deref_cast(tcx, body, rhs) {
                    true
                } else if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..)
                | Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) = rhs
                {
                    p.projection.is_empty() && result.contains(&p.local)
                } else {
                    false
                };
                if from_box && result.insert(target.local) {
                    changed = true;
                }
            }
        }
    }
    result
}

/// Whether `rvalue` is the compiler's lowering of the safe `*box` deref.
///
/// On recent nightlies the compiler tags this cast `BoxDerefTransmute` — a
/// precise, dedicated marker, so match it exactly and never treat other casts
/// of a `Box`-typed local (e.g. `transmute::<Box<T>, *mut T>`) as safe. On older
/// toolchains that lower `*box` to a plain `Transmute` of the `Unique`/`NonNull`
/// field, fall back to checking the cast source base local's type.
fn is_box_deref_cast(tcx: TyCtxt<'_>, body: &Body<'_>, rvalue: &Rvalue<'_>) -> bool {
    #[cfg(rapx_box_deref_transmute)]
    {
        let _ = (tcx, body);
        matches!(rvalue, Rvalue::Cast(CastKind::BoxDerefTransmute, _, _))
    }
    #[cfg(not(rapx_box_deref_transmute))]
    {
        let Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) = rvalue else {
            return false;
        };
        // The safe `*box` deref casts the box's `Unique`/`NonNull` *field* (a
        // projection); casting the whole box value is `transmute::<Box<T>, *mut
        // T>`, an explicit unsafe transmute that must not be skipped.
        if p.projection.is_empty() {
            return false;
        }
        let base_ty = body.local_decls[p.local].ty;
        matches!(
            base_ty.kind(),
            TyKind::Adt(adt, _) if lang_api::matches(tcx, adt.did(), LangItem::OwnedBox)
        )
    }
}

/// Collect all raw pointer dereference operations in `def_id` as
/// metadata records (block, pointer operand, pointee type, read-vs-write).
pub fn collect_raw_ptr_deref_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<RawPtrDerefInfo<'tcx>> {
    let mut infos = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return infos;
    }

    let body = tcx.optimized_mir(def_id);
    // The compiler lowers `*box` to a raw-pointer deref of the pointer produced
    // by casting the box's inner field to a raw pointer; that deref is safe by
    // the `Box` invariant, so it is not a raw-pointer-deref checkpoint.
    let box_derefs = box_deref_transmute_locals(tcx, body);
    // Filter: only check statements from the function's own source file,
    // not from inlined library code (Vec, Box, etc.).
    let fn_span = tcx.def_span(def_id);
    let local_file = tcx.sess.source_map().lookup_char_pos(fn_span.lo()).file;

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (stmt_index, stmt) in data.statements.iter().enumerate() {
            let stmt_file = tcx
                .sess
                .source_map()
                .lookup_char_pos(stmt.source_info.span.lo())
                .file;
            if !std::ptr::addr_eq(
                std::sync::Arc::as_ptr(&stmt_file),
                std::sync::Arc::as_ptr(&local_file),
            ) {
                continue;
            }
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (lhs, rhs) = &**assign;

            let is_write = place_has_raw_deref(body, lhs);
            let (is_read, is_ptr2ref, is_mut_ref) = match rhs {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) => {
                    (place_has_raw_deref(body, place), false, false)
                }
                Rvalue::Ref(_, borrow_kind, place) => (
                    place_has_raw_deref(body, place),
                    true,
                    matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }),
                ),
                _ => (false, false, false),
            };

            if !is_write && !is_read {
                continue;
            }

            let deref_place = if is_write {
                lhs
            } else {
                match rhs {
                    Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                    | Rvalue::Ref(_, _, place) => place,
                    _ => continue,
                }
            };

            // Skip safe `*box` derefs (see `box_deref_transmute_locals`).
            if box_derefs.contains(&deref_place.local) {
                continue;
            }

            let Some(ptr_operand) = ptr_operand_for_deref_place(deref_place) else {
                continue;
            };

            let Some(pointee) = pointee_ty(body.local_decls[deref_place.local].ty) else {
                continue;
            };

            infos.push(RawPtrDerefInfo {
                block: bb,
                ptr_operand,
                pointee_ty: pointee,
                is_read,
                is_ptr2ref,
                is_mut_ref,
                destination: lhs.local,
                statement_index: stmt_index,
            });
        }
    }

    infos
}

/// Extract the pointer operand from a dereference place.
fn ptr_operand_for_deref_place<'tcx>(place: &Place<'tcx>) -> Option<Operand<'tcx>> {
    let first_deref_idx = place
        .projection
        .iter()
        .position(|p| matches!(p.kind(), ProjectionElem::Deref));

    if let Some(idx) = first_deref_idx
        && idx > 0
    {
        return None;
    }

    Some(Operand::Copy(Place {
        local: place.local,
        projection: List::empty(),
    }))
}

/// Metadata for a `static mut` access found in MIR.
#[derive(Clone, Debug)]
pub struct StaticMutAccessInfo<'tcx> {
    /// Basic block containing the access.
    pub block: BasicBlock,
    /// The pointee type (i.e. the type of the static itself, `T` in `static mut X: T`).
    pub ty: Ty<'tcx>,
    /// The MIR operand holding the pointer to the static.
    pub ptr_operand: Operand<'tcx>,
    /// Statement position, or the statement count for a terminator argument.
    pub statement_index: usize,
    /// Unique access number within this function.
    pub site_ordinal: usize,
}

/// Collect all basic blocks that reference mutable statics in `def_id`.
///
/// Mutable statics appear as `Constant` operands whose `check_static_ptr` points
/// to a `static mut` item.  Both reads and writes are detected here; the
/// conservative `Init` property will be checked regardless of direction.
pub fn collect_static_mut_access_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<StaticMutAccessInfo<'tcx>> {
    let mut infos = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return infos;
    }

    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (_lhs, rhs) = &**assign;
                if let Rvalue::Use(op @ Operand::Constant(c), ..) = rhs
                    && let Some(static_id) = c.check_static_ptr(tcx)
                    && matches!(tcx.static_mutability(static_id), Some(m) if m.is_mut())
                {
                    let ty = tcx.type_of(static_id).skip_binder();
                    infos.push(StaticMutAccessInfo {
                        block: bb,
                        ty,
                        ptr_operand: op.clone(),
                        statement_index,
                        site_ordinal: infos.len(),
                    });
                }
            }
        }

        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } =
                &terminator.kind
        {
            for arg in args {
                if let op @ Operand::Constant(c) = &arg.node
                    && let Some(static_id) = c.check_static_ptr(tcx)
                    && matches!(tcx.static_mutability(static_id), Some(m) if m.is_mut())
                {
                    let ty = tcx.type_of(static_id).skip_binder();
                    infos.push(StaticMutAccessInfo {
                        block: bb,
                        ty,
                        ptr_operand: op.clone(),
                        statement_index: data.statements.len(),
                        site_ordinal: infos.len(),
                    });
                }
            }
        }
    }

    infos
}

/// Return the destination local for a checkpoint's call or deref.
pub fn call_destination<'tcx>(tcx: TyCtxt<'tcx>, checkpoint: &Checkpoint<'tcx>) -> Option<Local> {
    if checkpoint.kind == CheckpointKind::RawPtrDeref {
        return checkpoint.destination;
    }
    let body = tcx.optimized_mir(checkpoint.caller);
    let terminator = body.basic_blocks[checkpoint.block].terminator();
    let TerminatorKind::Call { destination, .. } = &terminator.kind else {
        return None;
    };
    Some(destination.local)
}
