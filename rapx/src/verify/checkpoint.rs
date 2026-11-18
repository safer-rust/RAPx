//! Verification checkpoint types and their MIR collection.
//!
//! A [`Checkpoint`] is a point in a function body that must be verified: an
//! unsafe call, a MIR intrinsic, a raw-pointer dereference, or a `static mut` access.  The
//! `collect_*` functions scan MIR and attach safety requirements; the rest of
//! the verifier consumes the resulting records.

use crate::def_ids::intrinsic_api;
#[cfg(not(rapx_box_deref_transmute))]
use crate::def_ids::lang_api::{self, LangItem};
use crate::helpers::{
    mir_scan::{get_fn_safety, place_has_raw_deref},
    mir_utils::pointee_ty,
    name::get_cleaned_def_path_name,
};

use rustc_hir::{def_id::DefId, Safety};
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, NonDivergingIntrinsic, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{self, List, Ty, TyCtxt},
};
#[cfg(rapx_box_deref_transmute)]
use rustc_middle::mir::CastKind;
#[cfg(not(rapx_box_deref_transmute))]
use rustc_middle::ty::TyKind;
use std::collections::HashSet;

use super::contract::{
    ContractExpr, ContractKind, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind,
};

/// MIR block containing a verification checkpoint.
///
/// # Agent Rules
/// Do not add new fields to this struct.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct CheckpointLocation {
    /// Function containing the operation.
    pub caller: DefId,
    /// Basic block containing the operation.
    pub block: BasicBlock,
}

/// Kind of an unsafe verification checkpoint inside a function body.
///
/// # Agent Rules
/// Do not add new variants to this enum.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum CheckpointKind {
    /// An unsafe call, including one lowered to a MIR intrinsic statement.
    UnsafeCall,
    /// A raw pointer dereference.
    RawPtrDeref,
    /// A mutable static variable access.
    StaticMutAccess,
}

/// A point in a function's MIR whose safety requirements are checked.
///
/// Most checkpoints are unsafe function calls. Calls lowered to MIR intrinsics,
/// raw-pointer dereferences, and `static mut` accesses use the same representation
/// and follow the same path extraction and verification pipeline.
///
/// # Agent Rules
/// Do not add new fields to this struct.
#[derive(Clone, Debug)]
pub(crate) struct Checkpoint<'tcx> {
    // Function and operation data.
    pub(super) caller: DefId,
    pub(super) callee: Option<DefId>,
    pub(super) args: Vec<Operand<'tcx>>,
    /// Local produced by this operation, if any.
    pub(super) destination: Option<Local>,

    // Position in the caller's MIR.
    pub(super) block: BasicBlock,
    /// Position of this checkpoint within the MIR block.
    pub(super) statement_index: usize,

    // Verification semantics.
    pub(super) kind: CheckpointKind,
    /// Requirements attached directly to this MIR operation.
    pub(super) requires: Vec<Property<'tcx>>,

    // Variant-specific metadata.
    /// For `RawPtrDeref` checkpoints: whether the deref produces a mutable
    /// reference (`&mut *ptr`) rather than a shared one (`&*ptr`).
    pub(super) is_mut_ref: bool,
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
        match self.callee {
            Some(def_id) => get_cleaned_def_path_name(tcx, def_id),
            None => match self.kind {
                CheckpointKind::RawPtrDeref => "raw-ptr-deref".to_string(),
                CheckpointKind::StaticMutAccess => "static-mut-access".to_string(),
                CheckpointKind::UnsafeCall => {
                    let body = tcx.optimized_mir(self.caller);
                    match body.basic_blocks[self.block]
                        .statements
                        .get(self.statement_index)
                        .map(|statement| &statement.kind)
                    {
                        Some(StatementKind::Intrinsic(intrinsic)) => {
                            intrinsic_api::lowered_mir_path(intrinsic).to_string()
                        }
                        _ => "unknown-callee".to_string(),
                    }
                }
            },
        }
    }
}

/// Collect unsafe calls in `def_id`'s optimized MIR as verification checkpoints.
///
/// This includes unsafe `Call` and `TailCall` terminators and calls to `assume`
/// or `copy_nonoverlapping` that rustc lowered to intrinsic statements. A direct
/// call records its `DefId`; an unsafe function-pointer call has no known callee
/// and records `None`. Each checkpoint retains the call arguments and MIR position
/// for later contract lookup and path analysis. Functions without MIR yield no
/// checkpoints. Raw-pointer dereferences and `static mut` accesses are collected
/// separately.
pub fn collect_unsafe_callsites<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Checkpoint<'tcx>> {
    let mut checkpoints = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return checkpoints;
    }

    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            if let StatementKind::Intrinsic(intrinsic) = &statement.kind {
                let args = match &**intrinsic {
                    NonDivergingIntrinsic::CopyNonOverlapping(copy) => {
                        vec![copy.src.clone(), copy.dst.clone(), copy.count.clone()]
                    }
                    NonDivergingIntrinsic::Assume(condition) => vec![condition.clone()],
                };
                checkpoints.push(Checkpoint {
                    caller: def_id,
                    callee: intrinsic_api::lowered_mir_def_id(tcx, intrinsic),
                    block: bb,
                    args,
                    kind: CheckpointKind::UnsafeCall,
                    requires: Vec::new(),
                    destination: None,
                    is_mut_ref: false,
                    statement_index,
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
            Operand::RuntimeChecks(_) => continue,
        };
        let ty::FnDef(callee_def_id, _) = func_ty.kind() else {
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
                    statement_index: data.statements.len(),
                });
            }
            continue;
        };
        if get_fn_safety(tcx, *callee_def_id) != Safety::Unsafe {
            continue;
        }

        checkpoints.push(Checkpoint {
            caller: def_id,
            callee: Some(*callee_def_id),
            block: bb,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
            kind: CheckpointKind::UnsafeCall,
            requires: Vec::new(),
            destination,
            is_mut_ref: false,
            statement_index: data.statements.len(),
        });
    }

    checkpoints
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

/// Collect raw pointer dereferences and their safety requirements.
pub fn collect_raw_ptr_deref_checkpoints<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Checkpoint<'tcx>> {
    let mut checkpoints = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return checkpoints;
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
                Rvalue::Ref(_, borrow_kind, place) => {
                    let reads_raw_ptr = place_has_raw_deref(body, place);
                    (
                        reads_raw_ptr,
                        reads_raw_ptr,
                        reads_raw_ptr
                            && matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }),
                    )
                }
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

            checkpoints.push(Checkpoint {
                caller: def_id,
                callee: None,
                block: bb,
                args: vec![ptr_operand],
                kind: CheckpointKind::RawPtrDeref,
                requires: raw_ptr_deref_requirements(pointee, is_read, is_ptr2ref),
                is_mut_ref,
                destination: (!is_write).then_some(lhs.local),
                statement_index: stmt_index,
            });
        }
    }

    checkpoints
}

fn raw_ptr_deref_requirements<'tcx>(
    pointee: Ty<'tcx>,
    is_read: bool,
    is_ptr2ref: bool,
) -> Vec<Property<'tcx>> {
    let target = PropertyArg::Expr(ContractExpr::Place(ContractPlace {
        base: PlaceBase::Arg(0),
        projections: vec![],
    }));
    let ty = PropertyArg::Ty(pointee);
    let count = PropertyArg::Expr(ContractExpr::Const(1));

    let mut properties = if is_ptr2ref {
        vec![
            Property::new_atom(
                PropertyKind::Init,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(PropertyKind::NonNull, vec![target.clone()]),
            Property::new_atom(
                PropertyKind::Allocated,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(
                PropertyKind::InBound,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
            {
                let mut property = Property::new_atom(PropertyKind::Alias, vec![target.clone()]);
                property.set_contract_kind(ContractKind::Hazard);
                property
            },
        ]
    } else {
        vec![
            Property::new_atom(
                PropertyKind::Allocated,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(
                PropertyKind::InBound,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
        ]
    };
    if is_read && !is_ptr2ref {
        properties.push(Property::new_atom(PropertyKind::Typed, vec![target, ty]));
    }
    properties
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

/// Collect checkpoints for mutable static accesses in `def_id`.
///
/// Mutable statics appear as `Constant` operands whose `check_static_ptr` points
/// to a `static mut` item.  Both reads and writes are detected here; the
/// conservative `Init` property will be checked regardless of direction.
pub fn collect_static_mut_checkpoints<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<Checkpoint<'tcx>> {
    let mut checkpoints = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return checkpoints;
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
                    checkpoints.push(static_mut_checkpoint(
                        tcx, def_id, bb, statement_index, op.clone(), static_id,
                    ));
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
                    checkpoints.push(static_mut_checkpoint(
                        tcx, def_id, bb, data.statements.len(), op.clone(), static_id,
                    ));
                }
            }
        }
    }

    checkpoints
}

fn static_mut_checkpoint<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    block: BasicBlock,
    statement_index: usize,
    operand: Operand<'tcx>,
    static_id: DefId,
) -> Checkpoint<'tcx> {
    let ty = PropertyArg::Ty(tcx.type_of(static_id).skip_binder());
    let target = PropertyArg::Expr(ContractExpr::Place(ContractPlace {
        base: PlaceBase::Arg(0),
        projections: vec![],
    }));
    let count = PropertyArg::Expr(ContractExpr::Const(1));
    Checkpoint {
        caller,
        callee: None,
        args: vec![operand],
        destination: None,
        block,
        statement_index,
        kind: CheckpointKind::StaticMutAccess,
        requires: vec![
            Property::new_atom(
                PropertyKind::Allocated,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(
                PropertyKind::InBound,
                vec![target.clone(), ty.clone(), count.clone()],
            ),
            Property::new_atom(PropertyKind::Align, vec![target.clone(), ty.clone()]),
            Property::new_atom(PropertyKind::Init, vec![target, ty, count]),
        ],
        is_mut_ref: false,
    }
}
