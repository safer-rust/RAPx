use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, Ty, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

use super::name::get_cleaned_def_path_name;

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
    /// A raw pointer dereference.
    RawPtrDeref,
    /// A mutable static variable access.
    StaticMutAccess,
}

/// A verification checkpoint in one MIR body.
///
/// Unifies unsafe calls, raw-pointer dereferences, and mutable static
/// accesses under a single type so they all flow through the same path
/// extraction and SMT verification pipeline.
#[derive(Clone, Debug)]
pub struct Checkpoint<'tcx> {
    pub caller: DefId,
    pub callee: Option<DefId>,
    pub block: BasicBlock,
    pub span: Span,
    pub args: Vec<Operand<'tcx>>,
    pub kind: CheckpointKind,
    pub is_ref: bool,
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
                CheckpointKind::UnsafeCall => "unknown-callee".to_string(),
            },
        }
    }
}

/// Checks the safety of a function signature.
pub fn check_safety(tcx: TyCtxt<'_>, def_id: DefId) -> Safety {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety()
}

/// Helper checking if a [`Place`] involves raw pointer dereference.
pub fn place_has_raw_deref<'tcx>(
    _tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> bool {
    let local = place.local;
    for proj in place.projection.iter() {
        if let ProjectionElem::Deref = proj.kind() {
            let ty = body.local_decls[local].ty;
            if let TyKind::RawPtr(_, _) = ty.kind() {
                return true;
            }
        }
    }
    false
}

/// Analyzes the MIR of the given function to collect all local variables
/// that are involved in dereferencing raw pointers (`*const T` or `*mut T`).
pub fn get_rawptr_deref(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<Local> {
    let mut raw_ptrs = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (lhs, rhs) = &**assign;
                    if place_has_raw_deref(tcx, &body, lhs) {
                        raw_ptrs.insert(lhs.local);
                    }
                    if let Rvalue::Use(op, ..) = rhs {
                        match op {
                            Operand::Copy(place) | Operand::Move(place) => {
                                if place_has_raw_deref(tcx, &body, place) {
                                    raw_ptrs.insert(place.local);
                                }
                            }
                            _ => {}
                        }
                    }
                    if let Rvalue::Ref(_, _, place) = rhs {
                        if place_has_raw_deref(tcx, &body, place) {
                            raw_ptrs.insert(place.local);
                        }
                    }
                }
            }
            if let Some(terminator) = &bb.terminator {
                match &terminator.kind {
                    rustc_middle::mir::TerminatorKind::Call { args, .. } => {
                        for arg in args {
                            match arg.node {
                                Operand::Copy(place) | Operand::Move(place) => {
                                    if place_has_raw_deref(tcx, &body, &place) {
                                        raw_ptrs.insert(place.local);
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    raw_ptrs
}

/// Collects pairs of global static variables and their corresponding local variables
/// within a function's MIR that are assigned from statics.
pub fn collect_global_local_pairs(tcx: TyCtxt<'_>, def_id: DefId) -> HashMap<DefId, Vec<Local>> {
    let mut globals: HashMap<DefId, Vec<Local>> = HashMap::new();

    if !tcx.is_mir_available(def_id) {
        return globals;
    }

    let body = tcx.optimized_mir(def_id);

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (lhs, rhs) = &**assign;
                if let Rvalue::Use(Operand::Constant(c), ..) = rhs {
                    if let Some(static_def_id) = c.check_static_ptr(tcx) {
                        globals.entry(static_def_id).or_default().push(lhs.local);
                    }
                }
            }
        }
    }

    globals
}

/// Scans MIR for calls to unsafe functions and returns the set of callee DefIds.
pub fn get_unsafe_callees(tcx: TyCtxt<'_>, def_id: DefId) -> HashSet<DefId> {
    let mut unsafe_callees = HashSet::new();
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        for bb in body.basic_blocks.iter() {
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Operand::Constant(func_constant) = func {
                    if let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() {
                        if check_safety(tcx, *callee_def_id) == Safety::Unsafe {
                            unsafe_callees.insert(*callee_def_id);
                        }
                    }
                }
            }
        }
    }
    unsafe_callees
}

/// Collect all unsafe MIR checkpoints in `def_id` with full per-checkpoint metadata.
pub fn collect_unsafe_callsites<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Checkpoint<'tcx>> {
    let mut checkpoints = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return checkpoints;
    }

    let body = tcx.optimized_mir(def_id);
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func,
            args,
            fn_span,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };

        let Operand::Constant(func_constant) = func else {
            continue;
        };

        let ty::FnDef(callee_def_id, callee_args) = func_constant.const_.ty().kind() else {
            continue;
        };
        #[cfg(rapx_rustc_ge_199)]
        let callee_args = callee_args.skip_binder();

        if check_safety(tcx, *callee_def_id) != Safety::Unsafe {
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
            span: *fn_span,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
            kind: CheckpointKind::UnsafeCall,
            is_ref: false,
        });
    }

    checkpoints
}

/// Resolve a (possibly trait-method) callee to the concrete impl method that
/// will actually be dispatched, given the caller context and the callee's
/// generic arguments.
///
/// This matters for contract lookup: `#[rapx::requires(...)]` annotations are
/// attached to the impl method, but in a generic caller the MIR `FnDef` refers
/// to the trait method declaration.  Resolving to the impl method lets the
/// verifier find those inline contracts.  Returns `None` when the callee cannot
/// be resolved to a distinct concrete item (e.g. still generic/virtual), in
/// which case callers should keep the original DefId.
fn resolve_callee_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller_def_id: DefId,
    callee_def_id: DefId,
    callee_args: ty::GenericArgsRef<'tcx>,
) -> Option<DefId> {
    // Only trait-associated methods need remapping; inherent/free functions
    // already point at their concrete definition.
    let assoc = tcx.opt_associated_item(callee_def_id)?;
    if assoc.trait_container(tcx).is_none() {
        return None;
    }

    let typing_env = ty::TypingEnv::post_analysis(tcx, caller_def_id);
    let instance = ty::Instance::try_resolve(tcx, typing_env, callee_def_id, callee_args)
        .ok()
        .flatten()?;

    let resolved = match instance.def {
        ty::InstanceKind::Item(def_id) => def_id,
        _ => return None,
    };

    if resolved == callee_def_id {
        None
    } else {
        Some(resolved)
    }
}

/// Metadata for a single raw pointer dereference operation found in MIR.
#[derive(Clone, Debug)]
pub struct RawPtrDerefInfo<'tcx> {
    pub block: BasicBlock,
    pub ptr_operand: Operand<'tcx>,
    pub pointee_ty: Ty<'tcx>,
    pub is_read: bool,
    pub is_ref: bool,
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
    // Filter: only check statements from the function's own source file,
    // not from inlined library code (Vec, Box, etc.).
    let fn_span = tcx.def_span(def_id);
    let local_file = tcx.sess.source_map().lookup_char_pos(fn_span.lo()).file;

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let stmt_file = tcx.sess.source_map().lookup_char_pos(stmt.source_info.span.lo()).file;
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

            let is_write = place_has_raw_deref(tcx, &body, lhs);
            let (is_read, is_ref) = match rhs {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) => {
                    (place_has_raw_deref(tcx, &body, place), false)
                }
                Rvalue::Ref(_, _, place) => (place_has_raw_deref(tcx, &body, place), true),
                _ => (false, false),
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

            let Some(ptr_operand) = ptr_operand_for_deref_place(deref_place) else {
                continue;
            };

            let Some(pointee_ty) = deref_place_pointee_ty(&body, deref_place) else {
                continue;
            };

            infos.push(RawPtrDerefInfo {
                block: bb,
                ptr_operand,
                pointee_ty,
                is_read,
                is_ref,
            });
        }
    }

    infos
}

/// Return the pointee type of the raw pointer being dereferenced.
fn deref_place_pointee_ty<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> Option<Ty<'tcx>> {
    let ty = body.local_decls[place.local].ty;
    match ty.kind() {
        TyKind::RawPtr(inner, _) => Some(*inner),
        _ => None,
    }
}

/// Extract the pointer operand from a dereference place.
fn ptr_operand_for_deref_place<'tcx>(place: &Place<'tcx>) -> Option<Operand<'tcx>> {
    use rustc_middle::ty::List;

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
    /// The mutable static being accessed.
    pub static_def_id: DefId,
    /// The pointee type (i.e. the type of the static itself, `T` in `static mut X: T`).
    pub ty: Ty<'tcx>,
    /// The MIR operand holding the pointer to the static.
    pub ptr_operand: Operand<'tcx>,
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
        for stmt in &data.statements {
            if let StatementKind::Assign(assign) = &stmt.kind {
                let (_lhs, rhs) = &**assign;
                if let Rvalue::Use(op @ Operand::Constant(c), ..) = rhs {
                    if let Some(static_id) = c.check_static_ptr(tcx) {
                        if matches!(tcx.static_mutability(static_id), Some(m) if m.is_mut()) {
                            let ty = tcx.type_of(static_id).skip_binder();
                            infos.push(StaticMutAccessInfo {
                                block: bb,
                                static_def_id: static_id,
                                ty,
                                ptr_operand: op.clone(),
                            });
                        }
                    }
                }
            }
        }

        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { args, .. } = &terminator.kind {
                for arg in args {
                    match &arg.node {
                        op @ Operand::Constant(c) => {
                            if let Some(static_id) = c.check_static_ptr(tcx) {
                                if matches!(tcx.static_mutability(static_id), Some(m) if m.is_mut())
                                {
                                    let ty = tcx.type_of(static_id).skip_binder();
                                    infos.push(StaticMutAccessInfo {
                                        block: bb,
                                        static_def_id: static_id,
                                        ty,
                                        ptr_operand: op.clone(),
                                    });
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    infos
}
