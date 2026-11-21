use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{
        Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{TyCtxt, TyKind},
};
use std::collections::{HashMap, HashSet};

use super::mir_utils::dep_callee_def_id;

/// Returns the [`Safety`] (`Safe`/`Unsafe`) of a function's signature.
pub fn get_fn_safety(tcx: TyCtxt<'_>, def_id: DefId) -> Safety {
    let poly_fn_sig = tcx.fn_sig(def_id);
    let fn_sig = poly_fn_sig.skip_binder();
    fn_sig.safety()
}

/// Helper checking if a [`Place`] involves raw pointer dereference.
pub(crate) fn place_has_raw_deref<'tcx>(body: &Body<'tcx>, place: &Place<'tcx>) -> bool {
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
                    if place_has_raw_deref(body, lhs) {
                        raw_ptrs.insert(lhs.local);
                    }
                    if let Rvalue::Use(op, ..) = rhs {
                        match op {
                            Operand::Copy(place) | Operand::Move(place)
                                if place_has_raw_deref(body, place) => {
                                    raw_ptrs.insert(place.local);
                                }
                            _ => {}
                        }
                    }
                    if let Rvalue::Ref(_, _, place) = rhs
                        && place_has_raw_deref(body, place) {
                            raw_ptrs.insert(place.local);
                        }
                }
            }
            if let Some(terminator) = &bb.terminator
                && let rustc_middle::mir::TerminatorKind::Call { args, .. } = &terminator.kind {
                    for arg in args {
                        match arg.node {
                            Operand::Copy(place) | Operand::Move(place)
                                if place_has_raw_deref(body, &place) => {
                                    raw_ptrs.insert(place.local);
                                }
                            _ => {}
                        }
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
                if let Rvalue::Use(Operand::Constant(c), ..) = rhs
                    && let Some(static_def_id) = c.check_static_ptr(tcx) {
                        globals.entry(static_def_id).or_default().push(lhs.local);
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
            if let TerminatorKind::Call { func, .. } = &bb.terminator().kind
                && let Some(callee_def_id) = dep_callee_def_id(func)
                    && get_fn_safety(tcx, callee_def_id) == Safety::Unsafe {
                        unsafe_callees.insert(callee_def_id);
                    }
        }
    }
    unsafe_callees
}
