use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, TyCtxt, TyKind},
};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};

use super::name::get_cleaned_def_path_name;

/// Stable MIR location for a call terminator inside one function body.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub struct CallsiteLocation {
    /// Function containing the call terminator.
    pub caller: DefId,
    /// Basic block whose terminator is the call.
    pub block: BasicBlock,
}

/// A concrete unsafe callsite in one MIR body.
#[derive(Clone, Debug)]
pub struct Callsite<'tcx> {
    /// Function containing this call.
    pub caller: DefId,
    /// Unsafe callee being invoked.
    pub callee: DefId,
    /// MIR block whose terminator is the call.
    pub block: BasicBlock,
    /// Source span attached to the MIR call terminator.
    pub span: Span,
    /// MIR operands passed to the callee.
    pub args: Vec<Operand<'tcx>>,
}

impl<'tcx> Callsite<'tcx> {
    /// Return the MIR location that identifies this callsite inside the verifier.
    pub fn location(&self) -> CallsiteLocation {
        CallsiteLocation {
            caller: self.caller,
            block: self.block,
        }
    }

    /// Return a stable human-readable callee path for diagnostics.
    pub fn callee_name(&self, tcx: TyCtxt<'tcx>) -> String {
        get_cleaned_def_path_name(tcx, self.callee)
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
                if let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind {
                    if place_has_raw_deref(tcx, &body, lhs) {
                        raw_ptrs.insert(lhs.local);
                    }
                    if let Rvalue::Use(op) = rhs {
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
            if let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind {
                if let Rvalue::Use(Operand::Constant(c)) = rhs {
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

/// Collect all unsafe MIR callsites in `def_id` with full per-callsite metadata.
pub fn collect_unsafe_callsites<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> Vec<Callsite<'tcx>> {
    let mut callsites = Vec::new();
    if !tcx.is_mir_available(def_id) {
        return callsites;
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

        let ty::FnDef(callee_def_id, _) = func_constant.const_.ty().kind() else {
            continue;
        };

        if check_safety(tcx, *callee_def_id) != Safety::Unsafe {
            continue;
        }

        callsites.push(Callsite {
            caller: def_id,
            callee: *callee_def_id,
            block: bb,
            span: *fn_span,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
        });
    }

    callsites
}
