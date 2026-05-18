//! Unsafe callsite discovery for the new verifier pipeline.
//!
//! This module records concrete MIR callsites instead of only collecting unique
//! callee `DefId`s.  Path extraction and later verification stages need the
//! caller block, call span, callee, and operands for each unsafe call.

use rustc_hir::{Safety, def_id::DefId};
use rustc_middle::{
    mir::{BasicBlock, Operand, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::Span;

use super::helpers::{check_safety, get_cleaned_def_path_name};

/// A concrete unsafe callsite in one MIR body.
#[derive(Clone, Debug)]
pub struct UnsafeCallsite<'tcx> {
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

impl<'tcx> UnsafeCallsite<'tcx> {
    /// Return a stable human-readable callee path for diagnostics.
    pub fn callee_name(&self, tcx: TyCtxt<'tcx>) -> String {
        get_cleaned_def_path_name(tcx, self.callee)
    }
}

/// Collect all unsafe MIR callsites in `def_id`.
pub fn collect_unsafe_callsites<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<UnsafeCallsite<'tcx>> {
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

        callsites.push(UnsafeCallsite {
            caller: def_id,
            callee: *callee_def_id,
            block: bb,
            span: *fn_span,
            args: args.iter().map(|arg| arg.node.clone()).collect(),
        });
    }

    callsites
}
