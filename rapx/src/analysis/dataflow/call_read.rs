//! Trace returned values read through raw pointers to call arguments.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Operand, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind},
    ty::{TyCtxt, TyKind},
};

use crate::def_ids::diagnostic_api;

use super::pointer_flow;

/// Argument supplying the pointer read to produce the return value.
pub(crate) fn read_source_arg(tcx: TyCtxt<'_>, callee: DefId) -> Option<usize> {
    if diagnostic_api::is_ptr_read(tcx, callee) {
        return Some(0);
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    let mut source = None;
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (destination, value) = &**assign;
            if destination.local != RETURN_PLACE || !destination.projection.is_empty() {
                continue;
            }
            let Rvalue::Use(Operand::Copy(place), _) = value else {
                return None;
            };
            if !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                || !matches!(body.local_decls[place.local].ty.kind(), TyKind::RawPtr(..))
            {
                return None;
            }
            let candidate =
                pointer_flow::trace_source_arg(tcx, body, place.local, &mut HashSet::new(), 5)?;
            if source.is_some_and(|previous| previous != candidate) {
                return None;
            }
            source = Some(candidate);
        }
    }
    source
}
