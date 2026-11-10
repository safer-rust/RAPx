//! Trace a raw pointer returned by MIR back to a function argument.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Local, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};
#[cfg(rapx_box_deref_transmute)]
use rustc_middle::mir::CastKind;

use crate::helpers::mir_utils;

pub(crate) fn return_source_arg(tcx: TyCtxt<'_>, callee: DefId) -> Option<usize> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    let result = rustc_middle::mir::RETURN_PLACE;
    if !matches!(body.local_decls[result].ty.kind(), TyKind::RawPtr(..)) {
        return None;
    }
    trace_source_arg(tcx, body, result, &mut HashSet::new(), 5)
}

/// A pointer result from a single, side-effect-free MIR block is safe to use
/// while tracking an existing pointer origin.
pub(crate) fn is_read_only_return(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if return_source_arg(tcx, callee) != Some(0) {
        return false;
    }
    let inputs = tcx.fn_sig(callee).skip_binder().inputs().skip_binder();
    if !inputs.first().is_some_and(|ty| mir_utils::pointee_ty(*ty).is_some()) {
        return false;
    }
    let body = tcx.optimized_mir(callee);
    let [block] = &body.basic_blocks[..] else {
        return false;
    };
    matches!(block.terminator().kind, TerminatorKind::Return)
        && block.statements.iter().all(|stmt| match &stmt.kind {
            StatementKind::Assign(assign) => !assign.0.projection.iter().any(|p| {
                matches!(p, rustc_middle::mir::ProjectionElem::Deref)
            }),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => true,
            _ => false,
        })
}

/// Follow pointer-preserving MIR values through fields and calls to an input.
pub(crate) fn trace_source_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    seen: &mut HashSet<Local>,
    depth: usize,
) -> Option<usize> {
    if !seen.insert(local) {
        return None;
    }
    let index = local.as_usize();
    if index > 0 && index <= body.arg_count {
        return Some(index - 1);
    }
    let mut source = None;
    for data in body.basic_blocks.iter() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (dest, value) = &**assign;
            if dest.local != local || !dest.projection.is_empty() {
                continue;
            }
            let candidate = match value {
                Rvalue::Use(operand, _) => mir_utils::operand_mir_place(operand).and_then(|place| {
                    trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
                }),
                #[cfg(rapx_box_deref_transmute)]
                Rvalue::Cast(CastKind::BoxDerefTransmute, operand, _) =>
                    mir_utils::operand_mir_place(operand).and_then(|place| {
                        trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
                    }),
                Rvalue::Cast(_, operand, _) => mir_utils::operand_mir_place(operand)
                    .filter(|place| mir_utils::pointee_ty(place.ty(body, tcx).ty).is_some())
                    .and_then(|place| {
                        trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
                    }),
                Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                    trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
                }
                Rvalue::Aggregate(kind, operands)
                    if matches!(&**kind, rustc_middle::mir::AggregateKind::RawPtr(..)) =>
                {
                    operands.iter().next()
                        .and_then(mir_utils::operand_mir_place)
                        .and_then(|place| {
                            trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
                        })
                }
                _ => None,
            }?;
            if source.is_some_and(|old| old != candidate) {
                return None;
            }
            source = Some(candidate);
        }
    }
    if depth > 0 {
        for data in body.basic_blocks.iter() {
            let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind else {
                continue;
            };
            if destination.local != local || !destination.projection.is_empty() {
                continue;
            }
            let callee = mir_utils::dep_callee_def_id(func)?;
            let arg_index = return_source_arg_with_depth(tcx, callee, depth - 1)?;
            let arg = args.get(arg_index)?;
            let candidate = mir_utils::operand_mir_place(&arg.node).and_then(|place| {
                trace_source_arg(tcx, body, place.local, &mut seen.clone(), depth)
            })?;
            if source.is_some_and(|old| old != candidate) {
                return None;
            }
            source = Some(candidate);
        }
    }
    source
}

fn return_source_arg_with_depth(tcx: TyCtxt<'_>, callee: DefId, depth: usize) -> Option<usize> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    let result = rustc_middle::mir::RETURN_PLACE;
    trace_source_arg(tcx, body, result, &mut HashSet::new(), depth)
}
