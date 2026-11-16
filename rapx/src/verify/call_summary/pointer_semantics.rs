//! VM rules for pointer-preserving calls and owner lifetimes.

use std::collections::HashMap;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand, ProjectionElem, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};

use crate::analysis::dataflow::pointer_flow::{is_nonnull_view, return_source_arg};
use crate::helpers::mir_utils;

/// Whether MIR shows a read-only pointer view of the first argument.
pub(crate) fn is_benign_origin_use(tcx: TyCtxt<'_>, callee: Option<DefId>) -> bool {
    callee.is_some_and(|did| is_read_only_return(tcx, did) || is_read_only_nonnull_view(tcx, did))
}

/// A `NonNull` view that leaves its input allocation unchanged.
pub(crate) fn is_read_only_nonnull_view(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    is_nonnull_view(tcx, callee) && single_block_without_effects(tcx.optimized_mir(callee))
}

/// A pointer result from a single, side-effect-free MIR block is safe to use
/// while tracking an existing pointer origin.
pub(crate) fn is_read_only_return(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    if return_source_arg(tcx, callee) != Some(0) {
        return false;
    }
    let inputs = tcx.fn_sig(callee).skip_binder().inputs().skip_binder();
    if !inputs
        .first()
        .is_some_and(|ty| mir_utils::pointee_ty(*ty).is_some())
    {
        return false;
    }
    single_block_without_effects(tcx.optimized_mir(callee))
}

/// A consumed owner remains allocated when a side-effect-free MIR body
/// returns its pointer without running a destructor.
pub(crate) fn returns_undropped_arg(tcx: TyCtxt<'_>, callee: DefId, arg: usize) -> bool {
    return_source_arg(tcx, callee) == Some(arg)
        && single_block_without_effects(tcx.optimized_mir(callee))
}

/// A single return block with no writes through a dereferenced place.
pub(crate) fn single_block_without_effects(body: &Body<'_>) -> bool {
    let [block] = &body.basic_blocks[..] else {
        return false;
    };
    matches!(block.terminator().kind, TerminatorKind::Return)
        && block.statements.iter().all(|stmt| match &stmt.kind {
            StatementKind::Assign(assign) => !assign
                .0
                .projection
                .iter()
                .any(|p| matches!(p, rustc_middle::mir::ProjectionElem::Deref)),
            StatementKind::StorageLive(_) | StatementKind::StorageDead(_) | StatementKind::Nop => {
                true
            }
            _ => false,
        })
}

/// Whether a callee can replace a pointer stored in one of its objects.
/// This follows MIR calls rather than identifying container methods by name.
pub(crate) fn callsite_replaces_pointer_field(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(callee) = mir_utils::dep_callee_def_id(func) else {
        return false;
    };
    replaces_pointer_field_rec(tcx, callee, 0, &mut HashMap::new())
}

fn replaces_pointer_field_rec(
    tcx: TyCtxt<'_>,
    callee: DefId,
    depth: usize,
    visited: &mut HashMap<DefId, usize>,
) -> bool {
    if depth > 10
        || !tcx.is_mir_available(callee)
        || visited
            .get(&callee)
            .is_some_and(|&previous| previous <= depth)
    {
        return false;
    }
    visited.insert(callee, depth);
    let body = tcx.optimized_mir(callee);
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let place = assign.0;
            if place.projection.first() == Some(&ProjectionElem::Deref)
                && place
                    .projection
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::Field(..)))
                && is_pointer_storage_ty(tcx, place.ty(body, tcx).ty, 0)
            {
                return true;
            }
        }
        if let Some(terminator) = &block.terminator
            && let TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } =
                &terminator.kind
            && let Some(nested) = mir_utils::dep_callee_def_id(func)
            && replaces_pointer_field_rec(tcx, nested, depth + 1, visited)
        {
            return true;
        }
    }
    false
}

fn is_pointer_storage_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>, depth: usize) -> bool {
    match ty.kind() {
        TyKind::RawPtr(..) => true,
        TyKind::Pat(inner, _) => is_pointer_storage_ty(tcx, *inner, depth + 1),
        TyKind::Adt(adt, args) if depth < 2 && adt.repr().transparent() && !adt.is_enum() => {
            adt.non_enum_variant().fields.iter().any(|field| {
                is_pointer_storage_ty(tcx, mir_utils::field_ty(tcx, field, args), depth + 1)
            })
        }
        _ => false,
    }
}
