//! Source and destination arguments of standard raw-pointer copy methods.

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Operand, StatementKind, TerminatorKind},
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::def_ids::{diagnostic_api, intrinsic_api};
use crate::helpers::mir_utils::dep_callee_def_id;

/// Derive `(source, destination)` from the copy operation in a standard
/// raw-pointer method's optimized MIR. The indices refer to method arguments,
/// including `self` at index zero.
pub(crate) fn std_raw_ptr_copy_args(tcx: TyCtxt<'_>, callee: DefId) -> Option<(usize, usize)> {
    if !matches!(tcx.crate_name(callee.krate).as_str(), "core" | "std")
        || !matches!(tcx.def_kind(callee), DefKind::AssocFn)
        || !tcx.is_mir_available(callee)
    {
        return None;
    }
    let impl_id = tcx.inherent_impl_of_assoc(callee)?;
    let self_ty = tcx.type_of(impl_id).instantiate_identity().skip_norm_wip();
    if !matches!(self_ty.kind(), TyKind::RawPtr(..)) {
        return None;
    }
    let sig = tcx.fn_sig(callee).skip_binder();
    let [first, second, count] = sig.inputs().skip_binder() else {
        return None;
    };
    let (TyKind::RawPtr(first_pointee, _), TyKind::RawPtr(second_pointee, _)) =
        (first.kind(), second.kind())
    else {
        return None;
    };
    if first_pointee != second_pointee
        || *count != tcx.types.usize
        || sig.output().skip_binder() != tcx.types.unit
    {
        return None;
    }

    let body = tcx.optimized_mir(callee);
    let mut copy_args = None;
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            if let StatementKind::Intrinsic(intrinsic) = &statement.kind
                && let rustc_middle::mir::NonDivergingIntrinsic::CopyNonOverlapping(copy) =
                    &**intrinsic
            {
                record_copy_args(body, &copy.src, &copy.dst, &copy.count, &mut copy_args)?;
            }
        }
        if let TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } =
            &block.terminator().kind
            && let Some(id) = dep_callee_def_id(func)
            && (diagnostic_api::is_ptr_copy(tcx, id)
                || intrinsic_api::intrinsic_name(tcx, Some(id))
                    .is_some_and(|name| matches!(name.as_str(), "copy" | "copy_nonoverlapping")))
            && let [src, dst, count] = &args[..]
        {
            record_copy_args(body, &src.node, &dst.node, &count.node, &mut copy_args)?;
        }
    }
    let (source, destination) = copy_args?;
    let inputs = [first, second];
    matches!(
        inputs[destination].kind(),
        TyKind::RawPtr(_, Mutability::Mut)
    )
    .then_some((source, destination))
}

fn record_copy_args(
    body: &Body<'_>,
    src: &Operand<'_>,
    dst: &Operand<'_>,
    count: &Operand<'_>,
    result: &mut Option<(usize, usize)>,
) -> Option<()> {
    let source = argument_index(body, src)?;
    let destination = argument_index(body, dst)?;
    if source >= 2 || destination >= 2 || source == destination || argument_index(body, count)? != 2
    {
        return None;
    }
    let candidate = (source, destination);
    if result.is_some_and(|previous| previous != candidate) {
        return None;
    }
    *result = Some(candidate);
    Some(())
}

fn argument_index(body: &Body<'_>, operand: &Operand<'_>) -> Option<usize> {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() {
        return None;
    }
    let local = place.local.as_usize();
    (local > 0 && local <= body.arg_count).then_some(local - 1)
}
