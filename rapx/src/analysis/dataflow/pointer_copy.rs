//! Source and destination arguments of pointer-copy calls.

use crate::compat::MirTerminatorExt as _;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Body, Operand, StatementKind, TerminatorKind},
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::def_ids::{diagnostic_api, intrinsic_api};
use crate::util::mir_utils::dep_callee_def_id;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct CopyFlow {
    pub source_arg: usize,
    pub destination_arg: usize,
}

/// The fixed argument flow of compiler and standard-library copy functions.
pub(crate) fn direct_copy_flow(tcx: TyCtxt<'_>, callee: DefId) -> Option<CopyFlow> {
    (intrinsic_api::is_ptr_copy(tcx, callee) || diagnostic_api::is_ptr_copy(tcx, callee)).then_some(CopyFlow {
        source_arg: 0,
        destination_arg: 1,
    })
}

/// Copy flow at this callee, including wrappers whose source and destination
/// are recovered from optimized MIR.
pub(crate) fn copy_flow(tcx: TyCtxt<'_>, callee: DefId) -> Option<CopyFlow> {
    direct_copy_flow(tcx, callee).or_else(|| mir_copy_flow(tcx, callee))
}

fn mir_copy_flow(tcx: TyCtxt<'_>, callee: DefId) -> Option<CopyFlow> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn)
        || !tcx.is_mir_available(callee)
    {
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
            &block.rapx_terminator().kind
            && let Some(id) = dep_callee_def_id(func)
            && direct_copy_flow(tcx, id).is_some()
            && let [src, dst, count] = &args[..]
        {
            record_copy_args(body, &src.node, &dst.node, &count.node, &mut copy_args)?;
        }
    }
    let flow: CopyFlow = copy_args?;
    let inputs = [first, second];
    matches!(
        inputs[flow.destination_arg].kind(),
        TyKind::RawPtr(_, Mutability::Mut)
    )
    .then_some(flow)
}

fn record_copy_args(
    body: &Body<'_>,
    src: &Operand<'_>,
    dst: &Operand<'_>,
    count: &Operand<'_>,
    result: &mut Option<CopyFlow>,
) -> Option<()> {
    let source = argument_index(body, src)?;
    let destination = argument_index(body, dst)?;
    if source >= 2 || destination >= 2 || source == destination || argument_index(body, count)? != 2
    {
        return None;
    }
    let candidate = CopyFlow {
        source_arg: source,
        destination_arg: destination,
    };
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
