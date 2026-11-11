//! Trace a raw pointer returned by MIR back to a function argument.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind, TypingEnv},
};
#[cfg(rapx_box_deref_transmute)]
use rustc_middle::mir::CastKind;

use crate::helpers::mir_utils;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PointerOffsetDirection {
    Forward,
    Backward,
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct PointerOffset {
    base: usize,
    count: Option<usize>,
    direction: PointerOffsetDirection,
}

/// Infer the direction of a pointer offset from optimized MIR, including
/// wrappers around `Offset` and the `arith_offset` intrinsic.
pub(crate) fn pointer_offset_direction(
    tcx: TyCtxt<'_>,
    callee: DefId,
) -> Option<PointerOffsetDirection> {
    let offset = pointer_offset(tcx, callee, 6)?;
    (offset.base == 0 && offset.count == Some(1)).then_some(offset.direction)
}

fn pointer_offset(tcx: TyCtxt<'_>, callee: DefId, depth: usize) -> Option<PointerOffset> {
    if depth == 0 || !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    let pointee = body
        .local_decls
        .get(Local::from_usize(1))
        .and_then(|decl| mir_utils::pointee_ty(decl.ty));
    let mut has_zst_switch = false;
    let only_zst_switches = body.basic_blocks.iter().all(|block| {
        let TerminatorKind::SwitchInt { discr, .. } = &block.terminator().kind else {
            return true;
        };
        has_zst_switch = true;
        zst_property_operand(tcx, body, discr, pointee)
    });
    let zst_branch = has_zst_switch && only_zst_switches;
    trace_pointer_offset(
        tcx,
        body,
        rustc_middle::mir::RETURN_PLACE,
        depth,
        zst_branch,
        &mut HashSet::new(),
    )
}

fn trace_pointer_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
    depth: usize,
    zst_branch: bool,
    seen: &mut HashSet<Local>,
) -> Option<PointerOffset> {
    if !seen.insert(local) {
        return None;
    }
    let index = local.as_usize();
    if index > 0 && index <= body.arg_count {
        return Some(PointerOffset {
            base: index - 1,
            count: None,
            direction: PointerOffsetDirection::Forward,
        });
    }
    let mut result = None;
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = &**assign;
            if dest.local != local || !dest.projection.is_empty() {
                continue;
            }
            let candidate = match rvalue {
                Rvalue::Use(op, _) | Rvalue::Cast(_, op, _) => {
                    let source = mir_utils::operand_mir_place(op)?;
                    trace_pointer_offset(
                        tcx, body, source.local, depth, zst_branch, &mut seen.clone(),
                    )?
                }
                Rvalue::BinaryOp(BinOp::Offset, operands) => {
                    let base = mir_utils::operand_mir_place(&operands.0)?;
                    let base = trace_pointer_offset(
                        tcx, body, base.local, depth, zst_branch, &mut seen.clone(),
                    )?;
                    if base.count.is_some() {
                        return None;
                    }
                    let (count, backward) =
                        trace_offset_count(tcx, body, &operands.1, &mut HashSet::new())?;
                    PointerOffset {
                        base: base.base,
                        count: Some(count),
                        direction: if backward {
                            PointerOffsetDirection::Backward
                        } else {
                            PointerOffsetDirection::Forward
                        },
                    }
                }
                Rvalue::Aggregate(kind, operands)
                    if operands.len() == 1
                        || matches!(&**kind, rustc_middle::mir::AggregateKind::RawPtr(..)) =>
                {
                    let source = mir_utils::operand_mir_place(operands.iter().next()?)?;
                    trace_pointer_offset(
                        tcx, body, source.local, depth, zst_branch, &mut seen.clone(),
                    )?
                }
                _ => return None,
            };
            result = Some(merge_pointer_offsets(result, candidate, zst_branch)?);
        }
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &block.terminator().kind
        else {
            continue;
        };
        if destination.local != local || !destination.projection.is_empty() {
            continue;
        }
        let callee = mir_utils::dep_callee_def_id(func)?;
        let intrinsic = tcx
            .intrinsic(callee)
            .map(|i| i.name.as_str() == "arith_offset")
            .unwrap_or(false);
        let nested = if intrinsic {
            PointerOffset {
                base: 0,
                count: Some(1),
                direction: PointerOffsetDirection::Forward,
            }
        } else {
            pointer_offset(tcx, callee, depth - 1)?
        };
        let base_arg = args.get(nested.base)?;
        let base_place = mir_utils::operand_mir_place(&base_arg.node)?;
        let base = trace_pointer_offset(
            tcx, body, base_place.local, depth, zst_branch, &mut seen.clone(),
        )?;
        if base.count.is_some() {
            return None;
        }
        let candidate = if let Some(count_index) = nested.count {
            let (count, negative) =
                trace_offset_count(tcx, body, &args.get(count_index)?.node, &mut HashSet::new())?;
            PointerOffset {
                base: base.base,
                count: Some(count),
                direction: if negative == (nested.direction == PointerOffsetDirection::Backward) {
                    PointerOffsetDirection::Forward
                } else {
                    PointerOffsetDirection::Backward
                },
            }
        } else {
            base
        };
        result = Some(merge_pointer_offsets(result, candidate, zst_branch)?);
    }
    result
}

fn zst_property_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    pointee: Option<rustc_middle::ty::Ty<'tcx>>,
) -> bool {
    let Some(pointee) = pointee else {
        return false;
    };
    let constant = match operand {
        Operand::Constant(constant) => Some(constant),
        Operand::Copy(place) | Operand::Move(place) => {
            let mut found = None;
            for stmt in body.basic_blocks.iter().flat_map(|block| &block.statements) {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                if assign.0.local != place.local {
                    continue;
                }
                let Rvalue::Use(Operand::Constant(value), _) = &assign.1 else {
                    return false;
                };
                if found.replace(value).is_some() {
                    return false;
                }
            }
            found
        }
        #[cfg(rapx_ge_95)]
        Operand::RuntimeChecks(_) => None,
    };
    let Some(constant) = constant else {
        return false;
    };
    let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_ else {
        return false;
    };
    mir_utils::is_sized_type_property(tcx, uneval.def, "IS_ZST")
        && uneval.args.types().next() == Some(pointee)
}

fn merge_pointer_offsets(
    current: Option<PointerOffset>,
    next: PointerOffset,
    zst_branch: bool,
) -> Option<PointerOffset> {
    match current {
        None => Some(next),
        Some(old) if old == next => Some(old),
        Some(old) if zst_branch && old.base == next.base && old.count.is_none() => Some(next),
        Some(old) if zst_branch && old.base == next.base && next.count.is_none() => Some(old),
        _ => None,
    }
}

fn trace_offset_count<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
    seen: &mut HashSet<Local>,
) -> Option<(usize, bool)> {
    let place = mir_utils::operand_mir_place(operand)?;
    let local = place.local;
    if !seen.insert(local) {
        return None;
    }
    let index = local.as_usize();
    if index > 0 && index <= body.arg_count {
        return Some((index - 1, false));
    }
    let mut result = None;
    for block in body.basic_blocks.iter() {
        for stmt in &block.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            if assign.0.local != local || !assign.0.projection.is_empty() {
                continue;
            }
            let candidate = match &assign.1 {
                Rvalue::Use(op, _) | Rvalue::Cast(_, op, _) => {
                    trace_offset_count(tcx, body, op, &mut seen.clone())?
                }
                Rvalue::BinaryOp(BinOp::Sub | BinOp::SubUnchecked, operands)
                    if is_zero_constant(tcx, &operands.0) =>
                {
                    let (arg, neg) = trace_offset_count(tcx, body, &operands.1, &mut seen.clone())?;
                    (arg, !neg)
                }
                _ => return None,
            };
            if result.is_some_and(|old| old != candidate) {
                return None;
            }
            result = Some(candidate);
        }
    }
    result
}

fn is_zero_constant<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>) -> bool {
    let Operand::Constant(c) = operand else {
        return false;
    };
    c.const_
        .eval(tcx, TypingEnv::fully_monomorphized(), rustc_span::DUMMY_SP)
        .ok()
        .and_then(|value| value.try_to_scalar_int())
        .is_some_and(|scalar| scalar.to_bits(scalar.size()) == 0)
}

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

/// Trace a returned reference to interior mutable storage back to its input.
pub(crate) fn interior_mutable_borrow_source_arg(tcx: TyCtxt<'_>, callee: DefId) -> Option<usize> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    let result = rustc_middle::mir::RETURN_PLACE;
    let TyKind::Ref(_, pointee, _) = body.local_decls[result].ty.kind() else {
        return None;
    };
    if !contains_unsafe_cell(tcx, *pointee, 4) {
        return None;
    }
    trace_source_arg(tcx, body, result, &mut HashSet::new(), 5)
}

fn contains_unsafe_cell<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    depth: usize,
) -> bool {
    if depth == 0 {
        return false;
    }
    let TyKind::Adt(adt, args) = ty.kind() else {
        return false;
    };
    if tcx.is_lang_item(adt.did(), crate::def_ids::lang_api::LangItem::UnsafeCell) {
        return true;
    }
    !adt.is_enum()
        && adt.non_enum_variant().fields.iter().any(|field| {
            contains_unsafe_cell(tcx, mir_utils::field_ty(tcx, field, args), depth - 1)
        })
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
    single_block_without_effects(tcx.optimized_mir(callee))
}

/// A consumed owner remains allocated when a side-effect-free MIR body
/// returns its pointer without running a destructor.
pub(crate) fn returns_undropped_arg(tcx: TyCtxt<'_>, callee: DefId, arg: usize) -> bool {
    return_source_arg(tcx, callee) == Some(arg)
        && single_block_without_effects(tcx.optimized_mir(callee))
}

/// Type of a shared owner whose raw pointer can later reconstruct a share.
pub(crate) fn shared_raw_owner_type(tcx: TyCtxt<'_>, callee: DefId) -> Option<DefId> {
    if !matches!(tcx.def_kind(callee), DefKind::Fn | DefKind::AssocFn) {
        return None;
    }
    let arg = return_source_arg(tcx, callee)?;
    if !single_block_without_effects(tcx.optimized_mir(callee)) {
        return None;
    }
    let inputs = tcx.fn_sig(callee).skip_binder().inputs().skip_binder();
    let ty = *inputs.get(arg)?;
    let TyKind::Adt(adt, _) = ty.kind() else {
        return None;
    };
    let reconstructs_share = tcx.inherent_impls(adt.did()).iter().any(|impl_id| {
        tcx.associated_item_def_ids(*impl_id).iter().any(|item| {
            matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn)
                && crate::verify::contract::json::query_json_contracts(tcx, *item)
                    .iter()
                    .any(|property| {
                        property.kind()
                            == Some(crate::verify::contract::PropertyKind::RefCountShare)
                    })
                && crate::verify::vm::alias_hazard::reconstructed_owner(tcx, *item)
                    .is_some_and(|(_, owner)| owner == adt.did())
        })
    });
    if !reconstructs_share {
        return None;
    }
    ty.needs_drop(tcx, TypingEnv::non_body_analysis(tcx, callee))
        .then_some(adt.did())
}

fn single_block_without_effects(body: &Body<'_>) -> bool {
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
