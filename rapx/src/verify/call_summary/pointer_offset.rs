//! Infer pointer offset direction from a callee's MIR.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BinOp, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TypingEnv},
};

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
                        tcx,
                        body,
                        source.local,
                        depth,
                        zst_branch,
                        &mut seen.clone(),
                    )?
                }
                Rvalue::BinaryOp(BinOp::Offset, operands) => {
                    let base = mir_utils::operand_mir_place(&operands.0)?;
                    let base = trace_pointer_offset(
                        tcx,
                        body,
                        base.local,
                        depth,
                        zst_branch,
                        &mut seen.clone(),
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
                        tcx,
                        body,
                        source.local,
                        depth,
                        zst_branch,
                        &mut seen.clone(),
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
            tcx,
            body,
            base_place.local,
            depth,
            zst_branch,
            &mut seen.clone(),
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
