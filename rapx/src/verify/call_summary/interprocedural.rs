use std::collections::{HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, BinOp, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path_analysis::graph::{PathEnumerator, PathGraph};
use crate::helpers::mir_utils as helpers;

use super::fn_simulator;

use super::CallEffect;

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast
/// assignments to the outer callee's argument local, returning its index.
fn trace_to_callee_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &Operand<'_>,
) -> Option<usize> {
    let local = match operand {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    let idx = local.as_usize();
    if idx >= 1 && idx <= body.arg_count {
        return Some(idx - 1);
    }
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return Some(cidx - 1);
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let dest = assign.0.local;
                if dest != current {
                    continue;
                }
                let source = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place), _)
                    | Rvalue::Cast(_, Operand::Move(place), _)
                    | Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => place.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
            }
            let Some(terminator) = &bb.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                continue;
            };
            if destination.local != current {
                continue;
            }
            let name = helpers::call_name(tcx, func);
            if !fn_simulator::is_as_ptr(&name) {
                continue;
            }
            let Some(source) = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                Operand::Constant(_) => None,
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => None,
            }) else {
                continue;
            };
            if !seen.contains(&source) {
                seen.insert(source);
                queue.push_back(source);
            }
        }
    }
    None
}

/// Detect when a local callee wraps a pointer-arithmetic call (add/sub) and
/// produce the correct `ReturnPointerAdd` / `ReturnPointerSub` effect.
pub(super) fn try_pointer_arith_wrapper_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    _destination: Option<Local>,
) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }

    let body = tcx.optimized_mir(callee);
    if body.basic_blocks.len() > 16 {
        return None;
    }
    let ret = Local::from_usize(0);

    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func,
            args,
            destination: call_dest,
            ..
        } = &terminator.kind
        else {
            continue;
        };

        let name = helpers::call_name(tcx, func);
        let is_add = fn_simulator::is_pointer_add(&name);
        let is_sub = fn_simulator::is_pointer_sub(&name);

        let inner_effect = if !is_add && !is_sub {
            helpers::dep_callee_def_id(func).and_then(|inner_callee| {
                let inner_name = helpers::call_name(tcx, func);
                if inner_name.contains("::intrinsics::")
                    || inner_name.starts_with("intrinsics::")
                    || inner_name.ends_with("::drop_in_place")
                {
                    return None;
                }
                try_pointer_arith_wrapper_effect(tcx, inner_callee, Some(call_dest.local))
            })
        } else {
            None
        };

        if !is_add && !is_sub && inner_effect.is_none() {
            continue;
        }

        let mut queue = VecDeque::from([call_dest.local]);
        let mut seen = HashSet::from([call_dest.local]);
        let mut reaches_ret = false;
        while let Some(current) = queue.pop_front() {
            if current == ret {
                reaches_ret = true;
                break;
            }
            for bb2 in body.basic_blocks.iter() {
                for stmt in &bb2.statements {
                    let StatementKind::Assign(assign) = &stmt.kind else {
                        continue;
                    };
                    let dest = assign.0.local;
                    if seen.contains(&dest) {
                        continue;
                    }
                    match &assign.1 {
                        Rvalue::Use(Operand::Copy(place), ..)
                        | Rvalue::Use(Operand::Move(place), ..) => {
                            if place.local == current {
                                queue.push_back(dest);
                                seen.insert(dest);
                            }
                        }
                        Rvalue::Cast(_, Operand::Copy(place), _)
                        | Rvalue::Cast(_, Operand::Move(place), _) => {
                            if place.local == current {
                                queue.push_back(dest);
                                seen.insert(dest);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        if !reaches_ret {
            continue;
        }

        if let Some(effect) = inner_effect {
            match effect {
                CallEffect::ReturnPointerAdd {
                    base_arg: inner_base,
                    offset_arg: inner_offset,
                    stride,
                }
                | CallEffect::ReturnPointerSub {
                    base_arg: inner_base,
                    offset_arg: inner_offset,
                    stride,
                } => {
                    let base_arg = trace_to_callee_arg(tcx, body, &args.get(inner_base)?.node)?;
                    let offset_arg = trace_to_callee_arg(tcx, body, &args.get(inner_offset)?.node)?;
                    return Some(match effect {
                        CallEffect::ReturnPointerSub { .. } => CallEffect::ReturnPointerSub {
                            base_arg,
                            offset_arg,
                            stride,
                        },
                        _ => CallEffect::ReturnPointerAdd {
                            base_arg,
                            offset_arg,
                            stride,
                        },
                    });
                }
                _ => {}
            }
            continue;
        }

        let base_arg = trace_to_callee_arg(tcx, body, &args[0].node)?;
        let offset_arg = trace_to_callee_arg(tcx, body, &args[1].node)?;
        let stride = if fn_simulator::is_byte_ptr_arith(&name) {
            Some(1)
        } else {
            fn_simulator::destination_stride(tcx, callee, Some(call_dest.local))
        };

        return if is_sub {
            Some(CallEffect::ReturnPointerSub {
                base_arg,
                offset_arg,
                stride,
            })
        } else {
            Some(CallEffect::ReturnPointerAdd {
                base_arg,
                offset_arg,
                stride,
            })
        };
    }

    None
}

/// Use the existing dataflow graph to approximate local callee return deps.
pub(super) fn local_return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }
    helpers::catch_panic(|| {
        let mut analyzer = DataflowAnalyzer::new(tcx, false);
        analyzer.build_graph(callee);
        let deps = analyzer.get_fn_arg2ret(callee);
        deps.iter_enumerated()
            .filter_map(|(local, depends)| {
                if *depends && local.as_usize() > 0 {
                    Some(local.as_usize() - 1)
                } else {
                    None
                }
            })
            .collect()
    })
    .ok()
}

/// Return callee argument indices that are definitely written on every
/// reachable return path.
pub(super) fn local_must_write_args(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }

    helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        let mut graph = PathGraph::new(tcx, callee);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(0);

        let mut must_write: Option<HashSet<usize>> = None;
        for path in paths.iter() {
            if !path_ends_in_return(body, &path) {
                continue;
            }
            let writes = write_args_on_path(tcx, body, &path);
            must_write = Some(match must_write {
                Some(current) => current.intersection(&writes).copied().collect(),
                None => writes,
            });
        }

        must_write
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>()
    })
    .ok()
}

/// Recognize the standard-library `get_disjoint_check_valid` helper as a
/// trusted index-disjoint validator by name.
pub(super) fn named_index_disjoint_validator(name: &str) -> Option<(usize, usize)> {
    let base = name
        .split('<')
        .next()
        .unwrap_or(name)
        .trim_end_matches("::");
    if base.ends_with("get_disjoint_check_valid") {
        Some((0, 1))
    } else {
        None
    }
}

/// Detect an "index disjoint validator": a function whose body loads elements
/// from an array argument, and returns early (`Err`) both when an element is
/// out of range against a scalar argument (`>= len`) and when two elements are
/// equal (a duplicate).  Returns `(indices_arg, len_arg)`.
pub(super) fn detect_index_disjoint_validator(tcx: TyCtxt<'_>, callee: DefId) -> Option<(usize, usize)> {
    callee.as_local()?;
    if !tcx.is_mir_available(callee) {
        return None;
    }
    helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        let arg_count = body.arg_count;
        let mut elem_load_arg: HashSet<(Local, usize)> = HashSet::new();
        let mut copy_of_arg: HashSet<(Local, usize)> = HashSet::new();

        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if !dest.projection.is_empty() {
                    continue;
                }
                let Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..) = rvalue else {
                    continue;
                };
                let Some(arg) = helpers::arg_of_local(place.local, arg_count) else {
                    continue;
                };
                if place
                    .projection
                    .iter()
                    .any(|p| matches!(p, ProjectionElem::Index(_)))
                {
                    elem_load_arg.insert((dest.local, arg));
                } else if place.projection.is_empty() {
                    copy_of_arg.insert((dest.local, arg));
                }
            }
        }

        let elem_arg = |op: &Operand<'_>| -> Option<usize> {
            let (Operand::Copy(p) | Operand::Move(p)) = op else {
                return None;
            };
            if !p.projection.is_empty() {
                return None;
            }
            elem_load_arg
                .iter()
                .find(|(l, _)| *l == p.local)
                .map(|(_, a)| *a)
        };
        let scalar_arg = |op: &Operand<'_>| -> Option<usize> {
            let (Operand::Copy(p) | Operand::Move(p)) = op else {
                return None;
            };
            if !p.projection.is_empty() {
                return None;
            }
            helpers::arg_of_local(p.local, arg_count).or_else(|| {
                copy_of_arg
                    .iter()
                    .find(|(l, _)| *l == p.local)
                    .map(|(_, a)| *a)
            })
        };

        let mut bounds: Option<(usize, usize)> = None;
        let mut disjoint_arg: Option<usize> = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (_, Rvalue::BinaryOp(op, pair)) = &**assign else {
                    continue;
                };
                let (a, b) = &**pair;
                match op {
                    BinOp::Ge | BinOp::Gt | BinOp::Le | BinOp::Lt => {
                        if let (Some(idx), Some(len)) = (elem_arg(a), scalar_arg(b)) {
                            bounds = Some((idx, len));
                        } else if let (Some(idx), Some(len)) = (elem_arg(b), scalar_arg(a)) {
                            bounds = Some((idx, len));
                        }
                    }
                    BinOp::Eq | BinOp::Ne => {
                        if let (Some(x), Some(y)) = (elem_arg(a), elem_arg(b))
                            && x == y
                        {
                            disjoint_arg = Some(x);
                        }
                    }
                    _ => {}
                }
            }
        }

        match (bounds, disjoint_arg) {
            (Some((idx, len)), Some(dj)) if dj == idx && idx != len => Some((idx, len)),
            _ => None,
        }
    })
    .ok()
    .flatten()
}
fn path_ends_in_return(body: &rustc_middle::mir::Body<'_>, path: &[usize]) -> bool {
    path.last().is_some_and(|block| {
        body.basic_blocks
            .get(BasicBlock::from_usize(*block))
            .and_then(|data| data.terminator.as_ref())
            .is_some_and(|terminator| matches!(terminator.kind, TerminatorKind::Return))
    })
}

fn write_args_on_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    path: &[usize],
) -> HashSet<usize> {
    let mut writes = HashSet::new();
    for block in path {
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(*block)) else {
            continue;
        };
        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let name = helpers::call_name(tcx, func);
        if !fn_simulator::is_ptr_write(&name) {
            continue;
        }
        if let Some(pointer_arg) = args
            .first()
            .and_then(|arg| trace_to_callee_arg(tcx, body, &arg.node))
        {
            writes.insert(pointer_arg);
        }
    }
    writes
}
