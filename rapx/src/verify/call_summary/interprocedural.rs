//! Interprocedural call summaries derived from MIR for local wrapper functions.
//!
//! When no hand-crafted summary exists, this module inspects a callee's own MIR
//! to approximate its effects: pointer-arithmetic wrappers, `from_raw_parts`
//! wrappers, argument-to-return dataflow, and index-disjointness validators.

use std::collections::{HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::helpers::mir_utils as helpers;

use super::CallEffect;

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast/
/// Ref/RawPtr assignments to the outer callee's argument local, returning its
/// index. `Ref`/`RawPtr` are treated as data-flow too, which is an
/// approximation (taking a reference is not a pure copy) but is adequate for
/// wrapper recognition.
fn trace_to_callee_arg<'tcx>(
    _tcx: TyCtxt<'tcx>,
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
            // Trace through pointer-preserving calls: `as_ptr`/`as_mut_ptr`
            // (and friends) return the pointee address, while `add`/`sub`/
            // `offset` return the base pointer shifted by an offset — the
            // provenance (and thus the written-through arg) is carried by
            // their first (base/receiver) argument.
            let callee = helpers::dep_callee_def_id(func);
            let traces_base = crate::verify::api_classify::is_as_ptr(callee)
                || crate::verify::api_classify::is_pointer_add(callee)
                || crate::verify::api_classify::is_pointer_sub(callee);
            if !traces_base {
                continue;
            }
            let Some(source) = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                Operand::Constant(_) => None,
                #[cfg(rapx_ge_99)]
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

        let callee_id = helpers::dep_callee_def_id(func);
        let is_add = crate::verify::api_classify::is_pointer_add(callee_id);
        let is_sub = crate::verify::api_classify::is_pointer_sub(callee_id);

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

        if !call_result_reaches_return(body, call_dest.local) {
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

        let base_arg = trace_to_callee_arg(tcx, body, &args.get(0)?.node)?;
        let offset_arg = trace_to_callee_arg(tcx, body, &args.get(1)?.node)?;
        let stride = if crate::verify::api_classify::is_byte_ptr_arith(callee_id) {
            Some(1)
        } else {
            helpers::destination_stride(tcx, callee, Some(call_dest.local))
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

/// Check whether a callee body contains pointer arithmetic calls.
pub(super) fn callee_contains_pointer_arithmetic(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(_) = callee.as_local() else {
        return false;
    };
    if !tcx.is_mir_available(callee) {
        return false;
    }
    let body = tcx.optimized_mir(callee);
    for bb in body.basic_blocks.iter() {
        let Some(terminator) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            continue;
        };
        if crate::verify::api_classify::is_pointer_add(helpers::dep_callee_def_id(func))
            || crate::verify::api_classify::is_pointer_sub(helpers::dep_callee_def_id(func))
        {
            return true;
        }
    }
    false
}

/// Use the existing dataflow graph to approximate callee return deps.
/// Works for any callee with available MIR (local or cross-crate `#[inline]`).
pub(super) fn local_return_dependencies(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
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

/// Detect when a local callee wraps `from_raw_parts(ptr, len)` and produce
/// a `ReturnFreshAllocation` effect with the correct element size.
pub(super) fn try_from_raw_parts_wrapper_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    _destination: Option<Local>,
) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.basic_blocks.len() > 8 {
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

        let inner_callee = helpers::dep_callee_def_id(func);
        if !crate::verify::api_classify::is_from_raw_parts(inner_callee) {
            continue;
        }

        // Verify the call result reaches return
        if !call_result_reaches_return(body, call_dest.local) {
            continue;
        }

        // Trace from_raw_parts args to callee args
        let pointer_arg = trace_to_callee_arg(tcx, body, &args.get(0)?.node)?;
        let size_arg = trace_to_callee_arg(tcx, body, &args.get(1)?.node)?;

        // Determine element size from return type (slice or Vec).
        let elem_size =
            crate::verify::call_summary::from_raw_parts_elem_size(tcx, callee, Some(ret));

        return Some(CallEffect::ReturnFreshAllocation {
            pointer_arg,
            size_arg,
            elem_size,
        });
    }
    None
}

/// Detect a field-getter callee from its MIR: a function whose body is
/// (essentially) `(*self).field` — a single `Deref` + `Field` load returned as
/// the function's result. Produces a `ReturnFieldOfArg` effect so the
/// materialized field is returned, without any name- or length-specific
/// knowledge.
///
/// The match is conservative: the body must contain *only* the field load
/// (plus a unit-return and storage markers).
pub(crate) fn try_field_load_effect(tcx: TyCtxt<'_>, callee: DefId) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.basic_blocks.len() > 4 || body.arg_count < 1 {
        return None;
    }

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::Assign(assign) => {
                    let (place, rvalue) = &**assign;
                    // `_0 = (*_1).<field>` (return value is a field read).
                    if place.local.as_usize() == 0 && place.projection.is_empty() {
                        let src_place = match rvalue {
                            Rvalue::Use(Operand::Copy(p), ..)
                            | Rvalue::Use(Operand::Move(p), ..) => p,
                            Rvalue::CopyForDeref(p) => p,
                            _ => return None,
                        };
                        if src_place.local.as_usize() == 1 {
                            let mut proj = src_place.projection.iter();
                            if !matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref))
                            {
                                return None;
                            }
                            let Some(ProjectionElem::Field(idx, _)) = proj.next().map(|p| p.kind())
                            else {
                                return None;
                            };
                            if proj.next().is_some() {
                                return None;
                            }
                            return Some(CallEffect::ReturnFieldOfArg {
                                arg: 0,
                                field: idx.as_usize(),
                            });
                        }
                        return None;
                    }
                    // Any other real statement disqualifies the shape.
                    return None;
                }
                StatementKind::StorageLive(_) | StatementKind::StorageDead(_) => {}
                _ => return None,
            }
        }
    }
    None
}

/// Return callee argument indices that are definitely written on every
/// reachable return path. Works for any callee with available MIR, and follows
/// wrapper calls (`Vec::push` → `push_mut`) with bounded depth.
pub(super) fn local_must_write_args(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    must_write_args_rec(tcx, callee, 0).map(|set| set.into_iter().collect())
}

fn must_write_args_rec(tcx: TyCtxt<'_>, callee: DefId, depth: usize) -> Option<HashSet<usize>> {
    if depth > 4 {
        return None;
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let name = tcx.def_path_str(callee);
    if name.contains("::intrinsics::")
        || name.starts_with("intrinsics::")
        || name.ends_with("::drop_in_place")
    {
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
            let writes = write_args_on_path(tcx, body, &path, depth);
            must_write = Some(match must_write {
                Some(current) => current.intersection(&writes).copied().collect(),
                None => writes,
            });
        }

        must_write.unwrap_or_default()
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
    if base.ends_with("get_disjoint_check_valid") || base.ends_with("get_disjoint_check_valid_ext")
    {
        Some((0, 1))
    } else {
        None
    }
}

/// Detect an "index disjoint validator": a function whose body loads elements
/// from an array argument, and returns early (`Err`) both when an element is
/// out of range against a scalar argument (`>= len`) and when two elements are
/// equal (a duplicate).  Returns `(indices_arg, len_arg)`.
pub(super) fn detect_index_disjoint_validator(
    tcx: TyCtxt<'_>,
    callee: DefId,
) -> Option<(usize, usize)> {
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
    depth: usize,
) -> HashSet<usize> {
    let mut writes = HashSet::new();
    for block in path {
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(*block)) else {
            continue;
        };

        // Direct writes through `&mut` args: `*self = ...`, `(*self).0 = ...`.
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let dest = &assign.0;
            if dest.projection.first() == Some(&ProjectionElem::Deref) {
                if let Some(arg) = helpers::arg_of_local(dest.local, body.arg_count) {
                    writes.insert(arg);
                }
            }
        }

        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };

        // `ptr::write`-style writes: trace the pointer arg to a callee arg.
        if crate::verify::api_classify::is_ptr_write(helpers::dep_callee_def_id(func)) {
            if let Some(pointer_arg) = args
                .first()
                .and_then(|arg| trace_to_callee_arg(tcx, body, &arg.node))
            {
                writes.insert(pointer_arg);
            }
            continue;
        }

        // Wrapper calls: a nested callee that writes its own args maps those
        // writes back onto this callee's args.
        if let Some(nested) = helpers::dep_callee_def_id(func) {
            if let Some(nested_writes) = must_write_args_rec(tcx, nested, depth + 1) {
                for (i, arg) in args.iter().enumerate() {
                    if nested_writes.contains(&i) {
                        if let Some(outer) = trace_to_callee_arg(tcx, body, &arg.node) {
                            writes.insert(outer);
                        }
                    }
                }
            }
        }
    }
    writes
}

/// Return true when `call_dest`'s value flows (via Copy/Move/Cast) to the
/// function's return place `_0`.
fn call_result_reaches_return<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    call_dest: Local,
) -> bool {
    let ret = Local::from_usize(0);
    let mut queue = VecDeque::from([call_dest]);
    let mut seen = HashSet::from([call_dest]);
    while let Some(current) = queue.pop_front() {
        if current == ret {
            return true;
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let dest = assign.0.local;
                if seen.contains(&dest) {
                    continue;
                }
                match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place), _)
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
    false
}

/// Return true if the callee body contains any Call terminator, meaning the
/// callee is not self-contained (a nested call may have side effects that a
/// shallow summary cannot capture).
pub(super) fn callee_calls_other_local(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let body = tcx.optimized_mir(callee);
    for bb in body.basic_blocks.iter() {
        if matches!(
            bb.terminator().kind,
            rustc_middle::mir::TerminatorKind::Call { .. }
        ) {
            return true;
        }
    }
    false
}
