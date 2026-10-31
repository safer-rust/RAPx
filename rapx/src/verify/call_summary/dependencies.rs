//! Backward call dependency summaries and MIR-derived argument flows.
//!
//! Uses registered effects when available and otherwise inspects callee MIR to
//! approximate return dependencies and arguments the callee may write.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, NonDivergingIntrinsic, Operand, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::compat::Spanned;
use crate::def_ids::intrinsic_api;
use crate::helpers::mir_utils as helpers;
use crate::verify::api_classify;

use super::{CallDependencySummary, CallEffect, callback, effects};

/// Return dependency information for a MIR call terminator.
pub(crate) fn dependency_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
    destination: Local,
    args: &[Spanned<Operand<'tcx>>],
    body: &Body<'tcx>,
) -> CallDependencySummary {
    let arg_count = args.len();
    let callee = helpers::dep_callee_def_id(func);

    if let Some(callee) = callee {
        if let Some(summary) = callback::estimate(tcx, callee, args, body) {
            return summary;
        }
        if arg_count > 0
            && (api_classify::is_iter_next(Some(callee))
                || api_classify::is_range_next(Some(callee))
                || crate::def_ids::other_api::iterator_next_trait_fns().contains(&callee))
        {
            let mut summary = CallDependencySummary::fallback(arg_count);
            summary.write_args.push(0);
            summary.write_inputs.push(0);
            return summary;
        }
        if let Some(summary) = intrinsic_dependency_summary(
            tcx, caller, Some(callee), func, destination, arg_count,
        ) {
            return summary;
        }
        if helpers::is_drop_in_place(callee) {
            return CallDependencySummary::fallback(arg_count);
        }

        // Writes and return-dependencies are orthogonal. Analyze both even
        // when a callee writes through an argument.
        let write_args = match local_write_args(tcx, callee) {
            Some(args) => args.into_iter().filter(|i| *i < arg_count).collect::<Vec<_>>(),
            None => tcx.fn_sig(callee).skip_binder().inputs().skip_binder().iter().enumerate()
                .filter_map(|(i, ty)| {
                    (i < arg_count && matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Mut) | TyKind::RawPtr(_, Mutability::Mut)))
                        .then_some(i)
                })
                .collect(),
        };
        let write_args = (!write_args.is_empty()).then_some(write_args);
        let return_deps = if api_classify::is_branch(Some(callee)) {
            Some(vec![0])
        } else {
            local_return_dependencies(tcx, callee)
                .map(|args| args.into_iter().filter(|i| *i < arg_count).collect::<Vec<_>>())
        };

        if write_args.is_some() || return_deps.is_some() {
            return CallDependencySummary {
                // An unavailable or failed MIR analysis says nothing about
                // return flow; preserve all arguments in that case.
                return_depends_on_args: return_deps.unwrap_or_else(|| (0..arg_count).collect()),
                write_inputs: write_args.clone().unwrap_or_default(),
                write_args: write_args.unwrap_or_default(),
            };
        }
    }

    CallDependencySummary::fallback(arg_count)
}

/// Derive backward dependencies from a registered intrinsic effect.
fn intrinsic_dependency_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: Option<DefId>,
    func: &Operand<'tcx>,
    _destination: Local,
    arg_count: usize,
) -> Option<CallDependencySummary> {
    let id = callee?;
    if !intrinsic_api::is_intrinsic(tcx, id) && !api_classify::is_ptr_copy(callee) {
        return None;
    }
    let modeled = effects::lookup_effect(tcx, caller, callee, func);
    if api_classify::is_ptr_copy(callee) && modeled.is_none() {
        return Some(CallDependencySummary {
            return_depends_on_args: (0..arg_count).collect(),
            write_args: (arg_count > 1).then_some(1).into_iter().collect(),
            write_inputs: (0..arg_count.min(3)).collect(),
        });
    }
    let write_args: Vec<usize> = if let Some(ref effects) = modeled {
        effects
            .iter()
            .flat_map(CallEffect::written_args)
            .filter(|arg| *arg < arg_count)
            .collect()
    } else {
        tcx.fn_sig(id)
            .skip_binder()
            .inputs()
            .skip_binder()
            .iter()
            .take(arg_count)
            .enumerate()
            .filter_map(|(index, ty)| {
                matches!(
                    ty.kind(),
                    TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut)
                )
                .then_some(index)
            })
            .collect()
    };
    let write_inputs = if let Some(ref effects) = modeled {
        effects
            .iter()
            .flat_map(CallEffect::write_inputs)
            .filter(|arg| *arg < arg_count)
            .collect()
    } else {
        write_args.clone()
    };
    Some(CallDependencySummary {
        return_depends_on_args: (0..arg_count).collect(),
        write_args,
        write_inputs,
    })
}

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast/
/// Ref/RawPtr/tuple assignments to the outer callee's argument locals.
/// `Ref`/`RawPtr` are treated as data-flow too, which is an
/// approximation (taking a reference is not a pure copy) but is adequate for
/// wrapper recognition.
fn trace_to_callee_args(
    body: &rustc_middle::mir::Body<'_>,
    operand: &Operand<'_>,
) -> HashSet<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => trace_local_to_callee_args(body, place.local),
        _ => HashSet::new(),
    }
}

fn trace_local_to_callee_args(
    body: &rustc_middle::mir::Body<'_>,
    local: rustc_middle::mir::Local,
) -> HashSet<usize> {
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    let mut outer_args = HashSet::new();
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            outer_args.insert(cidx - 1);
            continue;
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
                let sources: Vec<_> = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..)
                    | Rvalue::Cast(_, Operand::Copy(place), _)
                    | Rvalue::Cast(_, Operand::Move(place), _)
                    | Rvalue::Ref(_, _, place)
                    | Rvalue::RawPtr(_, place)
                    | Rvalue::CopyForDeref(place) => vec![place.local],
                    Rvalue::Aggregate(_, operands) => operands
                        .iter()
                        .filter_map(|operand| match operand {
                            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                            _ => None,
                        })
                        .collect(),
                    _ => Vec::new(),
                };
                for source in sources {
                    if seen.insert(source) {
                        queue.push_back(source);
                    }
                }
            }
            let Some(terminator) = &bb.terminator else {
                continue;
            };
            let (func, args, destination) = match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => (func, args, destination.local),
                TerminatorKind::TailCall { func, args, .. } => {
                    (func, args, rustc_middle::mir::Local::from_usize(0))
                }
                _ => continue,
            };
            if destination != current {
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
                #[cfg(rapx_ge_95)]
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
    outer_args
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

/// Memo keyed by `(callee, depth)`, shared within a single
/// `local_write_args` recursion.
type WriteMemo = HashMap<(DefId, usize), Option<HashSet<usize>>>;

/// Return callee argument indices that are written. Works for any callee with
/// available MIR, and follows wrapper calls (`Vec::push` → `push_mut`) with
/// bounded depth.
pub(super) fn local_write_args(tcx: TyCtxt<'_>, callee: DefId) -> Option<Vec<usize>> {
    write_args_rec(tcx, callee, 0, &mut HashMap::new()).map(|set| set.into_iter().collect())
}

fn write_args_rec(
    tcx: TyCtxt<'_>,
    callee: DefId,
    depth: usize,
    memo: &mut WriteMemo,
) -> Option<HashSet<usize>> {
    if depth > 4 {
        return None;
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    if crate::def_ids::intrinsic_api::is_intrinsic(tcx, callee) || helpers::is_drop_in_place(callee) {
        return None;
    }
    let key = (callee, depth);
    if let Some(summary) = memo.get(&key) {
        return summary.clone();
    }

    let summary = helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        let mut graph = PathGraph::new(tcx, callee);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(0);
        if paths.is_truncated() {
            return None;
        }

        let mut write: Option<HashSet<usize>> = None;
        for path in paths.iter() {
            if !path_ends_in_return(body, &path) {
                continue;
            }
            let writes = write_args_on_path(tcx, callee, body, &path, depth, memo);
            write = Some(match write {
                Some(mut current) => {
                    current.extend(writes);
                    current
                }
                None => writes,
            });
        }

        Some(write.unwrap_or_default())
    })
    .ok()
    .flatten();
    memo.insert(key, summary.clone());
    summary
}

fn path_ends_in_return(body: &rustc_middle::mir::Body<'_>, path: &[usize]) -> bool {
    path.last().is_some_and(|block| {
        body.basic_blocks
            .get(BasicBlock::from_usize(*block))
            .and_then(|data| data.terminator.as_ref())
            .is_some_and(|terminator| {
                matches!(
                    terminator.kind,
                    TerminatorKind::Return | TerminatorKind::TailCall { .. }
                )
            })
    })
}

fn write_args_on_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    body: &rustc_middle::mir::Body<'tcx>,
    path: &[usize],
    depth: usize,
    memo: &mut WriteMemo,
) -> HashSet<usize> {
    let mut writes = HashSet::new();
    for block in path {
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(*block)) else {
            continue;
        };

        for stmt in &data.statements {
            if let StatementKind::Intrinsic(intrinsic) = &stmt.kind
                && let NonDivergingIntrinsic::CopyNonOverlapping(copy) = &**intrinsic
            {
                writes.extend(trace_to_callee_args(body, &copy.dst));
            }
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let dest = &assign.0;
            if dest.projection.first() == Some(&ProjectionElem::Deref)
            {
                writes.extend(trace_local_to_callee_args(body, dest.local));
            }
        }

        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let (func, args, destination) = match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => (func, args, destination.local),
            TerminatorKind::TailCall { func, args, .. } => {
                (func, args, rustc_middle::mir::Local::from_usize(0))
            }
            _ => continue,
        };

        // `ptr::write`-style writes: trace the pointer arg to a callee arg.
        if crate::verify::api_classify::is_ptr_write(helpers::dep_callee_def_id(func)) {
            if let Some(pointer_arg) = args.first() {
                writes.extend(trace_to_callee_args(body, &pointer_arg.node));
            }
            continue;
        }

        if crate::verify::api_classify::is_ptr_copy(helpers::dep_callee_def_id(func)) {
            if let Some(destination_arg) = args.get(1) {
                writes.extend(trace_to_callee_args(body, &destination_arg.node));
            }
            continue;
        }

        // Wrapper calls: a nested callee that writes its own args maps those
        // writes back onto this callee's args.
        if let Some(nested) = helpers::dep_callee_def_id(func)
            && let Some(nested_writes) = intrinsic_dependency_summary(
                tcx,
                caller,
                Some(nested),
                func,
                destination,
                args.len(),
            )
            .map(|summary| summary.write_args.into_iter().collect::<HashSet<_>>())
            .or_else(|| {
                super::callback::estimate(tcx, nested, args, body)
                    .map(|summary| summary.write_args.into_iter().collect::<HashSet<_>>())
            })
            .or_else(|| write_args_rec(tcx, nested, depth + 1, memo))
        {
            for (i, arg) in args.iter().enumerate() {
                if nested_writes.contains(&i) {
                    writes.extend(trace_to_callee_args(body, &arg.node));
                }
            }
        }
    }
    writes
}
