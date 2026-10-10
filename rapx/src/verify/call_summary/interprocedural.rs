//! Interprocedural call summaries derived from MIR for local wrapper functions.
//!
//! When no hand-crafted summary exists, this module inspects a callee's own MIR
//! to approximate its effects: pointer-arithmetic wrappers, `from_raw_parts`
//! wrappers, argument-to-return dataflow, and index-disjointness validators.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::TyCtxt,
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::compat::Spanned;
use crate::helpers::mir_utils as helpers;

use super::CallContext;

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast/
/// Ref/RawPtr assignments to the outer callee's argument local, returning its
/// index. `Ref`/`RawPtr` are treated as data-flow too, which is an
/// approximation (taking a reference is not a pure copy) but is adequate for
/// wrapper recognition.
fn trace_to_callee_arg<'tcx>(
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
    None
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

/// Cached must-write summaries, keyed by `(callee, depth, context)`. Depth is
/// part of the key because the `depth > 4` cutoff makes a summary computed
/// deeper in the wrapper chain less complete than one computed higher up, and
/// the DFS reaches the deep ones first. The context is part of the key because
/// one query can reach the same callee with different concrete arguments, which
/// prune different paths.
type MustWriteMemo = HashMap<(DefId, usize, Vec<(usize, i128)>), Option<HashSet<usize>>>;

/// Canonical, sortable representation of a [`CallContext`]'s concrete
/// arguments, used as part of the memo key (`FxHashMap` is not `Hash`).
fn context_key(context: &CallContext) -> Vec<(usize, i128)> {
    let mut entries: Vec<(usize, i128)> = context.concrete.iter().map(|(k, v)| (*k, *v)).collect();
    entries.sort_unstable();
    entries
}

/// Return callee argument indices that are definitely written on every
/// reachable return path, pruning paths infeasible under `context`. Works for
/// any callee with available MIR, and follows wrapper calls
/// (`Vec::push` → `push_mut`) with bounded depth.
pub(super) fn local_must_write_args(
    tcx: TyCtxt<'_>,
    callee: DefId,
    context: &CallContext,
) -> Option<Vec<usize>> {
    must_write_args_rec(tcx, callee, 0, context, &mut HashMap::new())
        .map(|set| set.into_iter().collect())
}

fn must_write_args_rec(
    tcx: TyCtxt<'_>,
    callee: DefId,
    depth: usize,
    context: &CallContext,
    memo: &mut MustWriteMemo,
) -> Option<HashSet<usize>> {
    if depth > 4 {
        return None;
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    if tcx.intrinsic(callee).is_some() || helpers::is_drop_in_place(callee) {
        return None;
    }
    let key = (callee, depth, context_key(context));
    if let Some(summary) = memo.get(&key) {
        return summary.clone();
    }

    let summary = helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        let mut graph = PathGraph::new(tcx, callee);
        graph.find_scc();
        let mut enumerator = PathEnumerator::new(&graph);
        let paths = enumerator.enumerate_paths_repeat(0);
        // An intersection over only some of the paths can claim a write that a
        // missing path skips.
        if paths.is_truncated() {
            return None;
        }

        let mut must_write: Option<HashSet<usize>> = None;
        for path in paths.iter() {
            if !path_ends_in_return(body, &path) {
                continue;
            }
            if path_infeasible_under_context(body, &path, context) {
                continue;
            }
            let writes = write_args_on_path(tcx, body, &path, depth, context, memo);
            must_write = Some(match must_write {
                Some(current) => current.intersection(&writes).copied().collect(),
                None => writes,
            });
        }

        Some(must_write.unwrap_or_default())
    })
    .ok()
    .flatten();
    memo.insert(key, summary.clone());
    summary
}

/// Return `true` if `path` is provably infeasible under `context`, by folding a
/// `SwitchInt` whose discriminant is a direct copy of a concrete argument. Only
/// prunes when the taken target is uniquely determined, so a feasible path is
/// never removed.
fn path_infeasible_under_context(
    body: &rustc_middle::mir::Body<'_>,
    path: &[usize],
    context: &CallContext,
) -> bool {
    if context.concrete.is_empty() {
        return false;
    }
    for window in path.windows(2) {
        let (block, next) = (window[0], window[1]);
        let Some(data) = body.basic_blocks.get(BasicBlock::from_usize(block)) else {
            continue;
        };
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let TerminatorKind::SwitchInt { discr, targets } = &terminator.kind else {
            continue;
        };
        let Some(value) = switch_discriminant_concrete(body, discr, context) else {
            continue;
        };
        let expected = targets
            .iter()
            .find(|(val, _)| *val == value as u128)
            .map(|(_, t)| t)
            .unwrap_or_else(|| targets.otherwise());
        if expected.as_usize() != next {
            return true;
        }
    }
    false
}

/// Trace a `SwitchInt` discriminant back to a concrete argument value, following
/// only direct `Copy`/`Move` assignments (no casts or pointer arithmetic) so the
/// recovered value is identical to the argument's.
fn switch_discriminant_concrete(
    body: &rustc_middle::mir::Body<'_>,
    discr: &Operand<'_>,
    context: &CallContext,
) -> Option<i128> {
    let local = match discr {
        Operand::Copy(place) | Operand::Move(place) => place.local,
        _ => return None,
    };
    let mut queue = VecDeque::from([local]);
    let mut seen = HashSet::from([local]);
    while let Some(current) = queue.pop_front() {
        let cidx = current.as_usize();
        if cidx >= 1 && cidx <= body.arg_count {
            return context.concrete.get(&(cidx - 1)).copied();
        }
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                if assign.0.local != current {
                    continue;
                }
                let source = match &assign.1 {
                    Rvalue::Use(Operand::Copy(place), ..)
                    | Rvalue::Use(Operand::Move(place), ..) => place.local,
                    _ => continue,
                };
                if !seen.contains(&source) {
                    seen.insert(source);
                    queue.push_back(source);
                }
            }
        }
    }
    None
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
    context: &CallContext,
    memo: &mut MustWriteMemo,
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
            if dest.projection.first() == Some(&ProjectionElem::Deref)
                && let Some(arg) = helpers::arg_of_local(dest.local, body.arg_count) {
                    writes.insert(arg);
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
                .and_then(|arg| trace_to_callee_arg(body, &arg.node))
            {
                writes.insert(pointer_arg);
            }
            continue;
        }

        // Wrapper calls: a nested callee that writes its own args maps those
        // writes back onto this callee's args. The nested callee sees its own
        // argument positions, so rebuild its context from this call's arguments
        // (its own literals plus the outer concrete values passed through).
        if let Some(nested) = helpers::dep_callee_def_id(func) {
            let nested_context = nested_call_context(body, args, context);
            if let Some(nested_writes) =
                must_write_args_rec(tcx, nested, depth + 1, &nested_context, memo)
            {
                for (i, arg) in args.iter().enumerate() {
                    if nested_writes.contains(&i)
                        && let Some(outer) = trace_to_callee_arg(body, &arg.node) {
                            writes.insert(outer);
                        }
                }
            }
        }
    }
    writes
}

/// Build the `CallContext` a nested call sees, keyed by the *nested* callee's
/// own argument indices. Each nested argument is concrete either because it is a
/// literal at this call site, or because it passes an outer concrete value
/// straight through (`Copy`/`Move` of an argument). This keeps a caller's
/// literal at position `i` from being read as the nested callee's position-`i`
/// argument.
fn nested_call_context<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    context: &CallContext,
) -> CallContext {
    let mut nested_context = CallContext::default();
    for (i, arg) in args.iter().enumerate() {
        if let Some(v) = helpers::operand_const_u64(&arg.node) {
            nested_context.concrete.insert(i, v as i128);
        } else if let Some(outer) = trace_to_callee_arg(body, &arg.node)
            && let Some(v) = context.concrete.get(&outer) {
                nested_context.concrete.insert(i, *v);
            }
    }
    nested_context
}

