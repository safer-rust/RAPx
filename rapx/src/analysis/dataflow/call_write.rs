//! Trace writes through call arguments in MIR, including wrapper calls.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, NonDivergingIntrinsic, Operand, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{EarlyBinder, InstanceKind, TyCtxt, TypingEnv},
};

use crate::analysis::dataflow::pointer_copy;
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::compat::Spanned;
use crate::def_ids::diagnostic_api;
use crate::util::mir_utils as helpers;

/// API-specific facts needed by the MIR write tracer.
pub(crate) trait WriteSemantics {
    fn traces_base_pointer<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        func: &Operand<'tcx>,
    ) -> bool;
    fn direct_write_arg(&self, tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<usize>;
    fn special_write_args<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        body: &Body<'tcx>,
    ) -> Option<Vec<usize>>;
    fn skip_mir_write(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool;
}

/// Memo keyed by `(callee, depth)` for uninstantiated MIR summaries.
type WriteMemo = HashMap<(DefId, usize), Option<HashSet<usize>>>;

/// Trace backward from an operand (inner call arg) through Copy/Move/Cast/
/// Ref/RawPtr/tuple assignments to the outer callee's argument locals.
/// `Ref`/`RawPtr` are treated as data-flow too, which is an
/// approximation (taking a reference is not a pure copy) but is adequate for
/// wrapper recognition.
fn trace_to_callee_args<'tcx>(
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> HashSet<usize> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            trace_local_to_callee_args(semantics, tcx, caller, body, place.local)
        }
        _ => HashSet::new(),
    }
}

fn trace_local_to_callee_args<'tcx>(
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    body: &Body<'tcx>,
    local: Local,
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
                TerminatorKind::TailCall { func, args, .. } => (func, args, Local::from_usize(0)),
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
            if !semantics.traces_base_pointer(tcx, caller, func) {
                continue;
            }
            let Some(source) = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                Operand::Constant(_) => None,
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

/// Return arguments written by the concrete call, following wrapper calls
/// while retaining their generic arguments.
pub(crate) fn callsite_write_args<'tcx>(
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
) -> Option<Vec<usize>> {
    callsite_write_args_rec(semantics, tcx, caller, func, 0, &mut HashMap::new())
        .map(|set| set.into_iter().collect())
}

fn callsite_write_args_rec<'tcx>(
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    func: &Operand<'tcx>,
    depth: usize,
    memo: &mut WriteMemo,
) -> Option<HashSet<usize>> {
    if depth > 4 {
        return None;
    }
    let base = helpers::dep_callee_def_id(func)?;
    let is_trait_method = tcx
        .opt_associated_item(base)
        .and_then(|item| item.trait_container(tcx))
        .is_some();
    if !is_trait_method && !tcx.generics_of(base).requires_monomorphization(tcx) {
        return write_args_rec(semantics, tcx, base, depth, memo);
    }
    let Some(instance) = helpers::resolve_callee_instance(tcx, caller, func) else {
        return (!is_trait_method)
            .then(|| write_args_rec(semantics, tcx, base, depth, memo))
            .flatten();
    };
    if !matches!(instance.def, InstanceKind::Item(_)) || !tcx.is_mir_available(instance.def_id()) {
        return None;
    }
    let callee = instance.def_id();
    let mir = tcx.optimized_mir(callee);
    let body = instance
        .try_instantiate_mir_and_normalize_erasing_regions(
            tcx,
            TypingEnv::post_analysis(tcx, caller),
            EarlyBinder::bind(tcx, mir.clone()),
        )
        .ok()?;
    helpers::catch_panic(|| write_args_for_body(semantics, tcx, callee, &body, depth, memo))
        .ok()
        .flatten()
}

fn write_args_rec(
    semantics: &impl WriteSemantics,
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
    if semantics.skip_mir_write(tcx, callee) {
        return None;
    }
    let key = (callee, depth);
    if let Some(summary) = memo.get(&key) {
        return summary.clone();
    }

    let summary = helpers::catch_panic(|| {
        let body = tcx.optimized_mir(callee);
        write_args_for_body(semantics, tcx, callee, body, depth, memo)
    })
    .ok()
    .flatten();
    memo.insert(key, summary.clone());
    summary
}

fn write_args_for_body<'tcx>(
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    body: &Body<'tcx>,
    depth: usize,
    memo: &mut WriteMemo,
) -> Option<HashSet<usize>> {
    let mut graph = PathGraph::new(tcx, callee);
    graph.find_scc();
    let mut enumerator = PathEnumerator::new(&graph)
        .with_path_limit(crate::limit::DATAFLOW_CALL_WRITE_PATH_LIMIT);
    let paths = enumerator.enumerate_paths_repeat(0);
    if paths.is_truncated() {
        return None;
    }

    let mut write: Option<HashSet<usize>> = None;
    for path in paths.iter() {
        if !path_ends_in_return(body, &path) {
            continue;
        }
        let writes = write_args_on_path(semantics, tcx, callee, body, &path, depth, memo);
        write = Some(match write {
            Some(mut current) => {
                current.extend(writes);
                current
            }
            None => writes,
        });
    }

    Some(write.unwrap_or_default())
}

fn path_ends_in_return(body: &Body<'_>, path: &[usize]) -> bool {
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
    semantics: &impl WriteSemantics,
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    body: &Body<'tcx>,
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
                writes.extend(trace_to_callee_args(
                    semantics, tcx, caller, body, &copy.dst,
                ));
            }
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let dest = &assign.0;
            if dest.projection.first() == Some(&ProjectionElem::Deref) {
                writes.extend(trace_local_to_callee_args(
                    semantics, tcx, caller, body, dest.local,
                ));
            }
        }

        let Some(terminator) = data.terminator.as_ref() else {
            continue;
        };
        let (func, args) = match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => (func, args),
            TerminatorKind::TailCall { func, args, .. } => (func, args),
            _ => continue,
        };

        // `ptr::write`-style writes: trace the pointer arg to a callee arg.
        if let Some(write_arg) = semantics.direct_write_arg(tcx, func) {
            if let Some(arg) = args.get(write_arg) {
                writes.extend(trace_to_callee_args(
                    semantics, tcx, caller, body, &arg.node,
                ));
            }
            continue;
        }

        // Wrapper calls: a nested callee that writes its own args maps those
        // writes back onto this callee's args.
        if helpers::dep_callee_def_id(func).is_some()
            && let Some(nested_writes) = semantics
                .special_write_args(tcx, caller, func, args, body)
                .map(|args| args.into_iter().collect::<HashSet<_>>())
                .or_else(|| callsite_write_args_rec(semantics, tcx, caller, func, depth + 1, memo))
        {
            for (i, arg) in args.iter().enumerate() {
                if nested_writes.contains(&i) {
                    writes.extend(trace_to_callee_args(
                        semantics, tcx, caller, body, &arg.node,
                    ));
                }
            }
        }
    }
    writes
}

/// Destination pointer argument of copy and pointer-write APIs.
/// The destination's previous bytes need not be initialized.
pub(crate) fn write_target_arg(tcx: TyCtxt<'_>, callee: Option<DefId>) -> Option<usize> {
    let did = callee?;
    pointer_copy::copy_flow(tcx, did)
        .map(|flow| flow.destination_arg)
        .or_else(|| diagnostic_api::is_ptr_write_to_uninit(tcx, did).then_some(0))
}
