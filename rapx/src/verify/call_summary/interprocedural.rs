//! Interprocedural call summaries derived from MIR for local wrapper functions.
//!
//! When no hand-crafted summary exists, this module inspects a callee's own MIR
//! to approximate its effects: pointer-arithmetic wrappers, `from_raw_parts`
//! wrappers, argument-to-return dataflow, and index-disjointness validators.

use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};

use crate::analysis::dataflow::{DataflowAnalysis, default::DataflowAnalyzer};
use crate::analysis::path::graph::{PathEnumerator, PathGraph};
use crate::helpers::mir_utils as helpers;

use super::{CallContext, CallEffect};

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

/// Memo state for the transitive wrapper-effect walk: `Computing` marks a
/// callee currently being resolved (a re-entry is a self/mutual-recursive
/// cycle), `Done` caches the finished result.
enum WrapperEffectMemo {
    Computing,
    Done(Option<CallEffect>),
}

/// Resolve `callee`'s wrapper effect by walking nested wrapper calls, with
/// cycle detection and memoization. `probe` inspects `callee`'s body and, for
/// a nested call it follows, invokes `recurse`, which routes back through this
/// resolver so the memo applies uniformly. A callee re-entered while still
/// being resolved is a cycle and resolves to `None` (no finite wrapper chain).
fn resolve_wrapper_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    memo: &mut HashMap<DefId, WrapperEffectMemo>,
    probe: &dyn Fn(
        TyCtxt<'tcx>,
        DefId,
        &mut (dyn FnMut(DefId) -> Option<CallEffect> + '_),
    ) -> Option<CallEffect>,
) -> Option<CallEffect> {
    if let Some(state) = memo.get(&callee) {
        return match state {
            WrapperEffectMemo::Computing => None,
            WrapperEffectMemo::Done(effect) => effect.clone(),
        };
    }
    memo.insert(callee, WrapperEffectMemo::Computing);
    let result = {
        let recurse = &mut |inner: DefId| resolve_wrapper_effect(tcx, inner, memo, probe);
        probe(tcx, callee, recurse)
    };
    memo.insert(callee, WrapperEffectMemo::Done(result.clone()));
    result
}

/// Probe whether `callee` is a pointer-arithmetic (add/sub) wrapper, following
/// nested wrapper calls transitively. `effect_summary` runs this on every local
/// callee; it returns `None` for anything that is not — transitively — a
/// pointer add/sub wrapper.
pub(super) fn try_pointer_arith_wrapper_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    _destination: Option<Local>,
) -> Option<CallEffect> {
    let mut memo: HashMap<DefId, WrapperEffectMemo> = HashMap::new();
    resolve_wrapper_effect(tcx, callee, &mut memo, &pointer_arith_wrapper_probe)
}

/// Single-effect recognizer for [`resolve_wrapper_effect`]: does `callee`
/// directly wrap a pointer add/sub, or delegate to a nested callee that itself
/// resolves to one?
fn pointer_arith_wrapper_probe<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    recurse: &mut (dyn FnMut(DefId) -> Option<CallEffect> + '_),
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
                if tcx.intrinsic(inner_callee).is_some() || helpers::is_drop_in_place(inner_callee)
                {
                    return None;
                }
                recurse(inner_callee)
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
            let (inner_base, inner_offset, stride, dereferenceable) = match effect {
                CallEffect::ReturnPointerAdd {
                    base_arg,
                    offset_arg,
                    stride,
                    dereferenceable,
                } => (base_arg, offset_arg, stride, dereferenceable),
                CallEffect::ReturnPointerSub {
                    base_arg,
                    offset_arg,
                    stride,
                } => (base_arg, offset_arg, stride, false),
                _ => {
                    continue;
                }
            };
            let base_arg = trace_to_callee_arg(tcx, body, &args.get(inner_base)?.node)?;
            let offset_arg = trace_to_callee_arg(tcx, body, &args.get(inner_offset)?.node)?;
            let is_sub = matches!(effect, CallEffect::ReturnPointerSub { .. });
            return Some(if is_sub {
                CallEffect::ReturnPointerSub {
                    base_arg,
                    offset_arg,
                    stride,
                }
            } else {
                CallEffect::ReturnPointerAdd {
                    base_arg,
                    offset_arg,
                    stride,
                    dereferenceable,
                }
            });
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
                dereferenceable: false,
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

/// Detect a function that returns a raw-pointer field of its receiver
/// (`(*self).end_or_len`-shaped), even when the body also contains a
/// ZST/non-ZST branch and a preceding mutation call (e.g. an iterator's
/// `next_back_unchecked`). Produces a `ReturnFieldOfArg` effect so the returned
/// pointer keeps the field's provenance across the interprocedural boundary.
///
/// Unlike [`try_field_load_effect`], this does not require the body to be a
/// single field-load shape — it only requires that *some* return path loads a
/// raw-pointer field of the receiver directly into the return local. This is a
/// conservative over-approximation: for a ZST receiver the returned pointer is
/// never dereferenced (ZST accesses are vacuous), so preferring the raw field
/// is sound.
pub(crate) fn try_ptr_field_return_effect(tcx: TyCtxt<'_>, callee: DefId) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.arg_count < 1 {
        return None;
    }
    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    if !matches!(ret_ty.kind(), TyKind::RawPtr(..)) {
        return None;
    }
    // A preceding `pre_dec_end(offset)` on the receiver (arg 0) mutates its
    // `end_or_len` field *before* it is returned (e.g. `next_back_unchecked`).
    // In that case the returned pointer is `field - offset` elements past the
    // stored field value; returning the un-adjusted field would point one past
    // the last element. Record the offset so the effect can be adjusted.
    let pre_dec_offset = detect_pre_dec_end_offset(tcx, &body);
    // Trace backward from the return local through Copy/Move/Cast/CopyForDeref
    // assignments until a `(*arg).field` load of the receiver is reached. This
    // handles the optimized-MIR form where the field is first copied into a
    // temporary and then cast into the return slot (`_0 = _tmp as *const T`).
    let mut queue = VecDeque::from([Local::from_usize(0)]);
    let mut seen = HashSet::from([Local::from_usize(0)]);
    while let Some(cur) = queue.pop_front() {
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != cur || !dest.projection.is_empty() {
                    continue;
                }
                let src: Option<&Place<'_>> = match rvalue {
                    Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) => Some(p),
                    Rvalue::CopyForDeref(p) => Some(p),
                    Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) => Some(p),
                    _ => None,
                };
                let Some(src) = src else {
                    continue;
                };
                // `(*arg).field` — a raw-pointer field of the receiver.
                if src.local.as_usize() >= 1 && src.local.as_usize() <= body.arg_count {
                    let mut proj = src.projection.iter();
                    if matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref)) {
                        if let Some(ProjectionElem::Field(idx, _)) = proj.next().map(|p| p.kind()) {
                            if proj.next().is_none() {
                                let arg = src.local.as_usize() - 1;
                                let field = idx.as_usize();
                                return match pre_dec_offset {
                                    Some(offset) if offset > 0 => {
                                        Some(CallEffect::ReturnFieldOfArgSub { arg, field, offset })
                                    }
                                    _ => Some(CallEffect::ReturnFieldOfArg { arg, field }),
                                };
                            }
                        }
                    }
                }
                // Otherwise keep tracing through the source local.
                if src.projection.is_empty() && seen.insert(src.local) {
                    queue.push_back(src.local);
                }
            }
        }
    }
    None
}

/// Trace a local back through `x = copy y` / `x = move y` assignments to its
/// copy root (the original loop variable before MIR temporaries).
fn copy_root(body: &rustc_middle::mir::Body<'_>, mut local: Local) -> Local {
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(local) {
            break;
        }
        let mut next = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest.local != local || !dest.projection.is_empty() {
                    continue;
                }
                let Rvalue::Use(op, ..) = rvalue else {
                    continue;
                };
                let (Operand::Copy(p) | Operand::Move(p)) = op else {
                    continue;
                };
                if p.projection.is_empty() {
                    next = Some(p.local);
                }
            }
        }
        match next {
            Some(n) => local = n,
            None => break,
        }
    }
    local
}

/// Detect a `memchr`-style search function: it returns `Option<usize>` whose
/// `Some(i)` payload is an index guarded by a loop condition `i < arg.len()`
/// (where `arg` is a slice argument).  The summary lets a caller re-prove a
/// numeric invariant like `finger <= finger_back` after `finger += i + 1`.
pub(crate) fn try_slice_bounded_return_effect(
    tcx: TyCtxt<'_>,
    callee: DefId,
) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.basic_blocks.len() > 12 || body.arg_count < 1 {
        return None;
    }

    // (1) Find `_0 = Some(payload)` and record the payload's copy root.
    let mut payload_root: Option<Local> = None;
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if place.local.as_usize() != 0 || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(kind, operands) = rvalue else {
                continue;
            };
            let rustc_middle::mir::AggregateKind::Adt(adt, variant_idx, ..) = &**kind else {
                continue;
            };
            if !tcx.is_diagnostic_item(rustc_span::sym::Option, *adt) {
                continue;
            }
            if variant_idx.as_usize() != 1 {
                continue; // not `Some`
            }
            let Some(payload) = operands.iter().next() else {
                continue;
            };
            let (Operand::Copy(p) | Operand::Move(p)) = payload else {
                continue;
            };
            if p.projection.is_empty() {
                payload_root = Some(copy_root(&body, p.local));
            }
        }
    }
    let payload_root = payload_root?;

    // (2) Find `tmp = PtrMetadata(arg)` — the slice argument's length.
    let mut len_defs: Vec<(Local, usize)> = Vec::new();
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if !place.projection.is_empty() {
                continue;
            }
            let Rvalue::UnaryOp(op, operand) = rvalue else {
                continue;
            };
            if !matches!(op, rustc_middle::mir::UnOp::PtrMetadata) {
                continue;
            }
            let (Operand::Copy(p) | Operand::Move(p)) = operand else {
                continue;
            };
            if p.projection.is_empty()
                && p.local.as_usize() >= 1
                && p.local.as_usize() <= body.arg_count
            {
                len_defs.push((place.local, p.local.as_usize() - 1));
            }
        }
    }

    // (3) Find `x = Lt(payload, tmp)` (or `Le`) where `tmp` is a length temp.
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (_, rvalue) = &**assign;
            let Rvalue::BinaryOp(op, pair) = rvalue else {
                continue;
            };
            if !matches!(op, BinOp::Lt | BinOp::Le) {
                continue;
            }
            let (a, b) = &**pair;
            let a_root = match a {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                    copy_root(&body, p.local)
                }
                _ => continue,
            };
            if a_root != payload_root {
                continue;
            }
            let b_local = match b {
                Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            };
            let Some(&(_, arg)) = len_defs.iter().find(|(tmp, _)| Some(*tmp) == b_local) else {
                continue;
            };
            return match op {
                BinOp::Lt => Some(CallEffect::ReturnOptionSomeIndexLtArgLen { arg }),
                _ => None,
            };
        }
    }
    None
}

/// Detect `<Option<T> as Try>::branch`: `Option<T>` -> `ControlFlow<Option<!>, T>`.
/// The `Continue` payload (field 0) equals the `Some` payload (field 0), so a
/// `?`-operator `if let Some(..) = expr?` unwrap keeps the payload's provenance.
pub(crate) fn try_branch_effect(tcx: TyCtxt<'_>, callee: DefId) -> Option<CallEffect> {
    let name = tcx.def_path_str(callee);
    if !name.ends_with("::branch") {
        return None;
    }
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.arg_count != 1 {
        return None;
    }
    // Input is `Option<T>` (the `self` argument).
    let arg_ty = body.local_decls[Local::from_usize(1)].ty;
    let TyKind::Adt(arg_adt, _) = arg_ty.kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::sym::Option, arg_adt.did()) {
        return None;
    }
    // Output is `ControlFlow<..>`.
    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    let TyKind::Adt(ret_adt, _) = ret_ty.kind() else {
        return None;
    };
    if !tcx.def_path_str(ret_adt.did()).contains("ControlFlow") {
        return None;
    }
    Some(CallEffect::ReturnBranchPayload { arg: 0 })
}

/// Whether `callee` is `slice::get`/`get_mut` (an inherent method returning
/// `Option<&[T]>`/`Option<&mut [T]>`), which the VM summarizes without
/// inlining (see `try_slice_get`).  The path graph must not inline it — the
/// inlined `Some(&self[range])` body does not preserve the sub-slice's
/// provenance through the `?` operator.
pub(crate) fn is_slice_get_summary(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(assoc) = tcx.opt_associated_item(callee) else {
        return false;
    };
    let name = assoc.name();
    let name_str = name.as_str();
    if name_str != "get" && name_str != "get_mut" {
        return false;
    }
    // `slice::get`/`get_mut` return `Option<&[T]>` (or `Option<&[T]>` via a
    // `SliceIndex::Output` projection alias); identify by the `slice` impl
    // path rather than normalizing the projection type.
    let path = tcx.def_path_str(callee);
    path.contains("::slice::") || path.contains("slice::<impl")
}

/// Whether block `a` dominates block `b` (every path from the entry to `b`
/// passes through `a`).  Simple BFS: `a` dominates `b` iff `b` is *not*
/// reachable from the entry when `a` is skipped.
fn block_dominates(body: &rustc_middle::mir::Body<'_>, a: BasicBlock, b: BasicBlock) -> bool {
    let entry = 0usize;
    let mut queue = VecDeque::from([entry]);
    let mut seen = HashSet::from([entry]);
    while let Some(cur) = queue.pop_front() {
        if cur == b.as_usize() {
            return false; // reached b without passing a
        }
        if cur == a.as_usize() {
            continue; // skip a's successors
        }
        for succ in body.basic_blocks[BasicBlock::from_usize(cur)]
            .terminator()
            .successors()
        {
            if seen.insert(succ.as_usize()) {
                queue.push_back(succ.as_usize());
            }
        }
    }
    true
}

/// Detect a UTF-8-decoder shape: the function returns `Option<(.., usize, ..)>`
/// whose length field is a *constant* on each `Some` return, and each
/// `Some((.., len))` return is guarded by a `slice.get(len - 1)?` (so
/// `len <= slice.len()`).  Summarizes the tuple's length field as
/// `field <= arg.len()` so a caller can re-prove `finger <= finger_back` after
/// `finger += len`.
pub(crate) fn try_decode_length_return_effect(
    tcx: TyCtxt<'_>,
    callee: DefId,
) -> Option<CallEffect> {
    if !tcx.is_mir_available(callee) {
        return None;
    }
    let body = tcx.optimized_mir(callee);
    if body.arg_count < 1 {
        return None;
    }
    // Return type must be `Option<(.., usize, ..)>`.
    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    let TyKind::Adt(adt, substs) = ret_ty.kind() else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did()) {
        return None;
    }
    let inner = substs.type_at(0);
    let TyKind::Tuple(tys) = inner.kind() else {
        return None;
    };
    let Some(field) = tys
        .iter()
        .position(|t| matches!(t.kind(), TyKind::Uint(rustc_middle::ty::UintTy::Usize)))
    else {
        return None;
    };

    // Collect `Some((.., L))` returns with constant or computed length `L`.
    let mut returns: Vec<(BasicBlock, u64)> = Vec::new();
    let mut computed_returns: Vec<BasicBlock> = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        for stmt in &data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if place.local.as_usize() != 0 || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(kind, operands) = rvalue else {
                continue;
            };
            let rustc_middle::mir::AggregateKind::Adt(adt, variant_idx, ..) = &**kind else {
                continue;
            };
            if !tcx.is_diagnostic_item(rustc_span::sym::Option, *adt) {
                continue;
            }
            if variant_idx.as_usize() != 1 {
                continue; // not `Some`
            }
            let Some(payload) = operands.iter().next() else {
                continue;
            };
            // Payload is `(code, len)` (or a temp holding it).
            match tuple_field_len_kind(&body, payload, field) {
                Some(TupleFieldLen::Const(len)) => returns.push((bb, len)),
                Some(TupleFieldLen::LenSub) => computed_returns.push(bb),
                None => {}
            }
        }
    }
    if returns.is_empty() && computed_returns.is_empty() {
        return None;
    }

    // Collect `slice.get(k)` calls with a constant `k`.
    let mut gets: Vec<(BasicBlock, u64)> = Vec::new();
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call { func, args, .. } = &data.terminator().kind else {
            continue;
        };
        let Some(get_callee) = helpers::dep_callee_def_id(func) else {
            continue;
        };
        if !tcx.opt_associated_item(get_callee).is_some_and(|a| {
            let name = a.name();
            matches!(name.as_str(), "get" | "index" | "index_mut")
        }) {
            continue;
        }
        let Some(k) = args
            .get(1)
            .and_then(|a| helpers::operand_const_u64(&a.node))
        else {
            continue;
        };
        gets.push((bb, k));
    }
    if gets.is_empty() && computed_returns.is_empty() {
        return None;
    }

    // For each return with length `L`, `get(L - 1)` must dominate it.  The
    // `L == 1` (ASCII) case only needs the slice to be non-empty, which a
    // well-formed decoder establishes with its first byte access (often
    // optimized away from `get(0)` into a direct deref), so it is accepted.
    for (bb, len) in &returns {
        if *len <= 1 {
            continue;
        }
        let k = len.checked_sub(1)?;
        let Some(&(get_bb, _)) = gets.iter().find(|(_, kk)| *kk == k) else {
            return None;
        };
        if !block_dominates(&body, get_bb, *bb) {
            return None;
        }
    }

    Some(CallEffect::ReturnOptionSomeTupleFieldLeArgLen { field, arg: 0 })
}

/// Length kind of a decoder's returned tuple length field.
enum TupleFieldLen {
    /// A constant byte length (e.g. `Some((code, 2))`).
    Const(u64),
    /// `slice.len() - x` for a non-negative `x` (e.g. `decode_last_char`'s
    /// `n - lead_idx`), so `len <= slice.len()`.
    LenSub,
}

/// Classify the length field of a `(.., len, ..)` tuple, tracing through
/// copy/move temps and a `_tmp = (..)` tuple aggregate assignment.
fn tuple_field_len_kind<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &Operand<'tcx>,
    field: usize,
) -> Option<TupleFieldLen> {
    let tuple_local = match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
        _ => return None,
    };
    let mut field_operand: Option<Operand<'tcx>> = None;
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if place.local != tuple_local || !place.projection.is_empty() {
                continue;
            }
            let Rvalue::Aggregate(kind, operands) = rvalue else {
                continue;
            };
            if !matches!(&**kind, rustc_middle::mir::AggregateKind::Tuple) {
                continue;
            }
            field_operand = operands
                .get(rustc_abi::FieldIdx::from_usize(field))
                .cloned();
        }
    }
    let mut cur = field_operand?;

    loop {
        if let Some(c) = helpers::operand_const_u64(&cur) {
            return Some(TupleFieldLen::Const(c));
        }
        let local = match &cur {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            // `SubWithOverflow`/`AddWithOverflow` yield a tuple; the value is
            // the `.0` field, so strip a single Field(0) projection and keep
            // tracing the base local.
            Operand::Copy(p) | Operand::Move(p)
                if p.projection.len() == 1
                    && matches!(
                        p.projection[0].kind(),
                        rustc_middle::mir::ProjectionElem::Field(rustc_abi::FieldIdx::ZERO, _)
                    ) =>
            {
                p.local
            }
            _ => return None,
        };
        let mut defining: Option<&Rvalue<'tcx>> = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (place, rvalue) = &**assign;
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                defining = Some(rvalue);
            }
        }
        match defining? {
            Rvalue::Use(op, ..) => cur = op.clone(),
            Rvalue::BinaryOp(BinOp::Sub | BinOp::SubWithOverflow, pair) => {
                // `len = lhs - rhs`; sound iff `lhs == slice.len()` and
                // `rhs >= 0` (the latter holds because `rhs` is a `usize`).
                let (lhs, _) = &**pair;
                return operand_is_ptr_metadata(body, lhs).then_some(TupleFieldLen::LenSub);
            }
            _ => return None,
        }
    }
}

/// Whether `operand` (through copy/move temps) is `PtrMetadata(slice)`,
/// including a `slice.len()` call (which is semantically `PtrMetadata`).
fn operand_is_ptr_metadata<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    let mut cur = operand.clone();
    loop {
        let local = match &cur {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return false,
        };
        // A `slice.len()` call result is the slice's length.
        for bb in body.basic_blocks.iter() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &bb.terminator().kind
            else {
                continue;
            };
            if destination.local == local
                && crate::verify::api_classify::is_len(helpers::dep_callee_def_id(func))
            {
                return true;
            }
        }
        let mut defining: Option<&Rvalue<'tcx>> = None;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (place, rvalue) = &**assign;
                if place.local != local || !place.projection.is_empty() {
                    continue;
                }
                defining = Some(rvalue);
            }
        }
        match defining {
            Some(Rvalue::UnaryOp(op, _)) => {
                return matches!(op, rustc_middle::mir::UnOp::PtrMetadata);
            }
            Some(Rvalue::Use(op, ..)) => cur = op.clone(),
            _ => return false,
        }
    }
}

/// Detect a `pre_dec_end(offset)` call on the receiver (arg 0) and return its
/// constant offset. `next_back_unchecked` calls `self.pre_dec_end(1)` before
/// returning the `end_or_len` field, so the returned pointer must be adjusted
/// by `offset` elements.
fn detect_pre_dec_end_offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
) -> Option<u64> {
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &term.kind else {
            continue;
        };
        let Some(callee) = helpers::dep_callee_def_id(func) else {
            continue;
        };
        if !crate::helpers::mir_utils::is_pre_dec_end(tcx, callee) {
            continue;
        }
        // Receiver is arg 0 (the iterator), offset is arg 1.
        return args
            .get(1)
            .and_then(|a| helpers::operand_const_u64(&a.node));
    }
    None
}

/// Detect a slice-iterator constructor structurally: a callee whose argument
/// is a `&[T]`/`&mut [T]` and whose return type is a struct whose first two
/// fields are pointers into `T` (field 0 = start `NonNull<T>`, field 1 = end
/// `*const T`/`*mut T`). This matches `slice::Iter`/`IterMut` *and* same-shaped
/// local re-implementations by structure rather than by the type's name.
pub(super) fn try_iter_constructor_effect<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
) -> Option<CallEffect> {
    let fn_sig = tcx.fn_sig(callee).skip_binder();
    let output = fn_sig.output().skip_binder();
    let TyKind::Adt(adt, substs) = output.kind() else {
        return None;
    };
    let inputs = fn_sig.inputs().skip_binder();
    let Some(arg0) = inputs.first() else {
        return None;
    };
    let TyKind::Ref(_, inner, _) = arg0.kind() else {
        return None;
    };
    let TyKind::Slice(elem_ty) = inner.kind() else {
        return None;
    };
    let elem_ty = *elem_ty;
    if adt.is_enum() {
        return None;
    }
    let variant = adt.non_enum_variant();
    if variant.fields.len() < 2 {
        return None;
    }
    // A pointer field is one of `*const T`/`*mut T` or `NonNull<T>` (a
    // `NonNull` pointer wrapper), whose pointee is the slice element type.
    let is_elem_ptr = |ty: Ty<'tcx>| -> bool {
        match ty.kind() {
            TyKind::RawPtr(pointee, _) => *pointee == elem_ty,
            TyKind::Adt(a, args)
                if crate::verify::api_classify::is_std_nonnull(a.did())
                    && args.type_at(0) == elem_ty =>
            {
                true
            }
            _ => false,
        }
    };
    let mut fields = variant.fields.iter();
    let (Some(f0), Some(f1)) = (fields.next(), fields.next()) else {
        return None;
    };
    if !is_elem_ptr(helpers::field_ty(tcx, f0, substs))
        || !is_elem_ptr(helpers::field_ty(tcx, f1, substs))
    {
        return None;
    }
    // The shape alone is not sufficient — two pointers into `T` could be an
    // unrelated pair. Verify (following at most one thin `_0 = ctor(&*_1)`
    // wrapper) that the constructor actually reads the slice's length, which is
    // necessary for an iterator that covers the whole slice.
    if !iter_ctor_reads_slice_len(tcx, callee, 1) {
        return None;
    }
    Some(CallEffect::ReturnIter { receiver_arg: 0 })
}

/// Whether the callee (following at most `depth` single-call wrappers) reads
/// the length of its slice argument — a necessary condition for a slice
/// iterator, whose `end` field is `start + len`.
fn iter_ctor_reads_slice_len<'tcx>(tcx: TyCtxt<'tcx>, callee: DefId, depth: usize) -> bool {
    if !tcx.is_mir_available(callee) {
        return false;
    }
    let body = tcx.optimized_mir(callee);
    if body_reads_slice_len(tcx, body) {
        return true;
    }
    if depth > 0 {
        if let Some(target) = single_call_wrapper_target(tcx, callee) {
            return iter_ctor_reads_slice_len(tcx, target, depth - 1);
        }
    }
    false
}

/// Whether `body` contains a `len` call whose receiver traces back to argument 0.
fn body_reads_slice_len<'tcx>(tcx: TyCtxt<'tcx>, body: &rustc_middle::mir::Body<'tcx>) -> bool {
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else { continue };
        let TerminatorKind::Call { func, args, .. } = &term.kind else {
            continue;
        };
        if !crate::verify::api_classify::is_len(helpers::dep_callee_def_id(func)) {
            continue;
        }
        if let Some(arg0) = args.first()
            && trace_to_callee_arg(tcx, body, &arg0.node) == Some(0)
        {
            return true;
        }
    }
    false
}

/// The callee delegated to by a thin wrapper whose body is a single call
/// returning directly into `_0` (e.g. `slice::iter` → `Iter::new`).
fn single_call_wrapper_target<'tcx>(tcx: TyCtxt<'tcx>, callee: DefId) -> Option<DefId> {
    let body = tcx.optimized_mir(callee);
    let mut found: Option<DefId> = None;
    for bb in body.basic_blocks.iter() {
        let Some(term) = &bb.terminator else { continue };
        let TerminatorKind::Call {
            func, destination, ..
        } = &term.kind
        else {
            continue;
        };
        if destination.local.as_usize() != 0 {
            continue;
        }
        let Some(c) = helpers::dep_callee_def_id(func) else {
            return None;
        };
        match found {
            Some(f) if f != c => return None,
            _ => found = Some(c),
        }
    }
    found
}

/// Cached must-write summaries, keyed by `(callee, depth)`. Depth is part of
/// the key because the `depth > 4` cutoff makes a summary computed deeper in the
/// wrapper chain less complete than one computed higher up, and the DFS reaches
/// the deep ones first.
type MustWriteMemo = HashMap<(DefId, usize), Option<HashSet<usize>>>;

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
    if let Some(summary) = memo.get(&(callee, depth)) {
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
    memo.insert((callee, depth), summary.clone());
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
            if let Some(nested_writes) = must_write_args_rec(tcx, nested, depth + 1, context, memo) {
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
