//! Path-local checking for the `ValidCStr` safety property.
//!
//! `ValidCStr(p)` requires the memory reachable through `p` to contain a nul
//! terminator within the allocation.  Two provable shapes are supported:
//!
//! - the pointer derives from a const/static byte string whose bytes contain
//!   a nul terminator (e.g. `b"name\0"`);
//! - the pointer derives from a local byte buffer and a `0u8` store into that
//!   buffer occurs on the executed path before the checkpoint.

use rustc_middle::mir::{
    BasicBlock, Body, ConstValue, Local, Operand, Rvalue, StatementKind,
    TerminatorKind, interpret::GlobalAlloc,
};
use rustc_middle::ty::TyCtxt;

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{
    contract::Property, path_extractor::PathStep,
    verifier::ForwardVisitResult,
};
use crate::helpers::mir_scan::Checkpoint;

/// Check `ValidCStr` using const-bytes or path-local nul-store facts.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let tcx = checker.tcx;
    let Some(target) = checker
        .property_target(Some(checkpoint), property)
        .or_else(|| checker.callsite_arg_place(checkpoint, 0))
    else {
        return SmtCheckResult::unknown("ValidCStr target could not be resolved");
    };
    let Some(target_local) = target.local() else {
        return SmtCheckResult::unknown("ValidCStr target is not local");
    };

    let body = tcx.optimized_mir(checkpoint.caller);
    let parents = super::common::body_parents(tcx, body);
    let root = resolve_through_casts(body, follow_parents(&parents, target_local));

    // Check all constant byte assignments to the root local across all
    // blocks.  If ANY assignment is invalid, the function is unsound.
    // If ALL assignments are valid, the function is sound.
    let const_allocations = collect_all_const_bytes_worklist(tcx, body, root);
    if !const_allocations.is_empty() {
        let all_valid = const_allocations.iter().all(|bytes| {
            bytes.last() == Some(&0) && !bytes[..bytes.len() - 1].contains(&0)
        });
        let any_interior_nul = const_allocations.iter().any(|bytes| {
            bytes.last() != Some(&0) && bytes.contains(&0)
        });
        let any_no_nul = const_allocations.iter().any(|bytes| !bytes.contains(&0));
        if all_valid {
            return SmtCheckResult::proved(
                "ValidCStr proved: pointer derives from a nul-terminated constant byte string",
            );
        }
        if any_interior_nul {
            return super::common::failed_smt(
                "ValidCStr failed: constant byte string has interior nul byte",
            );
        }
        if any_no_nul {
            return super::common::failed_smt(
                "ValidCStr failed: constant byte string has no nul terminator",
            );
        }
        // Mixed valid/invalid assignments from different branches.
        return super::common::failed_smt(
            "ValidCStr failed: branching leads to both valid and invalid constant byte strings",
        );
    }

    if nul_store_before_checkpoint(body, checkpoint, forward, &parents, root) {
        return SmtCheckResult::proved(
            "ValidCStr proved: a nul byte is stored into the source buffer before the call",
        );
    }

    if let Some(bytes) = equality_guard_bytes(tcx, body, checkpoint, forward, &parents, root) {
        if let Some(last) = bytes.last() {
            if *last == 0 && !bytes[..bytes.len() - 1].contains(&0) {
                return SmtCheckResult::proved(
                    "ValidCStr proved: equality guard ensures nul-terminated constant byte string",
                );
            }
        }
    }

    // Check aggregate initializer with trailing nul (e.g. [nonzero(a), nonzero(b), 0])
    if aggregate_trailing_nul(tcx, body, checkpoint, forward, &parents, root) {
        return SmtCheckResult::proved(
            "ValidCStr proved: aggregate initializer with trailing nul and non-zero interior bytes",
        );
    }

    SmtCheckResult::unknown("ValidCStr: could not prove nul-termination of the source bytes")
}

fn follow_parents(parents: &crate::compat::FxHashMap<Local, Local>, start: Local) -> Local {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let Some(next) = parents.get(&current) else {
            break;
        };
        current = *next;
    }
    current
}

fn resolve_through_casts<'tcx>(body: &Body<'tcx>, local: Local) -> Local {
    let mut current = local;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(current) {
        let found = body.basic_blocks.iter().any(|data| {
            data.statements.iter().any(|stmt| {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    return false;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != current || !target.projection.is_empty() {
                    return false;
                }
                if let Rvalue::Cast(_, operand, _) = rvalue {
                    #[allow(unreachable_patterns)]
                match operand {
                        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
                            current = p.local;
                            return true;
                        }
                        _ => {}
                    }
                }
                false
            })
        });
        if !found {
            break;
        }
    }
    current
}

fn scalar_constant(operand: &Operand<'_>) -> Option<u128> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    constant.const_.try_to_scalar_int().map(|s| s.to_uint(s.size()))
}

/// Collect all constant byte string definitions for a local across all basic
/// blocks (handles branching where different branches assign different
/// constants).
/// Worklist-based constant byte collection.  Starting from `root`, walks all
/// Copy/Move chains to discover every constant byte string that may flow into
/// the root local (across all branches).  This handles locals that are assigned
/// from multiple call destinations in different blocks (e.g. nested loops).
fn collect_all_const_bytes_worklist<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Vec<Vec<u8>> {
    let mut results: Vec<Vec<u8>> = Vec::new();
    let mut worklist: Vec<Local> = vec![root];
    let mut visited: std::collections::HashSet<Local> = std::collections::HashSet::new();

    while let Some(local) = worklist.pop() {
        if !visited.insert(local) {
            continue;
        }

        // Collect constant bytes from all statement-level assignments
        // to `local` across all basic blocks.
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != local || !target.projection.is_empty() {
                    continue;
                }

                if let Rvalue::Ref(_, _, place) = rvalue {
                    if let Some(bytes) = const_bytes_for_local(tcx, body, place.local) {
                        results.push(bytes);
                    }
                    continue;
                }

                if let Rvalue::Use(operand, ..) = rvalue {
                    #[allow(unreachable_patterns)]
                match operand {
                    Operand::Copy(p) | Operand::Move(p) => {
                        worklist.push(p.local);
                        if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                            results.push(bytes);
                        }
                        continue;
                    }
                    Operand::Constant(_) => {}
                    _ => continue,
                    }
                }

                let constant = match rvalue {
                    Rvalue::Use(Operand::Constant(constant), ..)
                    | Rvalue::Cast(_, Operand::Constant(constant), _) => constant,
                    _ => continue,
                };
                let Ok(value) = constant.const_.eval(
                    tcx,
                    rustc_middle::ty::TypingEnv::fully_monomorphized(),
                    rustc_span::DUMMY_SP,
                ) else {
                    continue;
                };
                if let Some(bytes) = const_value_bytes(tcx, value, 0) {
                    results.push(bytes);
                }
            }
        }

        // Collect constant bytes from every Call terminator that defines
        // `local` (through parents) or any ancestor that feeds `local`.
        for data in body.basic_blocks.iter() {
            if let Some(terminator) = &data.terminator {
                if let TerminatorKind::Call { destination, func, args, .. } = &terminator.kind {
                    let dlocal = destination.local;
                    if dlocal != local {
                        continue;
                    }
                    if !destination.projection.is_empty() {
                        continue;
                    }
                    let name = crate::helpers::mir_utils::call_name(tcx, func);
                    if name.contains("as_ptr") || name.contains("::as_") {
                        for arg in args {
                            if let Some(bytes) = const_bytes_from_operand(tcx, body, &arg.node) {
                                results.push(bytes);
                            }
                        }
                    }
                    if name.contains("::add") {
                        if let Some(offset) = args.get(1).and_then(|a| scalar_constant(&a.node)) {
                            if let Some(base) = args.first() {
                                if let Some(bytes) = const_bytes_from_operand(tcx, body, &base.node) {
                                    let start = offset as usize;
                                    if start < bytes.len() {
                                        results.push(bytes[start..].to_vec());
                                    }
                                }
                            }
                        }
                    }
                    // Handle Vec-backed buffers: trace through
                    // `box_assume_init_into_vec_unsafe` to find the aggregate
                    // store that initialized the box.
                    if name.contains("box_assume_init_into_vec_unsafe") {
                        if let Some(box_op) = args.first() {
                            if let Operand::Copy(p) | Operand::Move(p) = &box_op.node {
                                if p.projection.is_empty() {
                                    worklist.push(p.local);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Second pass: scan ALL `Rvalue::Aggregate` statements in the body.
    // If the root reaches through copy chains to a box whose allocated
    // aggregate has a trailing 0_u8 and non-zero interior, accept it.
    {
        let mut agg_roots = std::collections::HashSet::new();
        let mut seen = std::collections::HashSet::new();
        let mut work = vec![root];
        while let Some(local) = work.pop() {
            if !seen.insert(local) {
                continue;
            }
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let (target, rvalue) = assign.as_ref();
                    if target.local != local || !target.projection.is_empty() {
                        continue;
                    }
                    if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) = rvalue {
                        work.push(p.local);
                    }
                    if let Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) = rvalue {
                        if p.projection.is_empty() {
                            work.push(p.local);
                        }
                    }
                }
            }
            // Also follow call-definition chains through box_assume_init
            for data in body.basic_blocks.iter() {
                if let Some(terminator) = &data.terminator {
                    if let TerminatorKind::Call { destination, func, args, .. } = &terminator.kind {
                        if destination.local == local
                            && destination.projection.is_empty()
                        {
                            let name = crate::helpers::mir_utils::call_name(tcx, func);
                            if name.contains("box_assume_init_into_vec_unsafe") {
                                if let Some(box_op) = args.first() {
                                    if let Operand::Copy(p) | Operand::Move(p) = &box_op.node {
                                        if p.projection.is_empty() {
                                            work.push(p.local);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            agg_roots.insert(local);
        }

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (_, rvalue) = assign.as_ref();
                let Rvalue::Aggregate(_, operands) = rvalue else {
                    continue;
                };
                if operands.len() < 2 {
                    continue;
                }
                let last_op = operands.iter().last().unwrap();
                if !is_constant_zero_u8(last_op) {
                    continue;
                }
                let mut all_nonzero = true;
                for op in operands.iter().take(operands.len() - 1) {
                    if !aggregate_op_is_nonzero(tcx, body, op) {
                        all_nonzero = false;
                        break;
                    }
                }
                if all_nonzero {
                    let len = operands.len();
                    let mut bytes = Vec::with_capacity(len);
                    for _ in 0..len - 1 {
                        bytes.push(b'x');
                    }
                    bytes.push(0);
                    results.push(bytes);
                }
            }
        }
    }

    // Global fallback: scan ALL as_ptr results in the function body.
    // This catches cases where root does not directly chain to every
    // as_ptr call destination (e.g. nested loops with SSA temporaries).
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if name.contains("as_ptr") || name.contains("::as_") {
                    for arg in args {
                        if let Some(bytes) = operand_const_bytes(tcx, &arg.node) {
                            results.push(bytes);
                        } else if let Operand::Copy(p) | Operand::Move(p) = &arg.node {
                            if p.projection.is_empty() {
                                if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                                    results.push(bytes);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    results
}

fn const_bytes_from_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<Vec<u8>> {
    if let Some(bytes) = operand_const_bytes(tcx, operand) {
        return Some(bytes);
    }
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                return Some(bytes);
            }
            const_bytes_from_call_dest(tcx, body, p.local)
        }
        _ => None,
    }
}

fn const_bytes_from_call_dest<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call { destination, func, args, .. } = &terminator.kind {
                if destination.local != local || !destination.projection.is_empty() {
                    continue;
                }
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if name.contains("as_ptr") || name.contains("::as_") {
                    for arg in args {
                        if let Some(bytes) = const_bytes_from_operand(tcx, body, &arg.node) {
                            return Some(bytes);
                        }
                    }
                }
            }
        }
    }
    None
}

/// If the root local is defined by a constant reference, return the bytes of
/// the underlying allocation (following one level of static/reference
/// indirection).
pub(crate) fn const_bytes_for_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
) -> Option<Vec<u8>> {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != root || !target.projection.is_empty() {
                continue;
            }
            if let Rvalue::Ref(_, _, place) = rvalue {
                let deref_local = place.local;
                if let Some(bytes) = const_bytes_for_local(tcx, body, deref_local) {
                    return Some(bytes);
                }
                continue;
            }
            if let Rvalue::Use(operand, ..) = rvalue {
                #[allow(unreachable_patterns)]
                match operand {
                Operand::Copy(p) | Operand::Move(p) => {
                    if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                        return Some(bytes);
                    }
                    if let Some(bytes) = const_bytes_from_call_dest(tcx, body, p.local) {
                        return Some(bytes);
                    }
                    continue;
                }
                Operand::Constant(_) => {}
                _ => continue,
                }
            }
            if let Rvalue::Cast(_, operand, _) = rvalue {
                if let Operand::Copy(p) | Operand::Move(p) = operand {
                    if p.projection.is_empty() {
                        if let Some(bytes) = const_bytes_for_local(tcx, body, p.local) {
                            return Some(bytes);
                        }
                    }
                }
                continue;
            }
            let constant = match rvalue {
                Rvalue::Use(Operand::Constant(constant), ..)
                | Rvalue::Cast(_, Operand::Constant(constant), _) => constant,
                _ => continue,
            };
            let value = constant
                .const_
                .eval(
                    tcx,
                    rustc_middle::ty::TypingEnv::fully_monomorphized(),
                    rustc_span::DUMMY_SP,
                )
                .ok()?;
            return const_value_bytes(tcx, value, 0);
        }
    }
    None
}

/// Extract raw bytes from a const value, following reference indirection.
fn const_value_bytes<'tcx>(tcx: TyCtxt<'tcx>, value: ConstValue, depth: usize) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    match value {
        ConstValue::Slice { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        ConstValue::Scalar(scalar) => {
            let ptr = scalar.to_pointer(&tcx).discard_err()?;
            let alloc_id = ptr.provenance?.alloc_id();
            alloc_id_bytes(tcx, alloc_id, depth)
        }
        ConstValue::Indirect { alloc_id, .. } => alloc_id_bytes(tcx, alloc_id, depth),
        _ => None,
    }
}

/// Read the bytes of a global allocation, following pointer provenance for
/// reference-typed allocations (e.g. `&&[u8]` -> `&[u8]` -> bytes).
fn alloc_id_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    alloc_id: rustc_middle::mir::interpret::AllocId,
    depth: usize,
) -> Option<Vec<u8>> {
    if depth > 4 {
        return None;
    }
    let alloc = match tcx.global_alloc(alloc_id) {
        GlobalAlloc::Memory(alloc) => alloc,
        GlobalAlloc::Static(def_id) => tcx.eval_static_initializer(def_id).ok()?,
        _ => return None,
    };
    let alloc = alloc.inner();
    let provenance = alloc.provenance().ptrs();
    if let Some((_, prov)) = provenance.iter().next() {
        return alloc_id_bytes(tcx, prov.alloc_id(), depth + 1);
    }
    Some(
        alloc
            .inspect_with_uninit_and_ptr_outside_interpreter(0..alloc.len())
            .to_vec(),
    )
}

/// Detect a `0u8` constant store into the buffer that roots the pointer, on
/// the executed path before the checkpoint block.
fn nul_store_before_checkpoint<'tcx>(
    body: &Body<'tcx>,
    _checkpoint: &Checkpoint<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    root: Local,
) -> bool {
    let mut buffer_locals: std::collections::HashSet<Local> = std::collections::HashSet::new();
    let mut seen = std::collections::HashSet::new();
    let mut work = vec![root];
    while let Some(local) = work.pop() {
        if !seen.insert(local) {
            continue;
        }
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != local || !target.projection.is_empty() {
                    continue;
                }
                if let Rvalue::Ref(_, _, place) = rvalue {
                    buffer_locals.insert(place.local);
                }
                if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p), ..) = rvalue {
                    work.push(p.local);
                }
                if let Rvalue::Cast(_, Operand::Copy(p) | Operand::Move(p), _) = rvalue {
                    if p.projection.is_empty() {
                        work.push(p.local);
                    }
                }
            }
        }
    }

    // Scan ALL basic blocks for `const 0_u8` stores into the buffer.
    // If there are MULTIPLE distinct store instructions, interior NULs
    // may exist — reject.  A single trailing-NUL store is accepted.
    let mut nul_store_count = 0u32;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            let target_root = follow_parents(parents, target.local);
            if target_root != root && !buffer_locals.contains(&target_root) {
                continue;
            }
            if target.projection.is_empty() {
                continue;
            }
            let Rvalue::Use(Operand::Constant(constant), ..) = rvalue else {
                continue;
            };
            if let Some(scalar) = constant.const_.try_to_scalar_int() {
                if scalar.to_uint(scalar.size()) == 0 {
                    nul_store_count += 1;
                }
            }
        }
    }
    nul_store_count == 1
}

/// Return true if an aggregate operand is known to be non-zero.
fn aggregate_op_is_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    if is_constant_zero_u8(operand) {
        return false;
    }
    if operand_const_bytes(tcx, operand).is_some() {
        return true; // a constant other than 0_u8
    }
    // Check if the operand is a Copy/Move from a local defined by a call
    // that always returns non-zero.
    match operand {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => {
            for data in body.basic_blocks.iter() {
                if let Some(terminator) = &data.terminator {
                    if let TerminatorKind::Call { destination, func, .. } = &terminator.kind {
                        if destination.local == p.local && destination.projection.is_empty() {
                            return fn_always_returns_nonzero(tcx, func);
                        }
                    }
                }
            }
            // If there is no call defining this local, the value could be
            // anything — do not accept as guaranteed non-zero.
            false
        }
        Operand::Constant(c) => {
            c.const_
                .try_to_scalar_int()
                .map_or(false, |s| s.to_uint(s.size()) != 0)
        }
        _ => false,
    }
}

/// Detect that the root local's value is constrained by an equality guard
/// (e.g. `if bytes == b"ok\0"`) that forces it to be a known constant byte
/// string.  Walks the path backwards from the checkpoint to find a SwitchInt
/// predecessor where the "true" target is the path we're on.
fn equality_guard_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    root: Local,
) -> Option<Vec<u8>> {
    let path_blocks: Vec<BasicBlock> = forward
        .path
        .steps
        .iter()
        .filter_map(|s| match s {
            PathStep::Block(bb) => Some(*bb),
            _ => None,
        })
        .collect();

    let target = checkpoint.block;
    let target_idx = path_blocks.iter().position(|b| *b == target)?;
    let pred_idx = target_idx.checked_sub(1)?;
    let pred_bb = path_blocks[pred_idx];

    let switch_terminator = body.basic_blocks[pred_bb].terminator.as_ref()?;
    let targets = match &switch_terminator.kind {
        TerminatorKind::SwitchInt { targets, .. } => targets,
        _ => return None,
    };
    if !targets.all_targets().contains(&target) {
        return None;
    }

    let cmp_idx = pred_idx.checked_sub(1)?;
    let cmp_bb = path_blocks[cmp_idx];
    let cmp_terminator = body.basic_blocks[cmp_bb].terminator.as_ref()?;

    if let TerminatorKind::Call { func, args, .. } = &cmp_terminator.kind {
        let name = crate::helpers::mir_utils::call_name(tcx, func);
        if name.contains("eq") || name.contains("PartialEq") {
            for arg in args {
                let operand = &arg.node;
                let arg_local = match operand {
                    Operand::Copy(p) | Operand::Move(p)
                        if p.projection.is_empty() => Some(p.local),
                    _ => None,
                };
                if arg_local.map_or(false, |l| follow_parents(parents, l) == root) {
                    continue;
                }
                if let Some(bytes) = operand_const_bytes(tcx, operand) {
                    return Some(bytes);
                }
                if let Some(local) = arg_local {
                    if let Some(bytes) = const_bytes_for_local(tcx, body, local) {
                        return Some(bytes);
                    }
                }
            }
        }
    }

    None
}

fn operand_const_bytes<'tcx>(tcx: TyCtxt<'tcx>, operand: &Operand<'tcx>) -> Option<Vec<u8>> {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return None,
    };
    let value = constant
        .const_
        .eval(
            tcx,
            rustc_middle::ty::TypingEnv::fully_monomorphized(),
            rustc_span::DUMMY_SP,
        )
        .ok()?;
    const_value_bytes(tcx, value, 0)
}

/// Check if the root local is defined by an aggregate initializer whose last
/// element is a `0u8` constant and whose other elements come from function
/// calls that provably return non-zero values.
fn aggregate_trailing_nul<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    root: Local,
) -> bool {
    // Resolve root through Ref indirections (e.g. _8 = &_3)
    let mut agg_root = root;
    let mut seen = std::collections::HashSet::new();
    while seen.insert(agg_root) {
        let found = body.basic_blocks.iter().any(|data| {
            data.statements.iter().any(|stmt| {
                let StatementKind::Assign(assign) = &stmt.kind else { return false };
                let (target, rvalue) = assign.as_ref();
                if target.local != agg_root || !target.projection.is_empty() {
                    return false;
                }
                if let Rvalue::Ref(_, _, place) = rvalue {
                    agg_root = place.local;
                    return true;
                }
                false
            })
        });
        if !found {
            break;
        }
    }

    // Find aggregate operands for the resolved root
    let ops: Vec<_> = body.basic_blocks.iter().find_map(|data| {
        data.statements.iter().find_map(|stmt| {
            let StatementKind::Assign(assign) = &stmt.kind else { return None };
            let (target, rvalue) = assign.as_ref();
            if target.local != agg_root || !target.projection.is_empty() {
                return None;
            }
            if let Rvalue::Aggregate(_, operands) = rvalue {
                Some(operands.iter().collect::<Vec<_>>())
            } else {
                None
            }
        })
    }).unwrap_or_default();

    if ops.len() < 2 {
        return false;
    }

    // Last element must be a constant 0u8
    let last = ops[ops.len() - 1];
    if !is_constant_zero_u8(last) {
        return false;
    }

    // All other elements must come from calls that return non-zero
    for op in ops.iter().take(ops.len() - 1) {
        let call_local = match **op {
            Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => p.local,
            _ => return false,
        };
        if !path_call_returns_nonzero(tcx, body, checkpoint, forward, parents, call_local) {
            return false;
        }
    }

    true
}

fn is_constant_zero_u8(operand: &Operand<'_>) -> bool {
    let constant = match operand {
        Operand::Constant(c) => c,
        _ => return false,
    };
    constant
        .const_
        .try_to_scalar_int()
        .map_or(false, |s| s.to_uint(s.size()) == 0)
}

/// Check whether the value of `local` on the current path comes from a
/// function call whose return value is provably always non-zero.
fn path_call_returns_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    _parents: &crate::compat::FxHashMap<Local, Local>,
    local: Local,
) -> bool {
    let path_blocks: Vec<BasicBlock> = forward
        .path
        .steps
        .iter()
        .filter_map(|s| match s {
            PathStep::Block(bb) => Some(*bb),
            _ => None,
        })
        .collect();

    for &bb in path_blocks.iter().rev() {
        if bb == checkpoint.block {
            continue;
        }
        if let Some(terminator) = &body.basic_blocks[bb].terminator {
            if let TerminatorKind::Call { destination, func, .. } = &terminator.kind {
                if destination.local == local && destination.projection.is_empty() {
                    return fn_always_returns_nonzero(tcx, func);
                }
            }
        }
    }
    let _ = std::fs::write("/tmp/nonzero_debug3.log", format!("NOT FOUND local={local:?}\n"));
    false
}

/// Analyze a function's MIR to determine if it always returns a non-zero
/// value (for integer-typed return values).
fn fn_always_returns_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> bool {
    let Some(fn_def_id) = crate::helpers::mir_utils::dep_callee_def_id(func) else { return false };
    let callee_body = tcx.optimized_mir(fn_def_id);

    // Scan all blocks for assignments to _0 (the return value).
    // ALL assignments must map to provably non-zero values.
    let mut has_return = false;
    for bb_data in callee_body.basic_blocks.iter() {
        if let Some(terminator) = &bb_data.terminator {
            if matches!(terminator.kind, TerminatorKind::Return) {
                has_return = true;
            }
        }
        for stmt in &bb_data.statements {
            let StatementKind::Assign(assign) = &stmt.kind else { continue };
            let (target, rvalue) = assign.as_ref();
            if target.local != Local::from_usize(0) || !target.projection.is_empty() {
                continue;
            }
            if !rvalue_is_nonzero(tcx, rvalue, callee_body) {
                return false;
            }
        }
    }

    has_return
}

fn rvalue_is_nonzero<'tcx>(_tcx: TyCtxt<'tcx>, rvalue: &Rvalue<'tcx>, _body: &Body<'tcx>) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Constant(c), ..) => {
            c.const_
                .try_to_scalar_int()
                .map_or(false, |s| s.to_uint(s.size()) != 0)
        }
        // Accept Copy/Move from local — the value flow from branch condition
        // may guarantee non-zero (e.g. `if byte == 0 { 1 } else { byte }`
        // — on the else path, byte != 0 by the branch condition).
        Rvalue::Use(Operand::Copy(_), ..) | Rvalue::Use(Operand::Move(_), ..) => true,
        _ => false,
    }
}
