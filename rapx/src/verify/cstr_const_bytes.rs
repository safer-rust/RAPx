//! Recovery of constant C-string byte contents.
//!
//! Discharges `ValidCStr` obligations when the buffer is a compile-time
//! constant: it traces `Ref`/`Use`/cast chains and `as_ptr`/`::add` calls back
//! to `b"..."`/aggregate literals, validating the trailing NUL and interior
//! bytes.

use rustc_middle::mir::{
    Body, Local, Operand, Rvalue, StatementKind,
    TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::DUMMY_SP;

use crate::compat::FxHashMap;

pub(crate) fn follow_parents(parents: &FxHashMap<Local, Local>, start: Local) -> Local {
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

pub(crate) fn resolve_through_casts<'tcx>(body: &Body<'tcx>, local: Local) -> Local {
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

pub(crate) fn collect_all_const_bytes_worklist<'tcx>(
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
                    DUMMY_SP,
                ) else {
                    continue;
                };
                if let Some(bytes) = crate::helpers::mir_utils::const_value_bytes(tcx, value, 0) {
                    results.push(bytes);
                }
            }
        }

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
                    DUMMY_SP,
                )
                .ok()?;
            return crate::helpers::mir_utils::const_value_bytes(tcx, value, 0);
        }
    }
    None
}

fn aggregate_op_is_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> bool {
    if is_constant_zero_u8(operand) {
        return false;
    }
    if operand_const_bytes(tcx, operand).is_some() {
        return true;
    }
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
            DUMMY_SP,
        )
        .ok()?;
    crate::helpers::mir_utils::const_value_bytes(tcx, value, 0)
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

fn fn_always_returns_nonzero<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
) -> bool {
    let Some(fn_def_id) = crate::helpers::mir_utils::dep_callee_def_id(func) else { return false };
    let callee_body = tcx.optimized_mir(fn_def_id);

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
        Rvalue::Use(Operand::Copy(_), ..) | Rvalue::Use(Operand::Move(_), ..) => true,
        _ => false,
    }
}

pub(crate) fn body_parents<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> FxHashMap<Local, Local> {
    let mut parents: FxHashMap<Local, Local> = Default::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            let source = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
                | Rvalue::Ref(_, _, place)
                | Rvalue::RawPtr(_, place)
                | Rvalue::CopyForDeref(place) => Some(place.local),
                _ => None,
            };
            if let Some(source) = source {
                parents.entry(target.local).or_insert(source);
            }
        }
        let Some(terminator) = &data.terminator else {
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
        let name = crate::helpers::mir_utils::call_name(tcx, func);
        if !crate::helpers::api_classify::is_as_ptr(&name) {
            continue;
        }
        let Some(source) = args.first().and_then(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        }) else {
            continue;
        };
        parents.entry(destination.local).or_insert(source);
    }
    parents
}
