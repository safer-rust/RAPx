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
    Body, ConstValue, Local, Operand, Rvalue, StatementKind, interpret::GlobalAlloc,
};
use rustc_middle::ty::TyCtxt;

use super::common::{SmtCheckResult, SmtChecker};
use crate::verify::{
    contract::Property, helpers::Checkpoint, primitive::PrimitiveCall, verifier::ForwardVisitResult,
};

/// Check `ValidCStr` using const-bytes or path-local nul-store facts.
pub(crate) fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let tcx = checker.tcx;
    let Some(target) = checker
        .property_target(checkpoint, property)
        .or_else(|| checker.callsite_arg_place(checkpoint, 0))
    else {
        return SmtCheckResult::unknown("ValidCStr target could not be resolved");
    };
    let Some(target_local) = target.local() else {
        return SmtCheckResult::unknown("ValidCStr target is not local");
    };

    let body = tcx.optimized_mir(checkpoint.caller);
    let parents = body_parents(tcx, body);
    let root = follow_parents(&parents, target_local);

    if let Some(bytes) = const_bytes_for_local(tcx, body, root) {
        if bytes.contains(&0) {
            return SmtCheckResult::proved(
                "ValidCStr proved: pointer derives from a nul-terminated constant byte string",
            );
        }
        return super::common::failed_smt(
            "ValidCStr failed: constant byte string has no nul terminator",
        );
    }

    if nul_store_before_checkpoint(tcx, body, checkpoint, forward, &parents, root) {
        return SmtCheckResult::proved(
            "ValidCStr proved: a nul byte is stored into the source buffer before the call",
        );
    }

    SmtCheckResult::unknown("ValidCStr: could not prove nul-termination of the source bytes")
}

/// Per-body provenance parents (copies, casts, refs, as_ptr-style calls).
fn body_parents<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> crate::compat::FxHashMap<Local, Local> {
    use rustc_middle::mir::TerminatorKind;

    let mut parents: crate::compat::FxHashMap<Local, Local> = Default::default();
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
        let name = crate::verify::call_summary::call_name(tcx, func);
        if !PrimitiveCall::classify(&name).is_some_and(|p| p.is_as_ptr_like()) {
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

/// If the root local is defined by a constant reference, return the bytes of
/// the underlying allocation (following one level of static/reference
/// indirection).
fn const_bytes_for_local<'tcx>(
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
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    root: Local,
) -> bool {
    use crate::verify::path_extractor::PathStep;
    let _ = tcx;

    for step in &forward.path.steps {
        let PathStep::Block(bb) = step else {
            break;
        };
        if *bb == checkpoint.block {
            break;
        }
        let Some(data) = body.basic_blocks.get(*bb) else {
            continue;
        };
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if follow_parents(parents, target.local) != root {
                continue;
            }
            if target.projection.is_empty() {
                continue;
            }
            let Rvalue::Use(Operand::Constant(constant), ..) = rvalue else {
                continue;
            };
            let Some(scalar) = constant.const_.try_to_scalar_int() else {
                continue;
            };
            if scalar.to_uint(scalar.size()) == 0 {
                return true;
            }
        }
    }
    false
}
