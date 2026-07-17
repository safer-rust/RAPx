//! Crate-level pointer pedigree analysis.
//!
//! Some pointer obligations (`NonNull`, `Init`, `ValidPtr`) cannot be proved
//! path-locally when the pointer comes from a private struct field or a
//! crate-private helper parameter.  In those cases the whole crate is the
//! verification boundary: if every construction site (or call site) derives
//! the pointer from a live reference — optionally pairing the element count
//! with the same source's length — the obligation holds for all safe uses.

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{AggregateKind, BasicBlock, Body, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use crate::verify::{
    contract::{ContractExpr, Property},
    helpers::Checkpoint,
    primitive::PrimitiveCall,
    verifier::ForwardVisitResult,
};

use super::{alias, common::SmtChecker};

/// How the element-count argument constrains the pointer source.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CountSpec {
    /// A constant count of one element: the source must be a reference to a
    /// sized value (not a slice, whose length could be zero).
    One,
    /// The count must be the length of the same aggregate that produced the
    /// pointer (`X.as_ptr()` paired with `X.len()`).
    PairedWithSource,
    /// No count constraint (NonNull only needs the pointer itself).
    Unconstrained,
}

/// Attempts a crate-level pedigree proof for the checkpoint's pointer arg.
/// Returns `Some(reason)` when every construction/call site guarantees the
/// property.
pub(super) fn pedigree_proof<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
    require_count: bool,
) -> Option<String> {
    let tcx = checker.tcx;
    let ptr_place = checker
        .property_target(checkpoint, property)
        .or_else(|| checker.callsite_arg_place(checkpoint, 0))?;
    let resolved = alias::resolve_forward_place(ptr_place, forward);

    let count = if require_count {
        resolve_count_spec(checker, checkpoint, property, forward)?
    } else {
        CountSpec::Unconstrained
    };

    if let Some(origin) = alias::self_field_origin(tcx, checkpoint.caller, &resolved) {
        let len_field = match count {
            CountSpec::PairedWithSource => {
                let len_place = checker.callsite_arg_place(checkpoint, 1)?;
                let len_resolved = alias::resolve_forward_place(len_place, forward);
                let len_origin = alias::self_field_origin(tcx, checkpoint.caller, &len_resolved)?;
                if len_origin.struct_def_id != origin.struct_def_id {
                    return None;
                }
                Some(len_origin.field_index)
            }
            _ => None,
        };
        return field_pedigree_proof(tcx, &origin, count, len_field);
    }

    let param_index = alias::param_index_of_origin(tcx, checkpoint.caller, &resolved)?;
    if alias::is_externally_reachable(tcx, checkpoint.caller) {
        return None;
    }
    let len_param = match count {
        CountSpec::PairedWithSource => {
            let len_place = checker.callsite_arg_place(checkpoint, 1)?;
            let len_resolved = alias::resolve_forward_place(len_place, forward);
            let body = tcx.optimized_mir(checkpoint.caller);
            let local = len_resolved.local()?;
            if !len_resolved.fields.is_empty()
                || local.as_usize() == 0
                || local.as_usize() > body.arg_count
            {
                return None;
            }
            Some(local.as_usize() - 1)
        }
        _ => None,
    };
    param_pedigree_proof(tcx, checkpoint.caller, param_index, count, len_param)
}

/// Determine the count discipline from the property's element-count argument.
fn resolve_count_spec<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    property: &Property<'tcx>,
    _forward: &ForwardVisitResult<'tcx>,
) -> Option<CountSpec> {
    match checker.property_len_expr(checkpoint, property) {
        Some(ContractExpr::Const(1)) => Some(CountSpec::One),
        Some(_) => Some(CountSpec::PairedWithSource),
        None => Some(CountSpec::One),
    }
}

/// Prove the pedigree for a private struct raw-pointer field.
fn field_pedigree_proof<'tcx>(
    tcx: TyCtxt<'tcx>,
    origin: &alias::SelfFieldOrigin,
    count: CountSpec,
    len_field: Option<usize>,
) -> Option<String> {
    let struct_def_id = origin.struct_def_id;
    if struct_def_id.as_local().is_none() {
        return None;
    }
    let adt = tcx.adt_def(struct_def_id);
    let field = adt.all_fields().nth(origin.field_index)?;
    if field.vis.is_public() && alias::is_externally_reachable(tcx, struct_def_id) {
        return None;
    }

    let mut store_count = 0usize;
    for def_id in crate_fn_ids(tcx) {
        let body = tcx.optimized_mir(def_id);
        let parents = body_parents(tcx, body);

        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();

                // Whole-struct construction.
                if let Rvalue::Aggregate(kind, operands) = rvalue {
                    let AggregateKind::Adt(adt_def_id, _, _, _, _) = **kind else {
                        continue;
                    };
                    if adt_def_id != struct_def_id {
                        continue;
                    }
                    store_count += 1;
                    let ptr_operand = operands.iter().nth(origin.field_index).cloned()?;
                    if !operand_is_ref_rooted(tcx, body, &parents, &ptr_operand, count) {
                        return None;
                    }
                    if let Some(len_index) = len_field {
                        let len_operand = operands.iter().nth(len_index).cloned()?;
                        if !operands_share_len_source(
                            tcx,
                            body,
                            &parents,
                            &ptr_operand,
                            &len_operand,
                        ) {
                            return None;
                        }
                    }
                    continue;
                }

                // Direct field store `x.field = v`.
                if target.projection.len() == 1 {
                    if let Some(field_idx) = target.projection.iter().find_map(|elem| match elem {
                        rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                        _ => None,
                    }) {
                        let base_ty = body.local_decls[target.local].ty.peel_refs();
                        let TyKind::Adt(target_adt, _) = base_ty.kind() else {
                            continue;
                        };
                        if target_adt.did() != struct_def_id || field_idx != origin.field_index {
                            continue;
                        }
                        store_count += 1;
                        let stored = match rvalue {
                            Rvalue::Use(operand, ..) | Rvalue::Cast(_, operand, _) => {
                                operand.clone()
                            }
                            _ => return None,
                        };
                        if !operand_is_ref_rooted(tcx, body, &parents, &stored, count) {
                            return None;
                        }
                        if len_field.is_some() {
                            // A lone pointer store cannot re-establish the
                            // paired length invariant; bail out.
                            return None;
                        }
                    }
                }
            }
        }
    }

    if store_count == 0 {
        return None;
    }
    Some(format!(
        "crate-level invariant: every store to `{}` derives from a live reference{}",
        origin.field_name,
        if len_field.is_some() {
            " with a matching source length"
        } else {
            ""
        }
    ))
}

/// Prove the pedigree for a crate-private function's raw-pointer parameter.
fn param_pedigree_proof<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee: DefId,
    ptr_param: usize,
    count: CountSpec,
    len_param: Option<usize>,
) -> Option<String> {
    let sites = alias::local_callsites(tcx, callee);
    if sites.is_empty() {
        return None;
    }
    for site in &sites {
        let body = tcx.optimized_mir(site.caller);
        let parents = body_parents(tcx, body);
        let ptr_operand = site.args.get(ptr_param)?.clone();
        if !operand_is_ref_rooted(tcx, body, &parents, &ptr_operand, count) {
            return None;
        }
        if let Some(len_param) = len_param {
            let len_operand = site.args.get(len_param)?.clone();
            if !operands_share_len_source(tcx, body, &parents, &ptr_operand, &len_operand) {
                return None;
            }
        }
    }
    Some(format!(
        "crate-private helper: all {} call site(s) pass a reference-derived pointer{}",
        sites.len(),
        if len_param.is_some() {
            " with a matching source length"
        } else {
            ""
        }
    ))
}

/// Detects the `Vec::from_raw_parts(x.as_mut_ptr(), x.len(), x.capacity())`
/// round-trip pattern: all three arguments derive from the same live Vec, so
/// the allocation, layout, and numeric preconditions hold by construction.
pub(super) fn vec_from_raw_parts_roundtrip<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<String> {
    let tcx = checker.tcx;
    let callee = checkpoint.callee?;
    let name = tcx.def_path_str(callee);
    if !(name.contains("from_raw_parts") && (name.contains("Vec") || name.contains("vec::"))) {
        return None;
    }
    let body = tcx.optimized_mir(checkpoint.caller);
    let parents = body_parents(tcx, body);

    let arg_local = |index: usize| -> Option<Local> {
        match checkpoint.args.get(index)? {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        }
    };

    let ptr_root = follow_parents(&parents, arg_local(0)?);
    let root_ty = body.local_decls[ptr_root].ty.peel_refs();
    let TyKind::Adt(adt, _) = root_ty.kind() else {
        return None;
    };
    if !tcx.def_path_str(adt.did()).contains("Vec") {
        return None;
    }

    let len_receiver =
        call_receiver_root(tcx, body, &parents, arg_local(1)?, |primitive, name| {
            primitive == Some(PrimitiveCall::Len) || name.ends_with("::len")
        })?;
    let cap_receiver = call_receiver_root(tcx, body, &parents, arg_local(2)?, |_, name| {
        name.ends_with("::capacity")
    })?;

    if len_receiver == ptr_root && cap_receiver == ptr_root {
        return Some(format!(
            "Vec round-trip: pointer, length, and capacity all derive from the same live Vec `{ptr_root:?}`"
        ));
    }
    None
}

/// Follow the operand to a defining call matching `matches`, returning the
/// provenance root of that call's receiver.
fn call_receiver_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    start: Local,
    matches: impl Fn(Option<PrimitiveCall>, &str) -> bool,
) -> Option<Local> {
    let mut current = start;
    let mut seen = std::collections::HashSet::new();
    loop {
        for data in body.basic_blocks.iter() {
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
            if destination.local != current {
                continue;
            }
            let name = crate::verify::call_summary::call_name(tcx, func);
            if !matches(PrimitiveCall::classify(&name), &name) {
                return None;
            }
            let receiver = args.first().and_then(|arg| match &arg.node {
                Operand::Copy(place) | Operand::Move(place) => Some(place.local),
                _ => None,
            })?;
            return Some(follow_parents(parents, receiver));
        }
        if !seen.insert(current) {
            return None;
        }
        let Some(next) = parents.get(&current) else {
            return None;
        };
        current = *next;
    }
}

/// All local function definitions with MIR available.
fn crate_fn_ids(tcx: TyCtxt<'_>) -> Vec<DefId> {
    tcx.mir_keys(())
        .iter()
        .map(|local| local.to_def_id())
        .filter(|def_id| {
            matches!(tcx.def_kind(*def_id), DefKind::Fn | DefKind::AssocFn)
                && tcx.is_mir_available(*def_id)
        })
        .collect()
}

/// Per-body provenance parents: copies, casts, refs, and pointer-extraction
/// calls collapse to the underlying source local.
fn body_parents<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
) -> crate::compat::FxHashMap<Local, Local> {
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

/// True when the operand's provenance root is a live reference (or an owned
/// aggregate) compatible with the count discipline.
fn operand_is_ref_rooted<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    operand: &Operand<'tcx>,
    count: CountSpec,
) -> bool {
    let Some(place) = (match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }) else {
        return false;
    };
    let root = follow_parents(parents, place.local);
    let root_ty = body.local_decls[root].ty;
    match root_ty.kind() {
        TyKind::Ref(_, inner, _) => match count {
            CountSpec::One => !matches!(inner.kind(), TyKind::Slice(_) | TyKind::Str),
            _ => true,
        },
        TyKind::Adt(adt, _) => {
            let name = tcx.def_path_str(adt.did());
            let owned = name.contains("Vec") || name.contains("Box") || name.contains("String");
            owned && count != CountSpec::One
        }
        TyKind::Array(..) => true,
        _ => false,
    }
}

/// True when the count operand is `len(X)` for the same root `X` that
/// produced the pointer operand.
fn operands_share_len_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    parents: &crate::compat::FxHashMap<Local, Local>,
    ptr_operand: &Operand<'tcx>,
    len_operand: &Operand<'tcx>,
) -> bool {
    let Some(ptr_place) = (match ptr_operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }) else {
        return false;
    };
    let Some(len_place) = (match len_operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }) else {
        return false;
    };
    let ptr_root = follow_parents(parents, ptr_place.local);

    // The len operand must reach a `len()` call whose receiver shares the
    // pointer's root.
    let mut current = len_place.local;
    let mut seen = std::collections::HashSet::new();
    loop {
        if let Some(receiver) = len_call_receiver(tcx, body, current) {
            return follow_parents(parents, receiver) == ptr_root;
        }
        if !seen.insert(current) {
            return false;
        }
        let Some(next) = parents.get(&current) else {
            return false;
        };
        current = *next;
    }
}

/// If `local` is the destination of a `len()` call, return the receiver local.
fn len_call_receiver<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, local: Local) -> Option<Local> {
    for data in body.basic_blocks.iter() {
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
        if destination.local != local {
            continue;
        }
        let name = crate::verify::call_summary::call_name(tcx, func);
        if PrimitiveCall::classify(&name) != Some(PrimitiveCall::Len) {
            return None;
        }
        return args.first().and_then(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place.local),
            _ => None,
        });
    }
    None
}

#[allow(dead_code)]
fn unused_block(_: BasicBlock) {}
