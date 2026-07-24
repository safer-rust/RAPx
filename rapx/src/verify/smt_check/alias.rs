//! Alias hazard checks for unsafe view-producing APIs.
//!
//! `Alias` is more stateful than numeric SPs such as `Align`: calls like
//! `from_raw_parts_mut` create a view whose lifetime constrains later uses of
//! the original raw pointer.  This module handles the first, deliberately small
//! slice-view model:
//!
//! - a local view only checks later uses in the same function;
//! - an escaped view from `self.field` checks whether the same struct still
//!   exposes or writes through that raw field via safe methods or public fields.

use std::collections::{HashMap, HashSet};

use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
    },
    ty::{self, AssocKind, GenericArgsRef, Ty, TyCtxt, TyKind},
};

use crate::{
    helpers::mir_scan::check_safety,
    verify::{
        def_use::{PlaceBaseKey, PlaceKey},
        helpers::Checkpoint,
        primitive::PrimitiveCall,
        verifier::{AbstractValue, ForwardVisitResult, StateFact},
    },
};

use super::common::{
    SmtCheckResult, SmtChecker, call_destination, failed_smt, operand_place, rvalue_source_place,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum HazardKind {
    SharedView,
    UniqueView,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AliasProducer {
    View(HazardKind),
    OwnershipTransfer,
}

#[derive(Clone, Debug)]
pub(super) struct SelfFieldOrigin {
    pub(super) struct_def_id: DefId,
    pub(super) field_index: usize,
    pub(super) field_name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RawAccessKind {
    Read,
    Write,
}

/// Determines whether a `Local(1)` origin is trivially alias-safe based on
/// the parameter type and the produced view kind. Returns `None` when the
/// origin type requires further checking (e.g., raw pointers).
fn alias_proved_for_param_local<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    local_index: usize,
    kind: HazardKind,
) -> Option<SmtCheckResult> {
    let body = tcx.optimized_mir(caller);
    let ty = body.local_decls[Local::from_usize(local_index)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => Some(SmtCheckResult::proved(
            "returned view reinterprets a &mut param; no hidden raw-pointer conflict",
        )),
        ty::Ref(_, _, ty::Mutability::Not) => {
            if kind == HazardKind::UniqueView {
                Some(failed_smt(
                    "shared reference origin cannot safely produce a unique mut view",
                ))
            } else {
                Some(SmtCheckResult::proved(
                    "returned shared view tied to shared reference; no alias conflict",
                ))
            }
        }
        _ => None,
    }
}

/// Check the path-sensitive / escaped hazard part of `Alias`.
pub fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    _forward_property: &crate::verify::contract::Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let Some(callee) = checkpoint.callee else {
        return SmtCheckResult::unknown("Alias target callee could not be resolved");
    };
    let callee_name = checker.tcx.def_path_str(callee);
    let Some(producer) = alias_producer(callee_name.as_str()) else {
        return SmtCheckResult::unknown(
            "Alias lowering currently supports view producers and ownership-transfer APIs",
        );
    };

    let Some(origin_arg) = checkpoint.args.first() else {
        return SmtCheckResult::unknown("Alias producer has no pointer argument");
    };
    let Some(origin_place) = operand_place(origin_arg) else {
        return SmtCheckResult::unknown("Alias pointer argument is not a MIR place");
    };
    let origin = resolve_forward_place(origin_place.clone(), forward);
    let mut local_origins = vec![origin_place.clone()];
    if !local_origins.contains(&origin) {
        local_origins.push(origin.clone());
    }
    let destination = call_destination(checker.tcx, checkpoint);

    let AliasProducer::View(kind) = producer else {
        if let Some(reason) = ownership_transfer_violation(
            checker.tcx,
            checkpoint.caller,
            checkpoint.block,
            destination,
            &origin_place,
        ) {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(
            "ownership-transfer API consumes the raw pointer and no later raw reuse was found",
        );
    };

    if let Some(reason) = local_hazard_violation(
        checker.tcx,
        checkpoint.caller,
        checkpoint.block,
        destination,
        &local_origins,
        kind,
    ) {
        return failed_smt(reason);
    }

    if !destination_flows_to_return(checker.tcx, checkpoint.caller, destination) {
        return SmtCheckResult::proved(
            "Alias hazard is local and no conflicting raw access was found after the view producer",
        );
    }

    if let Some(origin) = self_field_origin(checker.tcx, checkpoint.caller, &origin) {
        if let Some(reason) = escaped_self_field_violation(checker.tcx, checkpoint.caller, &origin)
        {
            return failed_smt(reason);
        }
        return SmtCheckResult::proved(format!(
            "returned view is backed by private field `{}` and no safe raw-field breaker was found",
            origin.field_name
        ));
    }

    if origin.base == PlaceBaseKey::Local(1) && origin.fields.is_empty() {
        if let PlaceBaseKey::Local(local_index) = origin.base {
            if let Some(result) =
                alias_proved_for_param_local(checker.tcx, checkpoint.caller, local_index, kind)
            {
                return result;
            }
        }
    }

    if let Some(result) =
        private_fn_callsite_delegation(checker.tcx, checkpoint.caller, &origin, kind)
    {
        return result;
    }

    let err_msg = format!(
        "returned view escapes while the original pointer is not owned by a private self field [origin={:?}]",
        origin
    );
    failed_smt(err_msg)
}

/// When the view producer lives in a crate-private helper whose pointer origin
/// is a parameter, the alias obligation is discharged at each in-crate call
/// site instead: the helper itself has no local conflicting access, so the
/// hazard (if any) must appear in the caller that owns both the pointer and
/// the returned view.
fn private_fn_callsite_delegation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: &PlaceKey,
    kind: HazardKind,
) -> Option<SmtCheckResult> {
    let param_index = param_index_of_origin(tcx, caller, origin)?;
    if is_externally_reachable(tcx, caller) {
        return None;
    }

    for site in local_callsites(tcx, caller) {
        let mut origins = callsite_arg_origins(tcx, site.caller, &site.args, param_index);
        if origins.is_empty() {
            continue;
        }
        let extra = as_ptr_provenance_origins(tcx, site.caller, &origins);
        for place in extra {
            if !origins.contains(&place) {
                origins.push(place);
            }
        }
        if let Some(reason) = local_hazard_violation_with(
            tcx,
            site.caller,
            site.block,
            site.destination,
            &origins,
            kind,
            true,
        ) {
            return Some(failed_smt(format!(
                "call site `{}` conflicts with the returned view: {reason}",
                tcx.def_path_str(site.caller)
            )));
        }
    }

    Some(SmtCheckResult::proved(
        "crate-private helper: every in-crate call site keeps the original pointer unused while the view is live",
    ))
}

/// Returns the parameter index (0-based) when the resolved origin is a raw
/// pointer parameter of `caller`.
pub(super) fn param_index_of_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origin: &PlaceKey,
) -> Option<usize> {
    let PlaceBaseKey::Local(local) = origin.base else {
        return None;
    };
    if !origin.fields.is_empty() {
        return None;
    }
    let body = tcx.optimized_mir(caller);
    if local == 0 || local > body.arg_count {
        return None;
    }
    let ty = body.local_decls[Local::from_usize(local)].ty;
    is_raw_pointer_ty(ty).then_some(local - 1)
}

/// Returns true when the function may be called from outside this crate.
pub(super) fn is_externally_reachable<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return true;
    };
    tcx.effective_visibilities(()).is_reachable(local)
}

pub(super) struct LocalCallsite<'tcx> {
    pub(super) caller: DefId,
    pub(super) block: BasicBlock,
    pub(super) args: Vec<Operand<'tcx>>,
    pub(super) destination: Option<Local>,
}

/// Finds all MIR call sites of `callee` inside the current crate.
pub(super) fn local_callsites<'tcx>(tcx: TyCtxt<'tcx>, callee: DefId) -> Vec<LocalCallsite<'tcx>> {
    let mut sites = Vec::new();
    for def_id in tcx.mir_keys(()) {
        let def_id = def_id.to_def_id();
        if def_id == callee {
            continue;
        }
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        if !tcx.is_mir_available(def_id) {
            continue;
        }
        let body = tcx.optimized_mir(def_id);
        for (block, data) in body.basic_blocks.iter_enumerated() {
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
            let Some(target) = call_target_def_id(func) else {
                continue;
            };
            if target != callee {
                continue;
            }
            sites.push(LocalCallsite {
                caller: def_id,
                block,
                args: args.iter().map(|arg| arg.node.clone()).collect(),
                destination: Some(destination.local),
            });
        }
    }
    sites
}

fn call_target_def_id<'tcx>(func: &Operand<'tcx>) -> Option<DefId> {
    let Operand::Constant(constant) = func else {
        return None;
    };
    match constant.const_.ty().kind() {
        TyKind::FnDef(def_id, _) => Some(*def_id),
        _ => None,
    }
}

/// Resolves the actual argument passed for `param_index` at a call site.
pub(super) fn callsite_arg_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    args: &[Operand<'tcx>],
    param_index: usize,
) -> Vec<PlaceKey> {
    let Some(arg) = args.get(param_index) else {
        return Vec::new();
    };
    let Some(place) = (match arg {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }) else {
        return Vec::new();
    };
    let aliases = collect_place_aliases(tcx, caller);
    let mut origins = vec![place.clone()];
    if let Some(local) = place.local() {
        if let Some(alias) = aliases.get(&local) {
            if !origins.contains(alias) {
                origins.push(alias.clone());
            }
        }
    }
    origins
}

/// Adds the receiver of `as_ptr`/`as_mut_ptr` calls that produced any of the
/// current origin locals, so writes through the original owner are also seen.
pub(super) fn as_ptr_provenance_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let aliases = collect_place_aliases(tcx, caller);
    let mut extra = Vec::new();
    for block in body.basic_blocks.iter() {
        let Some(terminator) = &block.terminator else {
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
        if !PrimitiveCall::classify(&name).is_some_and(|primitive| primitive.is_as_ptr_like()) {
            continue;
        }
        let destination_key = PlaceKey {
            base: PlaceBaseKey::Local(destination.local.as_usize()),
            fields: Vec::new(),
        };
        if !origins
            .iter()
            .any(|origin| destination_key.overlaps(origin))
        {
            continue;
        }
        let Some(receiver) = args.first() else {
            continue;
        };
        let Some(place) = (match &receiver.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            continue;
        };
        let resolved = resolve_mir_place(tcx, caller, place, &aliases);
        if !extra.contains(&resolved) {
            extra.push(resolved);
        }
    }
    extra
}

fn alias_producer(name: &str) -> Option<AliasProducer> {
    if name.contains("from_raw_parts_mut") {
        return Some(AliasProducer::View(HazardKind::UniqueView));
    }
    if name.contains("from_raw_parts") || name.contains("from_parts") || name.contains("from_ptr") {
        if is_vec_ownership_transfer_api(name) {
            return Some(AliasProducer::OwnershipTransfer);
        }
        return Some(AliasProducer::View(HazardKind::SharedView));
    }
    if is_ownership_transfer_api(name) {
        return Some(AliasProducer::OwnershipTransfer);
    }
    None
}

fn is_ownership_transfer_api(name: &str) -> bool {
    if is_vec_ownership_transfer_api(name) {
        return true;
    }
    let is_from_raw = name.contains("from_raw");
    is_from_raw
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString")
            || is_vec_ownership_transfer_api(name))
}

fn is_vec_ownership_transfer_api(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

pub(super) fn resolve_forward_place<'tcx>(
    mut place: PlaceKey,
    forward: &ForwardVisitResult<'tcx>,
) -> PlaceKey {
    let mut seen = HashSet::new();
    loop {
        if !seen.insert(place.clone()) {
            return place;
        }
        let Some(local) = place.local() else {
            return place;
        };
        let Some(value) = forward.values.get(&local) else {
            return place;
        };
        match value {
            AbstractValue::Place(next) | AbstractValue::Ref(next) | AbstractValue::RawPtr(next) => {
                place = next.clone();
            }
            AbstractValue::Cast(inner, _) => match inner.as_ref() {
                AbstractValue::Place(next)
                | AbstractValue::Ref(next)
                | AbstractValue::RawPtr(next) => place = next.clone(),
                _ => return place,
            },
            AbstractValue::CallResult(call)
                if PrimitiveCall::classify(&call.func)
                    .is_some_and(PrimitiveCall::is_as_ptr_like) =>
            {
                let Some(source) = forward.facts.iter().find_map(|fact| match fact {
                    StateFact::PointsTo { pointer, source } if pointer.overlaps(&place) => {
                        Some(source.clone())
                    }
                    _ => None,
                }) else {
                    return place;
                };
                place = resolve_forward_place(source, forward);
            }
            AbstractValue::CallResult(call)
                if PrimitiveCall::classify(&call.func)
                    .is_some_and(PrimitiveCall::is_pointer_arithmetic) =>
            {
                // ptr::add/sub/offset create a new pointer from the base;
                // follow PointsTo (ReturnPointerAdd effect) to the base.
                let Some(source) = forward.facts.iter().find_map(|fact| match fact {
                    StateFact::PointsTo { pointer, source } if pointer.overlaps(&place) => {
                        Some(source.clone())
                    }
                    _ => None,
                }) else {
                    return place;
                };
                place = resolve_forward_place(source, forward);
            }
            _ => return place,
        }
    }
}

fn destination_flows_to_return<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    destination: Option<Local>,
) -> bool {
    let Some(destination) = destination else {
        return false;
    };
    if destination.as_usize() == 0 {
        return true;
    }

    let body = tcx.optimized_mir(caller);
    if body.local_decls[Local::from_usize(0)].ty == body.local_decls[destination].ty {
        return true;
    }

    let mut aliases: HashMap<Local, PlaceKey> = HashMap::new();
    aliases.insert(
        destination,
        PlaceKey {
            base: PlaceBaseKey::Local(destination.as_usize()),
            fields: Vec::new(),
        },
    );

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local.as_usize() != 0 {
                continue;
            }
            if rvalue_mentions_local(rvalue, destination, &aliases) {
                return true;
            }
        }
    }
    false
}

fn rvalue_mentions_local<'tcx>(
    rvalue: &Rvalue<'tcx>,
    local: Local,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => place.local == local || aliases.contains_key(&place.local),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                place.local == local || aliases.contains_key(&place.local)
            }
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => false,
    }
}

fn local_hazard_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
) -> Option<String> {
    local_hazard_violation_with(tcx, caller, call_block, destination, origins, kind, false)
}

fn local_hazard_violation_with<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
    strict_call_escape: bool,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut aliases = collect_place_aliases(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&aliases, &mut origins);
    let mut hazard_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut hazard_locals);
    let vec_owners = vec_owners_for_origins(tcx, caller, &origins, &aliases);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    for (block_index, block) in reverse_postorder_blocks(body) {
        if !reachable.contains(&block_index) {
            continue;
        }

        for (statement_index, statement) in block.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::StorageDead(local) => {
                    hazard_locals.remove(local);
                }
                StatementKind::Assign(assign) => {
                    let (target, rvalue) = assign.as_ref();
                    if rvalue_mentions_any_local(rvalue, &hazard_locals) {
                        hazard_locals.insert(target.local);
                    }
                    if let Some(alias) = alias_from_rvalue(tcx, caller, rvalue, &aliases) {
                        aliases.insert(target.local, alias);
                    }
                    if !hazard_locals.is_empty()
                        && raw_access_conflicts(kind, RawAccessKind::Write)
                        && place_is_raw_access_to_any_origin(target, &origins, &aliases)
                        && hazard_used_after_statement(
                            tcx,
                            caller,
                            block_index,
                            statement_index,
                            &hazard_locals,
                        )
                    {
                        return Some(format!(
                            "raw write through original pointer after {:?} view creation",
                            kind
                        ));
                    }
                    if !hazard_locals.is_empty()
                        && raw_access_conflicts(kind, RawAccessKind::Read)
                        && rvalue_reads_any_origin(rvalue, &origins, &aliases)
                        && hazard_used_after_statement(
                            tcx,
                            caller,
                            block_index,
                            statement_index,
                            &hazard_locals,
                        )
                    {
                        return Some(format!(
                            "raw read through original pointer after {:?} view creation",
                            kind
                        ));
                    }
                }
                _ => {}
            }
        }

        if !hazard_locals.is_empty() {
            let Some(terminator) = &block.terminator else {
                continue;
            };
            if origins.iter().any(|origin| {
                terminator_writes_origin(tcx, caller, &terminator.kind, origin, &aliases)
            }) && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw write call through original pointer after {:?} view creation",
                    kind
                ));
            }
            if kind == HazardKind::UniqueView
                && !vec_owners.is_empty()
                && terminator_invalidates_vec_owner(
                    tcx,
                    caller,
                    &terminator.kind,
                    &vec_owners,
                    &aliases,
                )
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(
                    "Vec may reallocate while a raw-derived mutable view is still live".to_string(),
                );
            }
            if strict_call_escape
                && block_index != call_block
                && !terminator_is_benign_origin_use(tcx, &terminator.kind)
                && origins.iter().any(|origin| {
                    terminator_uses_origin(tcx, caller, &terminator.kind, origin, &aliases)
                })
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw pointer escapes to another call while the {:?} view is live",
                    kind
                ));
            }
        }
    }

    None
}

/// Calls that read pointer metadata without granting memory access.
fn terminator_is_benign_origin_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return true;
    };
    let name = crate::verify::call_summary::call_name(tcx, func);
    PrimitiveCall::classify(&name).is_some_and(|primitive| primitive.is_as_ptr_like())
        || name.ends_with("::len")
        || name.ends_with("::is_empty")
        || name.ends_with("::is_null")
        || name.ends_with("::addr")
        || name.ends_with("::cast")
}

fn reverse_postorder_blocks<'a, 'tcx>(
    body: &'a rustc_middle::mir::Body<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a rustc_middle::mir::BasicBlockData<'tcx>)> {
    rustc_middle::mir::traversal::reverse_postorder(body).map(|(block, data)| (block, data))
}

fn ownership_transfer_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origin_place: &PlaceKey,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut owner_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut owner_locals);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    // When any post-call block hands ownership back to a raw pointer via an
    // `into_raw`-style call on the owning value, later raw uses are governed
    // by that new transfer rather than this checkpoint.
    for block_index in &reachable {
        if let Some(terminator) = &body.basic_blocks[*block_index].terminator
            && terminator_returns_ownership(tcx, &terminator.kind, &owner_locals)
        {
            return None;
        }
    }

    let origins = places_holding_transferred_pointer(tcx, caller, call_block, origin_place);

    // Flow-sensitive forward scan from the transfer call.  Each CFG edge
    // carries the set of still-live origin places; an origin dies as soon as
    // its place is strongly redefined (a `Deref`-free assignment or call
    // destination) or its storage ends, and a copy of a live origin value
    // revives its target.  Loop back-edges therefore stop flagging reads of
    // *re-assigned* locals in later iterations as reuse of the transferred
    // pointer, while straight-line reuse is still detected.
    let start = match &body.basic_blocks[call_block].terminator().kind {
        TerminatorKind::Call {
            target: Some(target),
            ..
        } => *target,
        _ => return None,
    };

    let mut entry_states: HashMap<BasicBlock, Vec<PlaceKey>> = HashMap::new();
    let mut worklist: Vec<(BasicBlock, Vec<PlaceKey>)> = vec![(start, origins)];

    while let Some((block_index, incoming)) = worklist.pop() {
        let mut live = match entry_states.get_mut(&block_index) {
            Some(known) => {
                let mut changed = false;
                for origin in &incoming {
                    if !known.contains(origin) {
                        known.push(origin.clone());
                        changed = true;
                    }
                }
                if !changed {
                    continue;
                }
                known.clone()
            }
            None => {
                entry_states.insert(block_index, incoming.clone());
                incoming
            }
        };

        let block = &body.basic_blocks[block_index];
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(assign) => {
                    let (target, rvalue) = assign.as_ref();
                    if place_is_raw_access_to_live_origin(target, &live)
                        || rvalue_reads_live_origin(rvalue, &live)
                    {
                        return Some(
                            "raw pointer reused after ownership was transferred to an owning value"
                                .to_string(),
                        );
                    }
                    let copies_origin = rvalue_copies_live_origin_value(rvalue, &live);
                    kill_strongly_updated_origins(target, &mut live);
                    if copies_origin
                        && !target
                            .projection
                            .iter()
                            .any(|projection| matches!(projection, ProjectionElem::Deref))
                    {
                        let target_key = PlaceKey::from_mir_place(target);
                        if !live.contains(&target_key) {
                            live.push(target_key);
                        }
                    }
                }
                StatementKind::StorageDead(local) => {
                    live.retain(|origin| origin.base != PlaceBaseKey::Local(local.as_usize()));
                }
                _ => {}
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_uses_live_origin(&terminator.kind, &live) {
            return Some(
                "raw pointer passed to another call after ownership was transferred".to_string(),
            );
        }
        if let TerminatorKind::Call {
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            kill_strongly_updated_origins(call_destination, &mut live);
        }
        if live.is_empty() {
            continue;
        }
        for successor in terminator.successors() {
            worklist.push((successor, live.clone()));
        }
    }

    None
}

/// Collect the places that still hold the transferred pointer *value* when
/// the ownership-transfer call executes.
///
/// Starting from the callee argument, this walks the call block (and its
/// unique-predecessor chain) backwards, following value copies while a
/// kill-set records locals that are re-assigned between a definition and the
/// call: such stale locals no longer hold the pointer at the call and must
/// not seed the reuse scan.  This keeps loop-carried locals (re-assigned each
/// iteration) out of the origin set while straight-line aliases stay in.
fn places_holding_transferred_pointer<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    origin_place: &PlaceKey,
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut holders = vec![origin_place.clone()];
    let mut killed: HashSet<Local> = HashSet::new();
    let mut block_index = call_block;

    loop {
        let block = &body.basic_blocks[block_index];
        for statement in block.statements.iter().rev() {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Deref))
            {
                continue;
            }
            let target_key = PlaceKey::from_mir_place(target);
            let target_defines_holder =
                !killed.contains(&target.local) && holders.iter().any(|h| target_key.overlaps(h));

            let source_place = match rvalue {
                Rvalue::Use(Operand::Copy(place), ..)
                | Rvalue::Use(Operand::Move(place), ..)
                | Rvalue::Cast(_, Operand::Copy(place), _)
                | Rvalue::Cast(_, Operand::Move(place), _)
                | Rvalue::CopyForDeref(place) => Some(place),
                _ => None,
            };

            if target_defines_holder {
                // This is the latest pre-call definition of a holder: the
                // value came from the rvalue source, which therefore also
                // holds the pointer unless it was re-assigned afterwards.
                if let Some(source) = source_place
                    && !killed.contains(&source.local)
                {
                    let source_key = PlaceKey::from_mir_place(source);
                    for holder in holders.clone() {
                        if let Some(spliced) =
                            splice_holder_fields(&target_key, &holder, &source_key)
                            && !holders.contains(&spliced)
                        {
                            holders.push(spliced);
                        }
                    }
                }
            } else if let Some(source) = source_place
                && !killed.contains(&target.local)
                && !source
                    .projection
                    .iter()
                    .any(|projection| matches!(projection, ProjectionElem::Deref))
            {
                // A pre-call copy *out of* a holder: the target received the
                // pointer value earlier and has not been re-assigned since,
                // so it still holds it at the call.
                let source_key = PlaceKey::from_mir_place(source);
                if holders.iter().any(|h| source_key.overlaps(h)) && !holders.contains(&target_key)
                {
                    holders.push(target_key.clone());
                }
            }
            killed.insert(target.local);
        }

        // Step to the unique predecessor and account for its terminator.
        let predecessors = &body.basic_blocks.predecessors()[block_index];
        if predecessors.len() != 1 {
            break;
        }
        block_index = predecessors[0];
        let terminator = body.basic_blocks[block_index].terminator();
        if let TerminatorKind::Call {
            func,
            args,
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            let destination_key = PlaceKey::from_mir_place(call_destination);
            if !killed.contains(&call_destination.local)
                && holders.iter().any(|h| destination_key.overlaps(h))
            {
                let name = crate::verify::call_summary::call_name(tcx, func);
                if PrimitiveCall::classify(&name).is_some_and(PrimitiveCall::is_as_ptr_like)
                    && let Some(arg) = args.first()
                    && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                    && !killed.contains(&place.local)
                {
                    let key = PlaceKey::from_mir_place(place);
                    if !holders.contains(&key) {
                        holders.push(key);
                    }
                }
            }
            killed.insert(call_destination.local);
        }
    }

    holders
}

/// Rebase `holder` (a place rooted at `target`) onto `source`, keeping the
/// projection suffix that extends past the assignment target.
fn splice_holder_fields(
    target: &PlaceKey,
    holder: &PlaceKey,
    source: &PlaceKey,
) -> Option<PlaceKey> {
    if !place_key_is_prefix_of(target, holder) {
        return None;
    }
    let mut fields = source.fields.clone();
    fields.extend_from_slice(&holder.fields[target.fields.len()..]);
    Some(PlaceKey {
        base: source.base.clone(),
        fields,
    })
}

/// Remove origins invalidated by a strong update of `target`.
///
/// A `Deref`-free assignment fully redefines the assigned place, so any origin
/// it is a prefix of no longer holds the transferred pointer.  Writes through
/// pointers (`(*p).f = ...`) do not redefine the pointer-holding place itself
/// and keep every origin alive.
fn kill_strongly_updated_origins<'tcx>(target: &Place<'tcx>, live: &mut Vec<PlaceKey>) {
    if target
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return;
    }
    let target_key = PlaceKey::from_mir_place(target);
    live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
}

/// True when `prefix` denotes the same place as `place` or one of its parents
/// (same base and `prefix.fields` is a leading segment of `place.fields`).
fn place_key_is_prefix_of(prefix: &PlaceKey, place: &PlaceKey) -> bool {
    prefix.base == place.base
        && prefix.fields.len() <= place.fields.len()
        && place.fields[..prefix.fields.len()] == prefix.fields[..]
}

/// True when `place` reads or writes through a still-live transferred pointer.
fn place_is_raw_access_to_live_origin<'tcx>(place: &Place<'tcx>, live: &[PlaceKey]) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let key = PlaceKey::from_mir_place(place);
    live.iter().any(|origin| key.overlaps(origin))
}

/// True when the rvalue dereferences a still-live transferred pointer.
fn rvalue_reads_live_origin<'tcx>(rvalue: &Rvalue<'tcx>, live: &[PlaceKey]) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => place_is_raw_access_to_live_origin(place, live),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                place_is_raw_access_to_live_origin(place, live)
            }
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => false,
    }
}

/// True when the rvalue copies the *value* of a still-live origin (or takes
/// its address), so the assignment target keeps referring to the transferred
/// pointer and must join the live set.
fn rvalue_copies_live_origin_value<'tcx>(rvalue: &Rvalue<'tcx>, live: &[PlaceKey]) -> bool {
    let place = match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => place,
        _ => return false,
    };
    if place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let key = PlaceKey::from_mir_place(place);
    live.iter().any(|origin| key.overlaps(origin))
}

/// True when a call terminator passes a still-live transferred pointer to
/// another function.
fn terminator_uses_live_origin<'tcx>(kind: &TerminatorKind<'tcx>, live: &[PlaceKey]) -> bool {
    let TerminatorKind::Call { args, .. } = kind else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        let key = PlaceKey::from_mir_place(place);
        live.iter().any(|origin| key.overlaps(origin))
    })
}

fn expand_origin_aliases(aliases: &HashMap<Local, PlaceKey>, origins: &mut Vec<PlaceKey>) {
    let mut changed = true;
    while changed {
        changed = false;
        for (local, alias) in aliases {
            let local_key = PlaceKey {
                base: PlaceBaseKey::Local(local.as_usize()),
                fields: Vec::new(),
            };

            let related = origins.iter().any(|origin| {
                local_key.overlaps(origin)
                    || origin.overlaps(&local_key)
                    || alias.overlaps(origin)
                    || origin.overlaps(alias)
            });
            if !related {
                continue;
            }

            if !origins.contains(&local_key) {
                origins.push(local_key);
                changed = true;
            }
            if !origins.contains(alias) {
                origins.push(alias.clone());
                changed = true;
            }
        }
    }
}

fn expand_hazard_alias_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    hazard_locals: &mut HashSet<Local>,
) {
    let body = tcx.optimized_mir(caller);
    let mut changed = true;
    while changed {
        changed = false;
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if rvalue_mentions_any_local(rvalue, hazard_locals)
                    && hazard_locals.insert(target.local)
                {
                    changed = true;
                }
            }
        }
    }
}

fn hazard_used_after_statement<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    block: BasicBlock,
    statement_index: usize,
    hazard_locals: &HashSet<Local>,
) -> bool {
    let body = tcx.optimized_mir(caller);
    let data = &body.basic_blocks[block];
    for statement in data.statements.iter().skip(statement_index + 1) {
        if statement_uses_any_local(statement, hazard_locals) {
            return true;
        }
    }
    let terminator = data.terminator();
    if terminator_uses_any_local(&terminator.kind, hazard_locals) {
        return true;
    }
    hazard_used_after_block(tcx, caller, block, hazard_locals)
}

fn hazard_used_after_block<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    start: BasicBlock,
    hazard_locals: &HashSet<Local>,
) -> bool {
    let body = tcx.optimized_mir(caller);
    let mut seen = HashSet::new();
    let mut stack: Vec<_> = body.basic_blocks[start].terminator().successors().collect();

    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            if statement_uses_any_local(statement, hazard_locals) {
                return true;
            }
        }
        let terminator = data.terminator();
        if terminator_uses_any_local(&terminator.kind, hazard_locals) {
            return true;
        }
        stack.extend(terminator.successors());
    }

    false
}

fn statement_uses_any_local<'tcx>(
    statement: &rustc_middle::mir::Statement<'tcx>,
    locals: &HashSet<Local>,
) -> bool {
    let StatementKind::Assign(assign) = &statement.kind else {
        return false;
    };
    let (target, rvalue) = assign.as_ref();
    locals.contains(&target.local) || rvalue_mentions_any_local(rvalue, locals)
}

fn terminator_uses_any_local<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    locals: &HashSet<Local>,
) -> bool {
    match terminator {
        TerminatorKind::Call { args, .. } => args.iter().any(|arg| match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            match discr {
                Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
                Operand::Constant(_) => false,
                #[cfg(rapx_rustc_ge_196)]
                Operand::RuntimeChecks(_) => false,
            }
        }
        TerminatorKind::Drop { place, .. } => locals.contains(&place.local),
        _ => false,
    }
}

fn rvalue_mentions_any_local<'tcx>(rvalue: &Rvalue<'tcx>, locals: &HashSet<Local>) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => locals.contains(&place.local),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => false,
    }
}

fn blocks_reachable_after_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
) -> HashSet<BasicBlock> {
    let body = tcx.optimized_mir(caller);
    let mut starts = Vec::new();
    if let TerminatorKind::Call { target, .. } = &body.basic_blocks[call_block].terminator().kind
        && let Some(target) = target
    {
        starts.push(*target);
    }

    let mut seen = HashSet::new();
    let mut stack = starts;
    while let Some(block) = stack.pop() {
        if !seen.insert(block) {
            continue;
        }
        let terminator = body.basic_blocks[block].terminator();
        for successor in terminator.successors() {
            stack.push(successor);
        }
    }
    seen
}

fn raw_access_conflicts(kind: HazardKind, access: RawAccessKind) -> bool {
    match kind {
        HazardKind::SharedView => access == RawAccessKind::Write,
        HazardKind::UniqueView => true,
    }
}

pub(super) fn self_field_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<SelfFieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    if local != 1 || place.fields.is_empty() {
        return None;
    }
    let body = tcx.optimized_mir(caller);
    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let (struct_def_id, _) = adt_from_receiver_ty(self_ty)?;
    let field_index = place.fields[0];
    let adt = tcx.adt_def(struct_def_id);
    let field = adt.all_fields().nth(field_index)?;
    Some(SelfFieldOrigin {
        struct_def_id,
        field_index,
        field_name: field.name.to_string(),
    })
}

pub(super) fn escaped_self_field_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    current: DefId,
    origin: &SelfFieldOrigin,
) -> Option<String> {
    if public_raw_field(tcx, origin) {
        return Some(format!(
            "returned view escapes while raw field `{}` is public",
            origin.field_name
        ));
    }

    for impl_def_id in impls_for_struct(tcx, origin.struct_def_id) {
        for item in tcx.associated_item_def_ids(impl_def_id) {
            if *item == current {
                continue;
            }
            if !matches!(tcx.def_kind(*item), DefKind::Fn | DefKind::AssocFn) {
                continue;
            }
            if check_safety(tcx, *item) == Safety::Unsafe {
                continue;
            }
            let Some(assoc) = tcx.opt_associated_item(*item) else {
                continue;
            };
            if !matches!(assoc.kind, AssocKind::Fn { has_self: true, .. }) {
                continue;
            }
            if !tcx.is_mir_available(*item) {
                continue;
            }

            if method_writes_self_field(tcx, *item, origin.field_index) {
                return Some(format!(
                    "safe method `{}` writes through raw field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
            if method_exposes_self_field(tcx, *item, origin.field_index) {
                return Some(format!(
                    "safe method `{}` exposes raw field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
        }
    }

    None
}

fn impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = tcx
        .inherent_impls(struct_def_id)
        .iter()
        .copied()
        .collect::<Vec<_>>();

    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Impl(impl_details) = &item.kind else {
            continue;
        };
        let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(_, path)) =
            &impl_details.self_ty.kind
        else {
            continue;
        };
        let rustc_hir::def::Res::Def(_, def_id) = path.res else {
            continue;
        };
        if def_id != struct_def_id {
            continue;
        }
        let impl_def_id = item_id.owner_id.to_def_id();
        if !impls.contains(&impl_def_id) {
            impls.push(impl_def_id);
        }
    }

    impls
}

fn public_raw_field<'tcx>(tcx: TyCtxt<'tcx>, origin: &SelfFieldOrigin) -> bool {
    let adt = tcx.adt_def(origin.struct_def_id);
    let Some(field) = adt.all_fields().nth(origin.field_index) else {
        return false;
    };
    if !field.vis.is_public() {
        return false;
    }
    let args = ty::GenericArgs::identity_for_item(tcx, origin.struct_def_id);
    #[cfg(not(rapx_rustc_ge_198))]
    let field_ty = field.ty(tcx, args);
    #[cfg(rapx_rustc_ge_198)]
    let field_ty = field.ty(tcx, args).skip_norm_wip();
    is_raw_pointer_ty(field_ty)
}

fn method_writes_self_field<'tcx>(tcx: TyCtxt<'tcx>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);
    let aliases = collect_place_aliases(tcx, method);
    let origin = self_field_key(field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _) = assign.as_ref();
            if place_is_raw_access_to_origin(target, &origin, &aliases)
                || place_raw_accesses_self_field(tcx, method, target, field_index)
            {
                return true;
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_writes_origin(tcx, method, &terminator.kind, &origin, &aliases) {
            return true;
        }
    }

    false
}

fn place_raw_accesses_self_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    place: &Place<'tcx>,
    field_index: usize,
) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    local_traces_to_self_field(tcx, method, place.local, field_index, &mut HashSet::new())
}

fn local_traces_to_self_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    method: DefId,
    local: Local,
    field_index: usize,
    seen: &mut HashSet<Local>,
) -> bool {
    if !seen.insert(local) {
        return false;
    }
    let body = tcx.optimized_mir(method);
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local != local {
                continue;
            }
            let Some(source) = rvalue_source_place(rvalue) else {
                continue;
            };
            let source_key = PlaceKey::from_mir_place(source);
            if source_key.base == PlaceBaseKey::Local(1)
                && source_key.fields.first() == Some(&field_index)
            {
                return true;
            }
            if source_key.fields.is_empty()
                && local_traces_to_self_field(tcx, method, source.local, field_index, seen)
            {
                return true;
            }
        }
    }
    false
}

fn method_exposes_self_field<'tcx>(tcx: TyCtxt<'tcx>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);
    let aliases = collect_place_aliases(tcx, method);
    let origin = self_field_key(field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local.as_usize() == 0 && rvalue_mentions_origin(rvalue, &origin, &aliases) {
                return true;
            }
        }
    }

    false
}

fn self_field_key(field_index: usize) -> PlaceKey {
    PlaceKey {
        base: PlaceBaseKey::Local(1),
        fields: vec![field_index],
    }
}

fn collect_place_aliases<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> HashMap<Local, PlaceKey> {
    let body = tcx.optimized_mir(def_id);
    let mut aliases = HashMap::new();

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if let Some(alias) = alias_from_rvalue(tcx, def_id, rvalue, &aliases) {
                aliases.insert(target.local, alias);
            }
        }
    }

    aliases
}

fn alias_from_rvalue<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    rvalue: &Rvalue<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> Option<PlaceKey> {
    let place = match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }?;
    Some(resolve_mir_place(tcx, def_id, place, aliases))
}

fn resolve_mir_place<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _def_id: DefId,
    place: &Place<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> PlaceKey {
    let key = PlaceKey::from_mir_place(place);
    if !key.fields.is_empty() {
        return key;
    }
    aliases.get(&place.local).cloned().unwrap_or(key)
}

fn place_is_raw_access_to_origin<'tcx>(
    place: &Place<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let pointer = aliases
        .get(&place.local)
        .cloned()
        .unwrap_or_else(|| PlaceKey::from_mir_place(place));
    pointer.overlaps(origin)
}

fn place_is_raw_access_to_any_origin<'tcx>(
    place: &Place<'tcx>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    origins
        .iter()
        .any(|origin| place_is_raw_access_to_origin(place, origin, aliases))
}

fn rvalue_reads_any_origin<'tcx>(
    rvalue: &Rvalue<'tcx>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => place_is_raw_access_to_any_origin(place, origins, aliases),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                place_is_raw_access_to_any_origin(place, origins, aliases)
            }
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => false,
    }
}

fn rvalue_mentions_origin<'tcx>(
    rvalue: &Rvalue<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => resolve_mir_place_dummy(place, aliases).overlaps(origin),
        Rvalue::Aggregate(_, operands) => operands.iter().any(|operand| match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                resolve_mir_place_dummy(place, aliases).overlaps(origin)
            }
            Operand::Constant(_) => false,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => false,
        }),
        _ => false,
    }
}

fn resolve_mir_place_dummy<'tcx>(
    place: &Place<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> PlaceKey {
    let key = PlaceKey::from_mir_place(place);
    if !key.fields.is_empty() {
        key
    } else {
        aliases.get(&place.local).cloned().unwrap_or(key)
    }
}

fn terminator_writes_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::verify::call_summary::call_name(tcx, func);
    if PrimitiveCall::classify(&name) != Some(PrimitiveCall::PtrWrite) {
        return false;
    }
    let Some(arg0) = args.first() else {
        return false;
    };
    let Some(place) = (match &arg0.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }) else {
        return false;
    };
    resolve_mir_place(tcx, caller, place, aliases).overlaps(origin)
}

fn terminator_uses_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { args, .. } = terminator else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        resolve_mir_place(tcx, caller, place, aliases).overlaps(origin)
    })
}

fn terminator_returns_ownership<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
    owner_locals: &HashSet<Local>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::verify::call_summary::call_name(tcx, func);
    if !is_ownership_return_api(&name) {
        return false;
    }
    args.iter().any(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => owner_locals.contains(&place.local),
        Operand::Constant(_) => false,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => false,
    })
}

fn is_ownership_return_api(name: &str) -> bool {
    name.contains("into_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

fn vec_owners_for_origins<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut owners = Vec::new();

    for block in body.basic_blocks.iter() {
        let Some(terminator) = &block.terminator else {
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
        if !PrimitiveCall::classify(&name).is_some_and(|primitive| primitive.is_as_ptr_like()) {
            continue;
        }
        let destination_key = PlaceKey {
            base: PlaceBaseKey::Local(destination.local.as_usize()),
            fields: Vec::new(),
        };
        if !origins.iter().any(|origin| {
            destination_key.overlaps(origin)
                || aliases
                    .get(&destination.local)
                    .is_some_and(|alias| alias.overlaps(origin))
        }) {
            continue;
        }
        let Some(owner_arg) = args.first() else {
            continue;
        };
        let Some(owner_place) = (match &owner_arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            continue;
        };
        let owner = resolve_mir_place(tcx, caller, owner_place, aliases);
        if !owners.contains(&owner) {
            owners.push(owner);
        }
    }

    owners
}

fn terminator_invalidates_vec_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    owners: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::verify::call_summary::call_name(tcx, func);
    if !is_vec_invalidating_method(&name) {
        return false;
    }
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            Operand::Constant(_) => None,
            #[cfg(rapx_rustc_ge_196)]
            Operand::RuntimeChecks(_) => None,
        }) else {
            return false;
        };
        let arg = resolve_mir_place(tcx, caller, place, aliases);
        owners
            .iter()
            .any(|owner| arg.overlaps(owner) || owner.overlaps(&arg))
    })
}

fn is_vec_invalidating_method(name: &str) -> bool {
    (name.contains("Vec") || name.contains("vec::"))
        && (name.contains("::push")
            || name.contains("::reserve")
            || name.contains("::reserve_exact")
            || name.contains("::shrink_to_fit")
            || name.contains("::shrink_to")
            || name.contains("::insert")
            || name.contains("::remove")
            || name.contains("::clear")
            || name.contains("::truncate")
            || name.contains("::set_len"))
}

fn adt_from_receiver_ty<'tcx>(ty: Ty<'tcx>) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    match ty.kind() {
        TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => adt_from_receiver_ty(*inner),
        TyKind::Adt(adt, args) => Some((adt.did(), *args)),
        _ => None,
    }
}

fn is_raw_pointer_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(..))
}
