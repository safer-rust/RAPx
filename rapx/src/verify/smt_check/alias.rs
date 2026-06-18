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
        forward_visit::{AbstractValue, ForwardVisitResult},
        helpers::Callsite,
        primitive::PrimitiveCall,
        report::CheckResult,
    },
};

use super::common::{SmtCheckResult, SmtChecker};

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
struct SelfFieldOrigin {
    struct_def_id: DefId,
    field_index: usize,
    field_name: String,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RawAccessKind {
    Read,
    Write,
}

/// Check the path-sensitive / escaped hazard part of `Alias`.
pub fn check<'tcx>(
    checker: &SmtChecker<'tcx>,
    callsite: &Callsite<'tcx>,
    _forward_property: &crate::verify::contract::Property<'tcx>,
    forward: &ForwardVisitResult<'tcx>,
) -> SmtCheckResult {
    let callee_name = checker.tcx.def_path_str(callsite.callee);
    let Some(producer) = alias_producer(callee_name.as_str()) else {
        return SmtCheckResult::unknown(
            "Alias lowering currently supports view producers and ownership-transfer APIs",
        );
    };

    let Some(origin_arg) = callsite.args.first() else {
        return SmtCheckResult::unknown("Alias producer has no pointer argument");
    };
    let Some(origin_place) = operand_place(origin_arg) else {
        return SmtCheckResult::unknown("Alias pointer argument is not a MIR place");
    };
    let origin = resolve_forward_place(origin_place.clone(), forward);
    let mut local_origins = vec![origin_place];
    if !local_origins.contains(&origin) {
        local_origins.push(origin.clone());
    }
    let destination = call_destination(checker.tcx, callsite);

    let AliasProducer::View(kind) = producer else {
        if let Some(reason) = ownership_transfer_violation(
            checker.tcx,
            callsite.caller,
            callsite.block,
            destination,
            &local_origins,
        ) {
            return failed(reason);
        }
        return SmtCheckResult::proved(
            "ownership-transfer API consumes the raw pointer and no later raw reuse was found",
        );
    };

    if let Some(reason) = local_hazard_violation(
        checker.tcx,
        callsite.caller,
        callsite.block,
        destination,
        &local_origins,
        kind,
    ) {
        return failed(reason);
    }

    if !destination_flows_to_return(checker.tcx, callsite.caller, destination) {
        return SmtCheckResult::proved(
            "Alias hazard is local and no conflicting raw access was found after the view producer",
        );
    }

    if let Some(origin) = self_field_origin(checker.tcx, callsite.caller, &origin) {
        if let Some(reason) = escaped_self_field_violation(checker.tcx, callsite.caller, &origin) {
            return failed(reason);
        }
        return SmtCheckResult::proved(format!(
            "returned view is backed by private field `{}` and no safe raw-field breaker was found",
            origin.field_name
        ));
    }

    failed("returned view escapes while the original pointer is not owned by a private self field")
}

fn failed(note: impl Into<String>) -> SmtCheckResult {
    SmtCheckResult {
        result: CheckResult::Failed,
        query: None,
        notes: vec![note.into()],
    }
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

fn operand_place(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        Operand::Constant(_) => None,
        #[cfg(rapx_rustc_ge_196)]
        Operand::RuntimeChecks(_) => None,
    }
}

fn call_destination<'tcx>(tcx: TyCtxt<'tcx>, callsite: &Callsite<'tcx>) -> Option<Local> {
    let body = tcx.optimized_mir(callsite.caller);
    let terminator = body.basic_blocks[callsite.block].terminator();
    let TerminatorKind::Call { destination, .. } = &terminator.kind else {
        return None;
    };
    Some(destination.local)
}

fn resolve_forward_place<'tcx>(
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
    let body = tcx.optimized_mir(caller);
    let mut aliases = collect_place_aliases(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&aliases, &mut origins);
    let mut hazard_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut hazard_locals);
    let vec_owners = vec_owners_for_origins(tcx, caller, &origins, &aliases);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    for (block_index, block) in body.basic_blocks.iter_enumerated() {
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
        }
    }

    None
}

fn ownership_transfer_violation<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let aliases = collect_place_aliases(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&aliases, &mut origins);
    let mut owner_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut owner_locals);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    for (block_index, block) in body.basic_blocks.iter_enumerated() {
        if !reachable.contains(&block_index) {
            continue;
        }

        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if place_is_raw_access_to_any_origin(target, &origins, &aliases)
                || rvalue_reads_any_origin(rvalue, &origins, &aliases)
            {
                return Some(
                    "raw pointer reused after ownership was transferred to an owning value"
                        .to_string(),
                );
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_returns_ownership(tcx, &terminator.kind, &owner_locals) {
            return None;
        }
        if origins
            .iter()
            .any(|origin| terminator_uses_origin(tcx, caller, &terminator.kind, origin, &aliases))
        {
            return Some(
                "raw pointer passed to another call after ownership was transferred".to_string(),
            );
        }
    }

    None
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

fn self_field_origin<'tcx>(
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

fn escaped_self_field_violation<'tcx>(
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

fn rvalue_source_place<'a, 'tcx>(rvalue: &'a Rvalue<'tcx>) -> Option<&'a Place<'tcx>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place), ..)
        | Rvalue::Use(Operand::Move(place), ..)
        | Rvalue::Cast(_, Operand::Copy(place), _)
        | Rvalue::Cast(_, Operand::Move(place), _)
        | Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::CopyForDeref(place) => Some(place),
        _ => None,
    }
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
