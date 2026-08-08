//! Shared alias hazard analysis for both legacy and VM backends.
//!
//! This module extracts the MIR-level hazard scanning logic from
//! `smt_check/alias.rs` and makes it independent of the old forward
//! verifier (`ForwardVisitResult`, `PtsGraph`, `SmtChecker`).
//!
//! The VM backend provides its own origin resolution via
//! `vm/alias.rs` and calls into this module for hazard scanning.

use std::collections::{HashMap, HashSet};

#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;

use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Local, LocalDecls, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, AssocKind, TyCtxt, TyKind},
};

use crate::analysis::alias::{
    LocalOriginMap, collect_local_origins, resolve_place, resolve_self_field_origin,
};
use crate::{
    helpers::mir_scan::check_safety,
    verify::{
        call_summary::fn_simulator,
        def_use::{PlaceBaseKey, PlaceKey},
    },
};

// Re-export utility functions moved to helpers/mir_utils for
// backward compatibility.
pub use crate::helpers::mir_utils::{
    blocks_reachable_after_call, call_destination, collect_place_aliases, deep_resolve_place,
    operand_mir_place, operand_place, resolve_mir_place, rvalue_any_place_matching,
    trace_place_root, trace_raw_ptr_through_call,
};

// ── Shared types ─────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HazardKind {
    SharedView,
    UniqueView,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AliasProducer {
    View(HazardKind),
    OwnershipTransfer,
    ReadMemory,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RawAccessKind {
    Read,
    Write,
}

#[derive(Clone, Debug)]
pub struct SelfFieldOrigin {
    pub struct_def_id: DefId,
    pub field_index: usize,
    pub field_name: String,
}

#[derive(Clone, Debug)]
pub struct LocalCallsite<'tcx> {
    pub caller: DefId,
    pub block: BasicBlock,
    pub args: Vec<Operand<'tcx>>,
    pub destination: Option<Local>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HazardCheck {
    Safe(String),
    Violation(String),
    Inconclusive,
}

// ── API classification ───────────────────────────────────────────

pub fn alias_producer(name: &str) -> Option<AliasProducer> {
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
    if is_read_api(name) {
        return Some(AliasProducer::ReadMemory);
    }
    None
}

pub fn is_read_api(name: &str) -> bool {
    if name.contains("::ptr::") {
        if name.ends_with("::read")
            || name.ends_with("::read_unaligned")
            || name.ends_with("::read_volatile")
            || name.ends_with("::copy_to")
            || name.ends_with("::copy_to_nonoverlapping")
            || name.ends_with("::copy_from")
            || name.ends_with("::copy_from_nonoverlapping")
        {
            return true;
        }
    }
    if name.ends_with("::assume_init_read") {
        return true;
    }
    if name.contains("::intrinsics::")
        && (name.ends_with("::copy") || name.ends_with("::copy_nonoverlapping"))
    {
        return true;
    }
    false
}

pub fn is_ownership_transfer_api(name: &str) -> bool {
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

pub fn is_vec_ownership_transfer_api(name: &str) -> bool {
    (name.contains("from_raw_parts") || name.contains("from_parts"))
        && (name.contains("Vec") || name.contains("vec::"))
}

// ── Origin-based parameter safety ────────────────────────────────

pub fn alias_proved_for_param_local(
    tcx: TyCtxt<'_>,
    caller: DefId,
    local_index: usize,
    kind: HazardKind,
) -> HazardCheck {
    let body = tcx.optimized_mir(caller);
    let ty = body.local_decls[Local::from_usize(local_index)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) => HazardCheck::Safe(
            "returned view reinterprets a &mut param; no hidden raw-pointer conflict".into(),
        ),
        ty::Ref(_, _, ty::Mutability::Not) => {
            if kind == HazardKind::UniqueView {
                HazardCheck::Violation(
                    "shared reference origin cannot safely produce a unique mut view".into(),
                )
            } else {
                HazardCheck::Safe(
                    "returned shared view tied to shared reference; no shared alias conflict"
                        .into(),
                )
            }
        }
        _ if !matches!(ty.kind(), ty::RawPtr(..)) && local_index <= body.arg_count => {
            HazardCheck::Safe(
                "returned view derives from an owned parameter; no external alias risk".into(),
            )
        }
        _ => HazardCheck::Inconclusive,
    }
}

pub fn alias_proved_for_param_local_from_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origin: &PlaceKey,
    kind: HazardKind,
) -> HazardCheck {
    let body = tcx.optimized_mir(caller);
    let local = match origin.base {
        PlaceBaseKey::Local(l) => l,
        _ => return HazardCheck::Inconclusive,
    };
    if !origin.fields.is_empty() {
        return HazardCheck::Inconclusive;
    }
    let ty = body.local_decls[Local::from_usize(local)].ty;
    match ty.kind() {
        ty::Ref(_, _, ty::Mutability::Mut) if kind == HazardKind::SharedView => {
            HazardCheck::Safe("shared raw-ptr-deref view through &mut param".into())
        }
        ty::Ref(_, _, ty::Mutability::Mut) => HazardCheck::Inconclusive,
        ty::Ref(_, _, ty::Mutability::Not) if kind == HazardKind::SharedView => {
            HazardCheck::Safe("shared raw-ptr-deref view through shared reference".into())
        }
        ty::Ref(_, _, ty::Mutability::Not) => HazardCheck::Violation(
            "shared reference origin cannot safely produce a unique mut view".into(),
        ),
        _ => HazardCheck::Inconclusive,
    }
}

pub fn is_origin_a_reference(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> bool {
    let body = tcx.optimized_mir(caller);
    let PlaceBaseKey::Local(mut local) = origin.base else {
        return false;
    };
    if let ty::Ref(..) = body.local_decls[Local::from_usize(local)].ty.kind() {
        return true;
    }
    let origins = collect_local_origins(tcx, caller);
    let (resolved, _) = deep_resolve_place(local, &origins);
    if resolved >= 1 && resolved <= body.arg_count {
        local = resolved;
    }
    matches!(
        body.local_decls[Local::from_usize(local)].ty.kind(),
        ty::Ref(..)
    )
}

pub fn resolve_param_origin(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> Option<usize> {
    let body = tcx.optimized_mir(caller);
    if let PlaceBaseKey::Local(local) = origin.base {
        if local >= 1 && local <= body.arg_count {
            return Some(local);
        }
        let origins = collect_local_origins(tcx, caller);
        let (resolved, _fields) = deep_resolve_place(local, &origins);
        if resolved >= 1 && resolved <= body.arg_count {
            return Some(resolved);
        }
    }
    None
}

pub fn param_index_of_origin(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> Option<usize> {
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
    matches!(ty.kind(), TyKind::RawPtr(..)).then_some(local - 1)
}

pub fn is_externally_reachable(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let Some(local) = def_id.as_local() else {
        return true;
    };
    tcx.effective_visibilities(()).is_reachable(local)
}

// ── Escape analysis ──────────────────────────────────────────────

pub fn destination_flows_to_return(
    tcx: TyCtxt<'_>,
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
            if target.local.as_usize() == 0 {
                if rvalue_mentions_local(rvalue, destination, &aliases) {
                    return true;
                }
            }
            if rvalue_mentions_local(rvalue, destination, &aliases) {
                aliases.insert(target.local, aliases[&destination].clone());
            }
        }
    }
    false
}

pub fn self_field_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<SelfFieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    let resolved = resolve_self_field_origin(tcx, caller, local, &place.fields)?;
    Some(SelfFieldOrigin {
        struct_def_id: resolved.struct_def_id,
        field_index: resolved.field_index,
        field_name: resolved.field_name,
    })
}

pub fn any_struct_field_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<SelfFieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    if place.fields.is_empty() {
        return None;
    }
    let resolved =
        crate::analysis::alias::resolve_any_field_origin(tcx, caller, local, &place.fields)?;
    Some(SelfFieldOrigin {
        struct_def_id: resolved.struct_def_id,
        field_index: resolved.field_index,
        field_name: resolved.field_name,
    })
}

fn self_borrow_mutability(tcx: TyCtxt<'_>, def_id: DefId) -> Option<ty::Mutability> {
    let body = tcx.optimized_mir(def_id);
    if body.arg_count == 0 {
        return None;
    }
    match body.local_decls[Local::from_usize(1)].ty.kind() {
        TyKind::Ref(_, _, m) => Some(*m),
        _ => None,
    }
}

pub fn escaped_self_field_violation(
    tcx: TyCtxt<'_>,
    current: DefId,
    origin: &SelfFieldOrigin,
) -> Option<String> {
    if public_raw_field(tcx, origin) {
        return Some(format!(
            "returned view escapes while raw field `{}` is public",
            origin.field_name
        ));
    }
    let current_self = self_borrow_mutability(tcx, current);
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
            let item_self = self_borrow_mutability(tcx, *item);
            if method_writes_self_field(tcx, *item, origin.field_index) {
                if current_self.is_none() {
                    continue;
                }
                if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) =
                    (current_self, item_self)
                {
                    continue;
                }
                return Some(format!(
                    "safe method `{}` writes through raw field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
            if method_exposes_self_field(tcx, *item, origin.field_index) {
                if current_self.is_none() {
                    continue;
                }
                if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) =
                    (current_self, item_self)
                {
                    continue;
                }
                if let (Some(ty::Mutability::Mut), Some(ty::Mutability::Mut)) =
                    (current_self, item_self)
                {
                    continue;
                }
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

fn public_raw_field(tcx: TyCtxt<'_>, origin: &SelfFieldOrigin) -> bool {
    let adt = tcx.adt_def(origin.struct_def_id);
    let Some(field) = adt.all_fields().nth(origin.field_index) else {
        return false;
    };
    field.vis.is_public()
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

fn method_writes_self_field(tcx: TyCtxt<'_>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);
    let aliases = collect_place_aliases(tcx, method);
    let origin = self_field_key(field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _) = assign.as_ref();
            if place_is_raw_access_to_origin(target, &origin, &aliases, &body.local_decls)
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

fn place_raw_accesses_self_field(
    tcx: TyCtxt<'_>,
    method: DefId,
    place: &Place<'_>,
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

fn local_traces_to_self_field(
    tcx: TyCtxt<'_>,
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
            let Some(source) = crate::helpers::mir_utils::rvalue_source_place(rvalue) else {
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

fn method_exposes_self_field(tcx: TyCtxt<'_>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);

    if body.arg_count >= 1 {
        let self_ty = body.local_decls[Local::from_usize(1)].ty;
        if !matches!(self_ty.kind(), TyKind::Ref(_, _, _)) {
            return false;
        }
    }

    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    if !type_contains_ref_or_ptr(tcx, ret_ty) {
        return false;
    }

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

fn type_contains_ref_or_ptr<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _) => true,
        TyKind::Tuple(elems) => elems.iter().any(|t| type_contains_ref_or_ptr(tcx, t)),
        TyKind::Adt(def, args) => {
            if args.iter().any(|arg| {
                if let Some(t) = arg.as_type() {
                    type_contains_ref_or_ptr(tcx, t)
                } else {
                    false
                }
            }) {
                return true;
            }
            let adt = tcx.adt_def(def.did());
            adt.all_fields().any(|field| {
                #[cfg(not(rapx_rustc_ge_198))]
                let field_ty = field.ty(tcx, args);
                #[cfg(rapx_rustc_ge_198)]
                let field_ty = field.ty(tcx, args).skip_norm_wip();
                type_contains_ref_or_ptr(tcx, field_ty)
            })
        }
        _ => false,
    }
}

fn rvalue_mentions_origin(
    rvalue: &Rvalue<'_>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        let key = PlaceKey::from_mir_place(place);
        let resolved = if key.fields.is_empty() {
            aliases.get(&place.local).cloned().unwrap_or(key)
        } else {
            key
        };
        resolved.overlaps(origin)
    })
}

fn self_field_key(field_index: usize) -> PlaceKey {
    PlaceKey {
        base: PlaceBaseKey::Local(1),
        fields: vec![field_index],
    }
}

fn rvalue_mentions_local(
    rvalue: &Rvalue<'_>,
    local: Local,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    crate::helpers::mir_utils::rvalue_any_place_matching(rvalue, &mut |place| {
        place.local == local || aliases.contains_key(&place.local)
    })
}

pub fn raw_access_conflicts(kind: HazardKind, access: RawAccessKind) -> bool {
    match kind {
        HazardKind::SharedView => access == RawAccessKind::Write,
        HazardKind::UniqueView => true,
    }
}

// ── Local hazard scanning ────────────────────────────────────────

pub fn local_hazard_violation(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
    view_len_place: Option<PlaceKey>,
) -> Option<String> {
    local_hazard_violation_with(
        tcx,
        caller,
        call_block,
        destination,
        origins,
        kind,
        false,
        view_len_place,
    )
}

pub fn local_hazard_violation_with(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origins: &[PlaceKey],
    kind: HazardKind,
    strict_call_escape: bool,
    view_len_place: Option<PlaceKey>,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut aliases = collect_place_aliases(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&aliases, &mut origins);
    let mut hazard_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut hazard_locals);
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator {
            if let TerminatorKind::Call {
                func,
                destination: call_dest,
                ..
            } = &terminator.kind
            {
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if name.contains("::split_at") {
                    hazard_locals.insert(call_dest.local);
                }
            }
        }
    }
    origins.retain(|origin| !origin.local().is_some_and(|l| hazard_locals.contains(&l)));
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
                        let target_ty = body.local_decls[target.local].ty;
                        if matches!(
                            target_ty.kind(),
                            TyKind::Ref(_, _, _) | TyKind::RawPtr(_, _)
                        ) {
                            hazard_locals.insert(target.local);
                        }
                    }
                    if let Some(alias) = alias_from_rvalue(tcx, caller, rvalue, &aliases) {
                        aliases.insert(target.local, alias);
                    }
                    if !hazard_locals.is_empty()
                        && !hazard_locals.contains(&target.local)
                        && raw_access_conflicts(kind, RawAccessKind::Write)
                        && place_is_raw_access_to_any_origin(
                            target,
                            &origins,
                            &aliases,
                            &body.local_decls,
                        )
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
                        && !hazard_locals.contains(&target.local)
                        && raw_access_conflicts(kind, RawAccessKind::Read)
                        && !rvalue_has_hazard_local_base(rvalue, &hazard_locals)
                        && !rvalue_reads_like_view(rvalue, tcx, caller, &origins, &aliases)
                        && rvalue_reads_any_origin(rvalue, &origins, &aliases, &body.local_decls)
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
                    && !is_ownership_transfer_terminator(tcx, &terminator.kind)
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
            if view_len_place.is_some() {
                if let TerminatorKind::Call {
                    func,
                    args,
                    destination: call_dest,
                    ..
                } = &terminator.kind
                {
                    let name = crate::helpers::mir_utils::call_name(tcx, func);
                    if fn_simulator::is_from_raw_parts(&name) && args.len() >= 1 {
                        if let Some(ptr_place) = operand_place(&args[0].node) {
                            let offset_eq = is_ptr_add_offset_eq(
                                tcx,
                                caller,
                                &ptr_place,
                                view_len_place.as_ref().unwrap(),
                                &origins,
                            );
                            let from_add = is_ptr_from_ptr_add(tcx, caller, &ptr_place);
                            if offset_eq || from_add {
                                hazard_locals.insert(call_dest.local);
                                continue;
                            }
                        }
                    }
                    if name.contains("::split_at") {
                        hazard_locals.insert(call_dest.local);
                    }
                }
            }
        }
    }

    None
}

fn reverse_postorder_blocks<'a, 'tcx>(
    body: &'a rustc_middle::mir::Body<'tcx>,
) -> impl Iterator<Item = (BasicBlock, &'a rustc_middle::mir::BasicBlockData<'tcx>)> {
    rustc_middle::mir::traversal::reverse_postorder(body).map(|(block, data)| (block, data))
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

fn expand_hazard_alias_locals(tcx: TyCtxt<'_>, caller: DefId, hazard_locals: &mut HashSet<Local>) {
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

fn rvalue_mentions_any_local(rvalue: &Rvalue<'_>, locals: &HashSet<Local>) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| locals.contains(&place.local))
}

fn hazard_used_after_statement(
    tcx: TyCtxt<'_>,
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

fn hazard_used_after_block(
    tcx: TyCtxt<'_>,
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

fn statement_uses_any_local(
    statement: &rustc_middle::mir::Statement<'_>,
    locals: &HashSet<Local>,
) -> bool {
    let StatementKind::Assign(assign) = &statement.kind else {
        return false;
    };
    let (target, rvalue) = assign.as_ref();
    locals.contains(&target.local) || rvalue_mentions_any_local(rvalue, locals)
}

fn terminator_uses_any_local(terminator: &TerminatorKind<'_>, locals: &HashSet<Local>) -> bool {
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

fn alias_from_rvalue<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _def_id: DefId,
    rvalue: &Rvalue<'tcx>,
    aliases: &HashMap<Local, PlaceKey>,
) -> Option<PlaceKey> {
    let place = crate::helpers::mir_utils::rvalue_source_place(rvalue)?;
    Some(resolve_mir_place(_tcx, place, aliases))
}

fn place_is_raw_access_to_any_origin(
    place: &Place<'_>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'_>,
) -> bool {
    origins
        .iter()
        .any(|origin| place_is_raw_access_to_origin(place, origin, aliases, local_decls))
}

fn place_is_raw_access_to_origin(
    place: &Place<'_>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'_>,
) -> bool {
    let local = place.local;
    let has_raw_deref = place.projection.iter().any(|projection| {
        if let ProjectionElem::Deref = projection {
            matches!(local_decls[local].ty.kind(), TyKind::RawPtr(_, _))
        } else {
            false
        }
    });
    if !has_raw_deref {
        return false;
    }
    let pointer = aliases
        .get(&place.local)
        .cloned()
        .unwrap_or_else(|| PlaceKey::from_mir_place(place));
    pointer.overlaps(origin)
}

fn rvalue_reads_like_view(
    rvalue: &Rvalue<'_>,
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let Some(place) = crate::helpers::mir_utils::rvalue_source_place(rvalue) else {
        return false;
    };
    if !place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
    {
        return false;
    }
    let pointer = aliases
        .get(&place.local)
        .cloned()
        .unwrap_or_else(|| PlaceKey::from_mir_place(place));
    if !origins.iter().any(|origin| pointer.overlaps(origin)) {
        return false;
    }
    is_origin_a_reference(tcx, caller, &pointer)
}

fn rvalue_has_hazard_local_base(rvalue: &Rvalue<'_>, hazard_locals: &HashSet<Local>) -> bool {
    let Some(place) = crate::helpers::mir_utils::rvalue_source_place(rvalue) else {
        return false;
    };
    hazard_locals.contains(&place.local)
}

fn rvalue_reads_any_origin(
    rvalue: &Rvalue<'_>,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    local_decls: &LocalDecls<'_>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        place_is_raw_access_to_any_origin(place, origins, aliases, local_decls)
    })
}

fn terminator_writes_origin<'tcx>(
    tcx: TyCtxt<'tcx>,
    _caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !fn_simulator::is_ptr_write(&name) {
        return false;
    }
    let Some(arg0) = args.first() else {
        return false;
    };
    let Some(place) = (match &arg0.node {
        Operand::Copy(place) | Operand::Move(place) => Some(place),
        _ => None,
    }) else {
        return false;
    };
    resolve_mir_place(tcx, place, aliases).overlaps(origin)
}

fn is_ownership_transfer_terminator<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    name.contains("::from_raw") || name.contains("::drop_in_place")
}

fn terminator_uses_origin<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _caller: DefId,
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
            _ => None,
        }) else {
            return false;
        };
        resolve_mir_place(_tcx, place, aliases).overlaps(origin)
    })
}

fn terminator_is_benign_origin_use<'tcx>(
    tcx: TyCtxt<'tcx>,
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return true;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    fn_simulator::is_as_ptr(&name)
        || name.ends_with("::len")
        || name.ends_with("::is_empty")
        || name.ends_with("::is_null")
        || name.ends_with("::addr")
        || name.ends_with("::cast")
}

fn vec_owners_for_origins(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> Vec<PlaceKey> {
    find_as_ptr_receivers(tcx, caller, origins, aliases, true)
}

fn terminator_invalidates_vec_owner<'tcx>(
    tcx: TyCtxt<'tcx>,
    _caller: DefId,
    terminator: &TerminatorKind<'tcx>,
    owners: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !is_vec_invalidating_method(&name) {
        return false;
    }
    args.iter().any(|arg| {
        let Some(place) = (match &arg.node {
            Operand::Copy(place) | Operand::Move(place) => Some(place),
            _ => None,
        }) else {
            return false;
        };
        let arg = resolve_mir_place(tcx, place, aliases);
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

fn find_as_ptr_receivers(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
    aliases: &HashMap<Local, PlaceKey>,
    check_alias_dest: bool,
) -> Vec<PlaceKey> {
    let body = tcx.optimized_mir(caller);
    let mut result = Vec::new();
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
        let name = crate::helpers::mir_utils::call_name(tcx, func);
        if !fn_simulator::is_as_ptr(&name) {
            continue;
        }
        let destination_key = PlaceKey {
            base: PlaceBaseKey::Local(destination.local.as_usize()),
            fields: Vec::new(),
        };
        let dest_overlaps = || {
            origins
                .iter()
                .any(|origin| destination_key.overlaps(origin))
                || (check_alias_dest
                    && aliases
                        .get(&destination.local)
                        .is_some_and(|alias| origins.iter().any(|o| alias.overlaps(o))))
        };
        if !dest_overlaps() {
            continue;
        }
        let Some(receiver) = args.first() else {
            continue;
        };
        let Some(place) = operand_mir_place(&receiver.node) else {
            continue;
        };
        let resolved = resolve_mir_place(tcx, place, aliases);
        if !result.contains(&resolved) {
            result.push(resolved);
        }
    }
    result
}

fn is_ptr_add_offset_eq(
    tcx: TyCtxt<'_>,
    caller: DefId,
    ptr_place: &PlaceKey,
    view_len: &PlaceKey,
    _origins: &[PlaceKey],
) -> bool {
    let body = tcx.optimized_mir(caller);
    let origins_map = collect_local_origins(tcx, caller);
    let view_len_root = trace_place_root(&origins_map, view_len);
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        {
            let ptr_key = PlaceKey::from_mir_place(destination);
            if ptr_key != *ptr_place {
                continue;
            }
            let name = crate::helpers::mir_utils::call_name(tcx, func);
            if fn_simulator::is_pointer_add(&name) && args.len() >= 2 {
                if let Some(offset_place) = operand_place(&args[1].node) {
                    let offset_root = trace_place_root(&origins_map, &offset_place);
                    return offset_root == view_len_root;
                }
            }
        }
    }
    false
}

fn is_ptr_from_ptr_add(tcx: TyCtxt<'_>, caller: DefId, ptr_place: &PlaceKey) -> bool {
    let body = tcx.optimized_mir(caller);
    for (_bb, data) in body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Call {
            func, destination, ..
        } = &data.terminator().kind
        {
            let ptr_key = PlaceKey::from_mir_place(destination);
            if ptr_key != *ptr_place {
                continue;
            }
            let name = crate::helpers::mir_utils::call_name(tcx, func);
            return fn_simulator::is_pointer_add(&name);
        }
    }
    false
}

// ── Ownership transfer violation scanning ────────────────────────

pub fn ownership_transfer_violation(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    destination: Option<Local>,
    origin_place: &PlaceKey,
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let mut owner_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut owner_locals);
    let reachable = blocks_reachable_after_call(tcx, caller, call_block);

    for block_index in &reachable {
        if let Some(terminator) = &body.basic_blocks[*block_index].terminator
            && terminator_returns_ownership(tcx, &terminator.kind, &owner_locals)
        {
            return None;
        }
    }

    let origins = places_holding_transferred_pointer(tcx, caller, call_block, origin_place);

    if let Some(reason) = pre_existing_view_on_origin(tcx, caller, call_block, &reachable, &origins)
    {
        return Some(reason);
    }

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
                    let target_key = PlaceKey::from_mir_place(target);
                    let is_deref_to_pointee = target_key.fields.is_empty()
                        && target
                            .projection
                            .iter()
                            .any(|p| matches!(p, ProjectionElem::Deref));
                    if !is_deref_to_pointee {
                        live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
                    }
                    if place_is_raw_access_to_live_origin(target, &live)
                        || rvalue_reads_live_origin(rvalue, &live)
                    {
                        return Some(
                            "raw pointer reused after ownership was transferred to an owning value"
                                .into(),
                        );
                    }
                    let copies_origin = rvalue_copies_live_origin_value(rvalue, &live);
                    kill_strongly_updated_origins(&body.local_decls, target, &mut live);
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
                "raw pointer passed to another call after ownership was transferred".into(),
            );
        }
        if let TerminatorKind::Call {
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            kill_strongly_updated_origins(&body.local_decls, call_destination, &mut live);
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

fn places_holding_transferred_pointer(
    tcx: TyCtxt<'_>,
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

            let source_place = crate::helpers::mir_utils::rvalue_source_place(rvalue);

            if target_defines_holder {
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
                let source_key = PlaceKey::from_mir_place(source);
                if holders.iter().any(|h| source_key.overlaps(h)) && !holders.contains(&target_key)
                {
                    holders.push(target_key.clone());
                }
            }
            killed.insert(target.local);
        }

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
                let name = crate::helpers::mir_utils::call_name(tcx, func);
                if fn_simulator::is_as_ptr(&name)
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

fn kill_strongly_updated_origins(
    local_decls: &LocalDecls<'_>,
    target: &Place<'_>,
    live: &mut Vec<PlaceKey>,
) {
    let deref_count = target
        .projection
        .iter()
        .filter(|p| matches!(p, ProjectionElem::Deref))
        .count();
    if deref_count == 0 {
        let target_key = PlaceKey::from_mir_place(target);
        live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        return;
    }
    if deref_count == 1 && matches!(target.projection[0], ProjectionElem::Deref) {
        let ty = local_decls[target.local].ty;
        if matches!(ty.kind(), ty::Ref(_, _, ty::Mutability::Mut)) {
            let target_key = PlaceKey::from_mir_place(target);
            live.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        }
    }
}

fn place_key_is_prefix_of(prefix: &PlaceKey, place: &PlaceKey) -> bool {
    prefix.base == place.base
        && prefix.fields.len() <= place.fields.len()
        && place.fields[..prefix.fields.len()] == prefix.fields[..]
}

fn place_is_raw_access_to_live_origin(place: &Place<'_>, live: &[PlaceKey]) -> bool {
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

fn rvalue_reads_live_origin(rvalue: &Rvalue<'_>, live: &[PlaceKey]) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        place_is_raw_access_to_live_origin(place, live)
    })
}

fn rvalue_copies_live_origin_value(rvalue: &Rvalue<'_>, live: &[PlaceKey]) -> bool {
    let Some(place) = crate::helpers::mir_utils::rvalue_source_place(rvalue) else {
        return false;
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

fn terminator_uses_live_origin(kind: &TerminatorKind<'_>, live: &[PlaceKey]) -> bool {
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

fn terminator_returns_ownership(
    tcx: TyCtxt<'_>,
    terminator: &TerminatorKind<'_>,
    owner_locals: &HashSet<Local>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let name = crate::helpers::mir_utils::call_name(tcx, func);
    if !is_ownership_return_api(&name) {
        return false;
    }
    args.iter().any(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => owner_locals.contains(&place.local),
        _ => false,
    })
}

fn is_ownership_return_api(name: &str) -> bool {
    name.contains("into_raw")
        && (name.contains("boxed")
            || name.contains("Box")
            || name.contains("ffi::c_str")
            || name.contains("CString"))
}

fn pre_existing_view_on_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    reachable_after: &HashSet<BasicBlock>,
    origin_holders: &[PlaceKey],
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let origins = collect_local_origins(tcx, caller);

    let holder_origins: Vec<(usize, Vec<usize>)> = origin_holders
        .iter()
        .flat_map(|h| {
            if let PlaceBaseKey::Local(l) = h.base {
                let resolved = resolve_place_for_key(l, &h.fields, &origins);
                if resolved.0 == 1 && !resolved.1.is_empty() {
                    Some(resolved)
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    for (bb, data) in body.basic_blocks.iter_enumerated() {
        if reachable_after.contains(&bb) || bb == call_block {
            continue;
        }
        let terminator = data.terminator();
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind {
            let callee_name = crate::helpers::mir_utils::call_name(tcx, func);
            if callee_name.contains("::NonNull::<")
                && (callee_name.ends_with("::as_ref") || callee_name.ends_with("::as_mut"))
            {
                if let Some(arg) = args.first()
                    && let Some(place) = operand_mir_place(&arg.node)
                {
                    let arg_resolved = resolve_place(place, &origins);
                    if arg_resolved.0 == 1
                        && !arg_resolved.1.is_empty()
                        && holder_origins
                            .iter()
                            .any(|(h, hf)| *h == arg_resolved.0 && *hf == arg_resolved.1)
                    {
                        return Some(format!(
                            "pre-existing view from {} aliases the ownership-transferred pointer",
                            callee_name,
                        ));
                    }
                }
            }
        }

        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (_target, rvalue) = assign.as_ref();
            let src_place: Option<&Place<'_>> = match rvalue {
                Rvalue::Ref(_, _, place) => Some(place),
                Rvalue::Cast(kind, _, _)
                    if matches!(kind, rustc_middle::mir::CastKind::PtrToPtr) =>
                {
                    // Inline PtrToPtr extraction: the source operand is the
                    // derefed place.
                    let (_target, _cast_rvalue) = assign.as_ref();
                    if let Rvalue::Cast(_, operand, _) = _cast_rvalue {
                        match operand {
                            Operand::Copy(place) | Operand::Move(place) => Some(place),
                            _ => None,
                        }
                    } else {
                        None
                    }
                }
                _ => None,
            };
            let Some(place) = src_place else {
                continue;
            };
            if !place
                .projection
                .iter()
                .any(|p| matches!(p, ProjectionElem::Deref))
            {
                continue;
            }
            let resolved = resolve_place(place, &origins);
            if resolved.0 == 1
                && !resolved.1.is_empty()
                && holder_origins
                    .iter()
                    .any(|(h, hf)| *h == resolved.0 && *hf == resolved.1)
            {
                return Some(
                    "pre-existing &*raw_ptr view aliases the ownership-transferred pointer".into(),
                );
            }
        }
    }
    None
}

fn resolve_place_for_key(
    local: usize,
    local_fields: &[usize],
    origins: &LocalOriginMap,
) -> (usize, Vec<usize>) {
    if !local_fields.is_empty() {
        return (local, local_fields.to_vec());
    }
    origins
        .get(&local)
        .cloned()
        .unwrap_or((local, local_fields.to_vec()))
}

// ── Cross-crate callsite analysis ────────────────────────────────

pub fn private_fn_callsite_delegation(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origin: &PlaceKey,
    kind: HazardKind,
) -> Option<String> {
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
            None,
        ) {
            return Some(format!(
                "call site `{}` conflicts with the returned view: {reason}",
                tcx.def_path_str(site.caller)
            ));
        }
    }
    None
}

pub fn local_callsites(tcx: TyCtxt<'_>, callee: DefId) -> Vec<LocalCallsite<'_>> {
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

fn call_target_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(constant) = func else {
        return None;
    };
    match constant.const_.ty().kind() {
        TyKind::FnDef(def_id, _) => Some(*def_id),
        _ => None,
    }
}

pub fn callsite_arg_origins(
    tcx: TyCtxt<'_>,
    caller: DefId,
    args: &[Operand<'_>],
    param_index: usize,
) -> Vec<PlaceKey> {
    let Some(arg) = args.get(param_index) else {
        return Vec::new();
    };
    let Some(place) = (match arg {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        _ => None,
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

pub fn as_ptr_provenance_origins(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
) -> Vec<PlaceKey> {
    let aliases = collect_place_aliases(tcx, caller);
    find_as_ptr_receivers(tcx, caller, origins, &aliases, false)
}

// ── NonNull::as_mut escape analysis ──────────────────────────────

pub fn escaped_nonnull_as_mut_violation(
    tcx: TyCtxt<'_>,
    current: DefId,
    origin: &SelfFieldOrigin,
) -> Option<String> {
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
            if method_uses_nonnull_on_self_field(tcx, *item, origin.field_index) {
                return Some(format!(
                    "safe method `{}` creates a NonNull::as_mut reference from field `{}`",
                    tcx.def_path_str(*item),
                    origin.field_name
                ));
            }
        }
    }
    None
}

fn method_uses_nonnull_on_self_field(tcx: TyCtxt<'_>, method: DefId, field_index: usize) -> bool {
    let body = tcx.optimized_mir(method);
    let origins = collect_local_origins(tcx, method);

    for block in body.basic_blocks.iter() {
        let Some(terminator) = &block.terminator else {
            continue;
        };
        let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
            continue;
        };
        let callee_name = crate::helpers::mir_utils::call_name(tcx, func);
        if !callee_name.contains("::NonNull::<")
            || (!callee_name.ends_with("::as_ref") && !callee_name.ends_with("::as_mut"))
        {
            continue;
        }
        let Some(arg0) = args.first() else {
            continue;
        };
        let Some(place) = (match &arg0.node {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            _ => None,
        }) else {
            continue;
        };
        let (plocal, pfields) = resolve_place(place, &origins);
        if plocal == 1 && pfields.first() == Some(&field_index) {
            return true;
        }
    }

    false
}
