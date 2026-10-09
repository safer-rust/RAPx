//! MIR-level alias hazard scanning for the symbolic VM backend.
//!
//! This module holds the pure MIR hazard analysis (origin-based parameter
//! safety, escape analysis, local hazard scanning, and ownership-transfer
//! violation scanning) independent of VM state and Z3 terms. It was extracted
//! from the old forward verifier's `smt_check/alias.rs`.
//!
//! `vm/alias.rs` provides the VM-specific provenance→origin resolution and
//! orchestrates the overall alias check, calling into this module for the
//! underlying MIR scanning.

use crate::helpers::mir_utils;
use std::collections::{HashMap, HashSet};

use rustc_hir::{Safety, def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Local, LocalDecls, Operand, Place, ProjectionElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    ty::{self, AssocKind, TyCtxt, TyKind},
};

use crate::analysis::alias::{FieldOrigin, resolve_any_field_origin, resolve_self_field_origin};
use crate::helpers::fn_info::is_externally_reachable;
use crate::{
    helpers::mir_scan::check_safety,
    verify::def_use::{PlaceBaseKey, PlaceKey},
};

// Re-export the mir_utils helpers still consumed by `vm/alias.rs`.
pub(super) use crate::helpers::mir_utils::{call_destination, operand_mir_place, operand_place};
// Remaining mir_utils helpers used only within this module.
use crate::helpers::mir_utils::{blocks_reachable_after_call, rvalue_any_place_matching};

// ── Shared types ─────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum HazardKind {
    SharedView,
    UniqueView,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AliasProducer {
    View(HazardKind),
    OwnershipTransfer,
    ReadMemory,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RawAccessKind {
    Read,
    Write,
}

#[derive(Clone, Debug)]
struct LocalCallsite<'tcx> {
    pub caller: DefId,
    pub block: BasicBlock,
    pub args: Vec<Operand<'tcx>>,
    pub destination: Option<Local>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum HazardCheck {
    Safe(String),
    Violation(String),
    Inconclusive,
}

// ── API classification ───────────────────────────────────────────

pub(super) fn alias_producer(callee: DefId) -> Option<AliasProducer> {
    if crate::verify::api_classify::is_from_raw_parts_mut(Some(callee)) {
        return Some(AliasProducer::View(HazardKind::UniqueView));
    }
    if crate::verify::api_classify::is_vec_ownership_transfer(Some(callee)) {
        return Some(AliasProducer::OwnershipTransfer);
    }
    if crate::verify::api_classify::is_from_raw_parts(Some(callee))
        || crate::verify::api_classify::is_cstr_from_ptr(Some(callee))
    {
        return Some(AliasProducer::View(HazardKind::SharedView));
    }
    if crate::verify::api_classify::is_ownership_transfer(Some(callee)) {
        return Some(AliasProducer::OwnershipTransfer);
    }
    if crate::verify::api_classify::is_ptr_read(Some(callee)) {
        return Some(AliasProducer::ReadMemory);
    }
    None
}

// ── Origin-based parameter safety ────────────────────────────────

pub(super) fn alias_proved_for_param_local(
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
        _ if !matches!(ty.kind(), ty::RawPtr(..))
            && local_index >= 1
            && local_index <= body.arg_count =>
        {
            HazardCheck::Safe(
                "returned view derives from an owned parameter; no external alias risk".into(),
            )
        }
        _ => HazardCheck::Inconclusive,
    }
}

pub(super) fn alias_proved_for_param_local_from_origin(
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

pub(super) fn is_origin_a_reference(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> bool {
    let body = tcx.optimized_mir(caller);
    let PlaceBaseKey::Local(mut local) = origin.base else {
        return false;
    };
    if let ty::Ref(..) = body.local_decls[Local::from_usize(local)].ty.kind() {
        return true;
    }
    let (resolved, _) = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller)
        .resolve_local_to_root(Local::from_usize(local));
    if resolved >= 1 && resolved <= body.arg_count {
        local = resolved;
    }
    matches!(
        body.local_decls[Local::from_usize(local)].ty.kind(),
        ty::Ref(..)
    )
}

/// Resolve `origin` to a parameter MIR local, tracing through local-copy origins
/// when the base is not itself a parameter.
///
/// Returns a 1-based MIR local index (usable directly with `Local::from_usize`),
/// or `None` when the origin does not trace back to a parameter.
pub(super) fn resolve_param_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origin: &PlaceKey,
) -> Option<usize> {
    let body = tcx.optimized_mir(caller);
    if let PlaceBaseKey::Local(local) = origin.base {
        if local >= 1 && local <= body.arg_count {
            return Some(local);
        }
        let (resolved, _fields) = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller)
            .resolve_local_to_root(Local::from_usize(local));
        if resolved >= 1 && resolved <= body.arg_count {
            return Some(resolved);
        }
    }
    None
}

/// Return the 0-based argument index for `origin` when it is a direct, whole
/// raw-pointer parameter (no field projections, no local-copy tracing).
///
/// Unlike [`resolve_param_origin`], this returns a 0-based index into the call
/// argument list (used by `callsite_arg_origins`) and does not trace through the
/// alias tree.
fn param_index_of_origin(tcx: TyCtxt<'_>, caller: DefId, origin: &PlaceKey) -> Option<usize> {
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

// ── Escape analysis ──────────────────────────────────────────────

pub(super) fn destination_flows_to_return(
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
            if target.local.as_usize() == 0
                && rvalue_mentions_local(rvalue, destination, &aliases) {
                    return true;
                }
            if rvalue_mentions_local(rvalue, destination, &aliases) {
                aliases.insert(target.local, aliases[&destination].clone());
            }
        }
    }
    false
}

pub(super) fn self_field_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<FieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    resolve_self_field_origin(tcx, caller, local, &place.fields)
}

pub(super) fn any_struct_field_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    place: &PlaceKey,
) -> Option<FieldOrigin> {
    let PlaceBaseKey::Local(local) = place.base else {
        return None;
    };
    if place.fields.is_empty() {
        return None;
    }
    resolve_any_field_origin(tcx, caller, local, &place.fields)
}

/// The mutability (`Not` / `Mut`) of the borrow carried by `self_local`'s type
/// (a `&T` / `&mut T`), or `None` if it is not a reference. `self_local` is
/// `_1` for a method receiver, and any parameter for a free function.
fn self_borrow_mutability(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    self_local: Local,
) -> Option<ty::Mutability> {
    let body = tcx.optimized_mir(def_id);
    match body.local_decls[self_local].ty.kind() {
        TyKind::Ref(_, _, m) => Some(*m),
        _ => None,
    }
}

pub(super) fn escaped_self_field_violation(
    tcx: TyCtxt<'_>,
    current: DefId,
    origin: &FieldOrigin,
) -> Option<String> {
    if public_raw_field(tcx, origin) {
        return Some(format!(
            "returned view escapes while raw field `{}` is public",
            origin.field_name
        ));
    }
    let current_self = self_borrow_mutability(tcx, current, Local::from_usize(1));
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
            if let Some(reason) =
                check_fn_against_field(tcx, *item, origin, current_self, Local::from_usize(1))
            {
                return Some(reason);
            }
        }
    }
    // A raw field is also reachable from free functions in the same module
    // (Rust privacy is module-scoped), so a free fn that writes or exposes the
    // field breaks encapsulation exactly like a method would.
    for (fn_def_id, param_locals) in free_fns_for_struct(tcx, origin.struct_def_id) {
        if fn_def_id == current {
            continue;
        }
        if check_safety(tcx, fn_def_id) == Safety::Unsafe {
            continue;
        }
        if !tcx.is_mir_available(fn_def_id) {
            continue;
        }
        for param_local in param_locals {
            if let Some(reason) =
                check_fn_against_field(tcx, fn_def_id, origin, current_self, param_local)
            {
                return Some(reason);
            }
        }
    }
    None
}

/// Check whether `item` (a struct method or a same-module free function) writes
/// or exposes the raw field `origin` through the borrow carried by `self_local`.
/// A shared current borrow (`&self`) is not invalidated by a mutable item borrow
/// (`&mut self`), and a mutable/mutable pair is likewise fine; any other
/// combination is a violation. Returns the violation description, or `None`.
fn check_fn_against_field(
    tcx: TyCtxt<'_>,
    item: DefId,
    origin: &FieldOrigin,
    current_self: Option<ty::Mutability>,
    self_local: Local,
) -> Option<String> {
    let item_self = self_borrow_mutability(tcx, item, self_local);
    if method_writes_self_field(tcx, item, self_local, origin.field_index) {
        if current_self.is_none() || item_self.is_none() {
            return None;
        }
        if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) = (current_self, item_self) {
            return None;
        }
        return Some(format!(
            "safe fn `{}` writes through raw field `{}`",
            tcx.def_path_str(item),
            origin.field_name
        ));
    }
    if method_exposes_self_field(tcx, item, self_local, origin.field_index) {
        if current_self.is_none() || item_self.is_none() {
            return None;
        }
        if let (Some(ty::Mutability::Not), Some(ty::Mutability::Mut)) = (current_self, item_self) {
            return None;
        }
        if let (Some(ty::Mutability::Mut), Some(ty::Mutability::Mut)) = (current_self, item_self) {
            return None;
        }
        return Some(format!(
            "safe fn `{}` exposes raw field `{}`",
            tcx.def_path_str(item),
            origin.field_name
        ));
    }
    None
}

fn public_raw_field(tcx: TyCtxt<'_>, origin: &FieldOrigin) -> bool {
    let adt = tcx.adt_def(origin.struct_def_id);
    let Some(field) = adt.all_fields().nth(origin.field_index) else {
        return false;
    };
    field.vis.is_public()
}

fn impls_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<DefId> {
    let mut impls = tcx
        .inherent_impls(struct_def_id).to_vec();

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

/// Collect the free functions in the struct's own module that take a
/// `&Struct` / `&mut Struct` parameter. Rust privacy is module-scoped, so only
/// those can reach a private raw field. Each entry pairs the function with the
/// parameter locals that carry the struct reference.
fn free_fns_for_struct(tcx: TyCtxt<'_>, struct_def_id: DefId) -> Vec<(DefId, Vec<Local>)> {
    let Some(struct_local) = struct_def_id.as_local() else {
        return Vec::new();
    };
    let struct_module = tcx.parent_module_from_def_id(struct_local);
    let mut fns = Vec::new();
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let rustc_hir::ItemKind::Fn { .. } = &item.kind else {
            continue;
        };
        let fn_def_id = item_id.owner_id.to_def_id();
        let Some(fn_local) = fn_def_id.as_local() else {
            continue;
        };
        if tcx.parent_module_from_def_id(fn_local) != struct_module {
            continue;
        }
        let param_locals = struct_ref_param_locals(tcx, fn_def_id, struct_def_id);
        if !param_locals.is_empty() {
            fns.push((fn_def_id, param_locals));
        }
    }
    fns
}

/// Return the parameter locals of `def_id` whose type is a `&Struct` /
/// `&mut Struct` reference to `struct_def_id`.
fn struct_ref_param_locals(tcx: TyCtxt<'_>, def_id: DefId, struct_def_id: DefId) -> Vec<Local> {
    let body = tcx.optimized_mir(def_id);
    (1..=body.arg_count)
        .filter_map(|i| {
            let local = Local::from_usize(i);
            match body.local_decls[local].ty.kind() {
                TyKind::Ref(_, pointee, _) => match pointee.kind() {
                    TyKind::Adt(adt_def, _) => (adt_def.did() == struct_def_id).then_some(local),
                    _ => None,
                },
                _ => None,
            }
        })
        .collect()
}

/// Whether `method` writes through the raw field `field_index` of the struct
/// borrowed via `self_local` (`_1` for a method, any parameter for a free fn).
fn method_writes_self_field(
    tcx: TyCtxt<'_>,
    method: DefId,
    self_local: Local,
    field_index: usize,
) -> bool {
    let body = tcx.optimized_mir(method);
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, method);
    let origin = self_field_key(self_local, field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, _) = assign.as_ref();
            if place_is_raw_access_to_origin(target, &origin, &tree, &body.local_decls)
                || place_raw_accesses_self_field(tcx, method, target, self_local, field_index)
            {
                return true;
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_writes_origin(&terminator.kind, &origin, &tree) {
            return true;
        }
    }

    false
}

/// Whether `place` is a raw-pointer deref whose operand traces back to the
/// field `field_index` of the struct borrowed via `self_local`.
fn place_raw_accesses_self_field(
    tcx: TyCtxt<'_>,
    method: DefId,
    place: &Place<'_>,
    self_local: Local,
    field_index: usize,
) -> bool {
    let body = tcx.optimized_mir(method);
    let has_raw_deref = place.projection.iter().any(|projection| {
        if let ProjectionElem::Deref = projection {
            matches!(
                body.local_decls[place.local].ty.kind(),
                TyKind::RawPtr(_, _)
            )
        } else {
            false
        }
    });
    if !has_raw_deref {
        return false;
    }
    local_traces_to_self_field(
        tcx,
        method,
        place.local,
        self_local,
        field_index,
        &mut HashSet::new(),
    )
}

/// Backward-traces `local` through MIR assignments to check whether its value
/// is derived from `(*self_local).field_index`.
fn local_traces_to_self_field(
    tcx: TyCtxt<'_>,
    method: DefId,
    local: Local,
    self_local: Local,
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
            let Some(source) = mir_utils::rvalue_source_place(rvalue) else {
                continue;
            };
            let source_key = PlaceKey::from_mir_place(source);
            if source_key.base == PlaceBaseKey::Local(self_local.as_usize())
                && source_key.fields.first() == Some(&field_index)
            {
                return true;
            }
            if source_key.fields.is_empty()
                && local_traces_to_self_field(
                    tcx,
                    method,
                    source.local,
                    self_local,
                    field_index,
                    seen,
                )
            {
                return true;
            }
        }
    }
    false
}

/// Whether `method` returns a raw-pointer-bearing value derived from the field
/// `field_index` of the struct borrowed via `self_local`, i.e. it leaks the raw
/// field to the caller.
fn method_exposes_self_field(
    tcx: TyCtxt<'_>,
    method: DefId,
    self_local: Local,
    field_index: usize,
) -> bool {
    let body = tcx.optimized_mir(method);

    let self_ty = body.local_decls[self_local].ty;
    if !matches!(self_ty.kind(), TyKind::Ref(_, _, _)) {
        return false;
    }

    let ret_ty = body.local_decls[Local::from_usize(0)].ty;
    if !mir_utils::type_contains_raw_ptr(tcx, ret_ty) {
        return false;
    }

    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, method);
    let origin = self_field_key(self_local, field_index);

    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (target, rvalue) = assign.as_ref();
            if target.local.as_usize() == 0 && rvalue_mentions_origin(rvalue, &origin, &tree) {
                return true;
            }
        }
    }

    false
}

fn rvalue_mentions_origin(
    rvalue: &Rvalue<'_>,
    origin: &PlaceKey,
    tree: &crate::verify::vm::alias_tree::AliasTree,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        let key = PlaceKey::from_mir_place(place);
        let resolved = if key.fields.is_empty() {
            let (root, fields) = tree.resolve_local_to_root(place.local);
            PlaceKey::from_origin(root, fields)
        } else {
            key
        };
        resolved.overlaps(origin)
    })
}

/// The `PlaceKey` for `(*self_local).field_index`.
fn self_field_key(self_local: Local, field_index: usize) -> PlaceKey {
    PlaceKey {
        base: PlaceBaseKey::Local(self_local.as_usize()),
        fields: vec![field_index],
    }
}

fn rvalue_mentions_local(
    rvalue: &Rvalue<'_>,
    local: Local,
    aliases: &HashMap<Local, PlaceKey>,
) -> bool {
    mir_utils::rvalue_any_place_matching(rvalue, &mut |place| {
        // A deref of `local` reads the pointee rather than flowing `local`'s
        // value toward the return place, so it does not count as a copy.
        let has_deref = place
            .projection
            .iter()
            .any(|p| matches!(p, ProjectionElem::Deref));
        !has_deref && (place.local == local || aliases.contains_key(&place.local))
    })
}

// ── Local hazard scanning ────────────────────────────────────────

fn raw_access_conflicts(kind: HazardKind, access: RawAccessKind) -> bool {
    match kind {
        HazardKind::SharedView => access == RawAccessKind::Write,
        HazardKind::UniqueView => true,
    }
}

pub(super) fn local_hazard_violation(
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

fn local_hazard_violation_with(
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
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);
    let mut origins = origins.to_vec();
    expand_origin_aliases(&tree, &mut origins);
    let mut hazard_locals: HashSet<Local> = destination.into_iter().collect();
    expand_hazard_alias_locals(tcx, caller, &mut hazard_locals);
    for data in body.basic_blocks.iter() {
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call {
                func,
                destination: call_dest,
                ..
            } = &terminator.kind
                && crate::verify::api_classify::is_split_at(
                    mir_utils::dep_callee_def_id(func),
                ) {
                    hazard_locals.insert(call_dest.local);
                }
    }
    origins.retain(|origin| !origin.local().is_some_and(|l| hazard_locals.contains(&l)));
    let vec_owners = find_as_ptr_receivers(tcx, caller, &origins, &tree, true);
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
                    if !hazard_locals.is_empty()
                        && !hazard_locals.contains(&target.local)
                        && raw_access_conflicts(kind, RawAccessKind::Write)
                        && place_is_raw_access_to_any_origin(
                            target,
                            &origins,
                            &tree,
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
                        && !mir_utils::rvalue_source_place(rvalue)
                            .is_some_and(|place| hazard_locals.contains(&place.local))
                        && !rvalue_reads_like_view(rvalue, tcx, caller, &origins, &tree)
                        && rvalue_reads_any_origin(rvalue, &origins, &tree, &body.local_decls)
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
            if origins
                .iter()
                .any(|origin| terminator_writes_origin(&terminator.kind, origin, &tree))
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw write call through original pointer after {:?} view creation",
                    kind
                ));
            }
            if kind == HazardKind::UniqueView
                && !vec_owners.is_empty()
                && terminator_invalidates_vec_owner(&terminator.kind, &vec_owners, &tree)
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(
                    "Vec may reallocate while a raw-derived mutable view is still live".to_string(),
                );
            }
            if strict_call_escape
                && block_index != call_block
                && !terminator_is_benign_origin_use(&terminator.kind)
                && origins
                    .iter()
                    .any(|origin| terminator_uses_origin(&terminator.kind, origin, &tree))
                && hazard_used_after_block(tcx, caller, block_index, &hazard_locals)
            {
                return Some(format!(
                    "raw pointer escapes to another call while the {:?} view is live",
                    kind
                ));
            }
            if view_len_place.is_some()
                && let TerminatorKind::Call {
                    func,
                    args,
                    destination: call_dest,
                    ..
                } = &terminator.kind
                {
                    let callee = mir_utils::dep_callee_def_id(func);
                    if crate::verify::api_classify::is_from_raw_parts(callee) && !args.is_empty()
                        && let Some(ptr_place) = operand_place(&args[0].node) {
                            let offset_eq = is_ptr_add_offset_eq(
                                tcx,
                                caller,
                                &ptr_place,
                                view_len_place.as_ref().unwrap(),
                            );
                            let from_add = is_ptr_from_ptr_add(tcx, caller, &ptr_place);
                            if offset_eq || from_add {
                                hazard_locals.insert(call_dest.local);
                                continue;
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
    rustc_middle::mir::traversal::reverse_postorder(body)
}

/// Compute the set of locals that are live (between `StorageLive` and
/// `StorageDead`) at the deref point `(call_block, statement_index)`, scanning
/// the function in execution order up to that point. Used by the callsite
/// shared-XOR-mutable check to ignore temporaries that have already gone dead
/// (e.g. a method call's `&self` receiver).
pub(crate) fn live_locals_at(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    statement_index: usize,
    seed_params: bool,
    track_moves: bool,
) -> HashSet<Local> {
    let body = tcx.optimized_mir(caller);
    // Parameters (`_1..=arg_count`) are live on entry and have no explicit
    // `StorageLive`; seed them so a `&self`/`String`/`Box` parameter is treated
    // as live until its `StorageDead`.
    let mut live: HashSet<Local> = if seed_params {
        (1..=body.arg_count).map(Local::from_usize).collect()
    } else {
        HashSet::new()
    };
    for (block, data) in reverse_postorder_blocks(body) {
        let reached = block == call_block;
        for (i, statement) in data.statements.iter().enumerate() {
            if reached && i >= statement_index {
                break;
            }
            match &statement.kind {
                StatementKind::StorageLive(local) => {
                    live.insert(*local);
                }
                StatementKind::StorageDead(local) => {
                    live.remove(local);
                }
                StatementKind::Assign(assign) if track_moves => {
                    // A move out of a local (`std::mem::forget(data)` inlined as
                    // `_x = move data`) consumes it even without a `StorageDead`.
                    let (_, rvalue) = &**assign;
                    if let rustc_middle::mir::Rvalue::Use(operand, ..) = rvalue
                        && let Operand::Move(place) = operand {
                            live.remove(&place.local);
                        }
                }
                _ => {}
            }
        }
        if reached {
            break;
        }
        // A call that *moves* a local out (`Box::into_raw(value)`) consumes it,
        // even though its `StorageDead` may only appear at the end of the body.
        if track_moves
            && let TerminatorKind::Call { args, .. } = &data.terminator().kind {
                for arg in args {
                    if let Operand::Move(place) = &arg.node {
                        live.remove(&place.local);
                    }
                }
            }
    }
    live
}

fn expand_origin_aliases(
    tree: &crate::verify::vm::alias_tree::AliasTree,
    origins: &mut Vec<PlaceKey>,
) {
    let mut changed = true;
    while changed {
        changed = false;
        for node in &tree.nodes {
            let local_key = PlaceKey {
                base: PlaceBaseKey::Local(node.local.as_usize()),
                fields: Vec::new(),
            };
            let (root, fields) = tree.resolve_local_to_root(node.local);
            let alias = PlaceKey::from_origin(root, fields);
            let related = origins.iter().any(|origin| {
                local_key.overlaps(origin)
                    || origin.overlaps(&local_key)
                    || alias.overlaps(origin)
                    || origin.overlaps(&alias)
            });
            if !related {
                continue;
            }
            if !origins.contains(&local_key) {
                origins.push(local_key);
                changed = true;
            }
            if !origins.contains(&alias) {
                origins.push(alias);
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
            #[cfg(rapx_ge_95)]
            Operand::RuntimeChecks(_) => false,
        }),
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            match discr {
                Operand::Copy(place) | Operand::Move(place) => locals.contains(&place.local),
                Operand::Constant(_) => false,
                #[cfg(rapx_ge_95)]
                Operand::RuntimeChecks(_) => false,
            }
        }
        TerminatorKind::Drop { place, .. } => locals.contains(&place.local),
        _ => false,
    }
}

/// Resolve a MIR place through the alias tree: a field-projected place resolves
/// to itself; a whole-local place resolves to its ultimate origin.
fn resolve_mir_place_tree(
    tree: &crate::verify::vm::alias_tree::AliasTree,
    place: &Place<'_>,
) -> PlaceKey {
    let fields = PlaceKey::from_mir_place(place).fields;
    let (root, root_fields) = resolve_via_tree(tree, place.local, &fields);
    PlaceKey::from_origin(root, root_fields)
}

/// Resolve a place's *local* through the alias tree (ignoring the place's own
/// field projections), falling back to the MIR place itself when unmapped.
fn resolve_place_key_tree(
    tree: &crate::verify::vm::alias_tree::AliasTree,
    place: &Place<'_>,
) -> PlaceKey {
    if tree.tag_of(place.local).is_some() {
        let (root, fields) = tree.resolve_local_to_root(place.local);
        PlaceKey::from_origin(root, fields)
    } else {
        PlaceKey::from_mir_place(place)
    }
}

fn place_is_raw_access_to_any_origin(
    place: &Place<'_>,
    origins: &[PlaceKey],
    tree: &crate::verify::vm::alias_tree::AliasTree,
    local_decls: &LocalDecls<'_>,
) -> bool {
    origins
        .iter()
        .any(|origin| place_is_raw_access_to_origin(place, origin, tree, local_decls))
}

fn place_is_raw_access_to_origin(
    place: &Place<'_>,
    origin: &PlaceKey,
    tree: &crate::verify::vm::alias_tree::AliasTree,
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
    let pointer = resolve_place_key_tree(tree, place);
    pointer.overlaps(origin)
}

fn rvalue_reads_like_view(
    rvalue: &Rvalue<'_>,
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
    tree: &crate::verify::vm::alias_tree::AliasTree,
) -> bool {
    let Some(place) = mir_utils::rvalue_source_place(rvalue) else {
        return false;
    };
    if !place
        .projection
        .iter()
        .any(|p| matches!(p, ProjectionElem::Deref))
    {
        return false;
    }
    let pointer = resolve_place_key_tree(tree, place);
    if !origins.iter().any(|origin| pointer.overlaps(origin)) {
        return false;
    }
    is_origin_a_reference(tcx, caller, &pointer)
}

fn rvalue_reads_any_origin(
    rvalue: &Rvalue<'_>,
    origins: &[PlaceKey],
    tree: &crate::verify::vm::alias_tree::AliasTree,
    local_decls: &LocalDecls<'_>,
) -> bool {
    rvalue_any_place_matching(rvalue, &mut |place| {
        place_is_raw_access_to_any_origin(place, origins, tree, local_decls)
    })
}

fn terminator_writes_origin<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    tree: &crate::verify::vm::alias_tree::AliasTree,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    let callee = mir_utils::dep_callee_def_id(func);
    if !crate::verify::api_classify::is_ptr_write(callee) {
        return false;
    }
    let Some(arg0) = args.first() else {
        return false;
    };
    let Some(place) = operand_mir_place(&arg0.node) else {
        return false;
    };
    resolve_mir_place_tree(tree, place).overlaps(origin)
}

fn terminator_uses_origin<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    origin: &PlaceKey,
    tree: &crate::verify::vm::alias_tree::AliasTree,
) -> bool {
    let TerminatorKind::Call { args, .. } = terminator else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = operand_mir_place(&arg.node) else {
            return false;
        };
        resolve_mir_place_tree(tree, place).overlaps(origin)
    })
}

fn terminator_is_benign_origin_use<'tcx>(
    terminator: &TerminatorKind<'tcx>,
) -> bool {
    let TerminatorKind::Call { func, .. } = terminator else {
        return true;
    };
    crate::verify::api_classify::is_benign_origin_use(mir_utils::dep_callee_def_id(
        func,
    ))
}

fn terminator_invalidates_vec_owner<'tcx>(
    terminator: &TerminatorKind<'tcx>,
    owners: &[PlaceKey],
    tree: &crate::verify::vm::alias_tree::AliasTree,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    if !crate::verify::api_classify::is_vec_invalidating_method(
        mir_utils::dep_callee_def_id(func),
    ) {
        return false;
    }
    args.iter().any(|arg| {
        let Some(place) = operand_mir_place(&arg.node) else {
            return false;
        };
        let arg = resolve_mir_place_tree(tree, place);
        owners
            .iter()
            .any(|owner| arg.overlaps(owner) || owner.overlaps(&arg))
    })
}

fn find_as_ptr_receivers(
    tcx: TyCtxt<'_>,
    caller: DefId,
    origins: &[PlaceKey],
    tree: &crate::verify::vm::alias_tree::AliasTree,
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
        if !crate::verify::api_classify::is_as_ptr(mir_utils::dep_callee_def_id(
            func,
        )) {
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
                    && tree.tag_of(destination.local).is_some_and(|_| {
                        let (root, fields) = tree.resolve_local_to_root(destination.local);
                        let alias = PlaceKey::from_origin(root, fields);
                        origins.iter().any(|o| alias.overlaps(o))
                    }))
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
        let resolved = resolve_mir_place_tree(tree, place);
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
) -> bool {
    let body = tcx.optimized_mir(caller);
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);
    let view_len_root = view_len.local().map(|l| tree.resolve_local_to_root(l));
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
            if crate::verify::api_classify::is_pointer_add(
                mir_utils::dep_callee_def_id(func),
            ) && args.len() >= 2
                && let Some(offset_place) = operand_place(&args[1].node) {
                    let offset_root = offset_place.local().map(|l| tree.resolve_local_to_root(l));
                    return offset_root == view_len_root;
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
            return crate::verify::api_classify::is_pointer_add(
                mir_utils::dep_callee_def_id(func),
            );
        }
    }
    false
}

// ── Ownership transfer violation scanning ────────────────────────

pub(super) fn ownership_transfer_violation(
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
            && terminator_returns_ownership(&terminator.kind, &owner_locals)
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
        let mut live_origins = match entry_states.get_mut(&block_index) {
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
                        live_origins.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
                    }
                    if place_is_raw_access_to_live_origin(target, &live_origins)
                        || rvalue_any_place_matching(rvalue, &mut |place| {
                            place_is_raw_access_to_live_origin(place, &live_origins)
                        })
                    {
                        return Some(
                            "raw pointer reused after ownership was transferred to an owning value"
                                .into(),
                        );
                    }
                    let copies_origin = rvalue_copies_live_origin_value(rvalue, &live_origins);
                    kill_strongly_updated_origins(&body.local_decls, target, &mut live_origins);
                    if copies_origin
                        && !target
                            .projection
                            .iter()
                            .any(|projection| matches!(projection, ProjectionElem::Deref))
                    {
                        let target_key = PlaceKey::from_mir_place(target);
                        if !live_origins.contains(&target_key) {
                            live_origins.push(target_key);
                        }
                    }
                }
                StatementKind::StorageDead(local) => {
                    live_origins
                        .retain(|origin| origin.base != PlaceBaseKey::Local(local.as_usize()));
                }
                _ => {}
            }
        }

        let Some(terminator) = &block.terminator else {
            continue;
        };
        if terminator_uses_live_origin(&terminator.kind, &live_origins) {
            return Some(
                "raw pointer passed to another call after ownership was transferred".into(),
            );
        }
        if let TerminatorKind::Call {
            destination: call_destination,
            ..
        } = &terminator.kind
        {
            kill_strongly_updated_origins(&body.local_decls, call_destination, &mut live_origins);
        }
        if live_origins.is_empty() {
            continue;
        }
        for successor in terminator.successors() {
            worklist.push((successor, live_origins.clone()));
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

            let source_place = mir_utils::rvalue_source_place(rvalue);

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
                && crate::verify::api_classify::is_as_ptr(
                    mir_utils::dep_callee_def_id(func),
                ) && let Some(arg) = args.first()
                    && let Operand::Copy(place) | Operand::Move(place) = &arg.node
                    && !killed.contains(&place.local)
                {
                    let key = PlaceKey::from_mir_place(place);
                    if !holders.contains(&key) {
                        holders.push(key);
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
    live_origins: &mut Vec<PlaceKey>,
) {
    let deref_count = target
        .projection
        .iter()
        .filter(|p| matches!(p, ProjectionElem::Deref))
        .count();
    if deref_count == 0 {
        let target_key = PlaceKey::from_mir_place(target);
        live_origins.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        return;
    }
    if deref_count == 1 && matches!(target.projection[0], ProjectionElem::Deref) {
        let ty = local_decls[target.local].ty;
        if matches!(ty.kind(), ty::Ref(_, _, ty::Mutability::Mut)) {
            let target_key = PlaceKey::from_mir_place(target);
            live_origins.retain(|origin| !place_key_is_prefix_of(&target_key, origin));
        }
    }
}

fn place_key_is_prefix_of(prefix: &PlaceKey, place: &PlaceKey) -> bool {
    prefix.base == place.base
        && prefix.fields.len() <= place.fields.len()
        && place.fields[..prefix.fields.len()] == prefix.fields[..]
}

fn place_is_raw_access_to_live_origin(place: &Place<'_>, live_origins: &[PlaceKey]) -> bool {
    if !place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
    {
        return false;
    }
    let key = PlaceKey::from_mir_place(place);
    live_origins.iter().any(|origin| key.overlaps(origin))
}

fn rvalue_copies_live_origin_value(rvalue: &Rvalue<'_>, live_origins: &[PlaceKey]) -> bool {
    let Some(place) = mir_utils::rvalue_source_place(rvalue) else {
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
    live_origins.iter().any(|origin| key.overlaps(origin))
}

fn terminator_uses_live_origin(kind: &TerminatorKind<'_>, live_origins: &[PlaceKey]) -> bool {
    let TerminatorKind::Call { args, .. } = kind else {
        return false;
    };
    args.iter().any(|arg| {
        let Some(place) = operand_mir_place(&arg.node) else {
            return false;
        };
        let key = PlaceKey::from_mir_place(place);
        live_origins.iter().any(|origin| key.overlaps(origin))
    })
}

fn terminator_returns_ownership(
    terminator: &TerminatorKind<'_>,
    owner_locals: &HashSet<Local>,
) -> bool {
    let TerminatorKind::Call { func, args, .. } = terminator else {
        return false;
    };
    if !crate::verify::api_classify::is_ownership_return(
        mir_utils::dep_callee_def_id(func),
    ) {
        return false;
    }
    args.iter().any(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => owner_locals.contains(&place.local),
        _ => false,
    })
}

fn pre_existing_view_on_origin(
    tcx: TyCtxt<'_>,
    caller: DefId,
    call_block: BasicBlock,
    reachable_after: &HashSet<BasicBlock>,
    origin_holders: &[PlaceKey],
) -> Option<String> {
    let body = tcx.optimized_mir(caller);
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);

    let holder_origins: Vec<(usize, Vec<usize>)> = origin_holders
        .iter()
        .flat_map(|h| {
            if let PlaceBaseKey::Local(l) = h.base {
                let resolved = resolve_via_tree(&tree, Local::from_usize(l), &h.fields);
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
            let callee_name = mir_utils::call_name(tcx, func);
            if crate::verify::api_classify::is_nonnull_as_ref_as_mut(
                mir_utils::dep_callee_def_id(func),
            )
                && let Some(arg) = args.first()
                    && let Some(place) = operand_mir_place(&arg.node)
                {
                    let arg_resolved = resolve_via_tree(
                        &tree,
                        place.local,
                        &PlaceKey::from_mir_place(place).fields,
                    );
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

        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (_target, rvalue) = assign.as_ref();
            let src_place: Option<&Place<'_>> = match rvalue {
                Rvalue::Ref(_, _, place) => Some(place),
                Rvalue::Cast(rustc_middle::mir::CastKind::PtrToPtr, operand, _) => {
                    match operand {
                        Operand::Copy(place) | Operand::Move(place) => Some(place),
                        _ => None,
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
            let resolved =
                resolve_via_tree(&tree, place.local, &PlaceKey::from_mir_place(place).fields);
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

/// Resolve `(local, fields)` through the alias tree: a place that already names
/// a field path resolves to itself; a whole-local place resolves to its ultimate
/// `(root, fields)` origin.
fn resolve_via_tree(
    tree: &crate::verify::vm::alias_tree::AliasTree,
    local: Local,
    fields: &[usize],
) -> (usize, Vec<usize>) {
    if !fields.is_empty() {
        return (local.as_usize(), fields.to_vec());
    }
    tree.resolve_local_to_root(local)
}

// ── Cross-crate callsite analysis ────────────────────────────────

pub(super) fn private_fn_callsite_delegation(
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
        let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, site.caller);
        let extra = find_as_ptr_receivers(tcx, site.caller, &origins, &tree, false);
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

fn local_callsites(tcx: TyCtxt<'_>, callee: DefId) -> Vec<LocalCallsite<'_>> {
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
            let Some(target) = mir_utils::dep_callee_def_id(func) else {
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

fn callsite_arg_origins(
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
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);
    let mut origins = vec![place.clone()];
    if let Some(local) = place.local()
        && tree.tag_of(local).is_some()
    {
        let (root, fields) = tree.resolve_local_to_root(local);
        let alias = PlaceKey::from_origin(root, fields);
        if !origins.contains(&alias) {
            origins.push(alias);
        }
    }
    origins
}
