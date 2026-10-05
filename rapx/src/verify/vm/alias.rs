//! VM-specific alias origin tracing.
//!
//! Bridges `VmState` provenance tracking with the shared `alias_hazard`
//! MIR scanning infrastructure. The VM already tracks which `AllocId`
//! each local's value points to; this module traces that provenance
//! back to the originating parameter/local.

use super::alias_hazard::{self, AliasProducer, HazardKind};
use crate::analysis::alias::FieldOrigin;
use crate::helpers::mir_scan::Checkpoint;
use crate::verify::api_classify;
use crate::verify::contract::{Property, PropertyKind};
use crate::verify::def_use::PlaceKey;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand, ProjectionElem, Rvalue, StatementKind};

use super::state::{VmState, VmValue};

/// Information about a value's ultimate origin.
#[derive(Clone, Debug)]
pub(crate) struct VmOrigin {
    /// The local (parameter or stack variable) that is the root source.
    pub local: Local,
    /// The type of the origin local (Ref/MutRef/RawPtr/Adt/...).
    pub kind: VmOriginKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum VmOriginKind {
    MutRef,
    SharedRef,
    /// A raw pointer (`*const T` / `*mut T`). The const/mut distinction is
    /// compile-time-only (the casts are safe in both directions), so both are
    /// treated as one origin kind for alias analysis.
    RawPtr,
    Owned(DefId),
    Unknown,
}

impl VmOrigin {
    /// Whether this origin is a `&mut T` reference — safe to create a unique view from.
    pub(crate) fn is_mut_ref(&self) -> bool {
        matches!(self.kind, VmOriginKind::MutRef)
    }

    /// Whether this origin is a `&T` reference — safe to create a shared view from.
    pub(crate) fn is_shared_ref(&self) -> bool {
        matches!(self.kind, VmOriginKind::SharedRef)
    }

    /// Whether this origin is an owned type (Box, Vec) whose allocation was
    /// transferred to this function.
    pub(crate) fn is_owned(&self) -> bool {
        matches!(self.kind, VmOriginKind::Owned(_))
    }
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Trace the origin of a pointer value through VM provenance.
    ///
    /// Given a VmValue (extracted from a checkpoint argument), follows
    /// its provenance back to determine where the allocation came from.
    pub(crate) fn resolve_origin(&self, value: &VmValue<'z3, 'tcx>) -> Option<VmOrigin> {
        let Some(prov) = &value.provenance else {
            return None;
        };

        let alloc_id = prov.alloc_id;

        // Walk all locals to find which one(s) have the same provenance.
        // Prefer parameters (arg_count) over temporaries.
        let mut best: Option<VmOrigin> = None;

        for (local, val) in &self.current_frame.locals {
            let Some(val_prov) = &val.provenance else {
                continue;
            };
            if val_prov.alloc_id != alloc_id {
                continue;
            }

            let kind = self.classify_local(local);
            let candidate = VmOrigin {
                local: *local,
                kind,
            };

            // Prefer parameter locals and owned origins (Box/Vec), then the
            // lower local index.
            let is_param = local.as_usize() >= 1 && local.as_usize() <= self.body().arg_count;
            let is_owned = candidate.is_owned();

            match &best {
                None => best = Some(candidate),
                Some(existing) => {
                    let ex_is_param = existing.local.as_usize() >= 1
                        && existing.local.as_usize() <= self.body().arg_count;
                    let ex_is_owned = existing.is_owned();
                    let rank = |p: bool, o: bool| {
                        if p {
                            0
                        } else if o {
                            1
                        } else {
                            2
                        }
                    };
                    let cand_rank = rank(is_param, is_owned);
                    let ex_rank = rank(ex_is_param, ex_is_owned);
                    if cand_rank < ex_rank
                        || (cand_rank == ex_rank && local.as_usize() < existing.local.as_usize())
                    {
                        best = Some(candidate);
                    }
                }
            }
        }

        best
    }

    /// Classify a local by its type.
    fn classify_local(&self, local: &Local) -> VmOriginKind {
        let ty = self.body().local_decls[*local].ty;
        match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => {
                VmOriginKind::MutRef
            }
            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) => {
                VmOriginKind::SharedRef
            }
            rustc_middle::ty::TyKind::RawPtr(..) => VmOriginKind::RawPtr,
            rustc_middle::ty::TyKind::Adt(adt_def, _) => VmOriginKind::Owned(adt_def.did()),
            _ => VmOriginKind::Unknown,
        }
    }
}

// ── High-level VM alias check ────────────────────────────────────

/// Result of the VM-based alias check.
pub(crate) enum VmAliasResult {
    Proved,
    Failed(String),
    Unknown,
}

/// Whether a contract property tree contains an `Alias` atom (used to detect a
/// caller-declared `Alias`/`Ptr2Ref` precondition).
fn property_contains_alias(property: &Property<'_>) -> bool {
    match property {
        Property::Atom(a) => a.kind == PropertyKind::Alias,
        Property::And(and) => and.conjuncts.iter().any(|p| property_contains_alias(p)),
        Property::Or(or) => or.disjuncts.iter().any(|p| property_contains_alias(p)),
    }
}

/// Whether the caller declares an `Alias` assumption in its `#[rapx::requires]`
/// (directly or via a compound like `Ptr2Ref`). Such a function relies on its
/// caller-guaranteed precondition rather than on field encapsulation, so the
/// field-encapsulation escape check must not fire on it.
fn fn_has_alias_requires(tcx: rustc_middle::ty::TyCtxt<'_>, def_id: DefId) -> bool {
    crate::verify::target::get_contract_from_annotation(tcx, def_id)
        .iter()
        .any(property_contains_alias)
}

/// Flow-sensitive shared-XOR-mutable check for a view-producing checkpoint.
/// Walks the VM's *current* locals (not a static derivation tree), grouping a
/// live reference view as conflicting when it names the same allocation, or a
/// sub-allocation of it (`root_alloc` — `from_raw_parts`/`split_at` keep a
/// `parent` edge), with the opposite mutability.
fn flow_xor_violation<'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    unique: bool,
    statement_index: usize,
) -> Option<String> {
    let origin_arg = checkpoint.args.first()?;
    let origin_place = alias_hazard::operand_mir_place(origin_arg)?;
    let origin_local = origin_place.local;
    let origin_alloc = vm_state
        .value_of_operand(origin_arg)
        .provenance_alloc_id()?;
    let origin_root = vm_state.root_alloc(origin_alloc);
    let live = alias_hazard::live_locals_at(
        vm_state.tcx,
        checkpoint.caller,
        checkpoint.block,
        statement_index,
        false,
        false,
    );
    let body = vm_state.body();
    for (local, val) in &vm_state.current_frame.locals {
        if *local == origin_local {
            continue;
        }
        if !live.contains(local) {
            continue;
        }
        let Some(prov) = &val.provenance else {
            continue;
        };
        let mutability = match body.local_decls[*local].ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, _, m) => *m,
            _ => continue,
        };
        let same_alloc = prov.alloc_id == origin_alloc;
        let same_root = vm_state.root_alloc(prov.alloc_id) == origin_root;
        if !same_alloc && !same_root {
            continue;
        }
        let view_mut = mutability == rustc_middle::ty::Mutability::Mut;
        let conflicts = if unique { !view_mut } else { view_mut };
        if conflicts {
            let produced = if unique { "&mut" } else { "&" };
            let live_kind = if view_mut { "&mut" } else { "&" };
            return Some(format!(
                "producing {produced} while a live {live_kind} aliases the same data"
            ));
        }
    }
    None
}

/// Run the full alias hazard check for the VM backend.
///
/// This is the function the `PropertyChecker::check_alias` delegates to.
pub(crate) fn check_alias_vm<'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> VmAliasResult {
    let callee = match checkpoint.callee {
        Some(c) => c,
        // raw-ptr-deref / synthetic checkpoints: trace provenance to verify safety
        None => {
            let Some(origin_arg) = checkpoint.args.first() else {
                return VmAliasResult::Unknown;
            };
            let origin_val = vm_state.value_of_operand(origin_arg);
            // Step 4 (forward check): while the produced view is live, a later
            // raw access through the same origin violates shared-XOR-mutable.
            if let Some(origin_place) = alias_hazard::operand_place(origin_arg) {
                let kind = if checkpoint.is_mut_ref {
                    HazardKind::UniqueView
                } else {
                    HazardKind::SharedView
                };
                if let Some(reason) = alias_hazard::local_hazard_violation(
                    vm_state.tcx,
                    checkpoint.caller,
                    checkpoint.block,
                    checkpoint.destination,
                    &[origin_place],
                    kind,
                    None,
                ) {
                    return VmAliasResult::Failed(reason);
                }
            }
            if let Some(origin) = vm_state.resolve_origin(&origin_val) {
                // Step 3 (callsite check): unless an `Alias`/`Ptr2Ref` precondition
                // discharges the hazard, the deref must not violate shared-XOR-mutable
                // against a live alias of the opposite mutability (tree-based,
                // grouped by root or allocation).
                if !fn_has_alias_requires(vm_state.tcx, checkpoint.caller) {
                    if let Some(reason) = flow_xor_violation(
                        vm_state,
                        checkpoint,
                        checkpoint.is_mut_ref,
                        checkpoint.statement_index,
                    ) {
                        return VmAliasResult::Failed(reason);
                    }
                }
                if origin.is_mut_ref() {
                    // A mut view produced through a raw field of a reference
                    // parameter (`(*self).next`). When it escapes, trace to the
                    // root parameter and reject a shared-reference origin.
                    let dest_escapes = alias_hazard::destination_flows_to_return(
                        vm_state.tcx,
                        checkpoint.caller,
                        checkpoint.destination,
                    );
                    if dest_escapes
                        && let Some(mir_place) =
                            crate::helpers::mir_utils::operand_mir_place(origin_arg)
                    {
                        let (root, fields) = crate::verify::vm::alias_tree::AliasTree::build(
                            vm_state.tcx,
                            checkpoint.caller,
                        )
                        .resolve_local_to_root(mir_place.local);
                        if !fields.is_empty() && root >= 1 && root <= vm_state.body().arg_count {
                            let root_ty = vm_state.body().local_decls
                                [rustc_middle::mir::Local::from_usize(root)]
                            .ty;
                            if let rustc_middle::ty::TyKind::Ref(
                                _,
                                _,
                                rustc_middle::ty::Mutability::Not,
                            ) = root_ty.kind()
                                && checkpoint.is_mut_ref
                            {
                                return VmAliasResult::Failed(
                                    "&mut deref through a shared reference writes immutable data"
                                        .into(),
                                );
                            }
                        }
                    }
                    return VmAliasResult::Proved;
                }
                if origin.is_shared_ref() {
                    if checkpoint.is_mut_ref {
                        return VmAliasResult::Failed(
                            "&mut deref through a shared reference writes immutable data".into(),
                        );
                    }
                    // A shared view (`&*self.next`) produced through a raw field
                    // of a reference parameter. When the view escapes (flows to
                    // the return place), deep-resolve to that field and apply the
                    // same encapsulation check used by the view-producer path: a
                    // public or safe-code-exposed raw field cannot uphold the
                    // returned `&T`.
                    let dest_escapes = alias_hazard::destination_flows_to_return(
                        vm_state.tcx,
                        checkpoint.caller,
                        checkpoint.destination,
                    );
                    if dest_escapes
                        && let Some(mir_place) =
                            crate::helpers::mir_utils::operand_mir_place(origin_arg)
                    {
                        let (root, fields) = crate::verify::vm::alias_tree::AliasTree::build(
                            vm_state.tcx,
                            checkpoint.caller,
                        )
                        .resolve_local_to_root(mir_place.local);
                        if !fields.is_empty() && root >= 1 && root <= vm_state.body().arg_count {
                            let resolved = PlaceKey::from_origin(root, fields);
                            if let Some(sfo) = alias_hazard::self_field_origin(
                                vm_state.tcx,
                                checkpoint.caller,
                                &resolved,
                            ) {
                                // A caller that already declares an `Alias`
                                // precondition (e.g. `Ptr2Ref`) relies on its
                                // caller rather than field encapsulation, so the
                                // encapsulation check must not fire there.
                                if !fn_has_alias_requires(vm_state.tcx, checkpoint.caller) {
                                    return check_escaped_field(
                                        vm_state.tcx,
                                        checkpoint.caller,
                                        &sfo,
                                        HazardKind::SharedView,
                                    );
                                }
                            }
                        } else if root >= 1 && root <= vm_state.body().arg_count {
                            // A direct shared-reference parameter whose view
                            // escapes to the return must not claim a region that
                            // outlives its own (e.g. returning a `&'b str` as
                            // `&'a str` when `'a: 'b`).
                            if let Some(reason) = escape_region_violation(
                                vm_state.tcx,
                                checkpoint.caller,
                                root,
                            ) {
                                return VmAliasResult::Failed(reason);
                            }
                        }
                    }
                    return VmAliasResult::Proved;
                }
                if origin.is_owned() {
                    return VmAliasResult::Proved;
                }
                // An *independent* raw-pointer *parameter* (`*const T` / `*mut T`)
                // carries no borrow information. An `Alias`/`Ptr2Ref` precondition
                // discharges the hazard (the caller guarantees no aliasing), and a
                // local (non-escaping) view is safe; an escaping view without such
                // a precondition is an undeclared aliasing hazard — not a hard
                // violation, because the caller is an `unsafe fn` whose contract
                // (`Alias`/`Ptr2Ref` requires) carries the obligation. A
                // raw-pointer *field copy* (`_tmp = self.head`) is a temp local
                // above `arg_count`, derived from a borrow field — it falls
                // through to the field-type-aware check below.
                if matches!(origin.kind, VmOriginKind::RawPtr)
                    && origin.local.as_usize() <= vm_state.body().arg_count
                {
                    if fn_has_alias_requires(vm_state.tcx, checkpoint.caller) {
                        return VmAliasResult::Proved;
                    }
                    let escapes = alias_hazard::destination_flows_to_return(
                        vm_state.tcx,
                        checkpoint.caller,
                        checkpoint.destination,
                    );
                    if !escapes {
                        return VmAliasResult::Proved;
                    }
                    return VmAliasResult::Unknown;
                }
            }
            // A raw-pointer deref in a method whose `self` is a *by-value*
            // `NonNull<T>` is safe: consuming the `NonNull` transfers exclusive
            // ownership of its pointer (e.g. `NonNull::as_uninit_mut(self)`).
            // A *by-reference* `&NonNull<T>` / `&mut NonNull<T>` self is equally
            // safe (`NonNull::as_ref`/`as_mut`): the reference carries the borrow
            // (shared or exclusive) over the `NonNull`, whose pointer is the only
            // source of the deref.
            if vm_state.body().arg_count >= 1 {
                let self_ty = vm_state.body().local_decls[Local::from_usize(1)].ty;
                let nonnull_adt = match self_ty.kind() {
                    rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(*adt_def),
                    rustc_middle::ty::TyKind::Ref(_, pointee, _) => match pointee.kind() {
                        rustc_middle::ty::TyKind::Adt(adt_def, _) => Some(*adt_def),
                        _ => None,
                    },
                    _ => None,
                };
                if nonnull_adt.is_some_and(|adt| api_classify::is_std_nonnull(adt.did())) {
                    return VmAliasResult::Proved;
                }
            }
            // Pointer has provenance: check if it's safe.
            if let Some(prov) = &origin_val.provenance {
                let is_external = vm_state.alloc(prov.alloc_id).is_external();
                if !is_external {
                    return VmAliasResult::Proved;
                }
                // External provenance: safe for shared ref, unsafe for mut ref.
                let has_shared_ref = vm_state.body().local_decls.iter().any(|d| {
                    matches!(
                        d.ty.kind(),
                        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not)
                    )
                });
                if has_shared_ref {
                    return VmAliasResult::Proved;
                }
            }
            // Without provenance: fall back to any reference parameter.
            if origin_val.provenance.is_none() {
                for decl in &vm_state.body().local_decls {
                    if matches!(decl.ty.kind(), rustc_middle::ty::TyKind::Ref(..)) {
                        return VmAliasResult::Proved;
                    }
                }
            }
            // Field-type-aware check: if the raw-ptr-deref operand traces to a
            // struct field and that field is a shared reference, the view is safe.
            let tcx = vm_state.tcx;
            let caller = checkpoint.caller;
            let arg_place =
                alias_hazard::operand_mir_place(origin_arg).map(|p| PlaceKey::from_mir_place(p));
            if let Some(mir_place) = arg_place {
                let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);
                let local = mir_place
                    .local()
                    .unwrap_or(rustc_middle::mir::Local::from_usize(1));
                let (root, fields) = tree.resolve_local_to_root(local);
                if !fields.is_empty() {
                    // A raw-pointer field of a *by-value* `self` is exclusively
                    // owned by this call only when the `self` was *moved* (not
                    // copied), so re-borrowing it (`&mut *self.v`) cannot alias
                    // any live reference. A `Copy` by-value `self` is copied —
                    // the caller's copy still aliases the raw target — so it
                    // must not be treated as exclusive. A `&`/`&mut self` is
                    // handled by the shared/mut-ref origin paths above.
                    let root_ty =
                        vm_state.body().local_decls[rustc_middle::mir::Local::from_usize(root)].ty;
                    if !matches!(root_ty.kind(), rustc_middle::ty::TyKind::Ref(..)) {
                        let typing_env =
                            rustc_middle::ty::TypingEnv::post_analysis(tcx, caller);
                        if !tcx.type_is_copy_modulo_regions(typing_env, root_ty) {
                            return VmAliasResult::Proved;
                        }
                    }
                    let resolved = PlaceKey::from_origin(root, fields);
                    let sfo = alias_hazard::self_field_origin(tcx, caller, &resolved);
                    if let Some(sfo) = sfo {
                        if let Some(is_shared) = is_self_field_shared_ref(tcx, caller, &sfo) {
                            if is_shared {
                                return VmAliasResult::Proved;
                            }
                        }
                    }
                }
            }
            return VmAliasResult::Unknown;
        }
    };

    // NonNull::as_ref / as_mut fast-path (formerly part of Ptr2Ref checking):
    // NonNull guarantees non-null + aligned + initialized by construction, so
    // the only remaining question is whether the produced reference escapes.
    // An escaping `&mut` (as_mut) is a confirmed shared-XOR-mut violation — the
    // exclusive view is derived from a raw pointer with no borrow information,
    // so it cannot be exclusive while the enclosing `&mut self` is still live.
    // An escaping `&` (as_ref) is only a *possible* hazard → Unknown.
    if api_classify::is_nonnull_as_ref_as_mut(Some(callee)) {
        let ret_ty = vm_state.body().local_decls[rustc_middle::mir::RETURN_PLACE].ty;
        if crate::helpers::mir_utils::type_contains_reference(ret_ty) {
            if api_classify::is_nonnull_as_mut(Some(callee)) {
                return VmAliasResult::Failed(
                    "escaping `&mut` derived from a raw pointer without borrow information"
                        .into(),
                );
            }
            return VmAliasResult::Unknown;
        }
        return VmAliasResult::Proved;
    }

    // Step 1: Determine the producer
    let Some(producer) = alias_hazard::alias_producer(callee) else {
        return VmAliasResult::Unknown;
    };

    match producer {
        AliasProducer::View(kind) => check_view_alias(vm_state, checkpoint, kind),
        AliasProducer::OwnershipTransfer => check_ownership_transfer_alias(vm_state, checkpoint),
        AliasProducer::ReadMemory => check_read_memory_alias(vm_state, checkpoint),
    }
}

fn check_view_alias<'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    kind: HazardKind,
) -> VmAliasResult {
    let Some(origin_arg) = checkpoint.args.first() else {
        return VmAliasResult::Unknown;
    };
    let origin_val = vm_state.value_of_operand(origin_arg);

    let tcx = vm_state.tcx;
    let caller = checkpoint.caller;
    let call_block = checkpoint.block;
    let destination = alias_hazard::call_destination(tcx, checkpoint);

    // Tree-based shared-XOR-mutable: producing a view must not conflict with a
    // *live* opposite-mutability view of the same allocation. This runs before
    // the `Owned`/`MutRef`/`SharedRef` fast-paths below, which otherwise prove
    // without checking — e.g. two raw pointers split from one owned `Vec`, then
    // `&` and `&mut` views of each while the first is still live. An
    // `Alias`/`Ptr2Ref` precondition discharges the obligation.
    if !fn_has_alias_requires(vm_state.tcx, checkpoint.caller) {
        if let Some(reason) = flow_xor_violation(
            vm_state,
            checkpoint,
            kind == HazardKind::UniqueView,
            usize::MAX,
        ) {
            return VmAliasResult::Failed(reason);
        }
    }

    // Resolve origin PlaceKey from the checkpoint argument
    let origin_place = alias_hazard::operand_place(origin_arg).unwrap_or_else(|| {
        // Fallback: extract from the origin value's type
        PlaceKey::from_origin(
            crate::helpers::mir_utils::extract_local(origin_arg)
                .map(|l| l.as_usize())
                .unwrap_or(1),
            vec![],
        )
    });

    // Trace through local origins to resolve intermediate copies/casts.
    // e.g. `_tmp = self.ptr` → trace to `_1.0`
    let resolved_origin = resolve_origin_place_mir(tcx, caller, &origin_place);
    let mut origins = vec![origin_place.clone()];
    if resolved_origin != origin_place {
        origins.push(resolved_origin.clone());
    }

    // Also try to extract field projections from the checkpoint arg's MIR place.
    // If the arg directly references a struct field (e.g., `(*_1).0`), capture it.
    let mir_place_from_arg = checkpoint
        .args
        .first()
        .and_then(|a| alias_hazard::operand_mir_place(a));
    if let Some(place) = mir_place_from_arg {
        if !place.projection.is_empty() && place.local == Local::from_usize(1) {
            let field_key = PlaceKey::from_mir_place(place);
            if !field_key.fields.is_empty() && !origins.contains(&field_key) {
                origins.push(field_key);
            }
        }
    }

    // Try VM provenance tracing for fast-path checks
    if let Some(origin) = vm_state.resolve_origin(&origin_val) {
        match (kind, origin.kind) {
            (HazardKind::UniqueView, VmOriginKind::MutRef) => return VmAliasResult::Proved,
            (HazardKind::SharedView, VmOriginKind::SharedRef) => {
                // Aliasing-safe, but if the view escapes to the return, its
                // claimed region must not outlive the source reference's region.
                if let Some(reason) = shared_view_escape_region_violation(
                    tcx,
                    caller,
                    destination,
                    origin.local.as_usize(),
                ) {
                    return VmAliasResult::Failed(reason);
                }
                return VmAliasResult::Proved;
            }
            (HazardKind::UniqueView, VmOriginKind::SharedRef) => {
                // `&T` → `&mut T` violates shared-XOR-mutable regardless of
                // field encapsulation: the caller can re-enter the method and
                // obtain a second `&mut` to the same data.
                return VmAliasResult::Failed(
                    "shared reference cannot produce a unique mutable view".into(),
                );
            }
            // Raw-pointer origins (*const / *mut, compile-time-equivalent)
            // defer: the local hazard scan / escape / field analysis decides.
            _ => {}
        }
        if origin.is_owned() {
            let check = alias_hazard::alias_proved_for_param_local(
                tcx,
                caller,
                origin.local.as_usize(),
                kind,
            );
            // Skip the early Safe return for Vec/CString (reallocatable) types,
            // so MIR-level hazard scanning can detect reallocation hazards.
            let is_reallocatable = match &origin.kind {
                VmOriginKind::Owned(def_id) => {
                    api_classify::is_std_vec(*def_id) || api_classify::is_std_cstring(*def_id)
                }
                _ => false,
            };
            if matches!(check, alias_hazard::HazardCheck::Safe(_)) && !is_reallocatable {
                return VmAliasResult::Proved;
            }
        }
    }

    // Extract view length for from_raw_parts[_mut](ptr, len)
    let view_len_place = checkpoint
        .args
        .get(1)
        .and_then(|a| alias_hazard::operand_place(a));

    // Run MIR-level hazard scanning
    if let Some(reason) = alias_hazard::local_hazard_violation(
        tcx,
        caller,
        call_block,
        destination,
        &origins,
        kind,
        view_len_place,
    ) {
        return VmAliasResult::Failed(reason);
    }

    // Type-level safety checks (even when provenance is unavailable)
    let origin_pk = alias_hazard::resolve_param_origin(tcx, caller, &origin_place);
    if let Some(local_index) = origin_pk {
        match alias_hazard::alias_proved_for_param_local(tcx, caller, local_index, kind) {
            alias_hazard::HazardCheck::Safe(_) => return VmAliasResult::Proved,
            alias_hazard::HazardCheck::Violation(_) => {
                // Don't hard-fail here — the struct field analysis below may
                // override this for &self methods with private raw ptr fields.
            }
            alias_hazard::HazardCheck::Inconclusive => {}
        }
    }
    // Also try the origin local directly for reference-type checks
    let origin_local_place = if origin_place.fields.is_empty() {
        PlaceKey::from_origin(
            origin_place.local().map(|l| l.as_usize()).unwrap_or(1),
            vec![],
        )
    } else {
        origin_place.clone()
    };
    match alias_hazard::alias_proved_for_param_local_from_origin(
        tcx,
        caller,
        &origin_local_place,
        kind,
    ) {
        alias_hazard::HazardCheck::Violation(_) => {} // defer to struct field analysis
        alias_hazard::HazardCheck::Safe(_) => {}
        alias_hazard::HazardCheck::Inconclusive => {}
    }

    // Escape analysis
    let dest_escapes = alias_hazard::destination_flows_to_return(tcx, caller, destination);
    if dest_escapes {
        // Try resolved origin first (traces through local copies to struct fields)
        let field_origin =
            resolve_escaped_field_origin(tcx, caller, &resolved_origin, &origin_place, checkpoint);
        if let Some(sfo) = field_origin {
            return check_escaped_field(tcx, caller, &sfo, kind);
        }
        let any_field = alias_hazard::any_struct_field_origin(tcx, caller, &resolved_origin)
            .or_else(|| alias_hazard::any_struct_field_origin(tcx, caller, &origin_place));
        if let Some(sfo) = any_field {
            return check_escaped_field(tcx, caller, &sfo, kind);
        }
        if let Some(reason) =
            alias_hazard::private_fn_callsite_delegation(tcx, caller, &origin_place, kind)
        {
            return VmAliasResult::Failed(reason);
        }
        if kind == HazardKind::SharedView {
            let param_origin = alias_hazard::resolve_param_origin(tcx, caller, &origin_place);
            if let Some(local) = param_origin
                && alias_hazard::is_origin_a_reference(
                    tcx,
                    caller,
                    &PlaceKey::from_origin(local, vec![]),
                )
            {
                // The returned reference must not claim a region that outlives
                // the source reference's region: a shared view re-borrowed from
                // `&'b str` cannot be returned as `&'a str` when `'a: 'b` (the
                // source is only valid for the shorter `'b`).
                if let Some(reason) = escape_region_violation(tcx, caller, local) {
                    return VmAliasResult::Failed(reason);
                }
                return VmAliasResult::Proved;
            }
        }
    }

    // If no hazard found and view doesn't escape: local view is safe
    if !dest_escapes {
        return VmAliasResult::Proved;
    }

    // A unique view that escapes with a raw-pointer origin not backed by a
    // private struct field is a hazard.
    if kind == HazardKind::UniqueView {
        // Try to infer struct field from the caller's self type when origin
        // tracing fails. For &self/&mut self methods, scan the struct's fields
        // for a raw pointer field.
        if let Some(sfo) = infer_self_field_from_type(tcx, caller, checkpoint)
            .or_else(|| find_struct_field_origin_for_param(tcx, caller, checkpoint))
        {
            if alias_hazard::escaped_self_field_violation(tcx, caller, &sfo).is_none() {
                return VmAliasResult::Proved;
            }
        }
        let body = tcx.optimized_mir(caller);
        if body.arg_count >= 1 {
            let self_ty = body.local_decls[Local::from_usize(1)].ty;
            // A `NonNull<T>` consumed by value (e.g. `NonNull::as_uninit_mut(self)`)
            // transfers exclusive ownership of its pointer, so producing a unique
            // view is safe even though the receiver is not a `&mut self`.
            if let rustc_middle::ty::TyKind::Adt(adt_def, _) = self_ty.kind() {
                if api_classify::is_std_nonnull(adt_def.did()) {
                    return VmAliasResult::Proved;
                }
            }
        }
        return VmAliasResult::Failed(format!(
            "returned unique view escapes while the original pointer is not owned by a private self field [origin={:?}]",
            origin_place
        ));
    }

    // Conservatively proved (origin traced to safe type or no conflicts found)
    VmAliasResult::Proved
}

/// A shared view re-borrowed from the reference parameter `local` and returned
/// must not claim a region that outlives the parameter's own region. Returns a
/// violation reason when `local`'s region does not outlive the return region.
fn shared_view_escape_region_violation(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: DefId,
    destination: Option<Local>,
    local: usize,
) -> Option<String> {
    if !alias_hazard::destination_flows_to_return(tcx, caller, destination) {
        return None;
    }
    escape_region_violation(tcx, caller, local)
}

/// Check whether the shared view's claimed return region outlives the source
/// reference `local`'s region. Returns a violation reason when it does.
fn escape_region_violation(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: DefId,
    local: usize,
) -> Option<String> {
    // MIR `local_decls` erases lifetime regions (`ReErased`), so take the
    // precise (late-bound-liberated) regions from the function signature.
    let src_region =
        super::region::fn_arg_ty(tcx, caller, local - 1).and_then(|ty| match ty.kind() {
            rustc_middle::ty::TyKind::Ref(region, _, _) => Some(*region),
            _ => None,
        })?;
    let ret_region = super::region::fn_return_region(tcx, caller)?;
    if !super::region::region_outlives(tcx, caller, src_region, ret_region) {
        return Some(format!(
            "returned region `{ret_region:?}` outlives the source reference's region `{src_region:?}`"
        ));
    }
    None
}

/// Attempt to extract the MIR local index from an operand for PlaceKey construction.
/// Try to find a struct field origin by examining checkpoint arguments
/// and the function's self type. Handles the case where origin tracing
/// fails to resolve through intermediate locals.
fn find_struct_field_origin_for_param<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<FieldOrigin> {
    let body = tcx.optimized_mir(caller);
    let (adt_def, _) = self_adt(tcx, caller)?;

    // Try to resolve the checkpoint's first arg to determine which field
    let Some(arg0) = checkpoint.args.first() else {
        return None;
    };
    let arg_place = match arg0 {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };

    // If the arg already has projections, use them directly
    if !arg_place.projection.is_empty() && arg_place.local == Local::from_usize(1) {
        let fields: Vec<usize> = arg_place
            .projection
            .iter()
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if !fields.is_empty() {
            let field_index = fields[0];
            let adt = tcx.adt_def(adt_def);
            let field = adt.all_fields().nth(field_index)?;
            return Some(FieldOrigin {
                struct_def_id: adt_def,
                field_index,
                field_name: field.name.to_string(),
            });
        }
    }

    // Otherwise, scan MIR blocks for assignments from _1 to the arg's local
    let arg_local = arg_place.local;
    if arg_place.projection.is_empty() && arg_local != Local::from_usize(1) {
        for block in body.basic_blocks.iter() {
            for stmt in &block.statements {
                let StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (target, rvalue) = assign.as_ref();
                if target.local != arg_local {
                    continue;
                }
                let source = match rvalue {
                    #[cfg(rapx_rvalue_use_with_retag)]
                    Rvalue::Use(operand, _) => match operand {
                        Operand::Copy(p) | Operand::Move(p) => p,
                        _ => continue,
                    },
                    #[cfg(not(rapx_rvalue_use_with_retag))]
                    Rvalue::Use(operand) => match operand {
                        Operand::Copy(p) | Operand::Move(p) => p,
                        _ => continue,
                    },
                    Rvalue::CopyForDeref(p) => p,
                    _ => continue,
                };
                if source.local != Local::from_usize(1) {
                    continue;
                }
                let fields: Vec<usize> = source
                    .projection
                    .iter()
                    .filter_map(|p| match p {
                        ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                        _ => None,
                    })
                    .collect();
                if fields.is_empty() {
                    continue;
                }
                let field_index = fields[0];
                let adt = tcx.adt_def(adt_def);
                let field = adt.all_fields().nth(field_index)?;
                return Some(FieldOrigin {
                    struct_def_id: adt_def,
                    field_index,
                    field_name: field.name.to_string(),
                });
            }
        }
    }

    None
}

/// When origin tracing fails to resolve the exact struct field, try to infer
/// it from the function's self type. Looks for a raw pointer field in the struct
/// — for simple wrappers with a single raw pointer field, this works reliably.
fn infer_self_field_from_type<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<FieldOrigin> {
    let Some((adt_def, _)) = self_adt(tcx, caller) else {
        return None;
    };

    let adt = tcx.adt_def(adt_def);
    let mut raw_ptr_fields: Vec<(usize, String)> = Vec::new();
    let variant = adt.non_enum_variant();
    for (idx, field) in variant.fields.iter().enumerate() {
        let field_ty = crate::helpers::mir_utils::field_ty(
            tcx,
            field,
            rustc_middle::ty::GenericArgs::identity_for_item(tcx, adt_def),
        );
        if matches!(field_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
            raw_ptr_fields.push((idx, field.name.to_string()));
        }
    }

    if raw_ptr_fields.len() == 1 {
        let (field_index, field_name) = raw_ptr_fields.into_iter().next().unwrap();
        return Some(FieldOrigin {
            struct_def_id: adt_def,
            field_index,
            field_name,
        });
    }

    // Multiple raw ptr fields: try to match by the checkpoint arg's source
    // This is less reliable but serves as a fallback.
    if let Some(arg0) = checkpoint.args.first()
        && let Some(place) = alias_hazard::operand_mir_place(arg0)
    {
        let fields: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if let Some(&idx) = fields.first() {
            if let Some(field) = adt.all_fields().nth(idx) {
                return Some(FieldOrigin {
                    struct_def_id: adt_def,
                    field_index: idx,
                    field_name: field.name.to_string(),
                });
            }
        }
    }

    None
}
/// Check whether a self field's type is a shared reference (`&T` or `&[T]`).
/// Used by raw-ptr-deref alias checks to prove shared views are safe when the
/// underlying field is a shared reference.
fn is_self_field_shared_ref(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: DefId,
    origin: &FieldOrigin,
) -> Option<bool> {
    let (adt_def, args) = self_adt(tcx, caller)?;
    if adt_def != origin.struct_def_id {
        return Some(false);
    }
    let adt = tcx.adt_def(adt_def);
    let field = adt.all_fields().nth(origin.field_index)?;
    let field_ty = crate::helpers::mir_utils::field_ty(tcx, field, args);
    Some(matches!(
        field_ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not)
    ))
}

/// Shared escape + field-encapsulation check: a view that escapes and traces to
/// a struct field is safe only if the field is private and not written/exposed
/// by safe code. A unique (`&mut`) view escaping through a private raw field is
/// still unsound — the caller can re-enter and obtain a second `&mut`.
fn check_escaped_field(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: DefId,
    sfo: &FieldOrigin,
    kind: HazardKind,
) -> VmAliasResult {
    if let Some(reason) = alias_hazard::escaped_self_field_violation(tcx, caller, sfo) {
        return VmAliasResult::Failed(reason);
    }
    if kind == HazardKind::UniqueView {
        return VmAliasResult::Failed("unique view escapes through a private raw field".into());
    }
    VmAliasResult::Proved
}

/// Resolve the struct field an escaping view came from: try the derivation tree
/// first (via the resolved and raw origins), then fall back to self-type
/// heuristics when tree resolution fails to reach a field.
fn resolve_escaped_field_origin<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
    resolved_origin: &PlaceKey,
    origin_place: &PlaceKey,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<FieldOrigin> {
    alias_hazard::self_field_origin(tcx, caller, resolved_origin)
        .or_else(|| alias_hazard::self_field_origin(tcx, caller, origin_place))
        .or_else(|| find_struct_field_origin_for_param(tcx, caller, checkpoint))
}

/// copies/casts (e.g. `_tmp = self.ptr` → `_1.0`).
fn resolve_origin_place_mir(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    caller: DefId,
    place: &PlaceKey,
) -> PlaceKey {
    let Some(local) = place.local() else {
        return place.clone();
    };
    let tree = crate::verify::vm::alias_tree::AliasTree::build(tcx, caller);
    let (root_local, mut root_fields) = tree.resolve_local_to_root(local);

    // Preserve field projections from the original place if the root is same local
    if root_local == local.as_usize() && root_fields.is_empty() && !place.fields.is_empty() {
        root_fields = place.fields.clone();
    }

    // Combine: root's fields + any additional projections from the resolved chain
    // (e.g. if place = _tmp, root = _1 with fields [0], keep fields [0])
    if root_fields.is_empty() && !place.fields.is_empty() {
        return place.clone();
    }

    PlaceKey::from_origin(root_local, root_fields)
}

/// Extract the `&self`/`&mut self` receiver's ADT (peeling one reference layer),
/// or `None` for non-ADT receivers.  Shared by the struct-field origin heuristics.
fn self_adt<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
) -> Option<(DefId, rustc_middle::ty::GenericArgsRef<'tcx>)> {
    let body = tcx.optimized_mir(caller);
    if body.arg_count == 0 {
        return None;
    }
    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let inner = match self_ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
        _ => return None,
    };
    crate::analysis::alias::adt_from_ty(inner)
}

fn check_ownership_transfer_alias<'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> VmAliasResult {
    let Some(origin_arg) = checkpoint.args.first() else {
        return VmAliasResult::Unknown;
    };

    let tcx = vm_state.tcx;
    let caller = checkpoint.caller;
    let call_block = checkpoint.block;
    let destination = alias_hazard::call_destination(tcx, checkpoint);

    let origin_place = alias_hazard::operand_place(origin_arg);
    let Some(origin_place) = origin_place else {
        return VmAliasResult::Unknown;
    };

    if let Some(reason) = alias_hazard::ownership_transfer_violation(
        tcx,
        caller,
        call_block,
        destination,
        &origin_place,
    ) {
        return VmAliasResult::Failed(reason);
    }

    VmAliasResult::Proved
}

fn check_read_memory_alias<'z3, 'tcx>(
    vm_state: &VmState<'z3, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> VmAliasResult {
    let Some(origin_arg) = checkpoint.args.first() else {
        return VmAliasResult::Unknown;
    };

    let origin_val = vm_state.value_of_operand(origin_arg);

    // If the enclosing function accepted the structural-alias hazard via its
    // contract (e.g. `any(Trait(T, Copy), Alias(self, ret))`), the read is the
    // accepted hazard rather than a violation.
    if vm_state.path_facts.alias_hazard_accepted {
        return VmAliasResult::Proved;
    }

    // If the pointee type is Copy, read is safe
    if let rustc_middle::ty::TyKind::RawPtr(pointee, _) = origin_val.ty.kind() {
        let tcx = vm_state.tcx;
        let typing_env = rustc_middle::ty::TypingEnv::post_analysis(tcx, checkpoint.caller);
        if tcx.type_is_copy_modulo_regions(typing_env, *pointee) {
            return VmAliasResult::Proved;
        }
    }

    // If the returned value doesn't escape to the return, read is local and safe
    let tcx = vm_state.tcx;
    let destination = alias_hazard::call_destination(tcx, checkpoint);
    if !alias_hazard::destination_flows_to_return(tcx, checkpoint.caller, destination) {
        return VmAliasResult::Proved;
    }

    VmAliasResult::Failed(
        "read API value escapes while the source pointer persists — structural alias hazard".into(),
    )
}
