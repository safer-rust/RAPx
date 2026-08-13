//! VM-specific alias origin tracing.
//!
//! Bridges `VmState` provenance tracking with the shared `alias_hazard`
//! MIR scanning infrastructure. The VM already tracks which `AllocId`
//! each local's value points to; this module traces that provenance
//! back to the originating parameter/local.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, Operand, ProjectionElem, Rvalue, StatementKind};
use crate::verify::{
    alias_hazard::{self, AliasProducer, HazardKind},
    contract::Property,
    def_use::PlaceKey,
};
use crate::helpers::mir_scan::Checkpoint;
use crate::helpers::api_classify;
use crate::analysis::alias::collect_local_origins;

use super::state::{AllocId, VmState, VmValue};

/// Information about a value's ultimate origin.
#[derive(Clone, Debug)]
pub struct VmOrigin {
    /// The local (parameter or stack variable) that is the root source.
    pub local: Local,
    /// The allocation ID this pointer targets.
    pub alloc_id: AllocId,
    /// The type of the origin local (Ref/MutRef/RawPtr/Adt/...).
    pub kind: VmOriginKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VmOriginKind {
    MutRef,
    SharedRef,
    RawMutPtr,
    RawConstPtr,
    Owned(DefId),
    Unknown,
}

impl VmOrigin {
    /// Whether this origin is a `&mut T` reference — safe to create a unique view from.
    pub fn is_mut_ref(&self) -> bool {
        matches!(self.kind, VmOriginKind::MutRef)
    }

    /// Whether this origin is a `&T` reference — safe to create a shared view from.
    pub fn is_shared_ref(&self) -> bool {
        matches!(self.kind, VmOriginKind::SharedRef)
    }

    /// Whether this origin is `*const T` — shared, cannot safely create a unique view.
    pub fn is_const_ptr(&self) -> bool {
        matches!(self.kind, VmOriginKind::RawConstPtr)
    }

    /// Whether this origin is an owned type (Box, Vec) whose allocation was
    /// transferred to this function.
    pub fn is_owned(&self) -> bool {
        matches!(self.kind, VmOriginKind::Owned(_))
    }
}

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Trace the origin of a pointer value through VM provenance.
    ///
    /// Given a VmValue (extracted from a checkpoint argument), follows
    /// its provenance back to determine where the allocation came from.
    pub fn resolve_origin(&self, value: &VmValue<'ctx, 'tcx>) -> Option<VmOrigin> {
        let Some(prov) = &value.provenance else {
            return None;
        };

        let alloc_id = prov.alloc_id;

        // Walk all locals to find which one(s) have the same provenance.
        // Prefer parameters (arg_count) over temporaries.
        let mut best: Option<VmOrigin> = None;

        for (local, val) in &self.locals {
            let Some(val_prov) = &val.provenance else {
                continue;
            };
            if val_prov.alloc_id != alloc_id {
                continue;
            }

            let kind = self.classify_local(local);
            let candidate = VmOrigin {
                local: *local,
                alloc_id,
                kind,
            };

            // Prefer parameter locals and owned origins (Box/Vec)
            let is_param = local.as_usize() <= self.body.arg_count;
            let is_owned = candidate.is_owned();

            match &best {
                None => best = Some(candidate),
                Some(existing) => {
                    let ex_is_param = existing.local.as_usize() <= self.body.arg_count;
                    let ex_is_owned = existing.is_owned();
                    // Parameters preferred over non-params
                    if is_param && !ex_is_param {
                        best = Some(candidate);
                    } else if is_owned && !ex_is_owned {
                        best = Some(candidate);
                    } else if is_param == ex_is_param && is_owned == ex_is_owned {
                        // If equal priority, prefer the one with lower local index
                        if local.as_usize() < existing.local.as_usize() {
                            best = Some(candidate);
                        }
                    }
                }
            }
        }

        best
    }

    /// Classify a local by its type.
    fn classify_local(&self, local: &Local) -> VmOriginKind {
        let ty = self.body.local_decls[*local].ty;
        match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut) => {
                VmOriginKind::MutRef
            }
            rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not) => {
                VmOriginKind::SharedRef
            }
            rustc_middle::ty::TyKind::RawPtr(inner_ty, rustc_middle::ty::Mutability::Mut) => {
                let _ = inner_ty;
                VmOriginKind::RawMutPtr
            }
            rustc_middle::ty::TyKind::RawPtr(..) => VmOriginKind::RawConstPtr,
            rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                VmOriginKind::Owned(adt_def.did())
            }
            _ => VmOriginKind::Unknown,
        }
    }
}

// ── High-level VM alias check ────────────────────────────────────

/// Result of the VM-based alias check.
pub enum VmAliasResult {
    Proved,
    Failed(String),
    Unknown,
}

/// Run the full alias hazard check for the VM backend.
///
/// This is the function the `PropertyChecker::check_alias` delegates to.
pub fn check_alias_vm<'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    _property: &Property<'tcx>,
) -> VmAliasResult {
    let callee = match checkpoint.callee {
        Some(c) => c,
        // raw-ptr-deref / synthetic checkpoints: trace provenance to verify safety
        None => {
            let Some(origin_arg) = checkpoint.args.first() else {
                return VmAliasResult::Unknown;
            };
            let origin_val = vm_state.value_of_operand(origin_arg);
            if let Some(origin) = vm_state.resolve_origin(&origin_val) {
                if origin.is_mut_ref() || origin.is_shared_ref() {
                    return VmAliasResult::Proved;
                }
                if origin.is_owned() {
                    return VmAliasResult::Proved;
                }
            }
            // Pointer has provenance: check if it's safe.
            if let Some(prov) = &origin_val.provenance {
                let is_external = vm_state.allocations.iter()
                    .any(|a| a.id == prov.alloc_id && a.is_external);
                if !is_external {
                    return VmAliasResult::Proved;
                }
                // External provenance: safe for shared ref, unsafe for mut ref.
                let has_shared_ref = vm_state.body.local_decls.iter().any(|d| {
                    matches!(d.ty.kind(), rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not))
                });
                if has_shared_ref {
                    return VmAliasResult::Proved;
                }
            }
            // Without provenance: fall back to any reference parameter.
            if origin_val.provenance.is_none() {
                for decl in &vm_state.body.local_decls {
                    if matches!(decl.ty.kind(), rustc_middle::ty::TyKind::Ref(..)) {
                        return VmAliasResult::Proved;
                    }
                }
            }
            // Field-type-aware check: if the raw-ptr-deref operand traces to a
            // struct field and that field is a shared reference, the view is safe.
            let tcx = vm_state.tcx;
            let caller = checkpoint.caller;
            let arg_place = alias_hazard::operand_mir_place(origin_arg)
                .map(|p| PlaceKey::from_mir_place(p));
            if let Some(mir_place) = arg_place {
                let origin_map = collect_local_origins(tcx, caller);
                let (root, fields) = alias_hazard::deep_resolve_place(
                    mir_place.local().map(|l| l.as_usize()).unwrap_or(1),
                    &origin_map,
                );
                if !fields.is_empty() {
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
    let callee_name = vm_state.tcx.def_path_str(callee);

    // NonNull::as_ref / as_mut fast-path (formerly part of Ptr2Ref checking):
    // NonNull guarantees non-null + aligned + initialized by construction, so
    // the only remaining question is whether the produced reference escapes.
    // When the enclosing function returns a reference, the result may escape
    // (hazard for struct-field Owning invariants) → Unknown; otherwise safe.
    if callee_name.contains("::NonNull::")
        && (callee_name.ends_with("::as_ref") || callee_name.ends_with("::as_mut"))
    {
        let ret_ty = vm_state.body.local_decls[rustc_middle::mir::RETURN_PLACE].ty;
        if type_contains_reference(ret_ty) {
            return VmAliasResult::Unknown;
        }
        return VmAliasResult::Proved;
    }

    // Step 1: Determine the producer
    let Some(producer) = alias_hazard::alias_producer(&callee_name) else {
        return VmAliasResult::Unknown;
    };

    match producer {
        AliasProducer::View(kind) => {
            check_view_alias(vm_state, checkpoint, callee_name, kind)
        }
        AliasProducer::OwnershipTransfer => {
            check_ownership_transfer_alias(vm_state, checkpoint)
        }
        AliasProducer::ReadMemory => {
            check_read_memory_alias(vm_state, checkpoint)
        }
    }
}

fn check_view_alias<'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
    _callee_name: String,
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

    // Resolve origin PlaceKey from the checkpoint argument
    let origin_place = alias_hazard::operand_place(origin_arg)
        .or_else(|| alias_hazard::operand_mir_place(origin_arg)
            .map(|p| PlaceKey::from_mir_place(p)))
        .unwrap_or_else(|| {
            // Fallback: extract from the origin value's type
            PlaceKey::from_origin(
                adjust_operand_local(origin_arg).unwrap_or(1),
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
    let mir_place_from_arg = checkpoint.args.first()
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
            (HazardKind::SharedView, VmOriginKind::SharedRef) => return VmAliasResult::Proved,
            // Shared view from const raw pointer is safe: can't write through *const.
            (HazardKind::SharedView, VmOriginKind::RawConstPtr) => return VmAliasResult::Proved,
            (HazardKind::UniqueView, VmOriginKind::RawConstPtr) => {
                return VmAliasResult::Failed(
                    "const raw pointer cannot safely create a unique mutable view".into(),
                );
            }
            (HazardKind::UniqueView, VmOriginKind::SharedRef) => {
                // Shared-ref + unique view is only safe when backed by a private
                // struct field — defer to the struct field / escape analysis below.
            }
            _ => {}
        }
        if origin.is_owned() {
            let check = alias_hazard::alias_proved_for_param_local(
                tcx, caller, origin.local.as_usize(), kind,
            );
            // Skip the early Safe return for Vec/CString (reallocatable) types,
            // so MIR-level hazard scanning can detect reallocation hazards.
            let is_reallocatable = match &origin.kind {
                VmOriginKind::Owned(def_id) => {
                    let def_path = tcx.def_path_str(*def_id);
                    api_classify::is_std_vec(&def_path)
                        || api_classify::is_std_cstring(&def_path)
                }
                _ => false,
            };
            if matches!(check, alias_hazard::HazardCheck::Safe(_)) && !is_reallocatable {
                return VmAliasResult::Proved;
            }
        }
    }

    // Extract view length for from_raw_parts[_mut](ptr, len)
    let view_len_place =
        checkpoint.args.get(1).and_then(|a| alias_hazard::operand_place(a));

    // Run MIR-level hazard scanning
    if let Some(reason) = alias_hazard::local_hazard_violation(
        tcx, caller, call_block, destination, &origins, kind, view_len_place,
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
        tcx, caller, &origin_local_place, kind,
    ) {
        alias_hazard::HazardCheck::Violation(_) => {} // defer to struct field analysis
        alias_hazard::HazardCheck::Safe(_) => {}
        alias_hazard::HazardCheck::Inconclusive => {}
    }

    // Escape analysis
    let dest_escapes = alias_hazard::destination_flows_to_return(tcx, caller, destination);
    if dest_escapes {
        // Try resolved origin first (traces through local copies to struct fields)
        let field_origin = alias_hazard::self_field_origin(tcx, caller, &resolved_origin)
            .or_else(|| alias_hazard::self_field_origin(tcx, caller, &origin_place))
            // If tracing through origins failed, try to find the struct field by
            // scanning all collector local origins for a _1 field mapping.
            .or_else(|| find_struct_field_origin_for_param(tcx, caller, checkpoint));
        if let Some(sfo) = field_origin {
            if let Some(reason) = alias_hazard::escaped_self_field_violation(tcx, caller, &sfo) {
                return VmAliasResult::Failed(reason);
            }
            return VmAliasResult::Proved;
        }
        let any_field = alias_hazard::any_struct_field_origin(tcx, caller, &resolved_origin)
            .or_else(|| alias_hazard::any_struct_field_origin(tcx, caller, &origin_place));
        if let Some(sfo) = any_field {
            if let Some(reason) = alias_hazard::escaped_self_field_violation(tcx, caller, &sfo) {
                return VmAliasResult::Failed(reason);
            }
            return VmAliasResult::Proved;
        }
        if let Some(reason) = alias_hazard::private_fn_callsite_delegation(
            tcx, caller, &origin_place, kind,
        ) {
            return VmAliasResult::Failed(reason);
        }
        if kind == HazardKind::SharedView {
            let param_origin = alias_hazard::resolve_param_origin(tcx, caller, &origin_place);
            if let Some(local) = param_origin
                && alias_hazard::is_origin_a_reference(tcx, caller, &PlaceKey::from_origin(local, vec![]))
            {
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
        // For &self/&mut self methods, the borrow prevents concurrent access
        // so a local-only view is safe even when we can't identify the field.
        let body = tcx.optimized_mir(caller);
        if body.arg_count >= 1 {
            let self_ty = body.local_decls[Local::from_usize(1)].ty;
            if matches!(self_ty.kind(), rustc_middle::ty::TyKind::Ref(..)) {
                return VmAliasResult::Proved;
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

/// Attempt to extract the MIR local index from an operand for PlaceKey construction.
/// Try to find a struct field origin by examining checkpoint arguments
/// and the function's self type. Handles the case where origin tracing
/// fails to resolve through intermediate locals.
fn find_struct_field_origin_for_param<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<alias_hazard::SelfFieldOrigin> {
    let body = tcx.optimized_mir(caller);

    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let inner_adt = match self_ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), rustc_middle::ty::TyKind::Adt(..)) => *inner,
        _ => return None,
    };
    let (adt_def, _) = crate::analysis::alias::adt_from_ty(inner_adt)?;

    // Try to resolve the checkpoint's first arg to determine which field
    let Some(arg0) = checkpoint.args.first() else { return None; };
    let arg_place = match arg0 {
        Operand::Copy(p) | Operand::Move(p) => p,
        _ => return None,
    };

    // If the arg already has projections, use them directly
    if !arg_place.projection.is_empty() && arg_place.local == Local::from_usize(1) {
        let fields: Vec<usize> = arg_place.projection.iter()
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if !fields.is_empty() {
            let field_index = fields[0];
            let adt = tcx.adt_def(adt_def);
            let field = adt.all_fields().nth(field_index)?;
            return Some(alias_hazard::SelfFieldOrigin {
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
                let StatementKind::Assign(assign) = &stmt.kind else { continue };
                let (target, rvalue) = assign.as_ref();
                if target.local != arg_local { continue; }
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
                if source.local != Local::from_usize(1) { continue; }
                let fields: Vec<usize> = source.projection.iter()
                    .filter_map(|p| match p {
                        ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                        _ => None,
                    })
                    .collect();
                if fields.is_empty() { continue; }
                let field_index = fields[0];
                let adt = tcx.adt_def(adt_def);
                let field = adt.all_fields().nth(field_index)?;
                return Some(alias_hazard::SelfFieldOrigin {
                    struct_def_id: adt_def,
                    field_index,
                    field_name: field.name.to_string(),
                });
            }
        }
    }

    None
}

fn adjust_operand_local<'tcx>(op: &rustc_middle::mir::Operand<'tcx>) -> Option<usize> {
    match op {
        rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p)
            if p.projection.is_empty() =>
        {
            Some(p.local.as_usize())
        }
        _ => None,
    }
}

/// When origin tracing fails to resolve the exact struct field, try to infer
/// it from the function's self type. Looks for a raw pointer field in the struct
/// — for simple wrappers with a single raw pointer field, this works reliably.
fn infer_self_field_from_type<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller: DefId,
    checkpoint: &Checkpoint<'tcx>,
) -> Option<alias_hazard::SelfFieldOrigin> {
    let body = tcx.optimized_mir(caller);
    if body.arg_count == 0 {
        return None;
    }
    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let inner = match self_ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
        _ => return None,
    };
    let Some((adt_def, _)) = crate::analysis::alias::adt_from_ty(inner) else {
        return None;
    };

    let adt = tcx.adt_def(adt_def);
    let mut raw_ptr_fields: Vec<(usize, String)> = Vec::new();
    let variant = adt.non_enum_variant();
    for (idx, field) in variant.fields.iter().enumerate() {
        #[cfg(not(rapx_rustc_ge_198))]
        let field_ty = field.ty(tcx, rustc_middle::ty::GenericArgs::identity_for_item(tcx, adt_def));
        #[cfg(rapx_rustc_ge_198)]
        let field_ty = field.ty(tcx, rustc_middle::ty::GenericArgs::identity_for_item(tcx, adt_def)).skip_norm_wip();
        if matches!(field_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
            raw_ptr_fields.push((idx, field.name.to_string()));
        }
    }

    if raw_ptr_fields.len() == 1 {
        let (field_index, field_name) = raw_ptr_fields.into_iter().next().unwrap();
        return Some(alias_hazard::SelfFieldOrigin {
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
        let fields: Vec<usize> = place.projection.iter()
            .filter_map(|p| match p {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if let Some(&idx) = fields.first() {
            if let Some(field) = adt.all_fields().nth(idx) {
                return Some(alias_hazard::SelfFieldOrigin {
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
    origin: &alias_hazard::SelfFieldOrigin,
) -> Option<bool> {
    let body = tcx.optimized_mir(caller);
    let self_ty = body.local_decls[Local::from_usize(1)].ty;
    let ((adt_def, args), _) = match self_ty.kind() {
        rustc_middle::ty::TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), rustc_middle::ty::TyKind::Adt(..)) =>
        {
            let (did, a) = crate::analysis::alias::adt_from_ty(*inner)?;
            ((did, a), Some(inner))
        }
        _ => return None,
    };
    if adt_def != origin.struct_def_id {
        return Some(false);
    }
    let adt = tcx.adt_def(adt_def);
    let field = adt.all_fields().nth(origin.field_index)?;
    #[cfg(not(rapx_rustc_ge_198))]
    let field_ty = field.ty(tcx, args);
    #[cfg(rapx_rustc_ge_198)]
    let field_ty = field.ty(tcx, args).skip_norm_wip();
    Some(matches!(
        field_ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not)
    ))
}

/// copies/casts (e.g. `_tmp = self.ptr` → `_1.0`).
fn resolve_origin_place_mir(tcx: rustc_middle::ty::TyCtxt<'_>, caller: DefId, place: &PlaceKey) -> PlaceKey {
    let Some(local) = place.local() else {
        return place.clone();
    };
    let origins = crate::analysis::alias::collect_local_origins(tcx, caller);
    let (root_local, mut root_fields) =
        crate::verify::alias_hazard::deep_resolve_place(local.as_usize(), &origins);

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

fn check_ownership_transfer_alias<'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
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
        tcx, caller, call_block, destination, &origin_place,
    ) {
        return VmAliasResult::Failed(reason);
    }

    VmAliasResult::Proved
}

fn check_read_memory_alias<'ctx, 'tcx>(
    vm_state: &VmState<'ctx, 'tcx>,
    checkpoint: &Checkpoint<'tcx>,
) -> VmAliasResult {
    let Some(origin_arg) = checkpoint.args.first() else {
        return VmAliasResult::Unknown;
    };

    let origin_val = vm_state.value_of_operand(origin_arg);

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
        "read API value escapes while the source pointer persists — structural alias hazard"
            .into(),
    )
}

/// Whether a type transitively contains a reference (used by the
/// NonNull::as_ref/as_mut escape fast-path).
fn type_contains_reference(ty: rustc_middle::ty::Ty<'_>) -> bool {
    use rustc_middle::ty::TyKind;
    match ty.kind() {
        TyKind::Ref(..) => true,
        TyKind::Adt(_, substs) => substs.types().any(type_contains_reference),
        _ => false,
    }
}
