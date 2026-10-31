//! Symbolic memory model for the VM.

use crate::helpers::mir_utils;
use crate::verify::api_classify;
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{
    mir::{Local, Place, ProjectionElem},
    ty::{Ty, TyKind},
};
use z3::{Context, Sort, ast::{Array, Ast, Bool, Int}};

use super::state::{AllocId, AllocKind, Allocation, ElementTy, MemoryContent, MemoryUnit, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn copy_memory_values(
        &mut self,
        source: &VmValue<'z3, 'tcx>,
        target: &VmValue<'z3, 'tcx>,
        count: &VmValue<'z3, 'tcx>,
    ) {
        let concrete_count = count.z3_term.simplify().as_u64();
        if concrete_count == Some(0) {
            return;
        }
        let Some(pointee_ty) = mir_utils::pointee_ty(target.ty) else {
            self.unsupported_mir = true;
            return;
        };
        let local_target = self
            .find_local_by_address(&target.z3_term)
            .is_some_and(|local| self.body().local_decls[local].ty == pointee_ty);
        let inline_target = self
            .inline
            .arg_referents
            .iter()
            .enumerate()
            .any(|(i, referent)| {
                referent.is_some()
                    && self
                        .local_value(Local::from_usize(i + 1))
                        .is_some_and(|value| value.z3_term == target.z3_term)
            });
        let slice_target = target.provenance.as_ref().is_some_and(|prov| {
            matches!(self.alloc(prov.alloc_id).kind, AllocKind::Slice { .. } | AllocKind::ExternalSlice { .. })
        });
        let allocated_target = target.provenance.as_ref().is_some_and(|prov| {
            let alloc = self.alloc(prov.alloc_id);
            matches!(&alloc.kind, AllocKind::Object | AllocKind::Slice { .. })
                && alloc.element_ty.as_ty() == Some(pointee_ty)
                && (matches!(&alloc.kind, AllocKind::Slice { .. })
                    || prov.offset.simplify().as_u64() == Some(0))
        });
        let scratch_target_ty = target.provenance.as_ref().and_then(|prov| {
            let alloc = self.alloc(prov.alloc_id);
            let ty = alloc.element_ty.as_ty()?;
            match ty.kind() {
                TyKind::Adt(def, args)
                    if api_classify::is_maybe_uninit_type(def.did())
                        && prov.offset.simplify().as_u64() == Some(0) => {
                    args.first().and_then(|arg| arg.as_type())
                }
                _ => None,
            }
        });
        let scratch_target = scratch_target_ty.is_some();
        if !local_target && !inline_target && !allocated_target && !scratch_target {
            self.unsupported_mir = true;
            return;
        }
        if concrete_count != Some(1) && target.provenance.is_none() {
            self.unsupported_mir = true;
            return;
        }
        let source_value = self
            .find_local_by_address(&source.z3_term)
            .filter(|local| self.body().local_decls[*local].ty == pointee_ty)
            .and_then(|local| self.local_value(local).cloned())
            .or_else(|| {
                source
                    .provenance
                    .as_ref()
                    .and_then(|prov| self.load_value(prov.alloc_id, pointee_ty, &[]).cloned())
            });
        let source_initialized = source
            .provenance
            .as_ref()
            .is_some_and(|prov| {
                let content = self.content(prov.alloc_id);
                let maybe_uninit = self.alloc(prov.alloc_id).element_ty.as_ty().is_some_and(|ty| {
                    matches!(ty.kind(), TyKind::Adt(def, _)
                        if api_classify::is_maybe_uninit_type(def.did()))
                });
                (content.facts.initialized && !maybe_uninit)
                    || (prov.offset.simplify().as_u64() == Some(0)
                        && content.copied_prefix.as_ref().is_some_and(|(ty, copied_count)| {
                            *ty == pointee_ty
                                && self.path_implies(&count.z3_term.le(copied_count))
                        }))
            })
            || source_value.as_ref().is_some_and(|value| {
                value.facts.init && (source.provenance.is_none() || concrete_count == Some(1))
            });
        if (slice_target || scratch_target) && !source_initialized {
            self.unsupported_mir = true;
            return;
        }
        let mut copied = if concrete_count == Some(1) {
            source_value.unwrap_or_else(|| VmValue::new(self.fresh_int("copy_value"), pointee_ty))
        } else {
            VmValue::new(self.fresh_int("copy_value"), pointee_ty)
        };
        copied.facts.init |= source_initialized;
        if scratch_target {
            let alloc_id = target.provenance.as_ref().unwrap().alloc_id;
            self.forget_memory_values(alloc_id);
            if concrete_count == Some(1) && scratch_target_ty == Some(pointee_ty) {
                self.store_value(alloc_id, pointee_ty, Vec::new(), copied);
                self.content_mut(alloc_id).facts.initialized = true;
                self.content_mut(alloc_id).facts.written_pointee_ty = Some(pointee_ty);
            } else {
                self.content_mut(alloc_id).copied_prefix =
                    Some((pointee_ty, count.z3_term.clone()));
            }
            return;
        }
        if let Some(prov) = &target.provenance {
            self.forget_memory_values(prov.alloc_id);
        }
        if concrete_count == Some(1) {
            self.write_through_pointer(target, Vec::new(), copied);
        }
    }

    pub(crate) fn forget_memory_values(&mut self, alloc_id: AllocId) {
        let root = self.root_alloc(alloc_id);
        self.clear_write_evidence(root);
        let aliases: Vec<_> = (0..self.units.len())
            .map(AllocId)
            .filter(|id| self.root_alloc(*id) == root)
            .collect();
        for id in aliases {
            self.alloc_mut(id).facts.for_each = Default::default();
            let content = self.content_mut(id);
            content.values.clear();
            content.indexed_elements.clear();
            content.indexed_elements_modified = true;
            content.copied_prefix = None;
            content.facts.written_pointee_ty = None;
            content.clear_byte_writes();
            content.facts.cstr_trusted = false;
            content.facts.utf8_trusted = false;
            content.facts.split_transmute_to = None;
        }
    }

    pub(crate) fn swap_memory_values(&mut self, left: &VmValue<'z3, 'tcx>, right: &VmValue<'z3, 'tcx>) -> bool {
        if let Some((left_local, right_local)) = self
            .find_local_by_address(&left.z3_term)
            .zip(self.find_local_by_address(&right.z3_term))
        {
            let ty = self.body().local_decls[left_local].ty;
            if left_local != right_local
                && ty == self.body().local_decls[right_local].ty
                && matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                && let Some((left_value, right_value)) = self
                    .local_value(left_local)
                    .cloned()
                    .zip(self.local_value(right_local).cloned())
            {
                self.set_local(left_local, right_value);
                self.set_local(right_local, left_value);
                return true;
            }
        }
        let Some((left_prov, right_prov)) =
            left.provenance.as_ref().zip(right.provenance.as_ref())
        else {
            return false;
        };
        let Some(ty) = mir_utils::pointee_ty(left.ty) else {
            return false;
        };
        if mir_utils::pointee_ty(right.ty) != Some(ty) {
            return false;
        }
        for id in [left_prov.alloc_id, right_prov.alloc_id] {
            let root = self.root_alloc(id);
            let alloc = self.alloc(id);
            if alloc.element_ty.as_ty() != Some(ty)
                && self.alloc(root).element_ty.as_ty() != Some(ty)
            {
                return false;
            }
            if !self.content(id).facts.initialized && !self.content(root).facts.initialized {
                return false;
            }
        }
        self.forget_memory_values(left_prov.alloc_id);
        self.forget_memory_values(right_prov.alloc_id);
        true
    }

    pub(crate) fn clear_write_evidence(&mut self, alloc_id: AllocId) {
        let root = self.root_alloc(alloc_id);
        let aliases: crate::compat::FxHashSet<_> = (0..self.units.len())
            .map(AllocId)
            .filter(|id| self.root_alloc(*id) == root)
            .collect();
        self.typed_values.retain(|(id, _, _)| !aliases.contains(id));
        for id in aliases {
            self.units[id.0].content.copied_prefix = None;
            self.units[id.0].content.facts.written_pointee_ty = None;
        }
    }

    pub(crate) fn write_provenance_allocation(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        if self.write_indexed_allocation(pointer, value.clone()) {
            return true;
        }
        if self.write_field_allocation(pointer, value.clone()) {
            return true;
        }
        self.write_reinterpreted_integer_allocation(pointer, value)
    }

    /// A typed whole-object write through a cast pointer replaces the start of
    /// an integer buffer while keeping its original allocation element type.
    fn write_reinterpreted_integer_allocation(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        let Some(prov) = pointer.provenance.as_ref() else {
            return false;
        };
        if prov.offset.simplify().as_u64() != Some(0)
            || mir_utils::pointee_ty(pointer.ty) != Some(value.ty)
            || !value.facts.init
            || !matches!(self.alloc(prov.alloc_id).kind, AllocKind::Slice { .. } | AllocKind::External | AllocKind::ExternalSlice { .. })
            || !self.alloc(prov.alloc_id).element_ty.as_ty().is_some_and(|ty| {
                ty != value.ty && matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
            })
        {
            return false;
        }
        self.clear_write_evidence(prov.alloc_id);
        let written_ty = value.ty;
        let local_allocation = self.alloc(prov.alloc_id).facts.locally_allocated;
        if local_allocation {
            self.alloc_mut(prov.alloc_id).element_ty = ElementTy::Typed(written_ty);
        }
        let content = self.content_mut(prov.alloc_id);
        content.values.clear();
        content.indexed_elements.clear();
        content.indexed_elements_modified = true;
        content.clear_byte_writes();
        self.store_value(prov.alloc_id, value.ty, Vec::new(), value);
        if local_allocation {
            self.content_mut(prov.alloc_id).facts.written_pointee_ty = Some(written_ty);
        }
        true
    }

    pub(crate) fn invalidate_provenance_allocation(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
    ) {
        let Some(provenance) = pointer.provenance.as_ref() else {
            return;
        };
        let alloc_id = provenance.alloc_id;
        if !self.current_frame.local_alloc.values().any(|id| *id == alloc_id) {
            return;
        }
        self.clear_write_evidence(alloc_id);
        let content = self.content_mut(alloc_id);
        content.copied_prefix = None;
        content.values.clear();
        content.indexed_elements.clear();
        content.indexed_elements_modified = true;
        content.clear_byte_writes();
    }

    fn write_field_allocation(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        let Some(provenance) = pointer.provenance.as_ref() else {
            return false;
        };
        let Some(offset) = provenance.offset.simplify().as_u64() else {
            return false;
        };
        let Some(pointee_ty) = mir_utils::pointee_ty(pointer.ty) else {
            return false;
        };
        if value.ty != pointee_ty {
            return false;
        }
        let local = self.current_frame.local_alloc.iter().find_map(|(local, alloc_id)| {
            (*alloc_id == provenance.alloc_id).then_some(*local)
        });
        let Some(root_ty) = local
            .map(|local| self.body().local_decls[local].ty)
            .or_else(|| self.alloc(provenance.alloc_id).element_ty.as_ty()) else {
            return false;
        };
        let Some(path) = self.field_path_at_offset(root_ty, offset, pointee_ty) else {
            return false;
        };
        self.clear_write_evidence(provenance.alloc_id);
        self.content_mut(provenance.alloc_id).values.retain(|(ty, stored_path), _| {
            *ty == root_ty
                && !stored_path.starts_with(&path)
                && !path.starts_with(stored_path)
        });
        if matches!(pointee_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8)) {
            self.byte_write(provenance.alloc_id, &provenance.offset, &value.z3_term);
        } else {
            let content = self.content_mut(provenance.alloc_id);
            content.clear_byte_writes();
        }
        let aliases = self.current_frame.local_alloc.keys().copied().filter(|local| {
            let local_ty = self.body().local_decls[*local].ty;
            matches!(local_ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..))
                && mir_utils::pointee_ty(local_ty) == Some(root_ty)
                && self.local_value(*local)
                    .and_then(|value| value.provenance_alloc_id()) == Some(provenance.alloc_id)
        }).collect::<Vec<_>>();
        self.store_value(provenance.alloc_id, root_ty, path.clone(), value.clone());
        for local in aliases {
            self.write_local_path(local, path.clone(), value.clone());
        }
        true
    }

    fn field_path_at_offset(
        &self,
        ty: Ty<'tcx>,
        offset: u64,
        target_ty: Ty<'tcx>,
    ) -> Option<Vec<usize>> {
        let fields = match ty.kind() {
            TyKind::Adt(def, args) if !def.is_enum() && !def.is_union() => def
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| mir_utils::field_ty(self.tcx, field, args))
                .collect::<Vec<_>>(),
            TyKind::Tuple(fields) => fields.iter().collect::<Vec<_>>(),
            _ => return None,
        };
        let mut found = None;
        for (index, field_ty) in fields.into_iter().enumerate() {
            let start = self.field_offset_in_bytes(ty, index);
            let size = self.size_of_ty(field_ty);
            if offset < start || offset - start >= size {
                continue;
            }
            let nested = if offset == start && field_ty == target_ty {
                Some(Vec::new())
            } else {
                self.field_path_at_offset(field_ty, offset - start, target_ty)
            };
            if let Some(mut nested) = nested {
                nested.insert(0, index);
                if found.is_some() {
                    return None;
                }
                found = Some(nested);
            }
        }
        found
    }

    fn write_indexed_allocation(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        let Some(provenance) = pointer.provenance.as_ref() else {
            return false;
        };
        if self.alloc(provenance.alloc_id).slice_len().is_none() {
            return false;
        }
        let Some(pointee_ty) = mir_utils::pointee_ty(pointer.ty) else {
            return false;
        };
        let Some(mut element_ty) = self.alloc(provenance.alloc_id).element_ty.as_ty() else {
            return false;
        };
        while let TyKind::Array(inner, _) = element_ty.kind() {
            element_ty = *inner;
        }
        if element_ty != pointee_ty || value.ty != pointee_ty {
            return false;
        }
        let element_size = self.size_of_ty(pointee_ty);
        if element_size == 0 {
            return false;
        }
        let index = match &provenance.offset_kind {
            Some(super::state::OffsetKind::Element { index, stride })
                if stride.simplify() == Int::from_u64(self.z3_ctx, element_size).simplify() =>
            {
                Some(index.clone())
            }
            _ => provenance.offset.simplify().as_u64().and_then(|offset| {
                (offset % element_size == 0)
                    .then(|| Int::from_u64(self.z3_ctx, offset / element_size))
            }),
        };
        self.content_mut(provenance.alloc_id)
            .values
            .retain(|(_, path), _| path.is_empty());
        if element_size == 1
            && matches!(pointee_ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8))
        {
            self.byte_write(provenance.alloc_id, &provenance.offset, &value.z3_term);
        } else if self.content(provenance.alloc_id).byte_array.is_some() {
            if element_size <= 256 {
                for byte in 0..element_size {
                    let offset = Int::add(
                        self.z3_ctx,
                        &[&provenance.offset, &Int::from_u64(self.z3_ctx, byte)],
                    );
                    let unknown = self.fresh_int("written_byte");
                    self.byte_write(provenance.alloc_id, &offset, &unknown);
                }
            } else {
                let content = self.content_mut(provenance.alloc_id);
                content.clear_byte_writes();
            }
        }
        if let Some(index) = index {
            self.store_indexed_element(provenance.alloc_id, index, value);
        } else {
            let content = self.content_mut(provenance.alloc_id);
            content.indexed_elements.clear();
            content.indexed_elements_modified = true;
        }
        true
    }

    pub(crate) fn address_of_place(&mut self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        self.ensure_local_allocation(place.local);

        let zero = Int::from_u64(self.z3_ctx, 0);

        if place.projection.is_empty() {
            let base_addr = self.local_address(place.local);
            let ty = self.body().local_decls[place.local].ty;
            let is_manually_drop = matches!(ty.kind(), TyKind::Adt(def, _)
                if self.tcx.is_lang_item(def.did(), crate::def_ids::lang_api::LangItem::ManuallyDrop));
            let provenance = (!matches!(ty.kind(), TyKind::Array(..)) && !is_manually_drop)
                .then(|| self.local_value(place.local).and_then(|v| v.provenance.clone()))
                .flatten()
                .or_else(|| {
                    self.current_frame.local_alloc
                        .get(&place.local)
                        .copied()
                        .map(|alloc_id| Provenance {
                            alloc_id,
                            offset: zero,
                            offset_kind: None,
                        })
                });
            return Some(VmValue {
                z3_term: base_addr,
                ty,
                provenance,
                facts: ValueFacts::default(),
                source: ValueSource::None,
            });
        }

        let mut term = self.local_address(place.local);
        let mut provenance: Option<Provenance<'z3>> = self
            .current_frame.local_alloc
            .get(&place.local)
            .copied()
            .map(|alloc_id| Provenance {
                alloc_id,
                offset: zero.clone(),
                offset_kind: None,
            });
        let mut current_ty = self.body().local_decls[place.local].ty;
        let mut field_path: Vec<usize> = Vec::new();
        let mut view_ty = current_ty;

        for proj in place.projection.iter() {
            if let ProjectionElem::Index(local) = proj {
                // The element stride is the *element* size, not the container
                // size: peel `[T; N]` / `[T]` down to `T` (mirroring state.rs's
                // `Index` arm).  Keep `max(1)` so the stride matches the array
                // allocation's `elem_size` (`N·max(1)`), letting the SMT cancel
                // the factor for `idx + 1 <= N`.
                let elem_ty = match current_ty.kind() {
                    TyKind::Array(e, _) | TyKind::Slice(e) => *e,
                    _ => return None,
                };
                let elem_sz = Int::from_u64(self.z3_ctx, self.size_of_ty(elem_ty).max(1));
                let idx = self.local_value(local)?.z3_term.clone();
                let scaled = Int::mul(self.z3_ctx, &[&idx, &elem_sz]);
                term = Int::add(self.z3_ctx, &[&term, &scaled]);
                if let Some(ref mut prov) = provenance {
                    prov.offset = Int::add(self.z3_ctx, &[&prov.offset, &scaled]);
                }
                current_ty = elem_ty;
                continue;
            }
            match proj.kind() {
                ProjectionElem::Field(field_idx, _) => {
                    let fidx = field_idx.as_usize();
                    field_path.push(fidx);
                    let field_offset = self.field_offset_in_bytes(current_ty, fidx);
                    let field_off = Int::from_u64(self.z3_ctx, field_offset);
                    let field_ty = match current_ty.kind() {
                        TyKind::Adt(adt_def, substs) => {
                            let variant = adt_def.non_enum_variant();
                            variant
                                .fields
                                .get(rustc_abi::FieldIdx::from_usize(fidx))
                                .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                                .unwrap_or(current_ty)
                        }
                        _ => current_ty,
                    };
                    // A DST slice field (e.g. `CStr { inner: [u8] }`) carries its
                    // own allocation so its length stays symbolic.  Prefer that
                    // allocation over the parent struct's byte-offset address,
                    // otherwise `&raw const self.inner` collapses the slice length
                    // to the struct's own (minimal) size.
                    let field_replacement = match field_ty.kind() {
                        TyKind::Slice(_) => self
                            .field_value(place.local, &field_path)
                            .and_then(|fv| fv.provenance.clone().map(|p| (fv.z3_term.clone(), p))),
                        TyKind::Array(..) => {
                            // An array field decomposed into its own allocation by
                            // `decompose_pointee_fields` (e.g. `keys: [MaybeUninit<K>; N]`)
                            // carries a concrete element count. Prefer that allocation
                            // over the parent struct's byte-offset address so
                            // `&(*leaf).keys` keeps `len = N` for downstream InBound.
                            let alloc = provenance.as_ref().map(|p| p.alloc_id);
                            alloc.and_then(|a| {
                                self.units[a.0].content.values
                                    .get(&(view_ty, field_path.clone()))
                                    .and_then(|fv| {
                                        fv.provenance.clone().map(|p| (fv.z3_term.clone(), p))
                                    })
                            })
                        }
                        _ => None,
                    };
                    match field_replacement {
                        Some((fv_term, fv_prov)) => {
                            term = fv_term;
                            provenance = Some(fv_prov);
                        }
                        None => {
                            term = Int::add(self.z3_ctx, &[&term, &field_off]);
                            if let Some(ref mut prov) = provenance {
                                prov.offset = Int::add(self.z3_ctx, &[&prov.offset, &field_off]);
                            }
                        }
                    }
                    current_ty = field_ty;
                }
                ProjectionElem::Deref => {
                    field_path.clear();
                    let pointed = self.local_value(place.local)?;
                    term = pointed.z3_term.clone();
                    provenance = pointed.provenance.clone();
                    if provenance.is_none() && matches!(pointed.ty.kind(), TyKind::RawPtr(..))
                        && let Some(field0) = self.field_value(place.local, &[0]) {
                            provenance = field0.provenance.clone();
                        }
                    if let TyKind::Ref(_, deref_ty, _) = current_ty.kind() {
                        current_ty = *deref_ty;
                    } else if let TyKind::RawPtr(deref_ty, _) = current_ty.kind() {
                        current_ty = *deref_ty;
                    }
                    view_ty = current_ty;
                }
                _ => {
                    return None;
                }
            }
        }

        let ty = place.ty(self.body(), self.tcx).ty;
        Some(VmValue {
            z3_term: term,
            ty,
            provenance,
            facts: ValueFacts::default(),
            source: ValueSource::None,
        })
    }

    /// Lazily create a stack allocation for a MIR local if one doesn't exist.
    pub(crate) fn ensure_local_allocation(&mut self, local: Local) {
        if self.current_frame.local_alloc.contains_key(&local) {
            return;
        }
        let ty = self.body().local_decls[local].ty;
        let align = self.align_sym(ty);
        let name = format!("addr__{}", local.as_usize());
        let base = Int::new_const(self.z3_ctx, name.as_str());
        let id = AllocId(self.units.len());
        // For arrays, track the element type (not the array type) so that
        // len() computes `size / elem_size` correctly.  When the element size
        // is unknown (a generic `T`), `size_of::<[T; N]>()` collapses to 0, so
        // instead record the element count `N` as a symbolic term — this keeps
        // `len() = size / elem_size` equal to `N`, letting downstream
        // InBound checks (e.g. `get_unchecked_mut(idx)` where `idx < N`) be
        // discharged against the loop's `idx < N` path condition.
        let (size_term, element_ty, slice_len) = match ty.kind() {
            TyKind::Array(elem, const_len) => {
                // Concrete element size (`.max(1)` so a generic `T` collapses to
                // 1 byte, keeping `len() = size / elem_size` equal to the
                // symbolic element count `N`).  Deliberately *not* the symbolic
                // `size_sym(elem)`: materializing `sizeof_MaybeUninit<T>` here
                // would let `access_bytes` read it back as an unbounded access
                // size, breaking `Allocated(&mut MaybeUninit<T>, T, 1)` against
                // the iterator provenance (array_try_from_fn_ext).
                let elem_size = self.size_of_ty(*elem).max(1);
                let n_term = self.const_len_term(const_len);
                let size = match n_term.as_u64() {
                    Some(n) => Int::from_u64(self.z3_ctx, n.saturating_mul(elem_size)),
                    None => Int::mul(self.z3_ctx, &[&n_term, &Int::from_u64(self.z3_ctx, elem_size)]),
                };
                (size, Some(*elem), Some(n_term))
            }
            _ => {
                let size = self
                    .struct_size_sym(ty)
                    .unwrap_or_else(|| self.size_sym(ty));
                (size, Some(ty), None)
            }
        };
        let mut alloc = Allocation::new(base, size_term, align, element_ty, AllocKind::Object);
        if let Some(len) = slice_len {
            alloc.set_slice_len(len);
        }
        self.units.push(MemoryUnit {
            allocation: alloc,
            content: MemoryContent::default(),
        });
        self.current_frame.local_alloc.insert(local, id);
    }

    pub(crate) fn field_offset_in_bytes(&self, ty: Ty<'tcx>, field_idx: usize) -> u64 {
        mir_utils::field_offset_in_bytes(
            self.tcx,
            self.current_frame.current_def_id,
            ty,
            field_idx,
        )
    }

    pub(crate) fn size_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        mir_utils::layout_of_ty(self.tcx, self.current_frame.current_def_id, ty)
            .map(|l| l.size.bytes())
            .unwrap_or(0)
    }

    pub(crate) fn align_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        mir_utils::layout_of_ty(self.tcx, self.current_frame.current_def_id, ty)
            .map(|l| l.align.abi.bytes())
            .unwrap_or(1)
    }

    pub(crate) fn allocation_size(&self, alloc_id: AllocId) -> &Int<'z3> {
        &self.alloc(alloc_id).size
    }

    pub(crate) fn allocation_base(&self, alloc_id: AllocId) -> &Int<'z3> {
        &self.alloc(alloc_id).base
    }

    /// Get the element size (in bytes) for a pointer type, peeling
    /// through `*const T`, `*mut T`, `&T`, and `&[T]` to find `size_of(T)`.
    pub(crate) fn pointee_elem_size(&self, ty: Ty<'tcx>) -> u64 {
        let inner = match ty.kind() {
            TyKind::RawPtr(inner_ty, _) | TyKind::Ref(_, inner_ty, _) => *inner_ty,
            _ => ty,
        };
        match inner.kind() {
            TyKind::Slice(elem) => self.size_of_ty(*elem),
            _ => self.size_of_ty(inner),
        }
    }

    /// Element size of `ty` as a symbolic Z3 term.  For concrete types this is
    /// the constant byte size; for a generic type whose `size_of` is unknown
    /// (an unconstrained `T`) it is a single reusable symbolic constant with
    /// `>= 0` (so `T` may be a ZST).  Using the same constant everywhere (ptr
    /// strides, access counts, allocation sizes) lets SMT cancel the factor in
    /// `InBound`.
    pub(crate) fn size_sym(&mut self, ty: Ty<'tcx>) -> Int<'z3> {
        let ty = peel_slice_elem(ty);
        if let TyKind::Array(elem, count) = ty.kind() {
            let count = self.const_len_term(count);
            let zero = Int::from_u64(self.z3_ctx, 0);
            self.constraints.assertions.push(count.ge(&zero));
            let elem_size = self.size_sym(*elem);
            return Int::mul(self.z3_ctx, &[&count, &elem_size]);
        }
        let size = self.size_of_ty(ty);
        if size > 0 || !mir_utils::ty_has_type_param(ty) {
            return Int::from_u64(self.z3_ctx, size);
        }
        if let Some(s) = self.constraints.term_caches.sizes.get(&ty) {
            return s.clone();
        }
        let s = self.fresh_int(&format!("sizeof_{ty}"));
        self.constraints.term_caches.sizes.insert(ty, s.clone());
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(s.ge(&zero));
        if let TyKind::Adt(def, args) = ty.kind()
            && (def.is_struct() || def.is_union())
        {
            let min_size = def
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| self.size_of_ty(mir_utils::field_ty(self.tcx, field, args)))
                .max()
                .unwrap_or(0);
            if min_size > 0 {
                self.constraints
                    .assertions
                    .push(s.ge(&Int::from_u64(self.z3_ctx, min_size)));
            }
        }
        s
    }

    /// The array length `N` as a Z3 term (concrete value or symbolic const
    /// generic).  The symbolic name mirrors `value_of_operand`'s formatting so it
    /// is *identical* to the `const N` term appearing in path conditions.
    pub(crate) fn const_len_term(&self, const_len: &rustc_middle::ty::Const<'tcx>) -> Int<'z3> {
        match const_len.try_to_target_usize(self.tcx) {
            Some(v) => Int::from_u64(self.z3_ctx, v),
            None => self.symbolic_const_term(&rustc_middle::mir::Const::Ty(
                self.tcx.types.usize,
                *const_len,
            )),
        }
    }

    /// Read-only sibling of [`size_sym`](Self::size_sym): returns the symbolic
    /// size for `ty`, falling back to `1` when the symbolic constant has not
    /// been created yet (e.g. a checker invoked before the exec phase created
    /// it).  Non-ZST concrete types return their constant byte size; a concrete
    /// ZST or a not-yet-created generic constant falls back to `1` — a non-zero
    /// element size keeps `size / elem_size` derivations from dividing by zero.
    pub(crate) fn size_sym_read(&self, ty: Ty<'tcx>) -> Int<'z3> {
        let ty = peel_slice_elem(ty);
        if let TyKind::Array(elem, count) = ty.kind() {
            let count = self.const_len_term(count);
            let elem_size = self.size_sym_read(*elem);
            return Int::mul(self.z3_ctx, &[&count, &elem_size]);
        }
        let size = self.size_of_ty(ty);
        if size > 0 {
            return Int::from_u64(self.z3_ctx, size);
        }
        self.constraints.term_caches.sizes
            .get(&ty)
            .cloned()
            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1))
    }

    /// The *symbolic* element-size term of `alloc_id`'s element type, when it is
    /// a generic type parameter (so it may be `0` for a ZST or `≥ 1` for a
    /// non-ZST).  Returns `None` for concrete element types, where the size is a
    /// known constant and no case split is needed.
    pub(crate) fn generic_elem_size(&self, alloc_id: AllocId) -> Option<Int<'z3>> {
        let elem_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        if !mir_utils::ty_has_type_param(elem_ty) {
            return None;
        }
        let s = self.size_sym_read(elem_ty);
        if s.simplify().as_u64().is_some() {
            return None;
        }
        Some(s)
    }

    /// Alignment of `ty` as a symbolic Z3 term.  For a concrete type this is
    /// the constant byte alignment; for a generic type it is a reusable
    /// symbolic constant `align_T` with `>= 1`, lower-bounded by the trait
    /// bounds' minimum alignment, and linked to the element size by the layout
    /// constraint `sizeof_T % align_T == 0` (a type's size is always a multiple
    /// of its alignment).  For a generic struct, its alignment is additionally
    /// constrained to be a multiple of each field's alignment, so a field
    /// pointer (`(*node).value`) inherits the container's alignment.
    pub(crate) fn align_sym(&mut self, ty: Ty<'tcx>) -> Int<'z3> {
        let ty = peel_slice_elem(ty);
        if let TyKind::Array(elem, _) = ty.kind() {
            return self.align_sym(*elem);
        }
        let align = self.align_of_ty(ty);
        if align > 1 || !mir_utils::ty_has_type_param(ty) {
            return Int::from_u64(self.z3_ctx, align);
        }
        if let Some(a) = self.constraints.term_caches.aligns.get(&ty) {
            return a.clone();
        }
        let a = self.fresh_int(&format!("align_{ty}"));
        self.constraints.term_caches.aligns.insert(ty, a.clone());
        let one = Int::from_u64(self.z3_ctx, 1);
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(a.ge(&one));
        // Lower bound from the trait bounds (0 for an unconstrained `T`): any
        // implementor is at least this aligned.
        let min_a =
            mir_utils::min_align_of_generic_param(self.tcx, self.current_frame.current_def_id, ty);
        if min_a > 1 {
            self.constraints.assertions
                .push(a.ge(&Int::from_u64(self.z3_ctx, min_a)));
        }
        // Upper bound from the trait bounds (0 for an unconstrained `T`): any
        // implementor is at most this aligned, which is what lets a cross-cast
        // from a *more* aligned source (`&[U]` -> `*const T`) be discharged.
        let max_a =
            mir_utils::max_align_of_generic_param(self.tcx, self.current_frame.current_def_id, ty);
        if max_a > 0 {
            self.constraints.assertions
                .push(a.le(&Int::from_u64(self.z3_ctx, max_a)));
        }
        // A struct's alignment is a multiple of each field's alignment (both
        // are powers of two).  Pointer fields have a *concrete* alignment, so
        // this terminates even for recursively-defined containers.
        if let TyKind::Adt(adt_def, substs) = ty.kind()
            && !adt_def.is_enum() {
                let variant = adt_def.non_enum_variant();
                for field in variant.fields.iter() {
                    let field_ty = mir_utils::field_ty(self.tcx, field, substs);
                    let field_align = self.align_sym(field_ty);
                    self.constraints.assertions.push(a.rem(&field_align)._eq(&zero));
                    // Linear lower bound: a struct/union's alignment is at least
                    // each field's alignment (both powers of two), so Z3 can
                    // decide `align_struct >= align_field` without chaining the
                    // nonlinear `% == 0` (e.g. `align_of(MaybeUninit<T>) >=
                    // align_of(T)` for `swap`'s scratch slot).
                    self.constraints.assertions.push(a.ge(&field_align));
                }
                // A struct's size is at least the sum of its fields (padding may
                // add more).  This relates the symbolic `sizeof_Struct` constant
                // to the field-sum that `size_of::<Struct>()` lowers to (e.g.
                // `SIZE<LeafNode> + SIZE<[...; 12]>` for `InternalNode`), so
                // `Allocated(p, u8, layout.size)` is discharged against the
                // allocation size.
                if let Some(sum) = self.struct_size_sym(ty) {
                    let size = self.size_sym(ty);
                    self.constraints.assertions.push(size.ge(&sum));
                }
            }
        let size = self.size_sym(ty);
        self.constraints.assertions.push(size.rem(&a)._eq(&zero));
        a
    }

    /// Read-only sibling of [`align_sym`](Self::align_sym): returns the
    /// symbolic alignment for `ty`, falling back to the trait bounds' minimum
    /// alignment when the constant has not been created yet (e.g. a generic `U`
    /// that only appears in a cast/contract, never as an allocation element
    /// type).  Concrete types return their constant alignment.
    pub(crate) fn align_sym_read(&self, ty: Ty<'tcx>) -> Int<'z3> {
        let ty = peel_slice_elem(ty);
        if let TyKind::Array(elem, _) = ty.kind() {
            return self.align_sym_read(*elem);
        }
        let align = self.align_of_ty(ty);
        if align > 1 {
            return Int::from_u64(self.z3_ctx, align);
        }
        if let Some(a) = self.constraints.term_caches.aligns.get(&ty) {
            return a.clone();
        }
        let min_a =
            mir_utils::min_align_of_generic_param(self.tcx, self.current_frame.current_def_id, ty);
        Int::from_u64(self.z3_ctx, min_a.max(1))
    }

    /// Size of a struct/ADT as the *sum* of its fields' sizes (each via
    /// [`size_sym`](Self::size_sym)).  This lower-bounds the real layout so a
    /// field reference (`Allocated(&alloc)`) can be discharged against the
    /// struct allocation (`sizeof_A <= 8 + 8 + sizeof_A`).  Returns `None` for
    /// non-ADT or enum types.
    pub(crate) fn struct_size_sym(&mut self, ty: Ty<'tcx>) -> Option<Int<'z3>> {
        let TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if adt_def.is_enum() {
            return None;
        }
        let concrete = self.size_of_ty(ty);
        if concrete > 0 {
            return Some(Int::from_u64(self.z3_ctx, concrete));
        }
        let variant = adt_def.non_enum_variant();
        let mut total = Int::from_u64(self.z3_ctx, 0);
        for field in variant.fields.iter() {
            let field_ty = mir_utils::field_ty(self.tcx, field, substs);
            let field_size = self
                .struct_size_sym(field_ty)
                .unwrap_or_else(|| self.size_sym(field_ty));
            total = Int::add(self.z3_ctx, &[&total, &field_size]);
        }
        Some(total)
    }


    /// The shared `UNINIT` sentinel (≥ 256, outside the `u8` range).
    fn uninit_byte(&self) -> Int<'z3> {
        self.constraints
            .term_caches
            .uninit_byte
            .clone()
            .expect("uninit_byte is initialized in VmState::new")
    }

    /// A fresh `Array<Int, Int>` whose every offset reads `UNINIT`.
    fn fresh_byte_array(&self) -> Array<'z3> {
        // `const_array(domain, value)` takes the *index* sort; the array sort is
        // inferred as `Array<domain, value_sort>` (here `Array<Int, Int>`).
        Array::const_array(self.z3_ctx, &Sort::int(self.z3_ctx), &self.uninit_byte())
    }

    /// Read `byte[i]` at a (possibly symbolic) offset; unwritten offsets read `UNINIT`.
    ///
    /// The result is simplified so a `select(store(…), i)` chain (built up by
    /// repeated `byte_write` / `copy_byte_tracking`) collapses to its constant
    /// byte value when `i` is concrete, rather than leaking the nested
    /// `select`/`store` expression into downstream SMT obligations.
    pub(crate) fn byte_read(&self, alloc_id: AllocId, i: &Int<'z3>) -> Int<'z3> {
        match &self.units[alloc_id.0].content.byte_array {
            Some(arr) => arr.select(i).as_int().expect("byte array range is Int").simplify(),
            None => self.uninit_byte(),
        }
    }

    /// Write `byte[i] = v`.
    pub(crate) fn byte_write(&mut self, alloc_id: AllocId, i: &Int<'z3>, v: &Int<'z3>) {
        self.clear_write_evidence(alloc_id);
        let offset = i.simplify();
        let arr = self.units[alloc_id.0].content.byte_array.clone();
        let updated = match arr {
            Some(a) => a.store(&offset, v),
            None => self.fresh_byte_array().store(&offset, v),
        };
        let unit = &mut self.units[alloc_id.0];
        unit.content.byte_array = Some(updated);
        if let Some(off) = offset.as_u64() {
            unit.content.byte_written.insert(off as usize);
        }
    }

    /// Record a per-byte symbolic value at a concrete offset in an allocation.
    pub(crate) fn record_byte_value(&mut self, alloc_id: AllocId, offset: usize, term: Int<'z3>) {
        self.byte_write(alloc_id, &Int::from_u64(self.z3_ctx, offset as u64), &term);
    }

    /// Mark a byte as initialized (written) with an unknown value.
    pub(crate) fn mark_byte_init(&mut self, alloc_id: AllocId, offset: usize) {
        let unknown = self.fresh_int("byte_unknown");
        self.byte_write(alloc_id, &Int::from_u64(self.z3_ctx, offset as u64), &unknown);
    }

    /// Whether a byte at a concrete offset was written (`select != UNINIT`).
    pub(crate) fn is_byte_init(&self, alloc_id: AllocId, offset: usize) -> bool {
        let v = self.byte_read(alloc_id, &Int::from_u64(self.z3_ctx, offset as u64));
        !v.simplify().eq(&self.uninit_byte())
    }

    /// Whether a byte at a concrete offset is known NUL.
    pub(crate) fn is_byte_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.byte_read(alloc_id, &Int::from_u64(self.z3_ctx, offset as u64))
            .simplify()
            .as_u64()
            == Some(0)
    }

    /// Whether a byte at a concrete offset is known non-NUL.
    pub(crate) fn is_byte_non_nul(&self, alloc_id: AllocId, offset: usize) -> bool {
        self.byte_read(alloc_id, &Int::from_u64(self.z3_ctx, offset as u64))
            .simplify()
            .as_u64()
            .is_some_and(|v| v != 0)
    }

    /// Enumerate `(offset, term)` pairs for the *written* bytes of an allocation,
    /// in ascending offset order.
    pub(crate) fn alloc_byte_values(&self, alloc_id: AllocId) -> Vec<(usize, Int<'z3>)> {
        let mut offs: Vec<usize> = self.units[alloc_id.0]
            .content
            .byte_written
            .iter()
            .copied()
            .collect();
        offs.sort_unstable();
        offs.into_iter()
            .map(|off| (off, self.byte_read(alloc_id, &Int::from_u64(self.z3_ctx, off as u64))))
            .collect()
    }

    /// Offsets known to be NUL.
    pub(crate) fn alloc_nul_offsets(&self, alloc_id: AllocId) -> Vec<usize> {
        let mut offs: Vec<usize> = self.units[alloc_id.0]
            .content
            .byte_written
            .iter()
            .copied()
            .filter(|&off| self.is_byte_nul(alloc_id, off))
            .collect();
        offs.sort_unstable();
        offs
    }

    /// Offsets known to be non-NUL.
    pub(crate) fn alloc_non_nul_offsets(&self, alloc_id: AllocId) -> Vec<usize> {
        let mut offs: Vec<usize> = self.units[alloc_id.0]
            .content
            .byte_written
            .iter()
            .copied()
            .filter(|&off| self.is_byte_non_nul(alloc_id, off))
            .collect();
        offs.sort_unstable();
        offs
    }

    /// Copy the per-byte state (values + written-offset bound) of one allocation
    /// to another, shifting by `src_offset` so `dst[i] = src[i + src_offset]`.
    pub(crate) fn copy_byte_tracking(&mut self, src: AllocId, src_offset: usize, dst: AllocId) {
        let written: Vec<usize> = self.units[src.0]
            .content
            .byte_written
            .iter()
            .copied()
            .filter(|&off| off >= src_offset)
            .collect();
        for off in written {
            let v = self.byte_read(src, &Int::from_u64(self.z3_ctx, off as u64));
            self.byte_write(dst, &Int::from_u64(self.z3_ctx, (off - src_offset) as u64), &v);
        }
    }


    /// The value at a field offset *within an allocation* viewed as `view_ty`.
    ///
    /// This is the memory-contents (typed-value) layer ([`MemoryContent::values`]): the
    /// single source of truth for field values. [`Self::field_value`] is the
    /// local-facing wrapper that resolves a MIR local's backing allocation and
    /// declared type, then reads this same layer. The viewed type is part of the
    /// key so reinterpret casts (`LeafNode` ↔ `InternalNode`) resolve to the
    /// right field view.
    pub(crate) fn load_value(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        path: &[usize],
    ) -> Option<&VmValue<'z3, 'tcx>> {
        self.units[alloc_id.0]
            .content
            .values
            .get(&(view_ty, path.to_vec()))
    }

    /// Store a value at a field offset *within an allocation* viewed as `view_ty`.
    ///
    /// This is the write counterpart to [`Self::load_value`] on the same
    /// memory-contents layer ([`MemoryContent::values`]); the viewed type is part of the
    /// key so reinterpret casts resolve to the right field view.
    pub(crate) fn store_value(
        &mut self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) {
        self.units[alloc_id.0]
            .content
            .values
            .insert((view_ty, path), value);
    }

    /// Encode the UTF-8 validity DFA over this allocation's tracked bytes.
    /// Returns `None` when no bytes are tracked (validity is trivially
    /// satisfied), so callers can short-circuit to "proved".
    pub(crate) fn utf8_validity(&self, alloc_id: AllocId) -> Option<Bool<'z3>> {
        let byte_pairs = self.alloc_byte_values(alloc_id);
        if byte_pairs.is_empty() {
            return None;
        }
        let bytes: Vec<Int<'z3>> = byte_pairs.into_iter().map(|(_, t)| t).collect();
        Some(utf8_validity_dfa(self.z3_ctx, &bytes))
    }
}

/// Build the boolean expression "`bytes` form a valid UTF-8 sequence".
///
/// Encodes the UTF-8 DFA over the per-byte Z3 terms: every byte is ASCII, a
/// continuation byte, or a valid lead byte, and a `k`-byte lead must be
/// followed by exactly `k-1` continuation bytes.  Value-range refinements
/// reject overlong encodings, surrogates (U+D800..=U+DFFF), and code points
/// above U+10FFFF.
fn utf8_validity_dfa<'z3>(z3_ctx: &'z3 Context, bytes: &[Int<'z3>]) -> Bool<'z3> {
    let zero = Int::from_u64(z3_ctx, 0);
    let one = Int::from_u64(z3_ctx, 1);
    let two = Int::from_u64(z3_ctx, 2);
    let three = Int::from_u64(z3_ctx, 3);

    let c_0x80 = Int::from_u64(z3_ctx, 0x80);
    let c_0xc0 = Int::from_u64(z3_ctx, 0xC0);
    let c_0xc2 = Int::from_u64(z3_ctx, 0xC2);
    let c_0xe0 = Int::from_u64(z3_ctx, 0xE0);
    let c_0xf0 = Int::from_u64(z3_ctx, 0xF0);
    let c_0xf5 = Int::from_u64(z3_ctx, 0xF5);
    let c_0xa0 = Int::from_u64(z3_ctx, 0xA0);
    let c_0x90 = Int::from_u64(z3_ctx, 0x90);
    let c_0xed = Int::from_u64(z3_ctx, 0xED);
    let c_0xf4 = Int::from_u64(z3_ctx, 0xF4);

    let mut valid = Bool::from_bool(z3_ctx, true);
    let mut state = zero.clone();
    let mut lead = zero.clone();

    for b in bytes {
        let is_ascii = b.lt(&c_0x80);
        let is_cont = b.ge(&c_0x80) & b.lt(&c_0xc0);
        let is_2lead = b.ge(&c_0xc2) & b.lt(&c_0xe0);
        let is_3lead = b.ge(&c_0xe0) & b.lt(&c_0xf0);
        let is_4lead = b.ge(&c_0xf0) & b.lt(&c_0xf5);

        let refine_3 =
            (lead._eq(&c_0xe0).not() | b.ge(&c_0xa0)) & (lead._eq(&c_0xed).not() | b.lt(&c_0xa0));
        let refine_4 =
            (lead._eq(&c_0xf0).not() | b.ge(&c_0x90)) & (lead._eq(&c_0xf4).not() | b.lt(&c_0x90));

        let valid_s0 = is_ascii.clone() | is_2lead.clone() | is_3lead.clone() | is_4lead.clone();
        let valid_s1 = is_cont.clone();
        let valid_s2 = is_cont.clone() & refine_3;
        let valid_s3 = is_cont.clone() & refine_4;

        let state0 = state._eq(&zero);
        let state1 = state._eq(&one);
        let state2 = state._eq(&two);

        let byte_valid = Bool::ite(
            &state0,
            &valid_s0,
            &Bool::ite(
                &state1,
                &valid_s1,
                &Bool::ite(&state2, &valid_s2, &valid_s3),
            ),
        );

        let new_state_s0 = Bool::ite(
            &is_ascii,
            &zero,
            &Bool::ite(&is_2lead, &one, &Bool::ite(&is_3lead, &two, &three)),
        );
        let new_state_cont = Bool::ite(&state1, &zero, &Bool::ite(&state2, &one, &two));
        let new_state = Bool::ite(&state0, &new_state_s0, &new_state_cont);

        valid &= byte_valid;
        let is_lead34 = is_3lead | is_4lead;
        lead = Bool::ite(&(state0 & is_lead34), b, &lead);
        state = new_state;
    }

    valid &= state._eq(&zero);
    valid
}

/// Peel a slice type `[T]` to its element `T` (other types unchanged).
fn peel_slice_elem(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::Slice(elem) => *elem,
        _ => ty,
    }
}
