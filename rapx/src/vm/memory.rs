//! Symbolic memory model for the VM.

use crate::def_ids::type_ids;
use crate::util::mir_utils;
use rustc_abi::VariantIdx;
use rustc_middle::{
    mir::{Local, Operand, Place, ProjectionElem},
    ty::{Ty, TyKind, TypingEnv},
};
use z3::{Context, Sort, ast::{Array, Ast, Bool, Int}};

use super::state::{AllocId, AllocKind, Allocation, AllocBoundFact, ElementTy, MemoryContent, MemoryUnit, Provenance, ValueFacts, ValueSource, VmExecutor, VmValue, ARRAY_INDEX_MAX};
use super::integer;

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// The key of a bounded span. Unsized slices and strings also need their length.
    pub(crate) fn bounded_span(&self, value: &VmValue<'z3, 'tcx>, ty: Ty<'tcx>) -> Option<AllocBoundFact<'z3, 'tcx>> {
        let len = if matches!(ty.kind(), TyKind::Slice(_) | TyKind::Str) {
            Some(self.slice_len_from_value(value)?)
        } else {
            None
        };
        Some(AllocBoundFact::Object { address: value.z3_term.clone(), ty, len })
    }

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
            self.record_unsupported_effect("CopyMemory pointee type unavailable");
            return;
        };
        let local_target = self
            .find_local_by_address(&target.z3_term)
            .is_some_and(|local| self.body().local_decls[local].ty == pointee_ty);
        let inline_target = self.path_state
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
            self.alloc(prov.alloc_id).slice_len().is_some()
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
                    if type_ids::is_maybe_uninit_type(def.did())
                        && prov.offset.simplify().as_u64() == Some(0) => {
                    args.first().and_then(|arg| arg.as_type())
                }
                _ => None,
            }
        });
        let scratch_target = scratch_target_ty.is_some();
        if !local_target && !inline_target && !allocated_target && !scratch_target {
            self.record_unsupported_effect("CopyMemory target unavailable");
            return;
        }
        if concrete_count != Some(1) && target.provenance.is_none() {
            self.record_unsupported_effect("CopyMemory symbolic count without target provenance");
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
                        if type_ids::is_maybe_uninit_type(def.did()))
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
            self.record_unsupported_effect("CopyMemory source initialization unavailable");
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
        let aliases: Vec<_> = (0..self.path_state.mem_units.len())
            .map(AllocId)
            .filter(|id| self.root_alloc(*id) == root)
            .collect();
        for id in aliases {
            let content = self.content_mut(id);
            content.element_facts = Default::default();
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
        let aliases: crate::compat::FxHashSet<_> = (0..self.path_state.mem_units.len())
            .map(AllocId)
            .filter(|id| self.root_alloc(*id) == root)
            .collect();
        for id in aliases {
            self.path_state.mem_units[id.0].content.typed_facts.clear();
            self.path_state.mem_units[id.0].content.copied_prefix = None;
            self.path_state.mem_units[id.0].content.facts.written_pointee_ty = None;
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
            || !(self.alloc(prov.alloc_id).slice_len().is_some() || self.alloc(prov.alloc_id).is_raw_storage())
            || !self.alloc(prov.alloc_id).element_ty.as_ty().is_some_and(|ty| {
                ty != value.ty && matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
            })
        {
            return false;
        }
        self.clear_write_evidence(prov.alloc_id);
        let written_ty = value.ty;
        let local_allocation = self.alloc(prov.alloc_id).is_allocator();
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
        if !self.path_state.current_frame.local_alloc.values().any(|id| *id == alloc_id) {
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
        let local = self.path_state.current_frame.local_alloc.iter().find_map(|(local, alloc_id)| {
            (*alloc_id == provenance.alloc_id).then_some(*local)
        });
        let Some(root_ty) = local
            .map(|local| self.body().local_decls[local].ty)
            .or_else(|| self.alloc(provenance.alloc_id).element_ty.as_ty()) else {
            return false;
        };
        let Some(path) = self.field_path_at_offset(root_ty, offset, pointee_ty, false) else {
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
        let aliases = self.path_state.current_frame.local_alloc.keys().copied().filter(|local| {
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

    pub(crate) fn read_field_allocation(
        &self,
        pointer: &VmValue<'z3, 'tcx>,
        pointee_ty: Ty<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let provenance = pointer.provenance.as_ref()?;
        let offset = provenance.offset.simplify().as_u64()?;
        let root_ty = self.path_state
            .current_frame
            .local_alloc
            .iter()
            .find_map(|(local, id)| {
                (*id == provenance.alloc_id).then(|| self.body().local_decls[*local].ty)
            })
            .or_else(|| self.alloc(provenance.alloc_id).element_ty.as_ty())?;
        let path = if offset == 0 && root_ty == pointee_ty {
            Vec::new()
        } else {
            self.field_path_at_offset(root_ty, offset, pointee_ty, true)?
        };
        self.load_value(provenance.alloc_id, root_ty, &path)
            .filter(|value| value.ty == pointee_ty)
            .cloned()
            .or_else(|| {
                (0..path.len()).rev().find_map(|prefix_len| {
                    let stored = self.load_value(provenance.alloc_id, root_ty, &path[..prefix_len])?;
                    let mut ty = stored.ty;
                    for &field_index in &path[prefix_len..] {
                        let TyKind::Adt(adt, args) = ty.kind() else {
                            return None;
                        };
                        if !adt.repr().transparent() {
                            return None;
                        }
                        let field = adt
                            .non_enum_variant()
                            .fields
                            .get(rustc_abi::FieldIdx::from_usize(field_index))?;
                        let field_ty = mir_utils::field_ty(self.tcx, field, args);
                        if self.field_offset_in_bytes(ty, field_index) != 0
                            || self.size_of_ty(ty) != self.size_of_ty(field_ty)
                        {
                            return None;
                        }
                        ty = field_ty;
                    }
                    (ty == pointee_ty).then(|| {
                        let mut value = stored.clone();
                        value.ty = pointee_ty;
                        value
                    })
                })
            })
    }

    /// Copy materialized fields when a pointer reads one element of an array allocation.
    pub(crate) fn array_element_fields_at_pointer(
        &self,
        pointer: &VmValue<'z3, 'tcx>,
        element_ty: Ty<'tcx>,
    ) -> Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> {
        let Some(provenance) = &pointer.provenance else { return Vec::new() };
        let size = self.size_of_ty(element_ty);
        let Some(index) = provenance.offset.simplify().as_u64()
            .filter(|offset| size != 0 && offset % size == 0)
            .and_then(|offset| usize::try_from(offset / size).ok())
        else { return Vec::new() };
        let content = self.content(provenance.alloc_id);
        if content.indexed_elements_modified { return Vec::new(); }
        let values = &content.values;
        let mut view_ty = None;
        for (ty, _) in values.keys() {
            if let TyKind::Array(elem, len) = ty.kind()
                && *elem == element_ty
                && len.try_to_target_usize(self.tcx).is_some_and(|len| u64::try_from(index).is_ok_and(|index| index < len))
            {
                if view_ty.is_some_and(|seen| seen != *ty) { return Vec::new(); }
                view_ty = Some(*ty);
            }
        }
        let Some(view_ty) = view_ty else { return Vec::new() };
        values.iter().filter_map(|((ty, path), value)| {
            (*ty == view_ty && path.first() == Some(&index) && path.len() > 1)
                .then(|| (path[1..].to_vec(), value.clone()))
        }).collect()
    }

    fn field_path_at_offset(
        &self,
        ty: Ty<'tcx>,
        offset: u64,
        target_ty: Ty<'tcx>,
        allow_maybe_uninit_inner: bool,
    ) -> Option<Vec<usize>> {
        // Resolve a concrete array element before looking for ADT or tuple fields.
        if let TyKind::Array(element, length) = ty.kind() {
            let size = self.size_of_ty(*element);
            let index = offset.checked_div(size)?;
            if index >= length.try_to_target_usize(self.tcx)? { return None; }
            let remainder = offset % size;
            // Only reads may reuse a materialized T value at a MaybeUninit<T>
            // element slot; writes still need byte-level initialization tracking.
            let stored_inner = allow_maybe_uninit_inner && matches!(element.kind(), TyKind::Adt(adt, args)
                if type_ids::is_maybe_uninit_type(adt.did()) && args.type_at(0) == target_ty);
            let mut path = if remainder == 0 && (*element == target_ty || stored_inner) {
                Vec::new()
            } else {
                self.field_path_at_offset(*element, remainder, target_ty, allow_maybe_uninit_inner)?
            };
            path.insert(0, index as usize);
            return Some(path);
        }
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
                self.field_path_at_offset(field_ty, offset - start, target_ty, allow_maybe_uninit_inner)
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

    /// Find the array view and element index for a pointer into a known array.
    fn concrete_array_view(&self, pointer: &VmValue<'z3, 'tcx>) -> Option<(AllocId, Ty<'tcx>, usize)> {
        let provenance = pointer.provenance.as_ref()?;
        let pointee_ty = mir_utils::pointee_ty(pointer.ty)?;
        let size = self.size_of_ty(pointee_ty);
        let offset = provenance.offset.simplify().as_u64()?;
        if size == 0 || offset % size != 0 { return None; }
        let index = offset / size;
        if index >= self.alloc(provenance.alloc_id).slice_len()?.simplify().as_u64()? { return None; }
        let view_ty = self.content(provenance.alloc_id).values.keys().find_map(|(ty, path)| {
            (path.is_empty() && matches!(ty.kind(), TyKind::Array(inner, _) if *inner == pointee_ty)).then_some(*ty)
        })?;
        Some((provenance.alloc_id, view_ty, index as usize))
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
        let array_view = self.concrete_array_view(pointer).map(|(_, ty, index)| (ty, index));
        // A concrete element write invalidates that element and any repeated initializer.
        self.content_mut(provenance.alloc_id).values.retain(|(ty, path), _| {
            path.is_empty() || array_view.is_some_and(|(view_ty, index)| {
                *ty == view_ty && path.first() != Some(&index) && path.first() != Some(&ARRAY_INDEX_MAX)
            })
        });
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
            self.store_indexed_element(provenance.alloc_id, index, value.clone());
            if let Some((view_ty, index)) = array_view {
                self.store_value(provenance.alloc_id, view_ty, vec![index], value);
            }
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
                    self.path_state.current_frame.local_alloc
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
        let mut provenance: Option<Provenance<'z3>> = self.path_state
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
            // `slice::first` uses a ConstantIndex projection to form its result reference.
            if let ProjectionElem::ConstantIndex { offset, from_end, .. } = proj {
                let (elem_ty, len) = match current_ty.kind() {
                    TyKind::Array(elem, len) => (*elem, self.const_len_term(len)),
                    TyKind::Slice(elem) => (*elem, self.len_from_value(self.local_value(place.local)?)?),
                    _ => return None,
                };
                let index = Int::from_u64(self.z3_ctx, offset);
                let index = if from_end { Int::sub(self.z3_ctx, &[&len, &index]) } else { index };
                let stride = Int::from_u64(self.z3_ctx, self.size_of_ty(elem_ty).max(1));
                let scaled = Int::mul(self.z3_ctx, &[&index, &stride]);
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
                                self.path_state.mem_units[a.0].content.values
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
        if self.path_state.current_frame.local_alloc.contains_key(&local) {
            return;
        }
        let ty = self.body().local_decls[local].ty;
        let align = self.align_sym(ty);
        let name = format!("addr__{}", local.as_usize());
        let base = Int::new_const(self.z3_ctx, name.as_str());
        let id = AllocId(self.path_state.mem_units.len());
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
        self.path_state.mem_units.push(MemoryUnit {
            allocation: alloc,
            content: MemoryContent::default(),
        });
        self.path_state.current_frame.local_alloc.insert(local, id);
    }

    pub(crate) fn field_offset_in_bytes(&self, ty: Ty<'tcx>, field_idx: usize) -> u64 {
        mir_utils::field_offset_in_bytes(
            self.tcx,
            self.path_state.current_frame.current_def_id,
            ty,
            field_idx,
        )
    }

    pub(crate) fn size_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        mir_utils::layout_of_ty(self.tcx, self.path_state.current_frame.current_def_id, ty)
            .map(|l| l.size.bytes())
            .unwrap_or(0)
    }

    pub(crate) fn align_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        mir_utils::layout_of_ty(self.tcx, self.path_state.current_frame.current_def_id, ty)
            .map(|l| mir_utils::layout_align_bytes(&l))
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
            self.path_state.constraints.assertions.push(count.ge(&zero));
            let elem_size = self.size_sym(*elem);
            return Int::mul(self.z3_ctx, &[&count, &elem_size]);
        }
        let size = self.size_of_ty(ty);
        if size > 0 || !mir_utils::ty_has_type_param(ty) {
            return Int::from_u64(self.z3_ctx, size);
        }
        if let Some(s) = self.path_state.constraints.term_caches.sizes.get(&ty) {
            return s.clone();
        }
        let s = self.fresh_int(&format!("sizeof_{ty}"));
        self.path_state.constraints.term_caches.sizes.insert(ty, s.clone());
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.path_state.constraints.assertions.push(s.ge(&zero));
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
                self.path_state.constraints
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
        self.path_state.constraints.term_caches.sizes
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
        if let Some(a) = self.path_state.constraints.term_caches.aligns.get(&ty) {
            return a.clone();
        }
        let a = self.fresh_int(&format!("align_{ty}"));
        self.path_state.constraints.term_caches.aligns.insert(ty, a.clone());
        let one = Int::from_u64(self.z3_ctx, 1);
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.path_state.constraints.assertions.push(a.ge(&one));
        // Lower bound from the trait bounds (0 for an unconstrained `T`): any
        // implementor is at least this aligned.
        let min_a =
            mir_utils::min_align_of_generic_param(self.tcx, self.path_state.current_frame.current_def_id, ty);
        if min_a > 1 {
            self.path_state.constraints.assertions
                .push(a.ge(&Int::from_u64(self.z3_ctx, min_a)));
        }
        // Upper bound from the trait bounds (0 for an unconstrained `T`): any
        // implementor is at most this aligned, which is what lets a cross-cast
        // from a *more* aligned source (`&[U]` -> `*const T`) be discharged.
        let max_a =
            mir_utils::max_align_of_generic_param(self.tcx, self.path_state.current_frame.current_def_id, ty);
        if max_a > 0 {
            self.path_state.constraints.assertions
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
                    self.path_state.constraints.assertions.push(a.rem(&field_align)._eq(&zero));
                    // Linear lower bound: a struct/union's alignment is at least
                    // each field's alignment (both powers of two), so Z3 can
                    // decide `align_struct >= align_field` without chaining the
                    // nonlinear `% == 0` (e.g. `align_of(MaybeUninit<T>) >=
                    // align_of(T)` for `swap`'s scratch slot).
                    self.path_state.constraints.assertions.push(a.ge(&field_align));
                }
                // A struct's size is at least the sum of its fields (padding may
                // add more).  This relates the symbolic `sizeof_Struct` constant
                // to the field-sum that `size_of::<Struct>()` lowers to (e.g.
                // `SIZE<LeafNode> + SIZE<[...; 12]>` for `InternalNode`), so
                // `Allocated(p, u8, layout.size)` is discharged against the
                // allocation size.
                if let Some(sum) = self.struct_size_sym(ty) {
                    let size = self.size_sym(ty);
                    self.path_state.constraints.assertions.push(size.ge(&sum));
                }
            }
        let size = self.size_sym(ty);
        self.path_state.constraints.assertions.push(size.rem(&a)._eq(&zero));
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
        if let Some(a) = self.path_state.constraints.term_caches.aligns.get(&ty) {
            return a.clone();
        }
        let min_a =
            mir_utils::min_align_of_generic_param(self.tcx, self.path_state.current_frame.current_def_id, ty);
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
        self.path_state.constraints
            .term_caches
            .uninit_byte
            .clone()
            .expect("uninit_byte is initialized in VmExecutor::new")
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
        match &self.path_state.mem_units[alloc_id.0].content.byte_array {
            Some(arr) => arr.select(i).as_int().expect("byte array range is Int").simplify(),
            None => self.uninit_byte(),
        }
    }

    pub(crate) fn fill_byte_array(&mut self, pointer: &VmValue<'z3, 'tcx>, byte: u64) -> bool {
        let Some(ty) = mir_utils::pointee_ty(pointer.ty) else {
            return false;
        };
        let TyKind::Array(element, _) = ty.kind() else {
            return false;
        };
        if !matches!(element.kind(), TyKind::Uint(rustc_middle::ty::UintTy::U8)) {
            return false;
        }
        let size = self.size_of_ty(ty) as usize;
        if size == 0 {
            return true;
        }
        if size > 256 {
            return false;
        }
        let Some(provenance) = pointer.provenance.as_ref() else {
            return false;
        };
        let Some(offset) = provenance.offset.simplify().as_u64() else {
            return false;
        };
        let Some(end) = offset.checked_add(size as u64) else {
            return false;
        };
        if !self
            .allocation_size(provenance.alloc_id)
            .simplify()
            .as_u64()
            .is_some_and(|allocation_size| end <= allocation_size)
        {
            return false;
        }
        let alloc_id = provenance.alloc_id;
        let local_path = self.path_state.current_frame.local_alloc.iter().find_map(|(local, id)| {
            if *id != alloc_id {
                return None;
            }
            let root_ty = self.body().local_decls[*local].ty;
            let path = if root_ty == ty && offset == 0 {
                Some(Vec::new())
            } else {
                self.field_path_at_offset(root_ty, offset, ty, false)
            }?;
            Some((*local, path))
        });
        let content = self.content_mut(alloc_id);
        content.values.clear();
        content.indexed_elements.clear();
        content.indexed_elements_modified = true;
        content.copied_prefix = None;
        let value = Int::from_u64(self.z3_ctx, byte);
        for index in offset..end {
            self.record_byte_value(alloc_id, index as usize, value.clone());
        }
        if let Some((local, path)) = local_path {
            for index in 0..size {
                let mut element_path = path.clone();
                element_path.push(index);
                let mut element_value = VmValue::new(value.clone(), *element);
                element_value.facts.init = true;
                self.write_local_path(local, element_path, element_value);
            }
            if path.is_empty() {
                self.content_mut(alloc_id).indexed_elements_modified = false;
            }
        }
        if offset == 0 && end == self.allocation_size(alloc_id).simplify().as_u64().unwrap_or(0) {
            self.content_mut(alloc_id).facts.initialized = true;
        }
        true
    }

    /// Write `byte[i] = v`.
    pub(crate) fn byte_write(&mut self, alloc_id: AllocId, i: &Int<'z3>, v: &Int<'z3>) {
        self.clear_write_evidence(alloc_id);
        let offset = i.simplify();
        let arr = self.path_state.mem_units[alloc_id.0].content.byte_array.clone();
        let updated = match arr {
            Some(a) => a.store(&offset, v),
            None => self.fresh_byte_array().store(&offset, v),
        };
        let unit = &mut self.path_state.mem_units[alloc_id.0];
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
        let mut offs: Vec<usize> = self.path_state.mem_units[alloc_id.0]
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
        let mut offs: Vec<usize> = self.path_state.mem_units[alloc_id.0]
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
        let mut offs: Vec<usize> = self.path_state.mem_units[alloc_id.0]
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
        let written: Vec<usize> = self.path_state.mem_units[src.0]
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
        self.path_state.mem_units[alloc_id.0]
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
        self.path_state.mem_units[alloc_id.0].content.values.insert((view_ty, path), value);
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

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// Find the local whose symbolic address matches `term` (the address a
    /// reference value points at). Used to resolve a `&self`/`&mut self`
    /// receiver (often a reborrow temp) back to the referent local that carries
    /// the materialized field values.
    pub(crate) fn find_local_by_address(&self, term: &Int<'z3>) -> Option<Local> {
        for (local, id) in &self.path_state.current_frame.local_alloc {
            if self.path_state.mem_units[id.0].allocation.base == *term {
                return Some(*local);
            }
        }
        None
    }

    pub(crate) fn write_through_pointer(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        let full_inner_write = pointer.provenance.as_ref().and_then(|prov| {
            let ty = self.alloc(prov.alloc_id).element_ty.as_ty()?;
            match ty.kind() {
                TyKind::Adt(def, args)
                    if type_ids::is_maybe_uninit_type(def.did())
                        && path.is_empty()
                        && prov.offset.simplify().as_u64() == Some(0)
                        && value.facts.init =>
                {
                    args.first()
                        .and_then(|arg| arg.as_type())
                        .filter(|inner| *inner == value.ty)
                        .map(|inner| (prov.alloc_id, inner))
                }
                _ => None,
            }
        });
        if let Some(prov) = &pointer.provenance {
            self.clear_write_evidence(prov.alloc_id);
            if !path.is_empty()
                && path.iter().all(|field| *field == 0)
                && value.facts.init
                && matches!(mir_utils::pointee_ty(pointer.ty).map(|ty| ty.kind()),
                    Some(TyKind::Adt(def, args))
                        if type_ids::is_maybe_uninit_type(def.did())
                            && args.first().and_then(|arg| arg.as_type()) == Some(value.ty))
                && let Some(offset) = prov.offset.simplify().as_u64()
            {
                let end = offset.saturating_add(self.size_of_ty(value.ty)).min(4096);
                for byte in offset..end {
                    self.mark_byte_init(prov.alloc_id, byte as usize);
                }
            }
        }
        if path.is_empty()
            && let Some(prov) = &pointer.provenance
            && self.path_state
                .static_allocs
                .values()
                .any(|id| *id == prov.alloc_id)
            && prov.offset.simplify().as_u64() == Some(0)
            && self.alloc(prov.alloc_id).element_ty.as_ty() == Some(value.ty)
        {
            self.clear_write_evidence(prov.alloc_id);
            self.store_value(prov.alloc_id, value.ty, Vec::new(), value);
            self.content_mut(prov.alloc_id).facts.initialized = true;
            return true;
        }
        let caller_referent =
            self.path_state.inline
                .arg_referents
                .iter()
                .enumerate()
                .find_map(|(i, referent)| {
                    let param = Local::from_usize(i + 1);
                    self.local_value(param)
                        .filter(|arg| arg.z3_term == pointer.z3_term)
                        .and_then(|_| *referent)
                });
        if let Some(local) = caller_referent {
            let path = match &pointer.source {
                super::state::ValueSource::FieldBorrow { fields, .. } => {
                    let mut full = fields.clone();
                    full.extend(path);
                    full
                }
                _ => path,
            };
            let wrote_object = path.is_empty()
                && pointer.provenance.as_ref().is_some_and(|prov| {
                    self.alloc(prov.alloc_id).is_raw_storage()
                        && self.alloc(prov.alloc_id).element_ty.as_ty() != Some(value.ty)
                })
                && self.write_provenance_allocation(pointer, value.clone());
            self.path_state.inline.deferred_field_writes.push((local, path, value));
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
            }
            return wrote_object;
        }
        if path.is_empty()
            && let Some(prov) = &pointer.provenance
            && prov.offset.simplify().as_u64() == Some(0)
            && self.alloc(prov.alloc_id).element_ty.as_ty() == Some(value.ty)
            && matches!(
                self.alloc(prov.alloc_id).kind,
                super::state::AllocKind::Object
            )
            && self.find_local_by_address(&pointer.z3_term).is_none()
        {
            self.clear_write_evidence(prov.alloc_id);
            let content = self.content_mut(prov.alloc_id);
            content.values.clear();
            content.indexed_elements.clear();
            content.indexed_elements_modified = true;
            content.clear_byte_writes();
            content.facts.initialized = value.facts.init;
            self.store_value(prov.alloc_id, value.ty, Vec::new(), value);
            return true;
        }
        if path.is_empty() && self.write_provenance_allocation(pointer, value.clone()) {
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
                self.content_mut(id).facts.inner_uninit = false;
            }
            return true;
        }
        if let Some(local) = self.find_local_by_address(&pointer.z3_term) {
            self.write_local_path(local, path, value);
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
                self.content_mut(id).facts.inner_uninit = false;
            }
            true
        } else if path.is_empty() {
            self.invalidate_provenance_allocation(pointer);
            false
        } else {
            let Some((alloc_id, view_ty, index)) = self.concrete_array_view(pointer) else { return false };
            let mut full = vec![index];
            full.extend(path);
            self.store_value(alloc_id, view_ty, full, value);
            true
        }
    }

    pub(crate) fn indexed_element_target(&self, place: &Place<'tcx>) -> Option<(AllocId, Int<'z3>)> {
        let element_ty = place.ty(self.body(), self.tcx).ty;
        if !matches!(
            element_ty.kind(),
            rustc_middle::ty::TyKind::RawPtr(..)
                | rustc_middle::ty::TyKind::Int(..)
                | rustc_middle::ty::TyKind::Uint(..)
                | rustc_middle::ty::TyKind::Bool
                | rustc_middle::ty::TyKind::Char
                | rustc_middle::ty::TyKind::Float(..)
        ) {
            return None;
        }
        if !matches!(
            place.projection.last()?.kind(),
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
        ) {
            return None;
        }
        let mut current_ty = self.body().local_decls[place.local].ty;
        let mut fields = Vec::new();
        let mut index = Int::from_u64(self.z3_ctx, 0);
        let element_size = self.size_of_ty(element_ty);
        if element_size == 0 {
            return None;
        }
        let mut indexed = false;
        for projection in place.projection.iter() {
            match projection {
                ProjectionElem::Field(field, field_ty) if !indexed => {
                    fields.push(field.as_usize());
                    current_ty = field_ty;
                }
                ProjectionElem::Deref => {
                    current_ty = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Ref(_, inner, _)
                        | rustc_middle::ty::TyKind::RawPtr(inner, _) => *inner,
                        _ => return None,
                    };
                }
                ProjectionElem::Downcast(..) => {}
                ProjectionElem::Index(local) => {
                    let inner = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Array(inner, _)
                        | rustc_middle::ty::TyKind::Slice(inner) => *inner,
                        _ => return None,
                    };
                    let inner_size = self.size_of_ty(inner);
                    if inner_size == 0 || inner_size % element_size != 0 {
                        return None;
                    }
                    let term = self.local_value(local)?.z3_term.clone();
                    let stride = Int::from_u64(self.z3_ctx, inner_size / element_size);
                    let step = Int::mul(self.z3_ctx, &[&term, &stride]);
                    index = Int::add(self.z3_ctx, &[&index, &step]);
                    current_ty = inner;
                    indexed = true;
                }
                ProjectionElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    let (inner, length) = match current_ty.kind() {
                        rustc_middle::ty::TyKind::Array(inner, length) => (*inner, Some(length)),
                        rustc_middle::ty::TyKind::Slice(inner) => (*inner, None),
                        _ => return None,
                    };
                    let inner_size = self.size_of_ty(inner);
                    if inner_size == 0 || inner_size % element_size != 0 {
                        return None;
                    }
                    let position = if from_end {
                        length?.try_to_target_usize(self.tcx)?.checked_sub(offset)?
                    } else {
                        offset
                    };
                    let term = Int::from_u64(self.z3_ctx, position);
                    let stride = Int::from_u64(self.z3_ctx, inner_size / element_size);
                    let step = Int::mul(self.z3_ctx, &[&term, &stride]);
                    index = Int::add(self.z3_ctx, &[&index, &step]);
                    current_ty = inner;
                    indexed = true;
                }
                _ => return None,
            }
        }
        if current_ty != element_ty {
            return None;
        }
        let alloc_id = if fields.is_empty() {
            let local_ty = self.body().local_decls[place.local].ty;
            if matches!(local_ty.kind(), rustc_middle::ty::TyKind::Array(..)) {
                self.path_state.current_frame.local_alloc.get(&place.local).copied()?
            } else {
                self.local_value(place.local)
                    .and_then(|value| value.provenance_alloc_id())
                    .or_else(|| self.path_state.current_frame.local_alloc.get(&place.local).copied())?
            }
        } else {
            self.field_value(place.local, &fields)?
                .provenance_alloc_id()?
        };
        let stored_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        let mut stored_leaf_ty = stored_ty;
        while let rustc_middle::ty::TyKind::Array(inner, _) = stored_leaf_ty.kind() {
            stored_leaf_ty = *inner;
        }
        (stored_leaf_ty == element_ty).then_some((alloc_id, index))
    }

    pub(crate) fn store_indexed_element(
        &mut self,
        alloc_id: AllocId,
        index: Int<'z3>,
        value: VmValue<'z3, 'tcx>,
    ) {
        let retained = self
            .content(alloc_id)
            .indexed_elements
            .iter()
            .filter(|(stored_index, _)| self.path_implies(&stored_index._eq(&index).not()))
            .cloned()
            .collect();
        let content = self.content_mut(alloc_id);
        content.indexed_elements_modified = true;
        content.indexed_elements = retained;
        content.indexed_elements.push((index, value));
    }

    pub(crate) fn store_repeated_indexed_elements(
        &mut self,
        alloc_id: AllocId,
        base: Int<'z3>,
        count: u64,
        value: VmValue<'z3, 'tcx>,
    ) {
        let end = Int::add(self.z3_ctx, &[&base, &Int::from_u64(self.z3_ctx, count)]);
        let retained = self
            .content(alloc_id)
            .indexed_elements
            .iter()
            .filter(|(index, _)| {
                let outside = Bool::or(self.z3_ctx, &[&index.lt(&base), &index.ge(&end)]);
                self.path_implies(&outside)
            })
            .cloned()
            .collect::<Vec<_>>();
        let mut elements = retained;
        for offset in 0..count {
            let index = Int::add(self.z3_ctx, &[&base, &Int::from_u64(self.z3_ctx, offset)]);
            elements.push((index, value.clone()));
        }
        let content = self.content_mut(alloc_id);
        content.indexed_elements_modified = true;
        content.indexed_elements = elements;
    }

    fn stored_indexed_element(&self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let (alloc_id, index) = self.indexed_element_target(place)?;
        let elements = &self.content(alloc_id).indexed_elements;
        if let Some((_, value)) = elements.iter().rev().find(|(stored_index, _)| index == *stored_index) {
            return Some(value.clone());
        }
        for (stored_index, value) in elements.iter().rev() {
            if self.path_implies(&index._eq(stored_index)) {
                return Some(value.clone());
            }
        }
        None
    }

    /// Extract a VmValue from a MIR operand.
    pub(crate) fn value_of_operand(&self, operand: &Operand<'tcx>) -> VmValue<'z3, 'tcx> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let mut value = self.value_of_place(place).unwrap_or_else(|| self.unknown_value_for_place(place));
                if matches!(place.projection.last(), Some(ProjectionElem::Field(field, _)) if field.as_usize() == 0)
                    && matches!(value.ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                    && let Some(arm) = integer::known_ite_arm(&value.z3_term, &self.path_state.constraints.assertions)
                {
                    value.z3_term = arm;
                }
                value
            }
            Operand::Constant(constant) => {
                let text = format!("{:?}", constant.const_);
                // `size_of::<T>()` / `align_of::<T>()` lower to the
                // `SizedTypeProperties::SIZE`/`::ALIGN` associated consts for a
                // generic `T`.  Bind them to the shared symbolic `sizeof_T` /
                // `align_T` (created by `size_sym`/`align_sym` during
                // `init_parameters`) so they agree with allocation sizes and
                // pointer strides instead of being unrelated fresh constants.
                if let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_ {
                    if mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
                        && !uneval.args.is_empty()
                    {
                        let ty = uneval.args.type_at(0);
                        let size = if mir_utils::ty_has_type_param(ty) {
                            self.size_sym_read(ty)
                        } else {
                            Int::from_u64(self.z3_ctx, self.size_of_ty(ty))
                        };
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        let one = Int::from_u64(self.z3_ctx, 1);
                        return VmValue::new(size._eq(&zero).ite(&one, &zero), constant.const_.ty());
                    }
                    let is_size = mir_utils::is_sized_type_property(self.tcx, uneval.def, "SIZE");
                    let is_align = mir_utils::is_sized_type_property(self.tcx, uneval.def, "ALIGN");
                    if (is_size || is_align) && !uneval.args.is_empty() {
                        let ty = uneval.args.type_at(0);
                        let term = if is_size {
                            self.size_sym_read(ty)
                        } else {
                            self.align_sym_read(ty)
                        };
                        return VmValue::new(term, constant.const_.ty());
                    }
                }
                let int_val = mir_utils::eval_const_scalar_int(self.tcx, &constant.const_, &text)
                    .or_else(|| match constant.const_ {
                        rustc_middle::mir::Const::Ty(_, value) => value.try_to_target_usize(self.tcx)
                            .filter(|value| *value <= u32::MAX as u64)
                            .map(|value| value as i128),
                        _ => None,
                    });
                let field_offset = int_val.is_none() && mir_utils::offset_of_container(self.tcx, &constant.const_).is_some();
                let enum_variant = mir_utils::const_destructure(self.tcx, &constant.const_)
                    .and_then(|(variant, _)| variant)
                    .or_else(|| {
                        let TyKind::Adt(adt, args) = constant.const_.ty().kind() else {
                            return None;
                        };
                        (int_val == Some(0)
                            && self.tcx.is_diagnostic_item(rustc_span::sym::Option, adt.did())
                            && matches!(args.type_at(0).kind(), TyKind::Ref(..)))
                        .then_some(0)
                    });
                let ty = constant.const_.ty();
                let wide_literal = matches!(
                    ty.kind(),
                    TyKind::Int(rustc_middle::ty::IntTy::I128)
                        | TyKind::Uint(rustc_middle::ty::UintTy::U128)
                )
                .then(|| {
                    constant.const_.eval(self.tcx, TypingEnv::fully_monomorphized(), rustc_span::DUMMY_SP)
                        .ok()
                        .and_then(|value| value.try_to_scalar_int())
                        .and_then(|scalar| self.scalar_bits_term(ty, scalar.to_bits(scalar.size())))
                })
                .flatten();
                let term = wide_literal
                    .or_else(|| int_val.and_then(|value| self.scalar_bits_term(ty, value as u128)))
                    .unwrap_or_else(|| self.symbolic_const_term(&constant.const_));
                let enum_discriminant = enum_variant
                    .and_then(|variant| self.enum_discriminant_term(ty, VariantIdx::from_usize(variant as usize)));
                VmValue {
                    z3_term: term,
                    ty,
                    provenance: None,
                    facts: ValueFacts::default(),
                    source: if let Some(term) = enum_discriminant {
                        ValueSource::KnownDiscriminant(term)
                    } else if field_offset {
                        ValueSource::FieldOffset
                    } else {
                        ValueSource::None
                    },
                }
            }
            Operand::RuntimeChecks(_) => VmValue::new(
                self.fresh_int("runtime_checks"),
                self.body().local_decls[Local::from_usize(0)].ty,
            ),
        }
    }

    /// Read the byte at `offset` within a `repr(C)`-style ADT from its
    /// materialized scalar field values — the field→byte direction of the cast
    /// cross-view materialization.  Returns `None` when `offset` does not land
    /// inside a concrete scalar field (so the caller falls back to the base).
    fn byte_from_field(&self, alloc_id: AllocId, ty: Ty<'tcx>, offset: usize) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        let variant = adt_def.non_enum_variant();
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            let field_off = self.field_offset_in_bytes(ty, idx) as usize;
            let field_size = self.size_of_ty(field_ty) as usize;
            if offset >= field_off && offset < field_off + field_size {
                let fv = self.load_value(alloc_id, ty, &[idx])?;
                let byte_idx = offset - field_off;
                // Fields wider than 8 bytes (e.g. `u128`) cannot be shifted by a
                // `u64` divisor; fall back to the base rather than overflow.
                if byte_idx >= 8 {
                    return None;
                }
                let divisor = Int::from_u64(self.z3_ctx, 1u64 << (byte_idx * 8));
                let modulus = Int::from_u64(self.z3_ctx, 256);
                return Some(fv.z3_term.div(&divisor).rem(&modulus));
            }
        }
        None
    }

    /// Look up the value stored at a MIR place.
    pub(crate) fn value_of_place(&self, place: &Place<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        if place.projection.iter().any(|projection| matches!(projection, ProjectionElem::Deref))
            && let Some(alloc_id) = self.local_value(place.local).and_then(VmValue::provenance_alloc_id)
        {
            self.record_memory_use(alloc_id, place.local);
        }
        if place.projection.is_empty() {
            return self.local_value(place.local).cloned();
        }
        let place_ty = place.ty(self.body(), self.tcx).ty;
        if place.projection.len() == 3
            && matches!(place.projection[0].kind(), ProjectionElem::Deref)
            && matches!(place.projection[1].kind(), ProjectionElem::Downcast(..))
            && let ProjectionElem::Field(field, _) = place.projection[2].kind()
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && provenance.offset.simplify().as_u64() == Some(0)
            && let Some(pointee) = mir_utils::pointee_ty(pointer.ty)
            && matches!(pointee.kind(), TyKind::Adt(def, _) if def.is_enum())
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(pointee)
            && let Some(value) = self.load_value(provenance.alloc_id, pointee, &[field.as_usize()])
        {
            return Some(value.clone());
        }
        let last_is_index = place.projection.last().is_some_and(|projection| {
            matches!(projection.kind(), ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. })
        });
        let indexed_target_modified = last_is_index && self.indexed_element_target(place)
            .is_some_and(|(alloc_id, _)| self.content(alloc_id).indexed_elements_modified);
        let index_count = place
            .projection
            .iter()
            .filter(|projection| {
                matches!(
                    projection.kind(),
                    ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }
                )
            })
            .count();
        let indexed_value = last_is_index
            && (matches!(place_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                || index_count > 1
                || indexed_target_modified);
        if indexed_value {
            if let Some(value) = self.stored_indexed_element(place) {
                return Some(value);
            }
            if indexed_target_modified {
                return Some(self.unknown_value_for_place(place));
            }
            if let Some(&alloc_id) = self.path_state.current_frame.local_alloc.get(&place.local)
                && !self.content(alloc_id).indexed_elements_modified
            {
                let mut path = Vec::new();
                let mut supported = true;
                for projection in place.projection.iter() {
                    match projection {
                        ProjectionElem::Field(field, _) => path.push(field.as_usize()),
                        ProjectionElem::Index(local) => {
                            let index = self
                                .local_value(local)
                                .and_then(|value| value.z3_term.simplify().as_u64())
                                .and_then(|index| usize::try_from(index).ok())
                                .unwrap_or(ARRAY_INDEX_MAX);
                            path.push(index);
                        }
                        ProjectionElem::ConstantIndex {
                            offset,
                            from_end: false,
                            ..
                        } => {
                            path.push(offset as usize);
                        }
                        _ => supported = false,
                    }
                }
                if supported && let Some(value) = self.field_value(place.local, &path) {
                    return Some(value.clone());
                }
            }
        }
        if let Some(ProjectionElem::Index(index_local)) = place.projection.last()
            && place.projection[..place.projection.len() - 1]
                .iter()
                .all(|projection| matches!(projection.kind(), ProjectionElem::Field(..)))
            && let Some(index) = self
                .local_value(*index_local)
                .and_then(|value| value.z3_term.simplify().as_u64())
        {
            let mut path = place.projection[..place.projection.len() - 1]
                .iter()
                .filter_map(|projection| match projection.kind() {
                    ProjectionElem::Field(index, _) => Some(index.as_usize()),
                    _ => None,
                })
                .collect::<Vec<_>>();
            path.push(index as usize);
            if let Some(value) = self.field_value(place.local, &path) {
                return Some(value.clone());
            }
        }
        if indexed_value {
            return Some(self.unknown_value_for_place(place));
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(place_ty)
            && let Some(offset) = provenance.offset.simplify().as_u64()
            && let size = self.size_of_ty(place_ty)
            && size != 0
            && offset % size == 0
        {
            let value = self.path_state.mem_units[provenance.alloc_id.0]
                .content
                .values
                .iter()
                .find_map(|((ty, path), value)| {
                    (matches!(ty.kind(), rustc_middle::ty::TyKind::Array(elem, _) if *elem == place_ty)
                        && path.as_slice() == [offset as usize / size as usize])
                        .then_some(value.clone())
                });
            if let Some(value) = value {
                return Some(value);
            }
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && matches!(place_ty.kind(), TyKind::Adt(def, _) if def.is_enum())
            && let Some(pointer) = self.local_value(place.local)
            && let Some(provenance) = &pointer.provenance
            && provenance.offset.simplify().as_u64() == Some(0)
            && self.alloc(provenance.alloc_id).element_ty.as_ty() == Some(place_ty)
            && let Some(value) = self.load_value(provenance.alloc_id, place_ty, &[])
        {
            return Some(value.clone());
        }
        if place.projection.len() == 1
            && matches!(place.projection[0], ProjectionElem::Deref)
            && matches!(
                place_ty.kind(),
                rustc_middle::ty::TyKind::Int(_)
                    | rustc_middle::ty::TyKind::Uint(_)
                    | rustc_middle::ty::TyKind::Bool
                    | rustc_middle::ty::TyKind::Char
                    | rustc_middle::ty::TyKind::Float(_)
            )
        {
            let pointer = self.local_value(place.local)?;
            if let Some(value) = self.read_field_allocation(pointer, place_ty) {
                return Some(value);
            }
            if let Some(provenance) = &pointer.provenance
                && provenance.offset.simplify().as_u64() == Some(0)
                && let Some(value) = self.load_value(provenance.alloc_id, place_ty, &[])
            {
                return Some(value.clone());
            }
            return Some(self.unknown_value_for_place(place));
        }

        let field_path: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|proj| match proj.kind() {
                ProjectionElem::Field(field_idx, _) => Some(field_idx.as_usize()),
                _ => None,
            })
            .collect();

        // If we have a pure field path (only Field / Downcast projections),
        // look up in the per-field value map first.  For `Option`/`ControlFlow`,
        // the variant's data is stored under the same field index as the enum
        // field (the discriminant is tracked separately, not in the field map),
        // so `(x as Some).0` resolves to `x`'s field `[0]`.
        let is_pure_field = place.projection.iter().all(|p| {
            matches!(
                p.kind(),
                ProjectionElem::Field(..) | ProjectionElem::Downcast(..)
            )
        });
        let has_downcast = place.projection.iter().any(|p| matches!(p.kind(), ProjectionElem::Downcast(..)));
        if !field_path.is_empty() && is_pure_field {
            if let Some(val) = self.field_value(place.local, &field_path).cloned() {
                return Some(val);
            }
            if let Some(base_val) = self.local_value(place.local)
                && self.is_len_field_read(base_val.ty, &field_path)
                && let Some(len) = self.len_from_value(base_val)
            {
                return Some(VmValue::new(len, place_ty));
            }
            if let Some(base_val) = self.local_value(place.local)
                && self.is_cap_field_read(base_val.ty, &field_path)
                && let Some(cap) = self.capacity_from_value(base_val)
            {
                return Some(VmValue::new(cap, place_ty));
            }
            if !has_downcast {
                // Fallback: when the base local has provenance, propagate it
                // to field accesses. This handles pointer-wrapper types (Box,
                // Unique, NonNull) where accessing inner pointer fields yields
                // the same provenance as the container.
                if let Some(base_val) = self.local_value(place.local)
                    && let Some(ref prov) = base_val.provenance
                    && !matches!(place_ty.kind(), TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char | TyKind::Float(_))
                {
                    return Some(VmValue {
                        z3_term: base_val.z3_term.clone(),
                        ty: place_ty,
                        provenance: Some(prov.clone()),
                        facts: base_val.facts.clone(),
                        source: ValueSource::None,
                    });
                }
                return None;
            }
            // A Downcast without a materialized field falls through to the
            // Deref+Field / multi-element fallback below, which returns the
            // base local (preserving the pre-Downcast behavior instead of
            // forcing a fresh value).
        }

        if !field_path.is_empty()
            && field_path.len() < place.projection.len()
            && place
                .projection
                .iter()
                .any(|p| matches!(p.kind(), ProjectionElem::Deref))
        {
            let non_field_deref = place.projection.iter().all(|p| {
                matches!(
                    p.kind(),
                    ProjectionElem::Field(..)
                        | ProjectionElem::Deref
                        | ProjectionElem::Subslice { .. }
                )
            });
            if non_field_deref {
                if let Some(val) = self.field_value(place.local, &field_path).cloned() {
                    return Some(val);
                }
                // Resolve a Deref+Field access through the pointee allocation's
                // per-allocation field tracking (e.g. `(*leaf).len` → the
                // `LeafNode.len` field value materialized by
                // `decompose_pointee_fields`).  The viewed type (pointee) is part
                // of the key so reinterpret casts (e.g. `LeafNode` → `InternalNode`)
                // resolve to the right field view.
                if let Some(base_val) = self.local_value(place.local)
                    && let Some(alloc_id) = base_val.provenance_alloc_id()
                {
                    let view_ty = mir_utils::pointee_ty(base_val.ty).unwrap_or(base_val.ty);
                    if let Some(val) = self.load_value(alloc_id, view_ty, &field_path).cloned() {
                        return Some(val);
                    }
                }
                if let Some(base_val) = self.local_value(place.local)
                    && self.is_len_field_read(base_val.ty, &field_path)
                    && let Some(len) = self.len_from_value(base_val)
                {
                    return Some(VmValue::new(len, place_ty));
                }
                if let Some(base_val) = self.local_value(place.local)
                    && self.is_cap_field_read(base_val.ty, &field_path)
                    && let Some(cap) = self.capacity_from_value(base_val)
                {
                    return Some(VmValue::new(cap, place_ty));
                }
            }
        }

        let mut base = self.local_value(place.local)?.clone();
        for proj in place.projection.iter() {
            match proj.kind() {
                ProjectionElem::Deref => {
                    base.ty = place_ty;
                }
                ProjectionElem::Field(_field_idx, _) => {
                    if !field_path.is_empty()
                        && let Some(val) = self.field_value(place.local, &field_path).cloned()
                    {
                        return Some(val);
                    }
                    base.ty = place_ty;
                }
                _ => {}
            }
        }

        let proj = place.projection.last().expect("non-empty projection");
        let prefix_is_deref = place.projection[..place.projection.len() - 1]
            .iter()
            .all(|p| matches!(p.kind(), ProjectionElem::Deref));
        if prefix_is_deref {
            let index = match proj {
                ProjectionElem::Index(local) => self
                    .local_value(*local)
                    .and_then(|value| value.z3_term.simplify().as_u64()),
                ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => Some(*offset),
                _ => None,
            };
            if let Some(index) = index
                && let Some(value) = self.field_value(place.local, &[index as usize])
            {
                return Some(value.clone());
            }
            if let ProjectionElem::Index(local) = proj
                && let Some(index_value) = self.local_value(*local)
                && matches!(
                    place_ty.kind(),
                    rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                )
                && let rustc_middle::ty::TyKind::Array(_, length) =
                    self.body().local_decls[place.local].ty.kind()
                && let Some(length) = length.try_to_target_usize(self.tcx)
            {
                let repeated = self
                    .field_value(place.local, &[ARRAY_INDEX_MAX])
                    .cloned();
                let elements = if repeated.is_some() {
                    self.field_paths(place.local)
                        .into_iter()
                        .filter_map(|path| {
                            (path.len() == 1
                                && path[0] < length as usize
                                && path[0] != ARRAY_INDEX_MAX)
                                .then(|| {
                                    self.field_value(place.local, &path)
                                        .cloned()
                                        .map(|value| (path[0], value))
                                })
                                .flatten()
                        })
                        .collect::<Vec<_>>()
                } else {
                    (0..length)
                        .filter_map(|index| {
                            self.field_value(place.local, &[index as usize])
                                .cloned()
                                .map(|value| (index as usize, value))
                        })
                        .collect::<Vec<_>>()
                };
                if repeated.is_some() || elements.len() == length as usize {
                    let mut term = repeated
                        .map(|value| value.z3_term)
                        .unwrap_or_else(|| self.fresh_int("array_index"));
                    for (index, element) in elements {
                        let selected = index_value
                            .z3_term
                            ._eq(&Int::from_u64(self.z3_ctx, index as u64));
                        term = selected.ite(&element.z3_term, &term);
                    }
                    return Some(VmValue::new(term, place_ty));
                }
            }
        }
        if let ProjectionElem::Index(local) = proj {
            if prefix_is_deref && let Some(ref prov) = base.provenance {
                let alloc_id = prov.alloc_id;
                // The base's type may have been overwritten to the
                // element type by the Deref strip above; recover the
                // pointee element type from the base local's declared
                // type (`&[u8]` → `u8`, `&[T; N]` → `T`).
                let decl_ty = self.body().local_decls[place.local].ty;
                let inner_ty = match decl_ty.kind() {
                    rustc_middle::ty::TyKind::Array(inner, _) => *inner,
                    rustc_middle::ty::TyKind::Ref(_, inner, _) => match inner.kind() {
                        rustc_middle::ty::TyKind::Slice(e) => *e,
                        _ => return Some(base.clone()),
                    },
                    rustc_middle::ty::TyKind::Slice(e) => *e,
                    _ => return Some(base.clone()),
                };
                let elem_sz = self.size_of_ty(inner_ty) as usize;
                let step = elem_sz.max(1);
                if let Some(index_val) = self.local_value(*local) {
                    let offset = Int::mul(
                        self.z3_ctx,
                        &[&index_val.z3_term, &Int::from_u64(self.z3_ctx, step as u64)],
                    );
                    // Byte-level tracking only exists once some byte of the
                    // allocation has been written; otherwise fall through to
                    // the field→byte materialization below.  Even when the
                    // allocation has a byte array, the byte may still read
                    // `UNINIT` (e.g. a struct whose fields were written in
                    // the value layer only), so also fall through to the
                    // field→byte materialization in that case.
                    if self.path_state.mem_units[alloc_id.0].content.byte_array.is_some() {
                        let term = self.byte_read(alloc_id, &offset);
                        let is_uninit = offset
                            .simplify()
                            .as_u64()
                            .map(|off| !self.is_byte_init(alloc_id, off as usize))
                            .unwrap_or(false);
                        if !is_uninit {
                            return Some(VmValue {
                                z3_term: term,
                                ty: place_ty,
                                provenance: None,
                                facts: ValueFacts::default(),
                                source: ValueSource::None,
                            });
                        }
                    }
                    // Field→byte direction of the cast cross-view
                    // materialization: the buffer was reinterpreted from a
                    // struct whose scalar fields were written in the value
                    // layer, so read the byte back out of the field value.
                    if let Some(off) = offset.simplify().as_u64()
                        && let Some(ty) = self.alloc(alloc_id).element_ty.as_ty()
                        && let Some(b) = self.byte_from_field(alloc_id, ty, off as usize)
                    {
                        return Some(VmValue {
                            z3_term: b,
                            ty: place_ty,
                            provenance: None,
                            facts: ValueFacts::default(),
                            source: ValueSource::None,
                        });
                    }
                }
            }
            return Some(self.unknown_value_for_place(place));
        }
        if !field_path.is_empty()
            && matches!(place_ty.kind(), TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char | TyKind::Float(_))
        {
            return Some(self.unknown_value_for_place(place));
        }
        let mut val = base;
        val.ty = place_ty;
        Some(val)
    }

    /// Whether `field_path` selects a length field.
    fn is_len_field_read(&self, ty: Ty<'tcx>, field_path: &[usize]) -> bool {
        if field_path.is_empty() {
            return false;
        }
        let mut view_ty = match ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _)
            | rustc_middle::ty::TyKind::RawPtr(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::Slice(_) | rustc_middle::ty::TyKind::Str => {
                    return field_path == [1];
                }
                rustc_middle::ty::TyKind::Adt(..) => *inner,
                _ => return false,
            },
            rustc_middle::ty::TyKind::Adt(..) => ty,
            _ => return false,
        };
        if field_path.len() > 1
            && !matches!(view_ty.kind(), TyKind::Adt(adt, _) if type_ids::is_std_string(adt.did()))
        {
            return false;
        }
        for (index, &field_idx) in field_path.iter().enumerate() {
            let TyKind::Adt(adt, substs) = view_ty.kind() else {
                return false;
            };
            if !adt.is_struct() {
                return false;
            }
            let Some(field) = adt
                .non_enum_variant()
                .fields
                .get(rustc_abi::FieldIdx::from_usize(field_idx))
            else {
                return false;
            };
            if index + 1 == field_path.len() {
                return field.name.as_str() == "len";
            }
            view_ty = mir_utils::field_ty(self.tcx, field, substs);
        }
        false
    }

    pub(super) fn is_cap_field_read(&self, ty: Ty<'tcx>, field_path: &[usize]) -> bool {
        if field_path.is_empty() {
            return false;
        }
        let mut view_ty = match ty.kind() {
            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
            _ => ty,
        };
        if !matches!(view_ty.kind(), TyKind::Adt(adt, _) if type_ids::is_std_vec(adt.did()) || type_ids::is_std_string(adt.did()))
        {
            return false;
        }
        for (index, &field_idx) in field_path.iter().enumerate() {
            let TyKind::Adt(adt, substs) = view_ty.kind() else {
                return false;
            };
            let Some(field) = adt
                .non_enum_variant()
                .fields
                .get(rustc_abi::FieldIdx::from_usize(field_idx))
            else {
                return false;
            };
            if index + 1 == field_path.len() {
                return field.name.as_str() == "cap";
            }
            view_ty = mir_utils::field_ty(self.tcx, field, substs);
        }
        false
    }

    /// Create an unknown value for a place.
    ///
    /// The value carries no `non_null` (or any other) assumption: a raw pointer
    /// whose provenance was lost may still be null, so assuming non-null here
    /// would let `NonNull`/null-guard checks pass unsoundly.
    pub(crate) fn unknown_value_for_place(&self, place: &Place<'tcx>) -> VmValue<'z3, 'tcx> {
        let ty = place.ty(self.body(), self.tcx).ty;
        VmValue::new(self.fresh_int("unknown"), ty)
    }
}
