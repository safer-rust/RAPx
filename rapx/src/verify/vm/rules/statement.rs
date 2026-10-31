//! Transfer functions for state-changing MIR statements.

use rustc_middle::mir::{CopyNonOverlapping, Local, Operand, Place, ProjectionElem, Rvalue};
#[cfg(rapx_const_ext)]
use rustc_middle::ty::consts::ConstExt;
use z3::ast::{Ast, Bool, Int};

use super::super::state::{AllocKind, Provenance, VmState, VmValue};
use super::eval_rvalue;
use crate::helpers::mir_utils;

pub(crate) fn exec_assume<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, operand: &Operand<'tcx>) {
    let value = state.value_of_operand(operand);
    let zero = Int::from_u64(state.z3_ctx, 0);
    state
        .constraints
        .assertions
        .push(value.z3_term._eq(&zero).not());
}

pub(crate) fn exec_copy_nonoverlapping<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    copy: &CopyNonOverlapping<'tcx>,
) {
    let source = state.value_of_operand(&copy.src);
    let target = state.value_of_operand(&copy.dst);
    let count = state.value_of_operand(&copy.count);
    state.copy_memory_values(&source, &target, &count);
}

pub(crate) fn exec_assign<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    place: &Place<'tcx>,
    rvalue: &Rvalue<'tcx>,
) {
    let source_place = match rvalue {
        Rvalue::Use(Operand::Copy(source) | Operand::Move(source), ..)
        | Rvalue::WrapUnsafeBinder(Operand::Copy(source) | Operand::Move(source), _)
        | Rvalue::CopyForDeref(source) => Some(source),
        #[cfg(rapx_rvalue_has_reborrow)]
        Rvalue::Reborrow(_, _, source) => Some(source),
        _ => None,
    };
    let uninit_source = source_place
        .and_then(|source| state.current_frame.local_alloc.get(&source.local))
        .is_some_and(|id| state.possible_uninit_allocs.contains(id));
    let inner_uninit_source = source_place
        .and_then(|source| state.current_frame.local_alloc.get(&source.local))
        .is_some_and(|id| state.content(*id).facts.inner_uninit);
    let source_fields = source_place.map(|source| {
        let prefix = source.projection.iter().filter_map(|projection| {
            match projection.kind() {
                ProjectionElem::Field(field, _) => Some(field.as_usize()),
                _ => None,
            }
        }).collect::<Vec<_>>();
        if !source.projection.iter().all(|projection| {
            matches!(
                projection.kind(),
                ProjectionElem::Field(..)
                    | ProjectionElem::Deref
                    | ProjectionElem::Downcast(..)
                    | ProjectionElem::UnwrapUnsafeBinder(..)
            )
        }) {
            return Vec::new();
        }
        state.field_paths(source.local).into_iter().filter_map(|path| {
            let rest = if prefix.is_empty() {
                Some(path.clone())
            } else if path.len() > prefix.len() && path.starts_with(&prefix) {
                Some(path[prefix.len()..].to_vec())
            } else {
                None
            }?;
            state.field_value(source.local, &path).cloned().map(|value| (rest, value))
        }).collect::<Vec<_>>()
    }).unwrap_or_default();
    if place.projection.is_empty()
        && source_place.is_none_or(|source| source.local != place.local)
    {
        state.invalidate_indexed_array(place.local);
        state.invalidate_field_descendants(place.local, &[]);
    }
    if !place.projection.is_empty()
        && place.projection.iter().all(|projection| {
            matches!(projection.kind(), ProjectionElem::Field(..) | ProjectionElem::Downcast(..))
        })
    {
        let path = place.projection.iter().filter_map(|projection| {
            match projection.kind() {
                ProjectionElem::Field(field, _) => Some(field.as_usize()),
                _ => None,
            }
        }).collect::<Vec<_>>();
        if !path.is_empty() {
            state.invalidate_field_descendants(place.local, &path);
        }
    }
    let mut value = eval_rvalue(state, place, rvalue);

    let has_deref = place
        .projection
        .iter()
        .any(|p| matches!(p.kind(), ProjectionElem::Deref));

    if !place.projection.is_empty() {
        state.record_projected_store(place, &value);
        state.record_indexed_store(place, &value);
    }
    value.facts.init = true;

    if place.projection.is_empty() {
        state.set_local(place.local, value);
        if uninit_source && let Some(id) = state.current_frame.local_alloc.get(&place.local) {
            state.possible_uninit_allocs.insert(*id);
        }
        if inner_uninit_source && let Some(&id) = state.current_frame.local_alloc.get(&place.local) {
            state.content_mut(id).facts.inner_uninit = true;
        }
        // On a whole-place move (`_3 = move _4`), the destination is a fresh
        // container slot: re-point its whole-value provenance from the source's
        // stack slot to its own, so `container_data_alloc` later reads the
        // destination's owning field (copied below) rather than the moved-out
        // source's (which is invalidated after the propagation).
        let moved_from = match rvalue {
            Rvalue::Use(operand, ..) | Rvalue::WrapUnsafeBinder(operand, _) => match operand {
                Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                _ => None,
            },
            _ => None,
        };
        if let Some(src) = moved_from
            && let Some(&src_alloc) = state.current_frame.local_alloc.get(&src)
            && let Some(mut wv) = state.local_value(place.local).cloned()
            && wv
                .provenance
                .as_ref()
                .is_some_and(|p| p.alloc_id == src_alloc)
        {
            let dest_alloc = state.current_frame.local_alloc[&place.local];
            wv.provenance = Some(Provenance {
                alloc_id: dest_alloc,
                offset: Int::from_u64(state.z3_ctx, 0),
                offset_kind: None,
            });
            state.set_local(place.local, wv);
        }
        for (path, field) in source_fields {
            state.set_field_value(place.local, path, field);
        }
        // Invalidate the moved-out source's owner-field provenance *after* the
        // field propagation, so a later `Owning` check does not treat the source
        // as a second owner while the destination kept the pointer.
        if let Some(src) = moved_from {
            state.invalidate_owner_field(src);
        }
    } else if !has_deref {
        let field_indices: Vec<usize> = place
            .projection
            .iter()
            .filter_map(|p| match p.kind() {
                ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                _ => None,
            })
            .collect();
        if !field_indices.is_empty() {
            let track_iter = field_indices == [0];
            state.set_field_value(place.local, field_indices.clone(), value);
            for (path, field) in source_fields {
                let mut full = field_indices.clone();
                full.extend(path);
                state.set_field_value(place.local, full, field);
            }
            if track_iter {
                state.track_iter_ptr_update(place.local);
            }
        }
    } else {
        // Deref projection (`(*ptr).field = val`): resolve the referent local and
        // write the field there, so `&mut self` setters (`set_len`, `clear`, …)
        // actually update the referent's materialized fields instead of being
        // silently dropped.
        //
        // A pure `*ptr = val` (no trailing Field) still must NOT overwrite the
        // pointer local — writing through a pointer should not reassign the
        // pointer variable.
        let mut proj = place.projection.iter();
        if matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref)) {
            let field_indices: Vec<usize> = proj
                .filter_map(|p| match p.kind() {
                    ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                    _ => None,
                })
                .collect();
            if field_indices.is_empty() {
                let pointed = state.local_value(place.local).cloned();
                if let Some(pointed) = pointed {
                    let written_ty = value.ty;
                    let fully_initialized = value.facts.init;
                    let byte_buffer = pointed.provenance_alloc_id().filter(|&id| {
                        (matches!(state.alloc(id).kind, AllocKind::Slice { .. } | AllocKind::ExternalSlice { .. })
                            || state.alloc(id).facts.locally_allocated)
                            && state.alloc(id).element_ty.as_ty() == Some(state.tcx.types.u8)
                    });
                    let wrote_object = state.write_through_pointer(&pointed, Vec::new(), value);
                    for (path, field) in source_fields {
                        state.write_through_pointer(&pointed, path.clone(), field.clone());
                        if wrote_object && let Some(id) = byte_buffer {
                            state.store_value(id, written_ty, path, field);
                        }
                    }
                    // A whole-object write through a reinterpreted byte buffer
                    // establishes the type at this address, without changing
                    // the element type of the entire allocation.
                    if wrote_object
                        && fully_initialized
                        && mir_utils::pointee_ty(pointed.ty) == Some(written_ty)
                        && pointed.provenance.as_ref().is_some_and(|prov| {
                            prov.offset.simplify().as_u64() == Some(0)
                        })
                        && let Some(alloc_id) = pointed.provenance_alloc_id()
                    {
                        state.content_mut(alloc_id).facts.written_pointee_ty = Some(written_ty);
                    }
                }
                return;
            } else {
                let has_local_field = state.field_value(place.local, &field_indices).is_some();
                let pointed = state.local_value(place.local).cloned();
                let mut writes = vec![(field_indices.clone(), value)];
                for (path, field) in source_fields {
                    let mut full = field_indices.clone();
                    full.extend(path);
                    writes.push((full, field));
                }
                for (path, field) in writes {
                    if has_local_field {
                        state.write_local_path(place.local, path.clone(), field.clone());
                    }
                    if let Some(pointed) = &pointed {
                        state.write_through_pointer(pointed, path, field);
                    }
                }
                if has_local_field && field_indices == [0] {
                    state.track_iter_ptr_update(place.local);
                }
            }
        }
    }
}

pub(crate) fn exec_storage_live<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, local: Local) {
    state.ensure_local_allocation(local);
    let alloc_id = state.current_frame.local_alloc[&local];
    state.alloc_mut(alloc_id).facts.dead = false;
}

pub(crate) fn exec_storage_dead<'z3, 'tcx>(state: &mut VmState<'z3, 'tcx>, local: Local) {
    if let Some(alloc_id) = state.current_frame.local_alloc.get(&local).copied() {
        state.alloc_mut(alloc_id).facts.dead = true;
    }
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Record byte-level values when assigning to a place with projections.
    /// This handles patterns like `buf[i] = 0u8` (nul-store) and `arr[i] = val`.
    fn record_projected_store(&mut self, place: &Place<'tcx>, value: &VmValue<'z3, 'tcx>) {
        // Prefer the value's provenance (pointee alloc) over slots
        // (reference alloc) for ref/ptr parameters.
        let Some(alloc_id) = self
            .local_value(place.local)
            .and_then(|v| v.provenance_alloc_id())
            .or_else(|| self.current_frame.local_alloc.get(&place.local).copied())
        else {
            return;
        };

        let value_ty = value.ty;
        let value_size = self.size_of_ty(value_ty) as usize;

        let mut byte_offset: usize = 0;
        let mut concrete = true;

        let base_ty = self.body().local_decls[place.local].ty;
        let mut cur_ty = base_ty;

        for proj in place.projection.iter() {
            match proj.kind() {
                rustc_middle::mir::ProjectionElem::Field(field_idx, _) => {
                    let off = self.field_offset_in_bytes(cur_ty, field_idx.as_usize()) as usize;
                    byte_offset += off;
                    if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = cur_ty.kind()
                        && !adt_def.is_enum()
                    {
                        let variant = adt_def.non_enum_variant();
                        if let Some(field_def) = variant.fields.get(field_idx) {
                            cur_ty = mir_utils::field_ty(self.tcx, field_def, substs);
                        }
                    }
                }
                rustc_middle::mir::ProjectionElem::Deref => {
                    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = cur_ty.kind() {
                        cur_ty = *inner;
                    }
                }
                rustc_middle::mir::ProjectionElem::Index(_local) => {
                    concrete = false;
                    break;
                }
                rustc_middle::mir::ProjectionElem::Subslice {
                    from,
                    to: _,
                    from_end: _,
                } => {
                    byte_offset += from as usize;
                }
                _ => {}
            }
        }

        if concrete && value_size > 0 {
            self.content_mut(alloc_id).facts.initialized = true;
            if byte_offset == 0
                && self.alloc(alloc_id).element_ty.as_ty().is_some_and(|ty| {
                    matches!(ty.kind(), rustc_middle::ty::TyKind::Adt(def, args)
                        if crate::verify::api_classify::is_maybe_uninit_type(def.did())
                        && args.first().and_then(|arg| arg.as_type()) == Some(value_ty))
                })
            {
                self.content_mut(alloc_id).facts.written_pointee_ty = Some(value_ty);
            }

            let is_u8_write = matches!(
                value_ty.kind(),
                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
            );

            if is_u8_write {
                self.record_byte_value(alloc_id, byte_offset, value.z3_term.clone());
            }
        }
    }

    /// Track byte-level values for index-based stores (e.g. `buf[i] = 0u8`)
    /// that `record_projected_store` skips due to Index projections.
    fn record_indexed_store(&mut self, place: &Place<'tcx>, value: &VmValue<'z3, 'tcx>) {
        let index_count = place.projection.iter().filter(|projection| {
            matches!(projection.kind(), rustc_middle::mir::ProjectionElem::Index(_) | rustc_middle::mir::ProjectionElem::ConstantIndex { .. })
        }).count();
        if let Some((alloc_id, index)) = self.indexed_element_target(place)
            && (index_count > 1
                || matches!(value.ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                || self.content(alloc_id).indexed_elements_modified)
        {
            self.store_indexed_element(alloc_id, index, value.clone());
            if index_count > 1 || matches!(value.ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
                return;
            }
        }
        let mut element_ty = place.ty(self.body(), self.tcx).ty;
        let array_ty = element_ty;
        let mut array_depth = 0;
        while let rustc_middle::ty::TyKind::Array(inner, _) = element_ty.kind() {
            element_ty = *inner;
            array_depth += 1;
        }
        if array_depth > 0
            && matches!(
                element_ty.kind(),
                rustc_middle::ty::TyKind::RawPtr(..)
                    | rustc_middle::ty::TyKind::Int(..)
                    | rustc_middle::ty::TyKind::Uint(..)
                    | rustc_middle::ty::TyKind::Bool
                    | rustc_middle::ty::TyKind::Char
                    | rustc_middle::ty::TyKind::Float(..)
            )
            && let Some(address) = self.address_of_place(place)
            && let Some(provenance) = address.provenance
        {
            let element_size = self.size_of_ty(element_ty);
            if element_size > 0 {
                let start = provenance.offset.div(&Int::from_u64(self.z3_ctx, element_size));
                let count = Int::from_u64(self.z3_ctx, self.size_of_ty(array_ty) / element_size);
                let end = Int::add(self.z3_ctx, &[&start, &count]);
                let retained = self.content(provenance.alloc_id)
                    .indexed_elements
                    .iter()
                    .filter(|(index, _)| {
                        let distinct = Bool::or(
                            self.z3_ctx,
                            &[&index.lt(&start), &index.ge(&end)],
                        );
                        self.path_implies(&distinct)
                    })
                    .cloned()
                    .collect();
                let content = self.content_mut(provenance.alloc_id);
                content.indexed_elements = retained;
                content.indexed_elements_modified = true;
                return;
            }
        }
        if place.projection.len() == 1
            && let rustc_middle::mir::ProjectionElem::Index(index_local) = place.projection[0]
            && let rustc_middle::ty::TyKind::Array(elem_ty, _) =
                self.body().local_decls[place.local].ty.kind()
            && *elem_ty == value.ty
        {
            let array_ty = self.body().local_decls[place.local].ty;
            let index = self
                .local_value(index_local)
                .and_then(|v| v.z3_term.simplify().as_u64())
                .and_then(|v| usize::try_from(v).ok());
            if let Some(index) = index {
                if let Some(alloc_id) = self.current_frame.local_alloc.get(&place.local).copied() {
                    self.content_mut(alloc_id)
                        .values
                        .retain(|(ty, path), _| *ty != array_ty || path.first() != Some(&index));
                }
                if matches!(
                    value.ty.kind(),
                    rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                ) {
                    self.set_field_value(place.local, vec![index], value.clone());
                }
            } else {
                let index_term = self.local_value(index_local).map(|v| v.z3_term.clone());
                let length = match array_ty.kind() {
                    rustc_middle::ty::TyKind::Array(_, length) => {
                        length.try_to_target_usize(self.tcx)
                    }
                    _ => None,
                };
                let elements = length.and_then(|length| {
                    (0..length)
                        .map(|element| self.field_value(place.local, &[element as usize]).cloned())
                        .collect::<Option<Vec<_>>>()
                });
                if let (Some(index_term), Some(elements)) = (index_term, elements)
                    && matches!(
                        value.ty.kind(),
                        rustc_middle::ty::TyKind::Int(_)
                            | rustc_middle::ty::TyKind::Uint(_)
                            | rustc_middle::ty::TyKind::Bool
                            | rustc_middle::ty::TyKind::Char
                    )
                {
                    for (element, old) in elements.into_iter().enumerate() {
                        let selected = index_term._eq(&Int::from_u64(self.z3_ctx, element as u64));
                        let updated = VmValue::new(
                            selected.ite(&value.z3_term, &old.z3_term),
                            value.ty,
                        );
                        self.set_field_value(place.local, vec![element], updated);
                    }
                } else {
                    self.unsupported_mir = true;
                    if let Some(alloc_id) = self.current_frame.local_alloc.get(&place.local).copied() {
                        self.content_mut(alloc_id)
                            .values
                            .retain(|(ty, path), _| *ty != array_ty || path.is_empty());
                    }
                }
            }
        }
        let is_u8 = matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
        );
        if !is_u8 {
            return;
        }
        let has_index_with_concrete = place.projection.iter().any(|p| {
            if let rustc_middle::mir::ProjectionElem::Index(local) = p {
                self.local_value(local)
                    .and_then(|v| v.z3_term.simplify().as_u64())
                    .is_some()
            } else {
                false
            }
        });
        if !has_index_with_concrete {
            return;
        }
        if let Some(addr) = self.address_of_place(place)
            && let Some(ref prov) = addr.provenance
        {
            let alloc_id = prov.alloc_id;
            self.content_mut(alloc_id).facts.initialized = true;
            self.byte_write(alloc_id, &prov.offset, &value.z3_term);
        }
    }
}
