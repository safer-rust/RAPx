use rustc_middle::{
    mir::{Local, Operand},
    ty::TyKind,
};
use z3::ast::Int;

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::super::super::state::{Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn materialize_constructor_result(
        &mut self,
        destination: Local,
        args: &[VmValue<'z3, 'tcx>],
        first_operand: Option<&Operand<'tcx>>,
        callee: rustc_hir::def_id::DefId,
        has_invariant: bool,
    ) {
        let ty = self.body().local_decls[destination].ty;
        if !has_invariant {
            self.set_local(
                destination,
                VmValue::new(self.fresh_int("ctor_unknown"), ty),
            );
            return;
        }
        // A reconstructed owner points into the raw pointer's allocation.
        if let TyKind::Adt(adt, _) = ty.kind()
            && let Some((source, owner)) =
                super::super::super::alias_hazard::reconstructed_owner(self.tcx, callee)
            && adt.did() == owner
            && let Some(pointer) = args.get(source)
            && let Some(provenance) = pointer.provenance.as_ref()
            && let TyKind::RawPtr(data_ty, _) = pointer.ty.kind()
            && let Some(path) = self.container_ptr_field(ty)
            && let Some(field_ty) = self.field_type_at(destination, &path)
            && let Some(inner_ty) = self.find_nn_pointee(field_ty)
            && let TyKind::Adt(inner, inner_args) = inner_ty.kind()
            && !inner.is_enum()
            && let Some((value_field, field)) = inner
                .non_enum_variant()
                .fields
                .iter()
                .enumerate()
                .last()
            && mir_utils::field_ty(self.tcx, field, inner_args) == *data_ty
        {
            let offset = mir_utils::layout_of_ty(self.tcx, callee, inner_ty)
                .map(|layout| Int::from_u64(self.z3_ctx, layout.fields.offset(value_field).bytes()))
                .unwrap_or_else(|| self.fresh_int("raw_owner_data_offset"));
            let mut field = pointer.clone();
            field.ty = field_ty;
            field.z3_term = &pointer.z3_term - &offset;
            field.provenance = Some(Provenance {
                alloc_id: provenance.alloc_id,
                offset: &provenance.offset - &offset,
                offset_kind: None,
            });
            field.facts.ownership_transfer = None;
            let mut result = VmValue::new(self.fresh_int("raw_owner"), ty);
            result.facts.init = true;
            self.set_local(destination, result);
            self.set_field_value(destination, path, field);
            return;
        }
        let box_value_constructor = api_classify::is_std_box_value_constructor(self.tcx, callee);
        if let TyKind::Adt(adt, _) = ty.kind()
            && (api_classify::is_std_vec(adt.did())
                || api_classify::is_std_box(adt.did())
                || api_classify::is_std_string(adt.did())
                || api_classify::is_std_cstring(adt.did()))
            && let Some((index, pointer)) = args.iter().enumerate().find(|(_, value)| {
                value.provenance_alloc_id().is_some()
                    && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                        || matches!(value.ty.kind(), TyKind::Adt(def, _) if api_classify::is_std_nonnull(def.did())))
            })
            && !box_value_constructor
            && let Some(path) = self.container_ptr_field(ty)
        {
            let mut result = pointer.clone();
            result.ty = ty;
            result.facts.init = true;
            self.set_local(destination, result);
            self.set_field_value(destination, path, pointer.clone());
            if api_classify::is_std_vec(adt.did())
                && let Some(len) = args.get(index + 1)
                && let Some(alloc_id) = pointer.provenance_alloc_id()
            {
                self.alloc_mut(alloc_id).set_slice_len(len.z3_term.clone());
            }
            return;
        }
        if let TyKind::Adt(adt, substs) = ty.kind()
            && mir_utils::is_raw_ptr_wrapper(self.tcx, adt.did())
            && let [pointer] = args
            && matches!(pointer.ty.kind(), TyKind::RawPtr(..))
        {
            let field_ty = mir_utils::field_ty(
                self.tcx,
                adt.non_enum_variant().fields.iter().next().unwrap(),
                substs,
            );
            let mut field = pointer.clone();
            field.ty = field_ty;
            self.set_field_value(destination, vec![0], field);
            let mut value = pointer.clone();
            value.ty = ty;
            self.set_local(destination, value);
            return;
        }
        let mut facts = ValueFacts::default();
        if self.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts)
            || self.init_struct_param(destination, ty, destination.as_usize(), &mut facts)
        {
            if box_value_constructor
                && let Some(operand) = first_operand
                && let Some(pointee_ty) = args.first().map(|value| value.ty)
                && let Some(heap_id) = self
                    .local_value(destination)
                    .and_then(VmValue::provenance_alloc_id)
            {
                match operand {
                    Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                        let fields = self
                            .field_paths(place.local)
                            .into_iter()
                            .filter_map(|path| {
                                self.field_value(place.local, &path)
                                    .cloned()
                                    .map(|value| (path, value))
                            })
                            .collect::<Vec<_>>();
                        for (path, value) in fields {
                            self.store_value(heap_id, pointee_ty, path, value);
                        }
                        if let Some(value) = self.local_value(place.local).cloned() {
                            self.store_value(heap_id, pointee_ty, Vec::new(), value);
                        }
                    }
                    Operand::Constant(constant) => {
                        if matches!(
                            pointee_ty.kind(),
                            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char
                        ) && let Some(mut value) = args.first().cloned()
                        {
                            value.facts.init = true;
                            self.store_value(heap_id, pointee_ty, Vec::new(), value);
                        }
                        if let Some((_, fields)) =
                            mir_utils::const_destructure(self.tcx, &constant.const_)
                        {
                            for (index, (field, field_ty)) in fields.iter().enumerate() {
                                if let Some(scalar) = (*field).try_to_scalar_int()
                                    && let Some(term) = self
                                        .scalar_bits_term(*field_ty, scalar.to_bits(scalar.size()))
                                {
                                    let mut value = VmValue::new(term, *field_ty);
                                    value.facts.init = true;
                                    self.store_value(heap_id, pointee_ty, vec![index], value);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            return;
        }
        self.set_local(
            destination,
            VmValue {
                z3_term: self.fresh_int("ctor_result"),
                ty,
                provenance: None,
                facts,
                source: ValueSource::None,
            },
        );
    }
}
