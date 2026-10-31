//! Container layout, length, and backing-allocation queries.

use rustc_middle::mir::Local;
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Int};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{AllocId, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn materialize_slice_ref_return(&mut self, dest: Local) {
        let Some(mut value) = self.local_value(dest).cloned() else {
            return;
        };
        let TyKind::Ref(_, slice, _) = value.ty.kind() else {
            return;
        };
        let ValueSource::SliceLen(len) = &value.source else {
            return;
        };
        let Some(parent) = value.provenance.as_ref() else {
            return;
        };
        let parent_id = parent.alloc_id;
        let elem = match slice.kind() {
            TyKind::Slice(elem) => *elem,
            TyKind::Alias(..) => match self.alloc(parent_id).element_ty.as_ty() {
                Some(elem) => elem,
                None => return,
            },
            _ => return,
        };
        let parent_offset = parent.offset.simplify().as_u64();
        let len = len.clone();
        let align = self.align_sym(elem);
        let size = self.size_sym(elem);
        let (view_id, _) = self.allocate_slice(len, size, align.clone(), Some(elem));
        self.alloc_mut(view_id).base = value.z3_term.clone();
        self.alloc_mut(view_id).parent = Some(parent_id);
        if !self.alloc(parent_id).facts.dead {
            self.content_mut(view_id).facts.initialized = true;
        }
        if let Some(offset) = parent_offset {
            self.copy_byte_tracking(parent_id, offset as usize, view_id);
        }
        value.provenance = Some(Provenance {
            alloc_id: view_id,
            offset: Int::from_u64(self.z3_ctx, 0),
            offset_kind: None,
        });
        value.facts.non_null = true;
        value.facts.in_bounds = true;
        value.facts.align_n = Some(align);
        self.set_local(dest, value);
    }

    /// The slice/array element count for an allocation: the materialized
    /// `slice_len`, or `size / elem_size` as a fallback for allocations created
    /// before materialization (e.g. some call effects).  Uses the symbolic
    /// element size (`size_sym_read`) so `len = (len·S) / S` cancels to `len`
    /// for a generic element type — mirroring `set_len_from_alloc`.  Returns
    /// `None` when the element type is unknown.
    pub(crate) fn slice_len_of_alloc(&self, alloc_id: AllocId) -> Option<Int<'z3>> {
        let alloc = self.alloc(alloc_id);
        if let Some(len) = alloc.slice_len() {
            return Some(len.clone());
        }
        let elem_ty = alloc.element_ty.as_ty()?;
        let elem_term = self.size_sym_read(elem_ty);
        if elem_term.simplify().as_u64() == Some(1) {
            return Some(alloc.size.clone());
        }
        Some(alloc.size.div(&elem_term))
    }

    /// The slice length of a `&[T]` / `&mut [T]` value, from pointer metadata
    /// when available or its provenance allocation otherwise.
    pub(crate) fn slice_len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if let ValueSource::SliceLen(len) = &val.source {
            return Some(len.clone());
        }
        self.slice_len_of_alloc(val.provenance_alloc_id()?)
    }

    /// Resolve `x.len()` for a pointer whose pointee ADT carries a `len` field
    /// (e.g. `NodeRef<LeafNode>`: `len()` reads `(*ptr).len`).  Returns the
    /// pointee's `len` field term, or `None` when the pointee has no such field.
    pub(crate) fn try_adt_len_field(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let alloc_id = val.provenance_alloc_id()?;
        let elem_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        self.try_adt_len_field_at(alloc_id, elem_ty, elem_ty, &[])
    }

    /// Resolve a `len` field on `ty`, recursing into ADT sub-fields when there is
    /// no direct `len` (e.g. `String { vec: Vec { ptr, len, cap } }` resolves
    /// `String.len()` to `vec.len`).  `root_ty` stays fixed as the allocation's
    /// element type, which is how `decompose_pointee_fields` keys `MemoryContent::values`.
    fn try_adt_len_field_at(
        &self,
        alloc_id: AllocId,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        prefix: &[usize],
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        if let Some(len_idx) = variant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")
        {
            let mut path = prefix.to_vec();
            path.push(len_idx);
            return self.units[alloc_id.0].content.values
                .get(&(root_ty, path))
                .map(|v| v.z3_term.clone());
        }
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            if matches!(field_ty.kind(), rustc_middle::ty::TyKind::Adt(_, _)) {
                let mut path = prefix.to_vec();
                path.push(idx);
                if let Some(len) = self.try_adt_len_field_at(alloc_id, field_ty, root_ty, &path) {
                    return Some(len);
                }
            }
        }
        None
    }

    /// Resolve `len()` for `core::ops::IndexRange` (a private `{ start, end }`
    /// struct): `len() = end - start`.  The `len` field lookup above misses it
    /// because `IndexRange` has no `len` field — its `len()` computes the
    /// difference of its two private fields.
    pub(crate) fn try_index_range_len(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = val.ty.kind() else {
            return None;
        };
        if !api_classify::is_index_range(adt_def.did()) {
            return None;
        }
        let alloc_id = val.provenance_alloc_id()?;
        let view_ty = mir_utils::pointee_ty(val.ty).unwrap_or(val.ty);
        let start = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![0]))?
            .z3_term
            .clone();
        let end = self
            .units[alloc_id.0].content.values
            .get(&(view_ty, vec![1]))?
            .z3_term
            .clone();
        Some(Int::sub(self.z3_ctx, &[&end, &start]))
    }

    /// Resolve `len()` of a slice/ADT value: the pointee ADT's `len` field, then
    /// the materialized slice length, then `size / elem_size`.  Shared by the
    /// exec- and checker-side `Len` evaluators so the fallback chain is defined
    /// once.
    pub(crate) fn len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if let Some(len) = self.try_adt_len_field(val) {
            return Some(len);
        }
        if let Some(len) = self.try_index_range_len(val) {
            return Some(len);
        }
        let mut ty = val.ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = ty.kind() {
            ty = *inner;
        }
        if let TyKind::Adt(adt, _) = ty.kind()
            && (api_classify::is_std_vec(adt.did()) || api_classify::is_std_string(adt.did()))
            && let Some(data_id) = self.container_data_alloc(val.provenance_alloc_id()?, val.ty)
        {
            return self.slice_len_of_alloc(data_id);
        }
        self.slice_len_from_value(val)
    }

    pub(crate) fn capacity_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let mut ty = val.ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = ty.kind() {
            ty = *inner;
        }
        let TyKind::Adt(adt, _) = ty.kind() else {
            return None;
        };
        if !api_classify::is_std_vec(adt.did()) && !api_classify::is_std_string(adt.did()) {
            return None;
        }
        let root_id = val.provenance_alloc_id()?;
        let data_id = self.container_data_alloc(root_id, val.ty).unwrap_or(root_id);
        let alloc = self.alloc(data_id);
        let elem_ty = alloc.element_ty.as_ty()?;
        if self.size_of_ty(elem_ty) == 0 && !mir_utils::ty_has_type_param(elem_ty) {
            return Some(Int::from_u64(self.z3_ctx, usize::MAX as u64));
        }
        Some(alloc.size.div(&self.size_sym_read(elem_ty)))
    }

    /// Resolve `x.len()` for a struct `x` (e.g. `NodeRef`) whose `len()` method
    /// reads `(*x.field).len` through a `NonNull`/raw-pointer field.  Follows
    /// that field to its pointee allocation and reads the pointee's `len` field.
    pub(crate) fn try_struct_nn_len_field(
        &self,
        local: Local,
        field_path: &[usize],
        ty: Ty<'tcx>,
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        let mut found: Option<(usize, Ty<'tcx>)> = None;
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let fty = mir_utils::field_ty(self.tcx, field_def, substs);
            if let Some(pointee) = self.find_nn_pointee(fty) {
                found = Some((idx, pointee));
                break;
            }
        }
        let (nn_idx, pointee) = found?;
        let mut path = field_path.to_vec();
        path.push(nn_idx);
        let nn_val = self.field_value(local, &path)?;
        let alloc_id = nn_val.provenance_alloc_id()?;
        let rustc_middle::ty::TyKind::Adt(pointee_adt, _) = pointee.kind() else {
            return None;
        };
        let pvariant = pointee_adt.non_enum_variant();
        let len_idx = pvariant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")?;
        self.units[alloc_id.0].content.values
            .get(&(pointee, vec![len_idx]))
            .map(|v| v.z3_term.clone())
    }

    /// Resolve the type of a place (`local` + field path) by walking the ADT
    /// field definitions.
    pub(crate) fn field_type_at(&self, local: Local, field_path: &[usize]) -> Option<Ty<'tcx>> {
        let mut ty = self.body().local_decls[local].ty;
        for &idx in field_path {
            let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
                return None;
            };
            let variant = adt_def.non_enum_variant();
            let field_def = variant.fields.get(rustc_abi::FieldIdx::from_usize(idx))?;
            ty = mir_utils::field_ty(self.tcx, field_def, substs);
        }
        Some(ty)
    }

    /// Extract the pointee type if `ty` is a `#[repr(transparent)]`
    /// single-field raw-pointer wrapper (`NonNull<P>`) or wrapped in
    /// `Option<NonNull<P>>`. Returns `Some(P)`.
    ///
    /// Detected structurally (via `#[repr(transparent)]` + a raw-pointer field)
    /// rather than by name, so re-implemented std types in the challenge
    /// suites are modelled identically to their std counterparts.
    pub(crate) fn find_nn_pointee(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use rustc_middle::ty::TyKind;
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                if let Some(pointee) = self.transparent_ptr_pointee(adt_def, substs) {
                    return Some(pointee);
                }
                if self
                    .tcx
                    .is_diagnostic_item(rustc_span::sym::Option, adt_def.did())
                    && let Some(inner) = substs.first().and_then(|s| s.as_type())
                        && let TyKind::Adt(ia, is_) = inner.kind() {
                            return self.transparent_ptr_pointee(ia, is_);
                        }
                None
            }
            _ => None,
        }
    }

    /// Pointee type of a `#[repr(transparent)]` single-field raw-pointer
    /// wrapper such as `NonNull<T>` (`struct NonNull<T> { pointer: *const T }`).
    fn transparent_ptr_pointee(
        &self,
        adt_def: &rustc_middle::ty::AdtDef,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<Ty<'tcx>> {
        if !adt_def.repr().transparent() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().next()?;
        let field_ty = mir_utils::field_ty(self.tcx, field, substs);
        match field_ty.kind() {
            rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
            // NonNull's field is a pattern type `*const T is !null` on newer
            // toolchains; unwrap it to the underlying raw pointer.
            rustc_middle::ty::TyKind::Pat(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
                _ => None,
            },
            _ => None,
        }
    }

    /// Whether `ty` is a `#[repr(transparent)]` newtype (a single non-zero-sized
    /// field whose value *is* that field, e.g. `MaybeUninit<T>`, `ManuallyDrop<T>`,
    /// `Wrapping<T>`, `NonNull<T>`).  Construction and field reads are modelled
    /// transparently: the wrapper value is the field value itself.
    pub(crate) fn is_transparent_newtype(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => adt_def.repr().transparent(),
            _ => false,
        }
    }

    pub(crate) fn container_ptr_field(&self, ty: Ty<'tcx>) -> Option<Vec<usize>> {
        self.container_ptr_field_inner(ty, Vec::new(), 0)
    }

    fn container_ptr_field_inner(
        &self,
        ty: Ty<'tcx>,
        prefix: Vec<usize>,
        depth: usize,
    ) -> Option<Vec<usize>> {
        use rustc_middle::ty::TyKind;
        if depth > 4 {
            return None;
        }
        match ty.kind() {
            TyKind::Adt(adt, substs) => {
                if adt.is_enum() {
                    return None;
                }
                for (idx, field_def) in adt.non_enum_variant().fields.iter().enumerate() {
                    let field_ty =
                        mir_utils::field_ty(self.tcx, field_def, substs);
                    let mut path = prefix.clone();
                    path.push(idx);
                    if let TyKind::RawPtr(..) = field_ty.kind() {
                        return Some(path);
                    }
                    if self.find_nn_pointee(field_ty).is_some() {
                        return Some(path);
                    }
                    if let Some(found) =
                        self.container_ptr_field_inner(field_ty, path, depth + 1)
                    {
                        return Some(found);
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(crate) fn container_data_alloc(
        &self,
        header: AllocId,
        ty: Ty<'tcx>,
    ) -> Option<AllocId> {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return None;
        }
        let path = self.container_ptr_field(view_ty)?;
        self.load_value(header, view_ty, &path)?.provenance_alloc_id()
    }

    /// The data allocation behind a container header or a slice view's header.
    /// Tries the type-driven owning field first, then falls back to scanning the
    /// header's materialized fields for the first owning pointer (covers slice
    /// views whose header `AllocId` no longer carries a type key).
    pub(crate) fn data_alloc_of(&self, header: AllocId, ty: Ty<'tcx>) -> Option<AllocId> {
        let mut data_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = data_ty.kind() {
            data_ty = *inner;
        }
        let element_ty = match data_ty.kind() {
            TyKind::Slice(element) | TyKind::Array(element, _) => Some(*element),
            _ => None,
        };
        if element_ty.is_some_and(|element| self.alloc(header).element_ty.as_ty() == Some(element)) {
            return None;
        }
        self.container_data_alloc(header, ty).or_else(|| {
            // The header → data fallback is only for local (non-external) slice
            // views. An external parameter's header carries an `i64::MAX`
            // "unbounded" size that already discharges `Allocated`, so do not
            // redirect it to the (symbolic-sized) pointee.
            if self.alloc(header).is_external() {
                None
            } else {
                self.header_data_alloc(header)
            }
        })
    }

    /// Scan a header allocation's materialized fields for the owning pointer
    /// (its provenance names the data allocation). This is the header → data
    /// fallback for slice views (whose provenance names the container header,
    /// not the data), replacing the old `slice_data` edge.
    ///
    /// Returns the provenance only when the header has *exactly one* owning
    /// pointer field. A multi-owning-pointer header (e.g. a linked list's
    /// `head`/`tail`) is ambiguous, so fall back to `None` rather than guess.
    fn header_data_alloc(&self, header: AllocId) -> Option<AllocId> {
        let mut result = None;
        for ((_, p), v) in self.units[header.0].content.values.iter() {
            if p.is_empty() {
                continue;
            }
            let Some(prov) = v.provenance_alloc_id() else {
                continue;
            };
            if result.is_some() {
                return None;
            }
            result = Some(prov);
        }
        result
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn set_container_data_field(
        &mut self,
        header: AllocId,
        ty: Ty<'tcx>,
        data_alloc: AllocId,
        base: Int<'z3>,
        elem_ty: Ty<'tcx>,
    ) -> bool {
        use rustc_middle::ty::TyKind;
        let mut view_ty = ty;
        while let TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) = view_ty.kind() {
            view_ty = *inner;
        }
        if !matches!(view_ty.kind(), TyKind::Adt(..)) {
            return false;
        }
        let Some(path) = self.container_ptr_field(view_ty) else {
            return false;
        };
        let ptr_field = VmValue {
            z3_term: base,
            ty: elem_ty,
            provenance: Some(Provenance {
                alloc_id: data_alloc,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                in_bounds: true,
                ..ValueFacts::default()
            },
            source: ValueSource::None,
        };
        self.store_value(header, view_ty, path, ptr_field);
        true
    }


}
