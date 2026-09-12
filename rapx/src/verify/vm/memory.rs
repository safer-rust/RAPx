//! Symbolic memory model for the VM.

use rustc_middle::{
    mir::{Local, Place, ProjectionElem},
    ty::{Ty, TyKind},
};
use z3::ast::{Ast, Int};

use super::state::{AllocId, Allocation, Provenance, ValueInvariants, VmState, VmValue};

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    pub(crate) fn address_of_place(&mut self, place: &Place<'tcx>) -> Option<VmValue<'ctx, 'tcx>> {
        self.ensure_local_allocation(place.local);

        let zero = Int::from_u64(self.ctx, 0);

        if place.projection.is_empty() {
            let base_addr = self.local_address(place.local);
            let ty = self.body.local_decls[place.local].ty;
            // Prefer the local's value provenance over the stack-allocation
            // provenance. For Box/Vec parameters, the value tracks the heap
            // allocation while local_alloc_ids tracks the stack location.
            let provenance = self
                .locals
                .get(&place.local)
                .and_then(|v| v.provenance.clone())
                .or_else(|| {
                    self.local_alloc_ids
                        .get(&place.local)
                        .copied()
                        .map(|alloc_id| Provenance {
                            alloc_id,
                            offset: zero,
                            is_field_offset: false,
                        })
                });
            return Some(VmValue {
                term: base_addr,
                ty,
                provenance,
                invariants: ValueInvariants::default(),
            });
        }

        let mut term = self.local_address(place.local);
        let mut provenance: Option<Provenance<'ctx>> = self
            .local_alloc_ids
            .get(&place.local)
            .copied()
            .map(|alloc_id| Provenance {
                alloc_id,
                offset: zero.clone(),
                is_field_offset: false,
            });
        let mut current_ty = self.body.local_decls[place.local].ty;
        let mut field_path: Vec<usize> = Vec::new();

        for proj in place.projection.iter() {
            let mut handled = false;
            if let ProjectionElem::Index(local) = proj {
                // The element stride is the *element* size, not the container
                // size: peel `[T; N]` / `[T]` down to `T` (mirroring state.rs's
                // `Index` arm).  Keep `max(1)` so the stride matches the array
                // allocation's `elem_size` (`N·max(1)`), letting the SMT cancel
                // the factor for `idx + 1 <= N`.
                let elem_ty = match current_ty.kind() {
                    TyKind::Array(e, _) | TyKind::Slice(e) => *e,
                    _ => current_ty,
                };
                let elem_sz = Int::from_u64(self.ctx, self.size_of_ty(elem_ty).max(1));
                if let Some(val) = self.locals.get(&local) {
                    if let Some(idx) = val.term.simplify().as_u64() {
                        let scaled = Int::mul(self.ctx, &[&Int::from_u64(self.ctx, idx), &elem_sz]);
                        term = Int::add(self.ctx, &[&term, &scaled]);
                        if let Some(ref mut prov) = provenance {
                            prov.offset = Int::add(self.ctx, &[&prov.offset, &scaled]);
                        }
                        handled = true;
                    }
                }
                if !handled {
                    let idx = self.fresh_int("idx");
                    let scaled = Int::mul(self.ctx, &[&idx, &elem_sz]);
                    term = Int::add(self.ctx, &[&term, &scaled]);
                    if let Some(ref mut prov) = provenance {
                        prov.offset = Int::add(self.ctx, &[&prov.offset, &scaled]);
                    }
                }
                continue;
            }
            match proj.kind() {
                ProjectionElem::Field(field_idx, _) => {
                    let fidx = field_idx.as_usize();
                    field_path.push(fidx);
                    let field_offset = self.field_offset_in_bytes(current_ty, fidx);
                    let field_off = Int::from_u64(self.ctx, field_offset);
                    // Advance `current_ty` to the field's type so that subsequent
                    // projections resolve their offsets against the right layout.
                    let field_ty = match current_ty.kind() {
                        TyKind::Adt(adt_def, substs) => {
                            let variant = adt_def.non_enum_variant();
                            variant
                                .fields
                                .get(rustc_abi::FieldIdx::from_usize(fidx))
                                .map(|f| crate::helpers::mir_utils::field_ty(self.tcx, f, substs))
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
                        TyKind::Slice(_) => self.field_value(place.local, &field_path).and_then(
                            |fv| fv.provenance.clone().map(|p| (fv.term.clone(), p)),
                        ),
                        TyKind::Array(..) => {
                            // An array field decomposed into its own allocation by
                            // `decompose_pointee_fields` (e.g. `keys: [MaybeUninit<K>; N]`)
                            // carries a concrete element count. Prefer that allocation
                            // over the parent struct's byte-offset address so
                            // `&(*leaf).keys` keeps `len = N` for downstream InBound.
                            let alloc = provenance.as_ref().map(|p| p.alloc_id);
                            alloc.and_then(|a| {
                                self.alloc_field_values
                                    .get(&(a, field_path.clone()))
                                    .and_then(|fv| {
                                        fv.provenance.clone().map(|p| (fv.term.clone(), p))
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
                            term = Int::add(self.ctx, &[&term, &field_off]);
                            if let Some(ref mut prov) = provenance {
                                prov.offset = Int::add(self.ctx, &[&prov.offset, &field_off]);
                            }
                        }
                    }
                    current_ty = field_ty;
                }
                ProjectionElem::Deref => {
                    field_path.clear();
                    let pointed = self.locals.get(&place.local)?;
                    term = pointed.term.clone();
                    provenance = pointed.provenance.clone();
                    // For fat pointers (aggregates without provenance),
                    // use the first field's provenance (the data pointer).
                    if provenance.is_none() && matches!(pointed.ty.kind(), TyKind::RawPtr(..)) {
                        if let Some(field0) = self.field_value(place.local, &[0]) {
                            provenance = field0.provenance.clone();
                        }
                    }
                    if let TyKind::Ref(_, deref_ty, _) = current_ty.kind() {
                        current_ty = *deref_ty;
                    }
                }
                _ => {
                    self.notes
                        .push(format!("unsupported projection: {:?}", proj.kind()));
                    return None;
                }
            }
        }

        let ty = place.ty(self.body, self.tcx).ty;
        Some(VmValue {
            term,
            ty,
            provenance,
            invariants: ValueInvariants::default(),
        })
    }

    /// Lazily create a stack allocation for a MIR local if one doesn't exist.
    pub(crate) fn ensure_local_allocation(&mut self, local: Local) {
        if self.local_alloc_ids.contains_key(&local) {
            return;
        }
        let ty = self.body.local_decls[local].ty;
        let align = self.align_of_ty(ty);
        let base = self.local_address(local);
        let id = AllocId(self.next_alloc_id);
        self.next_alloc_id += 1;
        // For arrays, track the element type (not the array type) so that
        // len() computes `size / elem_size` correctly.  When the element size
        // is unknown (a generic `T`), `size_of::<[T; N]>()` collapses to 0, so
        // instead record the element count `N` as a symbolic term — this keeps
        // `len() = size / elem_size` equal to `N`, letting downstream
        // InBound checks (e.g. `get_unchecked_mut(idx)` where `idx < N`) be
        // discharged against the loop's `idx < N` path condition.
        let (size_term, element_ty, is_external) = match ty.kind() {
            TyKind::Array(elem, const_len) => {
                let elem_size = self.size_of_ty(*elem).max(1) as u64;
                // Mirror the const-generic symbolic name used by
                // `value_of_operand` (which formats `mir::Const::Ty`), so the
                // element-count term is *identical* to the `const N` term
                // appearing in path conditions (`idx < N`).  This lets the
                // later InBound SMT query discharge `idx + 1 <= len`.
                let const_text = format!("Ty({:?}, {:?})", self.tcx.types.usize, const_len);
                let n_term = match const_len.try_to_target_usize(self.tcx) {
                    Some(v) => Int::from_u64(self.ctx, v),
                    None => {
                        let name = format!("const_{}", const_text.replace([':', '#', ' '], "_"));
                        Int::new_const(self.ctx, name.as_str())
                    }
                };
                let size = match n_term.as_u64() {
                    Some(n) => Int::from_u64(self.ctx, n.saturating_mul(elem_size)),
                    None => Int::mul(self.ctx, &[&n_term, &Int::from_u64(self.ctx, elem_size)]),
                };
                (size, Some(*elem), false)
            }
            _ => {
                let size = self.struct_size_sym(ty).unwrap_or_else(|| self.size_sym(ty));
                (size, Some(ty), false)
            }
        };
        let alloc = Allocation::new(base, size_term, align, element_ty, is_external);
        self.allocations.push(alloc);
        self.local_alloc_ids.insert(local, id);
    }

    pub(crate) fn field_offset_in_bytes(&self, ty: Ty<'tcx>, field_idx: usize) -> u64 {
        crate::helpers::mir_utils::field_offset_in_bytes(
            self.tcx,
            self.caller_def_id,
            ty,
            field_idx,
        )
    }

    pub(crate) fn size_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        crate::helpers::mir_utils::layout_of_ty(self.tcx, self.caller_def_id, ty)
            .map(|l| l.size.bytes())
            .unwrap_or(0)
    }

    pub(crate) fn align_of_ty(&self, ty: Ty<'tcx>) -> u64 {
        crate::helpers::mir_utils::layout_of_ty(self.tcx, self.caller_def_id, ty)
            .map(|l| l.align.abi.bytes())
            .unwrap_or(1)
    }

    pub(crate) fn alloc_for_local(&self, local: Local) -> Option<AllocId> {
        self.local_alloc_ids.get(&local).copied()
    }

    pub(crate) fn allocation_size(&self, alloc_id: AllocId) -> &Int<'ctx> {
        &self.alloc(alloc_id).size
    }

    pub(crate) fn allocation_base(&self, alloc_id: AllocId) -> &Int<'ctx> {
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
    /// `>= 1`.  Using the same constant everywhere (ptr strides, access counts,
    /// allocation sizes) lets SMT cancel the factor in `InBound`.
    pub(crate) fn size_sym(&mut self, ty: Ty<'tcx>) -> Int<'ctx> {
        let ty = peel_slice_elem(ty);
        let size = self.size_of_ty(ty);
        if size > 0 || !crate::helpers::mir_utils::ty_has_type_param(ty) {
            return Int::from_u64(self.ctx, size);
        }
        if let Some(s) = self.sym_sizes.get(&ty) {
            return s.clone();
        }
        let s = self.fresh_int(&format!("sizeof_{ty}"));
        self.sym_sizes.insert(ty, s.clone());
        let one = Int::from_u64(self.ctx, 1);
        self.path_conditions.push(s.ge(&one));
        s
    }

    /// Read-only sibling of [`size_sym`](Self::size_sym): returns the symbolic
    /// size for `ty`, falling back to `1` when the symbolic constant has not
    /// been created yet (e.g. a checker invoked before the exec phase created
    /// it).  Concrete types still return their constant byte size.
    pub(crate) fn size_sym_read(&self, ty: Ty<'tcx>) -> Int<'ctx> {
        let ty = peel_slice_elem(ty);
        let size = self.size_of_ty(ty);
        if size > 0 {
            return Int::from_u64(self.ctx, size);
        }
        self.sym_sizes
            .get(&ty)
            .cloned()
            .unwrap_or_else(|| Int::from_u64(self.ctx, 1))
    }

    /// Size of a struct/ADT as the *sum* of its fields' sizes (each via
    /// [`size_sym`](Self::size_sym)).  This lower-bounds the real layout so a
    /// field reference (`Allocated(&alloc)`) can be discharged against the
    /// struct allocation (`sizeof_A <= 8 + 8 + sizeof_A`).  Returns `None` for
    /// non-ADT or enum types.
    pub(crate) fn struct_size_sym(&mut self, ty: Ty<'tcx>) -> Option<Int<'ctx>> {
        let TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if adt_def.is_enum() {
            return None;
        }
        let concrete = self.size_of_ty(ty);
        if concrete > 0 {
            return Some(Int::from_u64(self.ctx, concrete));
        }
        let variant = adt_def.non_enum_variant();
        let mut total = Int::from_u64(self.ctx, 0);
        for field in variant.fields.iter() {
            let field_ty = crate::helpers::mir_utils::field_ty(self.tcx, field, substs);
            let field_size = self
                .struct_size_sym(field_ty)
                .unwrap_or_else(|| self.size_sym(field_ty));
            total = Int::add(self.ctx, &[&total, &field_size]);
        }
        Some(total)
    }
}

/// Peel a slice type `[T]` to its element `T` (other types unchanged).
fn peel_slice_elem(ty: Ty<'_>) -> Ty<'_> {
    match ty.kind() {
        TyKind::Slice(elem) => *elem,
        _ => ty,
    }
}
