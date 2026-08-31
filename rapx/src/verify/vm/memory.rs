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

        for proj in place.projection.iter() {
            let mut handled = false;
            if let ProjectionElem::Index(local) = proj {
                if let Some(val) = self.locals.get(&local) {
                    if let Some(idx) = val.term.simplify().as_u64() {
                        let elem_sz = Int::from_u64(self.ctx, self.size_of_ty(current_ty));
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
                    let elem_size = self.size_of_ty(current_ty);
                    let elem_sz = Int::from_u64(self.ctx, elem_size);
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
                    let field_offset = self.field_offset_in_bytes(current_ty, field_idx.as_usize());
                    let field_off = Int::from_u64(self.ctx, field_offset);
                    term = Int::add(self.ctx, &[&term, &field_off]);
                    if let Some(ref mut prov) = provenance {
                        prov.offset = Int::add(self.ctx, &[&prov.offset, &field_off]);
                    }
                }
                ProjectionElem::Deref => {
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
                let size = self.size_of_ty(ty).max(1) as u64;
                (Int::from_u64(self.ctx, size), Some(ty), false)
            }
        };
        let alloc = Allocation {
            base,
            size: size_term,
            align,
            element_ty,
            is_external,
            dead: false,
            initialized: false,
            alive_assumed: false,
            nul_terminated: false,
            parent: None,
            slice_data: None,
        };
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

    pub(crate) fn allocation_size(&self, alloc_id: AllocId) -> Option<&Int<'ctx>> {
        Some(&self.alloc(alloc_id).size)
    }

    pub(crate) fn allocation_base(&self, alloc_id: AllocId) -> Option<&Int<'ctx>> {
        Some(&self.alloc(alloc_id).base)
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
}
