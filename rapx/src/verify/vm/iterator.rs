//! Iterator pointer, length, and offset tracking in the symbolic VM.

use rustc_middle::mir::Local;
use rustc_middle::ty::TyKind;
use z3::ast::{Ast, Bool, Int};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{AllocId, OffsetKind, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// The two pointer fields of an Iter/IterMut local (`[0]` = ptr, `[1]` =
    /// end_or_len), which share the same allocation.  Returns `None` when
    /// either field is missing or the two point into different allocations.
    pub(crate) fn iter_ptr_end(
        &self,
        local: Local,
    ) -> Option<(VmValue<'z3, 'tcx>, VmValue<'z3, 'tcx>)> {
        for (ptr_path, end_path) in [(&[0][..], &[1][..]), (&[0, 0][..], &[0, 1][..])] {
            let (Some(ptr), Some(end)) = (
                self.field_value(local, ptr_path),
                self.field_value(local, end_path),
            ) else {
                continue;
            };
            if ptr
                .provenance
                .as_ref()
                .zip(end.provenance.as_ref())
                .is_some_and(|(pp, ep)| pp.alloc_id == ep.alloc_id)
            {
                return Some((ptr.clone(), end.clone()));
            }
        }
        None
    }

    /// Element size of the type iterated by an Iter/IterMut pointer, symbolic
    /// (`sizeof_T`) for a generic element type so `size / elem_size` cancels.
    pub(crate) fn iter_elem_size(&self, ptr: &VmValue<'z3, 'tcx>) -> Int<'z3> {
        let elem_ty = match ptr.ty.kind() {
            TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
            TyKind::RawPtr(ty, _) | TyKind::Ref(_, ty, _) => Some(*ty),
            _ => None,
        };
        if elem_ty.is_some_and(|ty| matches!(ty.kind(), TyKind::Param(_)))
            && let Some(alloc_id) = ptr.provenance_alloc_id()
            && let Some(concrete) = self.alloc(alloc_id).element_ty.as_ty()
            && !matches!(concrete.kind(), TyKind::Param(_))
        {
            return self.size_sym_read(concrete);
        }
        match elem_ty {
            Some(t) => self.size_sym_read(t),
            None => Int::from_u64(self.z3_ctx, 1),
        }
    }

    /// Element count from two pointer fields sharing the same allocation:
    /// `(end.offset - ptr.offset) / elem_size`. When both pointers carry an
    /// element-structured offset (`OffsetKind::Element`, or the base), the
    /// count is computed element-wise (`end_elem - ptr_elem`) so the
    /// `(end·S - ptr·S)/S` division is avoided for a generic element size `S`.
    pub(crate) fn iter_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
    ) -> Option<Int<'z3>> {
        let pp = ptr.provenance.as_ref()?;
        let ep = end.provenance.as_ref()?;
        if pp.alloc_id != ep.alloc_id {
            return None;
        }
        let elem_of = |p: &Provenance<'z3>| -> Option<Int<'z3>> {
            match &p.offset_kind {
                Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
                Some(OffsetKind::Field) | None => Some(Int::from_u64(self.z3_ctx, 0)),
                _ => None,
            }
        };
        if let (Some(pe), Some(ee)) = (elem_of(pp), elem_of(ep)) {
            return Some(Int::sub(self.z3_ctx, &[&ee, &pe]));
        }
        let sz = self.iter_elem_size(ptr);
        let diff = Int::sub(self.z3_ctx, &[&ep.offset, &pp.offset]);
        Some(diff.div(&sz))
    }

    /// Remaining element count of an Iter/IterMut from its two pointer fields.
    /// When a tracked pointer offset exists (`iter_ptr_offset`), prefers the
    /// compact `base_len - offset` form; otherwise falls back to
    /// `(end.offset - ptr.offset) / elem_size`.
    pub(crate) fn iter_remaining_len_from_ptrs(
        &self,
        ptr: &VmValue<'z3, 'tcx>,
        end: &VmValue<'z3, 'tcx>,
        iter_owner: Option<&(AllocId, Int<'z3>)>,
    ) -> Option<Int<'z3>> {
        let ep = end.provenance.as_ref()?;
        let sz = self.iter_elem_size(ptr);
        if let Some((_, offset, base_len_elem)) =
            iter_owner.and_then(|id| self.constraints.term_caches.iter_ptr_offset.get(id))
        {
            let base_len = base_len_elem.clone().unwrap_or_else(|| ep.offset.div(&sz));
            let zero = Int::from_u64(self.z3_ctx, 0);
            Some(
                offset
                    .gt(&base_len)
                    .ite(&zero, &Int::sub(self.z3_ctx, &[&base_len, offset])),
            )
        } else {
            self.iter_len_from_ptrs(ptr, end)
        }
    }

    /// Compare pointers by their MIR-derived element indices when they use the
    /// same positive byte stride. The tracked std iterator offset remains a
    /// fallback when an element index is unavailable.
    pub(crate) fn iter_ptr_comparison(
        &mut self,
        op: rustc_middle::mir::BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
    ) -> Option<z3::ast::Bool<'z3>> {
        if !matches!(
            op,
            rustc_middle::mir::BinOp::Eq | rustc_middle::mir::BinOp::Ne
        ) {
            return None;
        }
        let lp = lhs.provenance.as_ref()?;
        let rp = rhs.provenance.as_ref()?;
        if lp.alloc_id != rp.alloc_id {
            return None;
        }
        let Some(pointee) = mir_utils::pointee_ty(lhs.ty) else {
            return None;
        };
        if Some(pointee) != mir_utils::pointee_ty(rhs.ty)
            || !pointee.is_sized(
                self.tcx,
                rustc_middle::ty::TypingEnv::post_analysis(
                    self.tcx,
                    self.current_frame.current_def_id,
                ),
            )
        {
            return None;
        }
        let element = |prov: &Provenance<'z3>| match &prov.offset_kind {
            Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
            None | Some(OffsetKind::Field) if prov.offset.simplify().as_u64() == Some(0) => {
                Some(Int::from_u64(self.z3_ctx, 0))
            }
            _ => None,
        };
        let stride = match (&lp.offset_kind, &rp.offset_kind) {
            (
                Some(OffsetKind::Element { stride: left, .. }),
                Some(OffsetKind::Element { stride: right, .. }),
            ) if left.simplify() == right.simplify() => Some(left.clone()),
            (Some(OffsetKind::Element { stride, .. }), None | Some(OffsetKind::Field))
                if element(rp).is_some() =>
            {
                Some(stride.clone())
            }
            (None | Some(OffsetKind::Field), Some(OffsetKind::Element { stride, .. }))
                if element(lp).is_some() =>
            {
                Some(stride.clone())
            }
            _ => None,
        };
        if let Some(stride) = stride
            && let Some((left, right)) = element(lp).zip(element(rp))
        {
            let positive = self.constraints.term_caches.non_zst.contains(&stride)
                || self.path_implies(&stride.gt(&Int::from_u64(self.z3_ctx, 0)));
            if positive {
                self.constraints.term_caches.non_zst.insert(stride);
                let eq = left._eq(&right);
                return Some(if matches!(op, rustc_middle::mir::BinOp::Eq) {
                    eq
                } else {
                    eq.not()
                });
            }
        }
        let is_std_iter_comparison = self.current_frame.local_alloc.keys().any(|local| {
            let Some(value) = self.local_value(*local) else {
                return false;
            };
            let rustc_middle::ty::TyKind::Ref(_, pointee, _) = value.ty.kind() else {
                return false;
            };
            let rustc_middle::ty::TyKind::Adt(adt, _) = pointee.kind() else {
                return false;
            };
            if !api_classify::is_std_iter_or_itermut(adt.did()) {
                return false;
            }
            let Some((ptr, end)) = self.iter_ptr_end(*local) else {
                return false;
            };
            (ptr.z3_term.simplify() == lhs.z3_term.simplify()
                && end.z3_term.simplify() == rhs.z3_term.simplify())
                || (ptr.z3_term.simplify() == rhs.z3_term.simplify()
                    && end.z3_term.simplify() == lhs.z3_term.simplify())
        });
        if !is_std_iter_comparison {
            return None;
        }
        let eq = {
            let mut candidates = self
                .constraints
                .term_caches
                .iter_ptr_offset
                .values()
                .filter(|(buffer, _, _)| *buffer == lp.alloc_id);
            let (_, offset, base_len) = candidates.next()?;
            if candidates.next().is_some() {
                return None;
            }
            offset._eq(base_len.as_ref()?)
        };
        Some(if matches!(op, rustc_middle::mir::BinOp::Eq) {
            eq
        } else {
            eq.not()
        })
    }

    /// If `local` is a reference to Iter/IterMut and field 0 (ptr)
    /// is updated, increment the cumulative ptr offset so that
    /// `interpreter_iter_len` can express `len = initial_len - offset`
    /// instead of nested `(end - (ptr + sz + sz + ...)) / sz`.
    pub(crate) fn track_iter_ptr_update(&mut self, local: Local) {
        let local_val = match self.local_value(local) {
            Some(v) => v,
            None => return,
        };
        if !self.is_iter_ref(local_val) {
            return;
        }
        let Some(iter_local) = self.find_local_by_address(&local_val.z3_term) else {
            return;
        };
        let Some(iter_prov) = local_val.provenance.as_ref() else {
            return;
        };
        let iter_key = (iter_prov.alloc_id, iter_prov.offset.simplify());
        let Some(buffer) = self.iter_buffer(iter_local) else {
            return;
        };
        let one = Int::from_u64(self.z3_ctx, 1);
        let (new_offset, base_len) =
            match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
                Some((_, prev, base)) => (Int::add(self.z3_ctx, &[prev, &one]), base.clone()),
                None => {
                    let base = self
                        .field_value(iter_local, &[1])
                        .and_then(|end| end.provenance.as_ref())
                        .and_then(|ep| match &ep.offset_kind {
                            Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
                            _ => None,
                        });
                    (one.clone(), base)
                }
            };
        if let Some(e) = &base_len {
            self.constraints.assertions.push(new_offset.le(e));
        }
        self.constraints
            .term_caches
            .iter_ptr_offset
            .insert(iter_key, (buffer, new_offset, base_len));
    }

    /// The buffer an `Iter`/`IterMut` at `local` walks: the provenance of its
    /// `end` field.  This is frame-independent (the buffer allocation is
    /// path-scoped), unlike the `local` itself. The iterator's own allocation
    /// keys its element index in `iter_ptr_offset`.
    fn iter_buffer(&self, local: Local) -> Option<AllocId> {
        self.field_value(local, &[1])
            .and_then(|end| end.provenance.as_ref())
            .map(|ep| ep.alloc_id)
    }

    /// The byte buffer walked by an iterator at `local`, possibly wrapped in
    /// adapter types (`Cloned`/`Rev`/…).  `Rvalue::Aggregate` flattens nested
    /// adapters, so the innermost `Iter`/`IterMut` `end` pointer is any tracked
    /// field whose path ends in `[1]`.  Return its allocation and end offset
    /// (the end offset doubles as the byte length when the element is `u8`).
    pub(crate) fn iter_utf8_buffer(&self, local: Local) -> Option<(AllocId, Int<'z3>)> {
        let mut best: Option<(usize, AllocId, Int<'z3>)> = None;
        for path in self.field_paths(local) {
            if path.last() != Some(&1) {
                continue;
            }
            let Some(v) = self.field_value(local, &path) else {
                continue;
            };
            let Some(prov) = v.provenance.as_ref() else {
                continue;
            };
            if best
                .as_ref()
                .is_none_or(|(depth, _, _)| path.len() < *depth)
            {
                best = Some((path.len(), prov.alloc_id, prov.offset.clone()));
            }
        }
        best.map(|(_, id, off)| (id, off))
    }

    pub(crate) fn is_iter_ref(&self, val: &VmValue<'z3, 'tcx>) -> bool {
        match val.ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, pointee, _) => match pointee.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                    adt_def.did().as_local().is_none()
                        && api_classify::is_std_iter_or_itermut(adt_def.did())
                }
                _ => false,
            },
            _ => false,
        }
    }
    pub(crate) fn find_iter_self_local(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Local> {
        match arg_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => {
                    if api_classify::is_std_iter_or_itermut(adt_def.did()) {
                        if let Some(local) = self.find_local_by_address(&arg_val.z3_term) {
                            return Some(local);
                        }
                        return Some(Local::from_usize(1));
                    }
                    None
                }
                TyKind::Param(_) => self.find_local_by_address(&arg_val.z3_term).or_else(|| {
                    let receiver = Local::from_usize(1);
                    self.iter_ptr_end(receiver).map(|_| receiver)
                }),
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn is_slice_iter_next_receiver(&self, receiver: &VmValue<'z3, 'tcx>) -> bool {
        let Some(local) = self.find_iter_self_local(receiver) else {
            return false;
        };
        if self.iter_ptr_end(local).is_none() {
            return false;
        }
        let Some(value) = self.local_value(local) else {
            return false;
        };
        let ty = match value.ty.kind() {
            TyKind::Ref(_, inner, _) => *inner,
            _ => value.ty,
        };
        let TyKind::Adt(adt, args) = ty.kind() else {
            return false;
        };
        if api_classify::is_std_iter_or_itermut(adt.did()) {
            return true;
        }
        self.tcx
            .is_diagnostic_item(rustc_span::Symbol::intern("Enumerate"), adt.did())
            && args.types().next().is_some_and(|inner| {
                matches!(inner.kind(), TyKind::Adt(iter, _)
                    if api_classify::is_std_iter_or_itermut(iter.did()))
            })
    }

    pub(crate) fn apply_iter_next_effect(&mut self, args: &[VmValue<'z3, 'tcx>], dest: Local) {
        if args.is_empty() {
            return;
        }
        let self_val = &args[0];
        let Some(local) = self.find_iter_self_local(self_val) else {
            return;
        };
        let Some(iter_prov) = self_val.provenance.as_ref() else {
            return;
        };
        let iter_key = (iter_prov.alloc_id, iter_prov.offset.simplify());
        let Some((ptr, end)) = self.iter_ptr_end(local) else {
            return;
        };
        let pp = ptr.provenance.as_ref().unwrap();
        let ep = end.provenance.as_ref().unwrap();
        let buffer = ep.alloc_id;
        let dest_ty = self.body().local_decls[dest].ty;
        let sz = self.iter_elem_size(&ptr);
        let ep_elem = match &ep.offset_kind {
            Some(OffsetKind::Element { index, .. }) => Some(index.clone()),
            _ => None,
        };
        let ep_offset = ep.offset.clone();
        let remaining = self
            .iter_remaining_len_from_ptrs(&ptr, &end, Some(&iter_key))
            .expect("iter_ptr_end guarantees same-alloc provenance");
        let is_empty = remaining._eq(&Int::from_u64(self.z3_ctx, 0));
        let zero = Int::from_u64(self.z3_ctx, 0);
        let cur_off = match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
            Some((_, prev, _)) => Int::mul(self.z3_ctx, &[prev, &sz]),
            None => pp.offset.clone(),
        };
        let old_ptr_val = VmValue {
            z3_term: Int::add(self.z3_ctx, &[self.allocation_base(pp.alloc_id), &cur_off]),
            ty: ptr.ty,
            provenance: Some(Provenance {
                alloc_id: pp.alloc_id,
                offset: cur_off.clone(),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                init: true,
                ..Default::default()
            },
            source: ValueSource::None,
        };
        let one_term = Int::from_u64(self.z3_ctx, 1);
        let (old_offset, base_len_elem) =
            match self.constraints.term_caches.iter_ptr_offset.get(&iter_key) {
                Some((_, prev, base)) => (prev.clone(), base.clone()),
                None => (pp.offset.div(&sz), ep_elem),
            };
        let new_offset = Int::add(self.z3_ctx, &[&old_offset, &one_term]);
        let base_len = base_len_elem.clone().unwrap_or_else(|| ep_offset.div(&sz));
        self.constraints.assertions.push(Bool::or(
            self.z3_ctx,
            &[&is_empty, &new_offset.le(&base_len)],
        ));
        self.constraints.term_caches.iter_ptr_offset.insert(
            iter_key,
            (
                buffer,
                is_empty.ite(&old_offset, &new_offset),
                base_len_elem,
            ),
        );
        let result_val = VmValue {
            z3_term: is_empty.ite(&zero, &old_ptr_val.z3_term),
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts::default(),
            source: ValueSource::Discriminant(is_empty.ite(&zero, &one_term)),
        };
        self.set_local(dest, result_val);
        self.set_field_value(dest, vec![0], old_ptr_val);
        let next_off = is_empty.ite(&cur_off, &Int::add(self.z3_ctx, &[&cur_off, &sz]));
        let mut next_ptr = ptr.clone();
        next_ptr.z3_term = Int::add(self.z3_ctx, &[self.allocation_base(pp.alloc_id), &next_off]);
        next_ptr.provenance = Some(Provenance {
            alloc_id: pp.alloc_id,
            offset: next_off,
            offset_kind: Some(OffsetKind::Element {
                index: is_empty.ite(&old_offset, &new_offset),
                stride: sz.clone(),
            }),
        });
        let ptr_path = if self
            .field_value(local, &[0])
            .is_some_and(|field| field.z3_term == ptr.z3_term)
        {
            vec![0]
        } else {
            vec![0, 0]
        };
        self.set_field_value(local, ptr_path, next_ptr);
    }
}
