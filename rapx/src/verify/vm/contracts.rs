//! Apply contract facts and pointee invariants to symbolic state.

use rustc_middle::{mir::Local, ty::Ty};
use z3::ast::{Ast, Bool, Int};

use crate::{
    compat::FxHashSet,
    verify::contract::{
        ContractExpr, ContractKind, ContractPlace, ContractProjection, PlaceBase, Property,
        PropertyArg, PropertyKind,
    },
};

use super::query::ContractTargetContext;
use super::state::{
    AllocId, ElementTy, Provenance, ValueFacts, ValueSource, VmState, VmValue,
};

use crate::verify::api_classify;
use crate::helpers::mir_utils;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn assert_call_result_invariants(
        &mut self,
        destination: Local,
    ) {
        if !self.assume_struct_invariants {
            return;
        }
        let Some(result) = self.local_value(destination) else {
            return;
        };
        if self.inline.inline_truncated_terms.contains(&result.z3_term) {
            return;
        }
        let ty = result.ty;
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return;
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for invariant in invariants {
            let mut bound = invariant;
            rebind_property_place(&mut bound, destination);
            self.assert_contract_fact(&bound);
        }
    }

    pub(crate) fn assert_summary_result_type_invariants(
        &mut self,
        callee: rustc_hir::def_id::DefId,
        destination: Local,
    ) {
        let Some(result) = self.local_value(destination) else {
            return;
        };
        if self.inline.inline_truncated_terms.contains(&result.z3_term) {
            return;
        }
        let ty = result.ty;
        let invariants = crate::verify::type_invariants::build_type_invariants_for_ty(
            self.tcx,
            callee,
            ty,
        );
        for mut invariant in invariants {
            rebind_property_place(&mut invariant, destination);
            self.assert_contract_fact(&invariant);
        }
    }

    pub(crate) fn assert_call_postconditions(
        &mut self,
        callee: rustc_hir::def_id::DefId,
        args: &[Option<Local>],
        destination: Local,
    ) {
        let ensures = crate::verify::target::get_trait_method_ensures(self.tcx, callee);
        if ensures.is_empty() {
            return;
        }
        let bound_index_requires: Vec<(Local, Local)> = if ensures
            .iter()
            .any(|property| property.kind() == Some(PropertyKind::SliceOffset))
        {
            let mut requires = crate::verify::target::get_trait_method_requires(self.tcx, callee);
            if requires.is_empty() {
                requires = crate::verify::contract::json::query_json_contracts(self.tcx, callee);
            }
            requires
                .into_iter()
                .filter_map(|mut requirement| {
                    bind_call_property(&mut requirement, args, destination)
                        .then(|| index_access_locals(&requirement))
                        .flatten()
                })
                .collect()
        } else {
            Vec::new()
        };
        for mut property in ensures {
            if bind_call_property(&mut property, args, destination) {
                let bounded_result = slice_offset_locals(&property).is_some_and(|(_, base, index)| {
                    bound_index_requires.contains(&(base, index))
                        && self.local_value(base).zip(self.local_value(index)).is_some_and(
                            |(base_value, index_value)| {
                                self.slice_index_start(index_value, index).is_some()
                                    || self.slice_len_from_value(base_value).is_some()
                            },
                        )
                });
                property.set_contract_kind(ContractKind::Precond);
                self.assert_contract_fact(&property);
                if bounded_result {
                    self.record_bounded_result_span(destination);
                }
            } else {
                self.record_unsupported(&format!(
                    "postcondition argument binding for {}",
                    self.tcx.def_path_str(callee)
                ));
            }
        }
    }

    /// Assert a contract fact as VM state invariants.
    pub(crate) fn assert_contract_fact(&mut self, property: &Property<'tcx>) {
        if property.contract_kind() == ContractKind::Postcond {
            return;
        }
        // Record the allocations named by every `Alias` atom (hazard like
        // `Alias(self, ret)`, or a `Ptr2Ref` precondition like `Alias(self.0)`),
        // so the alias checker discharges only those — not every alias.
        let mut allocs = FxHashSet::default();
        self.collect_alias_hazard_allocs(property, &mut allocs);
        self.alias_hazard_allocs.extend(allocs);
        match property {
            Property::Atom(atom) => {
                if atom.contract_kind == ContractKind::Hazard {
                    return;
                }
                self.assert_atom_direct(property);
                for sub in crate::verify::contract::compound::subsumption_closure(atom) {
                    self.assert_atom_direct(&Property::Atom(sub));
                }
            }
            Property::And(and) => {
                for conj in &and.conjuncts {
                    self.assert_contract_fact(conj);
                }
            }
            Property::Or(or) => {
                // Two guard patterns are materialized by asserting the
                // *non-guard* disjuncts (the guard is vacuous for the case the
                // deref actually runs in):
                //   `any(Null(p), (atoms…))`  — nullable pointer.
                //   `Size(T, 0) || Deref`     — ZST vs non-ZST (`ValidPtr`).
                // A general `Or` without such a guard disjunct is left to the
                // checker (only one disjunct holds, so no fact is sound to
                // assert unconditionally).
                let is_guard = |d: &Property<'tcx>| matches!(d, Property::Atom(a) if a.kind == PropertyKind::Null || a.kind == PropertyKind::Size);
                if !or.disjuncts.iter().any(is_guard) {
                    return;
                }
                for disj in &or.disjuncts {
                    if is_guard(disj) {
                        continue;
                    }
                    self.assert_contract_fact(disj);
                }
            }
        }
    }

    fn collect_alias_hazard_allocs(&self, property: &Property<'tcx>, out: &mut FxHashSet<AllocId>) {
        match property {
            Property::Atom(atom) => {
                if atom.kind != PropertyKind::Alias {
                    return;
                }
                let Some(PropertyArg::Expr(ContractExpr::Place(cp))) = atom.args.first() else {
                    return;
                };
                if let Some(alloc_id) = self.place_root_alloc(cp) {
                    out.insert(alloc_id);
                }
            }
            Property::And(and) => {
                for conj in &and.conjuncts {
                    self.collect_alias_hazard_allocs(conj, out);
                }
            }
            Property::Or(or) => {
                for disj in &or.disjuncts {
                    self.collect_alias_hazard_allocs(disj, out);
                }
            }
        }
    }

    fn place_root_alloc(&self, cp: &ContractPlace<'tcx>) -> Option<AllocId> {
        let local = cp.base.to_local();
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index, .. } => field_path.push(*index),
                _ => return None,
            }
        }
        let val = if field_path.is_empty() {
            self.local_value(local).cloned()
        } else {
            self.field_value(local, &field_path).cloned()
        };
        val.and_then(|v| v.provenance_alloc_id())
            .map(|id| self.root_alloc(id))
    }

    /// Apply a single atom's direct effect (its `match kind` arm), without
    /// recursing into its subsumption consequences.
    fn assert_atom_direct(&mut self, property: &Property<'tcx>) {
        let Property::Atom(atom) = property else {
            return;
        };
        let kind = atom.kind;
        match kind {
            PropertyKind::SliceOffset => {
                if let Some((dest, base_local, index_local)) = slice_offset_locals(property)
                    && let (Some(base), Some(index)) = (
                        self.local_value(base_local).cloned(),
                        self.local_value(index_local).cloned(),
                    )
                {
                    let previous = self.local_value(dest).cloned();
                    if self.apply_slice_offset(dest, &base, &index, index_local) {
                        if let (Some(previous), Some(expected)) = (previous, self.local_value(dest)) {
                            self.constraints.assertions.push(previous.z3_term._eq(&expected.z3_term));
                        }
                        let indexed_in_bounds = self.index_access_facts.iter().any(
                            |(slice, index_term, slice_local, indexed_local)| {
                                *slice_local == base_local
                                    && *indexed_local == index_local
                                    && *slice == base.z3_term
                                    && *index_term == index.z3_term
                            },
                        );
                        if indexed_in_bounds {
                            self.record_bounded_result_span(dest);
                        }
                    } else {
                        self.record_unsupported("SliceOffset index");
                    }
                }
            }
            PropertyKind::NonNull => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_non_null_for_value(property, val);
                }
            }
            PropertyKind::Align => {
                if property.for_each().is_none()
                    && let Some(val) = self.contract_target_value(property)
                {
                    self.set_align_for_value(property, val);
                }
                self.record_for_each_align(property);
            }
            PropertyKind::Init => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_init_for_value(property, val);
                }
            }
            PropertyKind::Owning => {
                if property.for_each().is_none()
                    && let Some(val) = self.contract_target_value(property)
                {
                    self.set_owning_for_value(val);
                }
                self.record_for_each_owning(property);
            }
            PropertyKind::Alive => {
                if let Some(id) = self.contract_alloc_id_field_aware(property) {
                    // The region is bound at parse time (`bind_alive_regions`):
                    // struct invariants against the struct, function `requires`
                    // against the function.
                    if let Some(PropertyArg::Region(region)) = property.args().get(1) {
                        self.alloc_mut(id).facts.liveness = Some(*region);
                    }
                }
            }
            PropertyKind::InBound => {
                self.record_index_access_fact(property);
                if property.for_each().is_none()
                    && let Some(val) = self.contract_target_value(property)
                {
                    if let (Some(alloc_id), Some(ty)) =
                        (val.provenance_alloc_id(), property.ty_arg(1))
                    {
                        self.bounded_object_spans
                            .push((alloc_id, val.z3_term.clone(), ty));
                    }
                    self.set_in_bounds_for_value(property, val);
                }
                if let Some(fe_place) = property.for_each() {
                    self.assert_in_bound_for_each(property, fe_place);
                } else {
                    self.assert_in_bound_single(property);
                }
                // The pointer-and-count form `InBound(p, T, n)` also guarantees
                // the allocation backs `n` elements — materialize that size so a
                // downstream `ptr.add(n)`/`ptr.sub(n)` can discharge `InBound`
                // against a concrete (or `i64::MAX`) size rather than the coarse
                // `in_bounds` flag (which only covers `count == 1`).
                if property.args().len() >= 3 && property.for_each().is_none() {
                    self.assert_allocated_fact(property);
                }
            }
            PropertyKind::Allocated => {
                if property.for_each().is_none() {
                    self.assert_allocated_fact(property);
                }
                self.record_for_each_allocated(property);
            }
            PropertyKind::Typed => {
                if let Some(val) = self.contract_target_value(property)
                    && let Some(expected_ty) = property.ty_arg(1)
                        .or_else(|| mir_utils::pointee_ty(val.ty))
                {
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        if property.for_each().is_none()
                            && property.args().len() <= 2
                            && let Some(prov) = &val.provenance
                        {
                            self.typed_values.insert((
                                alloc_id,
                                prov.offset.clone(),
                                expected_ty,
                            ));
                        }
                        if property.for_each().is_some() {
                            self.alloc_mut(alloc_id).facts.for_each.target_ty = Some(expected_ty);
                        }
                        if property.for_each().is_none()
                            && self.alloc(alloc_id).element_ty.is_generic()
                        {
                            self.alloc_mut(alloc_id).element_ty = ElementTy::Typed(expected_ty);
                        }
                    }
                }
            }
            PropertyKind::SplitTransmute => {
                // Anchor the license on the slice's data allocation: the
                // transmute re-interprets *that* allocation's bytes into the
                // destination element type, so `check_split_transmute` finds the
                // license through the receiver slice's provenance.
                let src = property.ty_arg(0);
                let dst = property.ty_arg(1);
                if let (Some(src), Some(dst)) = (src, dst) {
                    // `SplitTransmute([T], [U])` licenses re-interpretation into
                    // the *element* type `U` (the `[U]` slice wrapper unwraps).
                    let dst_elem = match dst.kind() {
                        rustc_middle::ty::TyKind::Slice(e) => *e,
                        _ => dst,
                    };
                    // Find the entry parameter whose pointee slice is `src`
                    // (e.g. `slice: &[T]` for `SplitTransmute([T], [U])`) and
                    // mark its data allocation.
                    let arg_count = self.body().arg_count;
                    for local_idx in 1..=arg_count {
                        let local = Local::from_usize(local_idx);
                        if let Some(val) = self.local_value(local).cloned() {
                            let is_match = match val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner == src,
                                _ => false,
                            };
                            if is_match && let Some(prov) = &val.provenance {
                                self.content_mut(prov.alloc_id).facts.split_transmute_to =
                                    Some(dst_elem);
                            }
                        }
                    }
                }
            }
            PropertyKind::ValidCStr => {
                self.assert_valid_cstr_fact(property);
            }
            PropertyKind::ValidString => {
                let id = self.contract_alloc_id_field_aware(property).or_else(|| {
                    // Iterator form (`ValidString(bytes)` with `bytes: &mut I`):
                    // trace the iterator to its backing byte buffer.
                    let local = self.contract_target_local(property)?;
                    let val = self.local_value(local)?.clone();
                    let iter_local = self.find_local_by_address(&val.z3_term)?;
                    self.iter_utf8_buffer(iter_local).map(|(id, _)| id)
                });
                if let Some(id) = id {
                    self.content_mut(id).facts.initialized = true;
                    self.content_mut(id).facts.utf8_trusted = true;
                }
            }
            PropertyKind::ValidNum => {
                if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
                    for pred in predicates {
                        if let Some(condition) = self.eval_predicate_as_bool(pred) {
                            self.constraints.assertions.push(condition);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn record_bounded_result_span(&mut self, destination: Local) {
        if let Some(result) = self.local_value(destination)
            && let Some(alloc_id) = result.provenance_alloc_id()
            && let Some(pointee) = mir_utils::pointee_ty(result.ty)
        {
            self.bounded_object_spans
                .push((alloc_id, result.z3_term.clone(), pointee));
        }
    }

    /// Get the local referenced by a contract property's target.
    fn contract_target_local(&self, property: &Property<'tcx>) -> Option<Local> {
        let cp = property.target_place()?;
        Some(cp.base.to_local())
    }

    fn assert_valid_cstr_fact(&mut self, property: &Property<'tcx>) {
        let id = self.contract_alloc_id_field_aware(property).or_else(|| {
            let local = self.contract_target_local(property)?;
            self.local_value(local)?.provenance_alloc_id()
        });
        let Some(id) = id else { return };
        self.alloc_mut(id).facts.dead = false;
        let region = self
            .contract_target_local(property)
            .and_then(|local| {
                let ty = if local.as_usize() > 0
                    && local.as_usize() <= self.body().arg_count
                {
                    super::region::fn_arg_ty(
                        self.tcx,
                        self.current_frame.current_def_id,
                        local.as_usize() - 1,
                    )
                } else {
                    self.local_value(local).map(|value| value.ty)
                }?;
                match ty.kind() {
                    rustc_middle::ty::TyKind::Ref(region, ..) => Some(*region),
                    _ => None,
                }
            });
        if let Some(region) = region
            && !matches!(region.kind(), rustc_middle::ty::RegionKind::ReErased)
        {
            self.alloc_mut(id).facts.liveness = Some(region);
        }
        self.content_mut(id).facts.initialized = true;
        self.content_mut(id).facts.cstr_trusted = true;
        if let Some(n) = property.args().get(1).and_then(|a| match a {
            PropertyArg::Expr(ContractExpr::Const(_)) => None,
            a => self.resolve_contract_count(a),
        }) {
            let one = Int::from_u64(self.z3_ctx, 1);
            self.constraints.assertions.push(n.ge(&one));
            self.constraints.assertions.push(self.alloc(id).size.ge(&n));
            let zero = Int::from_u64(self.z3_ctx, 0);
            let terminal = Int::sub(self.z3_ctx, &[&n, &one]);
            self.byte_write(id, &terminal, &zero);
        }
    }

    /// Materialize a fresh external allocation for an `Allocated` contract
    /// fact, returning a value carrying the allocation's provenance.
    /// Mark the target pointer's existing allocation as live (and record its
    /// element type for downstream `Typed` checks).  Returns `true` when the
    /// pointer already carried an allocation, so a fresh external allocation
    /// should *not* be materialized (which would loosen bound checks).
    fn mark_alloc_live_keep(&mut self, val: &VmValue<'z3, 'tcx>, elem_ty: Ty<'tcx>) -> bool {
        let Some(alloc_id) = val.provenance_alloc_id() else {
            return false;
        };
        self.alloc_mut(alloc_id).facts.dead = false;
        if self.alloc(alloc_id).is_external() {
            self.alloc_mut(alloc_id).facts.liveness = Some(self.tcx.lifetimes.re_static);
        }
        if self.alloc(alloc_id).element_ty.is_generic() {
            self.alloc_mut(alloc_id).element_ty = ElementTy::Typed(elem_ty);
        }
        true
    }

    fn materialize_external_alloc(
        &mut self,
        elem_ty: Ty<'tcx>,
        count_term: Option<Int<'z3>>,
        val_ty: Ty<'tcx>,
        huge: bool,
    ) -> VmValue<'z3, 'tcx> {
        let elem_sz_raw = self.size_of_ty(elem_ty);
        let heap_align = self.align_sym(elem_ty);
        let heap_align_n = Self::non_trivial_align(heap_align.clone());
        let (heap_id, heap_base) = if huge || elem_sz_raw == 0 {
            // Struct-field targets (and generic element types): use an
            // unbounded external allocation so `Allocated`/`InBound` checks
            // auto-pass regardless of the symbolic element size.
            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
            self.allocate_external(max_size, heap_align.clone(), Some(elem_ty))
        } else {
            let elem_sz = Int::from_u64(self.z3_ctx, elem_sz_raw);
            let count = count_term.unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
            let total = Int::mul(self.z3_ctx, &[&count, &elem_sz]);
            self.allocate_external(total, heap_align, Some(elem_ty))
        };
        self.content_mut(heap_id).facts.initialized = true;
        VmValue {
            z3_term: heap_base,
            ty: val_ty,
            provenance: Some(Provenance {
                alloc_id: heap_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            facts: ValueFacts {
                non_null: true,
                dangling: false,
                init: true,
                in_bounds: true,
                align_n: heap_align_n,
            },
            source: ValueSource::None,
        }
    }

    /// Assert an `Allocated(p, T, n)` contract fact by materializing a fresh
    /// external allocation for the pointer-typed target.
    ///
    /// - For a whole pointer parameter (`src`), the allocation is sized
    ///   `n * sizeof(T)` so downstream pointer arithmetic stays in bounds.
    /// - For a plain pointer *field* (e.g. `RawVecInner::ptr`), the allocation
    ///   is written back to the field via `set_contract_target_value`, and is
    ///   unbounded so field-subrange `InBound` checks auto-pass.
    /// - For `Downcast` targets, the legacy whole-local behaviour applies.
    fn assert_allocated_fact(&mut self, property: &Property<'tcx>) {
        let elem_ty = property.ty_arg(1);
        let count_term = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a));
        let Some(elem_ty) = elem_ty else { return };

        let has_nonfield = property
            .target_place()
            .map(|cp| {
                cp.projections.iter().any(|p| {
                    !matches!(p, crate::verify::contract::ContractProjection::Field { .. })
                })
            })
            .unwrap_or(false);

        if has_nonfield {
            let Some(local) = self.contract_target_local(property) else {
                return;
            };
            let Some(val) = self.local_value(local).cloned() else {
                return;
            };
            if let Some(alloc_id) = val.provenance_alloc_id() {
                self.alloc_mut(alloc_id).facts.dead = false;
            }
            let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
            self.set_local(local, v);
        } else {
            let Some((local, field_path)) = self.contract_field_path(property) else {
                return;
            };
            if field_path.is_empty() {
                let Some(val) = self.local_value(local).cloned() else {
                    return;
                };
                if self.mark_alloc_live_keep(&val, elem_ty) {
                    return;
                }
                let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
                self.set_local(local, v);
            } else {
                // Field target. Only a *direct* pointer field (`NonNull<T>` /
                // `*mut T` / `*const T`) to a *simple* element type (primitive or
                // generic param, e.g. `NonNull<u8>`) carries the allocation
                // itself without a nested field decomposition; a wrapped field
                // (`Option<NonNull>`, `Box`) or a pointer-to-ADT (`NonNull<LeafNode>`,
                // whose fields were decomposed by param init) is handled via the
                // legacy whole-local path to avoid losing those relationships.
                let is_direct_simple_ptr = self
                    .field_value(local, &field_path)
                    .map(|val| {
                        (matches!(val.ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                            || matches!(val.ty.kind(), rustc_middle::ty::TyKind::Adt(adt, _)
                                if api_classify::is_std_nonnull(adt.did())
                                    || mir_utils::is_raw_ptr_wrapper(self.tcx, adt.did())))
                            && (elem_ty.is_primitive()
                                || matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Param(_)))
                    })
                    .unwrap_or(false);
                let Some(val) = self.field_value(local, &field_path).cloned() else {
                    return;
                };
                if let rustc_middle::ty::TyKind::Adt(adt, _) = self.body().local_decls[local].ty.kind()
                    && (api_classify::is_std_vec(adt.did()) || api_classify::is_std_string(adt.did()))
                    && val.provenance_alloc_id().is_some_and(|id| {
                        self.alloc(id).slice_len().is_some()
                            && self.alloc(id).element_ty.as_ty() == Some(elem_ty)
                    })
                {
                    return;
                }
                if let Some(alloc_id) = val.provenance_alloc_id() {
                    self.alloc_mut(alloc_id).facts.dead = false;
                    if self.alloc(alloc_id).size.as_u64().is_some() {
                        return;
                    }
                }
                // A direct simple pointer field carries the allocation itself; a
                // wrapped field / pointer-to-ADT materializes the *field* target
                // (unbounded via `huge`) so a downstream `Allocated` sees the
                // freshly-sized allocation.
                let mut v = self.materialize_external_alloc(
                    elem_ty,
                    count_term,
                    val.ty,
                    is_direct_simple_ptr,
                );
                // The size materialization must not clobber a *stronger*
                // alignment fact already on the field (e.g. `Align(ptr, usize)`
                // set `align_n = 8`, but `Allocated(ptr, u8, n)` re-materializes
                // with `u8`'s align of 1 → `align_n = None`).
                if v.facts.align_n.is_none() {
                    v.facts.align_n = val.facts.align_n.clone();
                }
                self.set_field_value(local, field_path, v);
            }
        }
    }

    /// Resolve a contract place to `(local, field_path)`. Field projections
    /// are accumulated into `field_path`; `Downcast`/`ForEach` terminate
    /// the path (they unwrap the value in place).
    fn contract_field_path(&self, property: &Property<'tcx>) -> Option<(Local, Vec<usize>)> {
        let cp = property.target_place()?;
        let local = cp.base.to_local();
        let mut path = Vec::new();
        for proj in &cp.projections {
            match proj {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    path.push(*index);
                }
                _ => break,
            }
        }
        Some((local, path))
    }

    /// Get the VmValue for a contract property's target, following field
    /// projections so that `Align(self.heap, T)` resolves to the `heap` field
    /// value rather than the whole `self` reference.
    fn contract_target_value(&self, property: &Property<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let place = property.target_place()?;
        self.contract_place_value_at(ContractTargetContext::Bound, place)
    }

    /// Write a contract target value back to its (possibly field) location.
    fn set_contract_target_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
        if let Some((local, path)) = self.contract_field_path(property) {
            if path.is_empty() {
                self.set_local(local, val);
            } else {
                self.set_field_value(local, path, val);
            }
        }
    }

    /// Resolve the alloc_id for a contract property target, following
    /// field projections to locate the actual field value's provenance.
    fn contract_alloc_id_field_aware(&self, property: &Property<'tcx>) -> Option<AllocId> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp,
            _ => return None,
        };
        cp.plain_field_path()?;
        self.contract_place_value_at(ContractTargetContext::Bound, cp)?.provenance_alloc_id()
    }

    /// Resolve a contract count argument to a Z3 term by looking up
    /// the corresponding function parameter in the VM state.
    fn resolve_contract_count(&self, arg: &PropertyArg<'tcx>) -> Option<Int<'z3>> {
        match arg {
            PropertyArg::Expr(expr) => self.eval_contract_expr_simple(expr),
            _ => None,
        }
    }

    /// Evaluate a numeric predicate to a Z3 Bool for path-condition assertion.
    fn eval_predicate_as_bool(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        let lhs = self.eval_contract_expr_simple(&pred.lhs)?;
        let rhs = self.eval_contract_expr_simple(&pred.rhs)?;
        Some(self.contract_relop_bool(pred.op, &lhs, &rhs))
    }

    fn eval_numeric_binary(
        &self,
        left: &Int<'z3>,
        right: &Int<'z3>,
        op: crate::verify::contract::NumericBinOp,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::NumericBinOp;
        match op {
            NumericBinOp::Div => Some(left.div(right)),
            NumericBinOp::Rem => Some(left.rem(right)),
            _ => self.contract_binary_term(op, left, right),
        }
    }

    /// Set non_null invariant on the target value.
    fn set_non_null_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.facts.non_null = true;
        self.set_contract_target_value(property, val);
    }

    fn set_in_bounds_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.facts.in_bounds = true;
        self.set_contract_target_value(property, val);
    }

    fn assert_in_bound_for_each(
        &mut self,
        property: &Property<'tcx>,
        fe_place: &crate::verify::contract::ContractPlace<'tcx>,
    ) {
        let Some(fe_local) = fe_place.base.try_to_local() else {
            return;
        };
        let fe_val = match self.local_value(fe_local).cloned() {
            Some(v) => v,
            None => return,
        };
        let fe_alloc_id = match fe_val.provenance_alloc_id() {
            Some(id) => id,
            None => return,
        };
        let byte_vals: Vec<(usize, Int<'z3>)> = self.alloc_byte_values(fe_alloc_id);
        if byte_vals.is_empty() {
            return;
        }
        let slice_local = match property.args().first() {
            Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. })) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => cp.base.try_to_local(),
                    _ => None,
                }
            }
            Some(PropertyArg::Expr(ContractExpr::Place(cp))) => cp.base.try_to_local(),
            _ => None,
        };
        let slice_val = slice_local.and_then(|loc| self.local_value(loc));
        let slice_alloc_id = slice_val.and_then(|sl_val| sl_val.provenance_alloc_id());
        let data_size = slice_alloc_id.map(|da_id| self.alloc(da_id).size.clone());
        let elem_sz = slice_alloc_id
            .and_then(|da_id| self.alloc(da_id).element_ty.as_ty())
            .map(|ty| self.size_of_ty(ty))
            .unwrap_or(1)
            .max(1);
        let Some(data_size) = data_size else { return };
        let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
        let len = slice_val
            .and_then(|sl_val| self.slice_len_from_value(sl_val))
            .unwrap_or_else(|| data_size.div(&elem_sz_term));
        let zero = Int::from_u64(self.z3_ctx, 0);
        for (_, term) in &byte_vals {
            self.constraints.assertions.push(term.ge(&zero));
            self.constraints.assertions.push(term.lt(&len));
        }
    }

    /// Record the numeric `index < len` bound for a single-index
    /// `InBound(slice, index)`, so a derived index (e.g. `index - 1` guarded by
    /// `index >= 1`) can be discharged by SMT rather than only via the coarse
    /// `in_bounds` flag. Range indices (`start..end`) are left to the checker's
    /// `extract_range_end` (`end <= len`).
    fn assert_in_bound_single(&mut self, property: &Property<'tcx>) {
        let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args().first()
        else {
            return;
        };
        let ContractExpr::Place(index_place) = index.as_ref() else {
            return;
        };
        let index_local = index_place.base.to_local();
        if !matches!(
            self.body().local_decls[index_local].ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::Usize)
        ) {
            return;
        }
        let slice_local = match slice.as_ref() {
            ContractExpr::Place(cp) => cp.base.try_to_local(),
            _ => None,
        };
        let Some(slice_local) = slice_local else {
            return;
        };
        let Some(da_id) = self
            .local_value(slice_local)
            .and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        let len = self
            .slice_len_of_alloc(da_id)
            .unwrap_or_else(|| self.alloc(da_id).size.clone());
        let Some(index_term) = self.eval_contract_expr_simple(index) else {
            return;
        };
        self.constraints.assertions.push(index_term.lt(&len));
    }

    fn record_index_access_fact(&mut self, property: &Property<'tcx>) {
        let Some((slice_local, index_local)) = index_access_locals(property) else {
            return;
        };
        if let (Some(slice), Some(index)) = (
            self.local_value(slice_local),
            self.local_value(index_local),
        ) {
            self.index_access_facts.push((
                slice.z3_term.clone(),
                index.z3_term.clone(),
                slice_local,
                index_local,
            ));
        }
    }

    /// When a `&T`/`&mut T` reference is created (e.g. via `&*NonNull<T>`), assume
    /// `T`'s `#[rapx::invariant]`s on the new reference local, rebinding the
    /// invariant's `self` place to that reference. This is what lets a struct's
    /// invariants flow through pointer dereferences into the caller's state.
    pub(crate) fn assert_pointee_struct_invariants(
        &mut self,
        dest_ty: Ty<'tcx>,
        dest_local: Local,
    ) {
        let pointee = match dest_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
            _ => return,
        };
        let adt_def = match pointee.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => *adt_def,
            _ => return,
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let mut rebound = inv.clone();
            rebind_property_place(&mut rebound, dest_local);
            self.assert_contract_fact(&rebound);
        }
    }

    /// Assert a pointee ADT's `#[rapx::invariant]` struct invariants directly
    /// against its materialized per-allocation field values.  This is the
    /// pointer-field analogue of [`assert_pointee_struct_invariants`](Self::
    /// assert_pointee_struct_invariants): that helper covers `&T` references,
    /// while this one covers `NonNull<T>` / `Box<T>` pointer *fields* whose
    /// pointee is decomposed by `init_ptr_field` (e.g. `NodeRef.node:
    /// NonNull<LeafNode>` must satisfy `LeafNode`'s `len <= CAPACITY`).
    pub(crate) fn assert_alloc_pointee_invariants(
        &mut self,
        alloc_id: AllocId,
        pointee_ty: Ty<'tcx>,
    ) {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = pointee_ty.kind() else {
            return;
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let Property::Atom(atom) = inv else {
                continue;
            };
            if atom.kind != PropertyKind::ValidNum {
                continue;
            }
            let Some(PropertyArg::Predicates(preds)) = atom.args.first() else {
                continue;
            };
            for pred in preds {
                if let Some(cond) = self.eval_pointee_predicate_as_bool(alloc_id, pointee_ty, pred)
                {
                    self.constraints.assertions.push(cond);
                }
            }
        }
    }

    /// Evaluate a `ValidNum` predicate against a pointee allocation (not a MIR
    /// local): field places resolve through `MemoryContent::values` keyed by the
    /// pointee type.
    fn eval_pointee_predicate_as_bool(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        let lhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.lhs)?;
        let rhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.rhs)?;
        Some(self.contract_relop_bool(pred.op, &lhs, &rhs))
    }

    /// Evaluate a numeric `ContractExpr` against a pointee allocation.
    fn eval_pointee_expr(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        match expr {
            ContractExpr::Const(v) => Some(Int::from_u64(self.z3_ctx, *v as u64)),
            ContractExpr::SizeOf(ty) => Some(self.size_sym_read(*ty)),
            ContractExpr::AlignOf(ty) => Some(self.align_sym_read(*ty)),
            ContractExpr::Place(cp) => {
                let path = cp.plain_field_path()?;
                self.units[alloc_id.0]
                    .content
                    .values
                    .get(&(view_ty, path))
                    .map(|v| v.z3_term.clone())
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_pointee_expr(alloc_id, view_ty, lhs)?;
                let r = self.eval_pointee_expr(alloc_id, view_ty, rhs)?;
                self.eval_numeric_binary(&l, &r, *op)
            }
            ContractExpr::Len(inner, _) => {
                let val = self.eval_pointee_expr_value(alloc_id, view_ty, inner)?;
                self.slice_len_from_value(&val)
            }
            _ => None,
        }
    }

    /// Resolve a `Place` (or `Len` inner) against a pointee allocation, returning
    /// the materialized `VmValue` so slice-length fallbacks can read provenance.
    fn eval_pointee_expr_value(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let ContractExpr::Place(cp) = expr else {
            return None;
        };
        let path = cp.plain_field_path()?;
        self.units[alloc_id.0]
            .content
            .values
            .get(&(view_ty, path))
            .cloned()
    }

    /// Set align invariant on the target value.
    fn set_align_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        if let Some(PropertyArg::Ty(ty)) = property.args().get(1) {
            let align = self.align_sym(*ty);
            let align_u64 = align.simplify().as_u64();
            if align_u64 != Some(1) {
                val.facts.align_n = Some(align.clone());
                // For a *concrete* alignment, also record `term % align == 0` as a
                // path condition.  `align_n` is a value invariant that pointer
                // arithmetic (`ptr.add(n)`) drops, but the alignment fact itself
                // persists: a downstream `Align(p, T)` on `p = ptr.add(n)` can then
                // combine `term % align == 0` with the `n % align == 0` mask fact to
                // prove `p % align == 0`.  (A symbolic `align_T` is skipped — the
                // non-linear `% align_T` is not decidable, so `align_n` alone is
                // used for that case.)
                if align_u64.is_some() {
                    self.constraints
                        .assertions
                        .push(val.z3_term.rem(&align)._eq(&Int::from_u64(self.z3_ctx, 0)));
                }
            }
        }
        self.set_contract_target_value(property, val);
    }

    /// Set init invariant on the target value and its allocation.
    fn set_init_for_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
        // `Init(p, MaybeUninit<T>, n)` reduces to `Typed(p, MaybeUninit<T>)`: the
        // content carries no validity invariant, so there is nothing to mark
        // initialized — the `Init ⇒ Typed` subsumption records the element type.
        let is_maybe_uninit = property.ty_arg(1)
            .map(api_classify::is_maybe_uninit_ty)
            .unwrap_or(false);
        if is_maybe_uninit {
            return;
        }
        if let Some(prov) = &val.provenance {
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
        if let Some((local, path)) = self.contract_field_path(property) {
            let existing = if path.is_empty() {
                self.local_value(local).cloned()
            } else {
                self.field_value(local, &path).cloned()
            };
            if let Some(mut existing) = existing {
                self.mark_initialized(&mut existing);
                if path.is_empty() {
                    self.set_local(local, existing);
                } else {
                    self.set_field_value(local, path, existing);
                }
            }
        }
    }

    /// Set owning invariant on the target value.
    fn set_owning_for_value(&mut self, val: VmValue<'z3, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.alloc_mut(prov.alloc_id).facts.owning = Some(val.z3_term.clone());
            self.content_mut(prov.alloc_id).facts.initialized = true;
        }
    }

    fn for_each_target_alloc(&self, property: &Property<'tcx>) -> Option<AllocId> {
        property.for_each()?;
        self.contract_target_value(property)?.provenance_alloc_id()
    }

    /// Record the `Align(container.iter(), T)` for_each fact: every element
    /// pointer is aligned to `align_of(T)`.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Align(cur, T)`.
    fn record_for_each_align(&mut self, property: &Property<'tcx>) {
        let Some(ty) = property.ty_arg(1) else {
            return;
        };
        let Some(alloc_id) = self.for_each_target_alloc(property) else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.aligned_ty = Some(ty);
    }

    /// Record the `Allocated(container.iter(), T, n)` for_each fact: every
    /// element pointer backs `>= n` `T` elements (`n` may be symbolic).
    fn record_for_each_allocated(&mut self, property: &Property<'tcx>) {
        let Some(ty) = property.ty_arg(1) else {
            return;
        };
        let count = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a))
            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
        let Some(alloc_id) = self.for_each_target_alloc(property) else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.allocated = Some((ty, count));
    }

    /// Record the `Owning(container.iter())` for_each fact: every element
    /// pointer is the sole owner of its pointee.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Owning(cur)`.
    fn record_for_each_owning(&mut self, property: &Property<'tcx>) {
        let Some(alloc_id) = self.for_each_target_alloc(property) else {
            return;
        };
        self.alloc_mut(alloc_id).facts.for_each.owning = true;
    }
}

fn index_access_locals(property: &Property<'_>) -> Option<(Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::InBound {
        return None;
    }
    let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) = atom.args.first()
    else { return None };
    let (ContractExpr::Place(slice), ContractExpr::Place(index)) = (slice.as_ref(), index.as_ref())
    else { return None };
    (slice.projections.is_empty() && index.projections.is_empty())
        .then(|| (slice.base.to_local(), index.base.to_local()))
}

fn slice_offset_locals(property: &Property<'_>) -> Option<(Local, Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::SliceOffset {
        return None;
    }
    let locals: Option<Vec<Local>> = atom.args.iter().map(|arg| {
        let PropertyArg::Expr(ContractExpr::Place(place)) = arg else { return None };
        place.projections.is_empty().then(|| place.base.to_local())
    }).collect();
    let locals = locals?;
    let [dest, base, index] = locals.as_slice() else { return None };
    Some((*dest, *base, *index))
}

fn bind_call_property<'tcx>(
    property: &mut Property<'tcx>,
    args: &[Option<Local>],
    destination: Local,
) -> bool {
    let mut bound = true;
    map_property_places(property, &mut |place| {
        let local = match place.base {
            PlaceBase::Return | PlaceBase::Local(0) => Some(destination),
            PlaceBase::Arg(index) => args.get(index).copied().flatten(),
            PlaceBase::Local(index) => args.get(index - 1).copied().flatten(),
        };
        if let Some(local) = local {
            place.base = PlaceBase::Local(local.as_usize());
        } else {
            bound = false;
        }
    });
    bound
}

/// Rebind every `self` place in a struct invariant to the given MIR local, so
/// an invariant parsed against the struct's own `self` can be asserted on a
/// freshly-created reference (`&*NonNull<T>` → `&T`).
fn rebind_property_place<'tcx>(property: &mut Property<'tcx>, local: Local) {
    map_property_places(property, &mut |place| {
        place.base = PlaceBase::Local(local.as_usize());
    });
}

fn map_property_places<'tcx>(
    property: &mut Property<'tcx>,
    map: &mut impl FnMut(&mut ContractPlace<'tcx>),
) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                match arg {
                    PropertyArg::Expr(expr) => map_expr_places(expr, map),
                    PropertyArg::Predicates(preds) => {
                        for pred in preds {
                            map_expr_places(&mut pred.lhs, map);
                            map_expr_places(&mut pred.rhs, map);
                        }
                    }
                    _ => {}
                }
            }
            if let Some(place) = &mut atom.for_each {
                map(place);
            }
        }
        Property::And(and) => {
            for c in &mut and.conjuncts {
                map_property_places(c, map);
            }
        }
        Property::Or(or) => {
            for d in &mut or.disjuncts {
                map_property_places(d, map);
            }
        }
    }
}

fn map_expr_places<'tcx>(
    expr: &mut ContractExpr<'tcx>,
    map: &mut impl FnMut(&mut ContractPlace<'tcx>),
) {
    match expr {
        ContractExpr::Place(cp) => map(cp),
        ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
            map_expr_places(inner, map)
        }
        ContractExpr::IndexAccess { slice, index } => {
            map_expr_places(slice, map);
            map_expr_places(index, map);
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            map_expr_places(lhs, map);
            map_expr_places(rhs, map);
        }
        ContractExpr::Unary { expr: inner, .. } => map_expr_places(inner, map),
        ContractExpr::MethodCall { receiver, args, .. } => {
            map_expr_places(receiver, map);
            for arg in args {
                map_expr_places(arg, map);
            }
        }
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            map_expr_places(&mut cond.lhs, map);
            map_expr_places(&mut cond.rhs, map);
            map_expr_places(then_expr, map);
            map_expr_places(else_expr, map);
        }
        _ => {}
    }
}
