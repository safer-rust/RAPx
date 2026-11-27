//! Read-only queries over the symbolic VM state used by property checks.

use crate::contract::{ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property};
use crate::def_ids::type_ids;
use crate::util::mir_utils;
use crate::verify::checkpoint::Checkpoint;
use crate::vm::state::{AllocId, AllocBoundFact, OffsetKind, VmExecutor, VmValue};
use rustc_middle::{
    mir::{Local, Operand},
    ty::{Ty, TyKind},
};
use z3::ast::{Ast, Int};

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// Resolve a property's target using the checkpoint's call arguments.
    pub(crate) fn callsite_contract_target_value(&self, args: &[Operand<'tcx>], property: &Property<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let place = match property.args().first()?.expr()? {
            ContractExpr::Const(index) => ContractPlace { base: PlaceBase::Arg(usize::try_from(*index).ok()?), projections: vec![] },
            ContractExpr::Place(place) => place.clone(),
            ContractExpr::IndexAccess { slice, .. } => match slice.as_ref() {
                ContractExpr::Place(place) => place.clone(),
                _ => return None,
            },
            _ => return None,
        };
        self.callsite_contract_place_value(args, &place)
    }

    fn callsite_contract_place_value(&self, args: &[Operand<'tcx>], place: &ContractPlace) -> Option<VmValue<'z3, 'tcx>> {
        if place.projections.is_empty() {
            return match place.base {
                PlaceBase::Return => self.local_value(Local::from_usize(0)).cloned(),
                PlaceBase::Arg(index) => args.get(index).map(|arg| self.value_of_operand(arg)),
                PlaceBase::Local(index) => self.local_value(Local::from_usize(index)).cloned(),
            };
        }
        let local = match place.base {
            PlaceBase::Return => Local::from_usize(0),
            PlaceBase::Arg(index) => match args.get(index)? {
                Operand::Copy(operand_place) | Operand::Move(operand_place) => operand_place.local,
                _ => return None,
            },
            PlaceBase::Local(index) => Local::from_usize(index),
        };
        let mut fields = Vec::new();
        for projection in &place.projections {
            match projection {
                ContractProjection::Field { index } => fields.push(*index),
                ContractProjection::Downcast { variant_index } => {
                    let base_value = self.field_value(local, &fields).cloned().or_else(|| self.local_value(local).cloned())?;
                    let enum_ty = if fields.is_empty() {
                        base_value.ty
                    } else {
                        let root_ty = match place.base {
                            PlaceBase::Arg(index) => match args.get(index)? {
                                Operand::Copy(operand_place) | Operand::Move(operand_place) => operand_place.ty(self.body(), self.tcx).ty,
                                _ => return None,
                            },
                            _ => self.body().local_decls[local].ty,
                        };
                        mir_utils::projected_field_ty(self.tcx, root_ty, &fields).unwrap_or(base_value.ty)
                    };
                    let inner_ty = match enum_ty.kind() {
                        TyKind::Adt(adt, substs) if adt.is_enum() => {
                            let variant = &adt.variants()[rustc_abi::VariantIdx::from_usize(*variant_index)];
                            if variant.fields.is_empty() {
                                None
                            } else {
                                Some(mir_utils::field_ty(self.tcx, &variant.fields[rustc_abi::FieldIdx::from_usize(0)], substs))
                            }
                        }
                        _ => None,
                    }.unwrap_or(base_value.ty);
                    return Some(VmValue {
                        z3_term: base_value.z3_term,
                        ty: inner_ty,
                        provenance: base_value.provenance,
                        facts: base_value.facts,
                        source: base_value.source.field_offset_only(),
                    });
                }
                ContractProjection::ForEach => {
                    if let Some(value) = self.field_value(local, &fields) {
                        return Some(value.clone());
                    }
                    if let Some(base_value) = self.local_value(local) && base_value.has_provenance() {
                        return Some(VmValue {
                            z3_term: base_value.z3_term.clone(),
                            ty: base_value.ty,
                            provenance: base_value.provenance.clone(),
                            facts: base_value.facts.clone(),
                            source: base_value.source.field_offset_only(),
                        });
                    }
                    return None;
                }
            }
        }
        if let Some(value) = self.field_value(local, &fields) {
            return Some(value.clone());
        }
        if !fields.is_empty() && local == Local::from_usize(0) {
            for block in self.body().basic_blocks.iter() {
                for statement in &block.statements {
                    if let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind {
                        let (target, value) = &**assign;
                        if let rustc_middle::mir::Rvalue::Aggregate(_, operands) = value
                            && target.local == local
                            && let Some(operand) = operands.get(rustc_abi::FieldIdx::from_usize(fields[0]))
                            && fields.len() == 1
                        {
                            return Some(self.value_of_operand(operand));
                        }
                    }
                }
            }
        }
        if let Some(base_value) = self.local_value(local) && let Some(provenance) = &base_value.provenance {
            return Some(VmValue {
                z3_term: base_value.z3_term.clone(),
                ty: base_value.ty,
                provenance: Some(provenance.clone()),
                facts: base_value.facts.clone(),
                source: base_value.source.field_offset_only(),
            });
        }
        None
    }

    pub(crate) fn has_bounded_object_span(
        &self,
        alloc_id: AllocId,
        value: &VmValue<'z3, 'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        self.bounded_span(value, ty)
            .is_some_and(|span| self.alloc(alloc_id).bounds.contains(&span))
    }

    pub(crate) fn has_bounded_range(
        &self,
        alloc_id: AllocId,
        address: &Int<'z3>,
        bytes: &Int<'z3>,
    ) -> bool {
        let ranges = &self.alloc(alloc_id).bounds;
        if ranges.is_empty() {
            return false;
        }
        let solver = z3::Solver::new(self.z3_ctx);
        self.assert_path_constraints(&solver);
        let end = Int::add(self.z3_ctx, &[address, bytes]);
        ranges.iter().any(|bound| {
            let AllocBoundFact::Bytes { address: start, size } = bound else {
                return false;
            };
            let limit = Int::add(self.z3_ctx, &[start, size]);
            let covered = z3::ast::Bool::and(
                self.z3_ctx,
                &[
                    &address.ge(start),
                    &address.le(&limit),
                    &end.ge(start),
                    &end.le(&limit),
                ],
            );
            solver.push();
            // A recorded byte range has nonnegative length, including when
            // its usize count is no longer a live local in this frame.
            solver.assert(&size.ge(&Int::from_u64(self.z3_ctx, 0)));
            solver.assert(&covered.not());
            let proved = crate::vm::integer_solver::check(&solver) == z3::SatResult::Unsat;
            solver.pop(1);
            proved
        })
    }

    pub(crate) fn callsite_operand_for_local<'a>(
        &self,
        checkpoint: &'a Checkpoint<'tcx>,
        local: usize,
    ) -> Option<&'a Operand<'tcx>> {
        let callee = checkpoint.callee?;
        let index = mir_utils::callee_param_index_for_local(self.tcx, callee, local)?;
        checkpoint.args.get(index)
    }

    /// Bind a contract place to a term at this checkpoint. A callee parameter
    /// local refers to its callsite operand when one is available.
    pub(crate) fn contract_place_term_at(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        place: &ContractPlace,
    ) -> Option<Int<'z3>> {
        if !place.projections.is_empty() {
            let fields = place.plain_field_path()?;
            let local = match place.base {
                PlaceBase::Arg(index) => checkpoint.args.get(index)?.place()?.local,
                PlaceBase::Local(index) => self
                    .callsite_operand_for_local(checkpoint, index)
                    .and_then(|operand| operand.place())
                    .map(|place| place.local)
                    .unwrap_or(Local::from_usize(index)),
                PlaceBase::Return => Local::from_usize(0),
            };
            return self
                .field_value(local, &fields)
                .map(|value| value.z3_term.clone());
        }
        match place.base {
            PlaceBase::Arg(index) => checkpoint
                .args
                .get(index)
                .map(|operand| self.value_of_operand(operand).z3_term),
            PlaceBase::Local(index) => {
                let operand = self.callsite_operand_for_local(checkpoint, index);
                if let Some(operand) = operand {
                    Some(self.value_of_operand(operand).z3_term)
                } else {
                    self.local_value(Local::from_usize(index))
                        .map(|value| value.z3_term.clone())
                }
            }
            PlaceBase::Return => None,
        }
    }

    /// Penetrate a reference/raw-pointer target down to the owned heap behind
    /// it.  A target like `&mut ManuallyDrop<Box<T>>` or `*mut Box<T>` carries
    /// the *stack* provenance of the referent; the properties that matter
    /// (`Allocated`/`Owning`/`ValidPtr`) concern the heap object inside, so
    /// resolve through the referent local's owned heap field.
    pub(crate) fn resolve_pointer_provenance(
        &self,
        mut value: VmValue<'z3, 'tcx>,
    ) -> VmValue<'z3, 'tcx> {
        if matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Ref(..) | rustc_middle::ty::TyKind::RawPtr(..)
        ) && let Some(owner) = self.find_local_by_address(&value.z3_term)
            && let Some(heap_field) = self.owner_ptr_field(owner)
            && heap_field.has_provenance()
        {
            value.z3_term = heap_field.z3_term.clone();
            value.provenance = heap_field.provenance.clone();
            value.facts = heap_field.facts.clone();
        }
        value
    }

    /// Whether `value` has tracked alignment or sits at a base with known alignment above 1.
    pub(crate) fn is_value_aligned(&self, value: &VmValue<'z3, 'tcx>) -> bool {
        value.facts.align_n.is_some()
            || value.provenance.as_ref().is_some_and(|p| {
                p.offset.simplify().as_u64() == Some(0)
                    && self.alloc(p.alloc_id).align.simplify().as_u64().is_some_and(|align| align > 1)
            })
    }

    /// Whether `value` is a `MaybeUninit`-typed pointer access into `alloc_id`.
    ///
    /// `assume_init_drop` / `as_mut_ptr` (and friends) legitimately consume an
    /// initialized element from storage that may be going out of scope, so the
    /// `Init`/`Allocated` requirement concerns the write, not the allocation's
    /// live/dead flag.
    pub(crate) fn is_maybe_uninit_ptr(
        &self,
        value: &VmValue<'z3, 'tcx>,
        alloc_id: AllocId,
    ) -> bool {
        value.facts.init
            && value.facts.non_null
            && self.is_value_aligned(value)
            && (matches!(value.ty.kind(), TyKind::RawPtr(..))
                || matches!(value.ty.kind(), TyKind::Ref(_, inner, _)
                    if matches!(inner.kind(), TyKind::Adt(adt, _)
                        if type_ids::is_maybe_uninit_type(adt.did()))))
            && {
                let a = self.alloc(alloc_id);
                !a.is_raw_storage()
                    && a.element_ty.as_ty().is_some_and(|ty| {
                        if let TyKind::Adt(adt, _) = ty.kind() {
                            type_ids::is_maybe_uninit_type(adt.did())
                        } else {
                            false
                        }
                    })
            }
    }

    /// Element count of one object when the access is to an unsized `[T]`:
    /// the slice length from the pointer's metadata. An unknown length stays
    /// unknown. Other objects return `None`.
    pub(crate) fn unsized_slice_len(
        &self,
        value: &VmValue<'z3, 'tcx>,
        required_ty: Option<Ty<'tcx>>,
    ) -> Option<Int<'z3>> {
        let accessed = required_ty
            .filter(|ty| !matches!(ty.kind(), TyKind::Alias(..)))
            .or_else(|| mir_utils::pointee_ty(value.ty))?;
        if !matches!(accessed.kind(), TyKind::Slice(_)) {
            return None;
        }
        Some(
            self.slice_len_from_value(value)
                .unwrap_or_else(|| self.fresh_int("slice_access_len")),
        )
    }

    /// Byte span requested by a pointer property, using the VM's element-size
    /// model for concrete and generic pointee types.
    pub(crate) fn access_bytes(
        &self,
        value: &VmValue<'z3, 'tcx>,
        required_ty: Option<Ty<'tcx>>,
        count: Int<'z3>,
    ) -> Int<'z3> {
        let elem_ty = required_ty
            .filter(|ty| self.size_of_ty(*ty) > 0)
            .or_else(|| {
                mir_utils::pointee_ty(value.ty).map(|ty| match ty.kind() {
                    TyKind::Slice(elem) | TyKind::Array(elem, _) => *elem,
                    _ => ty,
                })
            });
        let elem_size = elem_ty
            .map(|ty| self.size_sym_read(ty))
            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
        let count = match self.unsized_slice_len(value, required_ty) {
            Some(len) => Int::mul(self.z3_ctx, &[&count, &len]),
            None => count,
        };
        if let (Some(elem), Some(count)) =
            (elem_size.simplify().as_u64(), count.simplify().as_u64())
        {
            if let Some(bytes) = elem.max(1).checked_mul(count.max(1)) {
                return Int::from_u64(self.z3_ctx, bytes);
            }
        }
        Int::mul(self.z3_ctx, &[&elem_size, &count])
    }

    /// Whether this atom's target or a checkpoint argument depends on an
    /// unconstrained value introduced by incomplete inlining.
    pub(crate) fn atom_depends_on_inline_terms(
        &self,
        checkpoint: &Checkpoint<'tcx>,
        property: &Property<'tcx>,
        terms: &rustc_hash::FxHashSet<Int<'z3>>,
    ) -> bool {
        if terms.is_empty() {
            return false;
        }
        for operand in &checkpoint.args {
            if self.value_involves_terms(terms, &self.value_of_operand(operand)) {
                return true;
            }
        }
        if let Some(value) = self.callsite_contract_target_value(&checkpoint.args, property)
            && self.value_involves_terms(terms, &value)
        {
            return true;
        }
        false
    }

    fn value_involves_terms(
        &self,
        terms: &rustc_hash::FxHashSet<Int<'z3>>,
        value: &VmValue<'z3, 'tcx>,
    ) -> bool {
        if VmExecutor::term_involves(terms, &value.z3_term) {
            return true;
        }
        value.provenance.as_ref().is_some_and(|p| {
            VmExecutor::term_involves(terms, &p.offset)
                || matches!(
                    &p.offset_kind,
                    Some(OffsetKind::Element { index, .. }) if VmExecutor::term_involves(terms, index)
                )
        })
    }
}
