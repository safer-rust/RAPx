//! Read-only queries over the symbolic VM state used by property checks.

use crate::helpers::mir_utils;
use crate::verify::api_classify;
use crate::verify::checkpoint::Checkpoint;
use crate::verify::contract::{
    ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, PropertyArg,
};
use rustc_middle::{
    mir::{Local, Operand},
    ty::{Ty, TyKind},
};
use z3::ast::{Ast, Int};

use super::state::{AllocId, OffsetKind, VmState, VmValue};

#[derive(Clone, Copy)]
pub(crate) enum ContractTargetContext<'a, 'tcx> {
    Bound,
    Callsite(&'a Checkpoint<'tcx>),
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    fn bound_field_value(&self, local: Local, path: &[usize]) -> Option<VmValue<'z3, 'tcx>> {
        if path.is_empty() {
            self.local_value(local).cloned()
        } else {
            self.field_value(local, path).cloned()
        }
    }

    pub(crate) fn has_bounded_object_span(
        &self,
        alloc_id: AllocId,
        address: &Int<'z3>,
        ty: Ty<'tcx>,
    ) -> bool {
        self.alloc(alloc_id)
            .facts
            .bounded_spans
            .contains(&(address.clone(), ty))
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
        place: &ContractPlace<'tcx>,
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

    /// Resolve a property's target in its contract binding context.
    pub(crate) fn contract_target_value_at(
        &self,
        context: ContractTargetContext<'_, 'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Const(n)) => {
                let idx = usize::try_from(*n).ok()?;
                crate::verify::contract::ContractPlace {
                    base: PlaceBase::Arg(idx),
                    projections: vec![],
                }
            }
            PropertyArg::Predicates(_) | PropertyArg::Ty(_) | PropertyArg::Ident(_) => return None,
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(cp) => cp.clone(),
                _ => return None,
            },
            _ => return None,
        };
        self.contract_place_value_at(context, &cp)
    }

    /// Resolve a contract place with the same binding context as
    /// [`Self::contract_target_value_at`].
    pub(crate) fn contract_place_value_at(
        &self,
        context: ContractTargetContext<'_, 'tcx>,
        cp: &ContractPlace<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let checkpoint = match context {
            ContractTargetContext::Bound => None,
            ContractTargetContext::Callsite(checkpoint) => Some(checkpoint),
        };
        if cp.projections.is_empty() {
            return match cp.base {
                PlaceBase::Return => self.local_value(Local::from_usize(0)).cloned(),
                PlaceBase::Arg(n) => match checkpoint {
                    Some(checkpoint) => checkpoint.args.get(n).map(|op| self.value_of_operand(op)),
                    None => self.local_value(cp.base.to_local()).cloned(),
                },
                PlaceBase::Local(n) => self.local_value(Local::from_usize(n)).cloned(),
            };
        }
        let base_local = match cp.base {
            PlaceBase::Return => Local::from_usize(0),
            PlaceBase::Arg(n) if checkpoint.is_some() => {
                let checkpoint = checkpoint?;
                let operand = checkpoint.args.get(n)?;
                match operand {
                    Operand::Copy(place) | Operand::Move(place) => place.local,
                    _ => return None,
                }
            }
            PlaceBase::Arg(_) => cp.base.to_local(),
            PlaceBase::Local(n) => Local::from_usize(n),
        };
        let mut field_path: Vec<usize> = Vec::new();
        let mut last_field_ty: Option<Ty<'tcx>> = None;

        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index, ty } => {
                    field_path.push(*index);
                    last_field_ty = *ty;
                }
                ContractProjection::Downcast { variant_index } => {
                    if checkpoint.is_none() {
                        return self.bound_field_value(base_local, &field_path);
                    }
                    let base_val = self
                        .field_value(base_local, &field_path)
                        .cloned()
                        .or_else(|| self.local_value(base_local).cloned());
                    let base_val = base_val?;

                    let enum_ty = last_field_ty.unwrap_or(base_val.ty);
                    let inner_ty = match enum_ty.kind() {
                        TyKind::Adt(adt_def, substs) => {
                            if adt_def.is_enum() {
                                let variant = &adt_def.variants()
                                    [rustc_abi::VariantIdx::from_usize(*variant_index)];
                                if !variant.fields.is_empty() {
                                    Some(mir_utils::field_ty(
                                        self.tcx,
                                        &variant.fields[rustc_abi::FieldIdx::from_usize(0)],
                                        substs,
                                    ))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    let inner_ty = inner_ty.unwrap_or(base_val.ty);

                    return Some(VmValue {
                        z3_term: base_val.z3_term.clone(),
                        ty: inner_ty,
                        provenance: base_val.provenance.clone(),
                        facts: base_val.facts,
                        source: base_val.source.field_offset_only(),
                    });
                }
                ContractProjection::ForEach => {
                    if checkpoint.is_none() {
                        return self.bound_field_value(base_local, &field_path);
                    }
                    if let Some(val) = self.field_value(base_local, &field_path) {
                        return Some(val.clone());
                    }
                    if let Some(base_val) = self.local_value(base_local)
                        && base_val.is_pointer()
                    {
                        return Some(VmValue {
                            z3_term: base_val.z3_term.clone(),
                            ty: base_val.ty,
                            provenance: base_val.provenance.clone(),
                            facts: base_val.facts.clone(),
                            source: base_val.source.field_offset_only(),
                        });
                    }
                    return None;
                }
            }
        }

        if let Some(val) = self.field_value(base_local, &field_path) {
            return Some(val.clone());
        }
        if checkpoint.is_none() {
            return None;
        }
        if !field_path.is_empty() && base_local == Local::from_usize(0) {
            for bb in self.body().basic_blocks.iter() {
                for stmt in &bb.statements {
                    if let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind {
                        let (ref place, ref rval) = **assign;
                        if let rustc_middle::mir::Rvalue::Aggregate(_, operands) = rval
                            && place.local == base_local
                            && let Some(operand) =
                                operands.get(rustc_abi::FieldIdx::from_usize(field_path[0]))
                        {
                            let val = self.value_of_operand(operand);
                            if field_path.len() == 1 {
                                return Some(val);
                            }
                        }
                    }
                }
            }
        }
        if let Some(base_val) = self.local_value(base_local)
            && let Some(ref prov) = base_val.provenance
        {
            return Some(VmValue {
                z3_term: base_val.z3_term.clone(),
                ty: base_val.ty,
                provenance: Some(prov.clone()),
                facts: base_val.facts.clone(),
                source: base_val.source.field_offset_only(),
            });
        }
        None
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
            && heap_field.is_pointer()
        {
            value.z3_term = heap_field.z3_term.clone();
            value.provenance = heap_field.provenance.clone();
            value.facts = heap_field.facts.clone();
        }
        value
    }

    /// Whether `value` is known to be aligned: either `align_n` carries a
    /// concrete alignment, or the value sits at the base of an allocation whose
    /// `align` is not 1.
    pub(crate) fn is_value_aligned(&self, value: &VmValue<'z3, 'tcx>) -> bool {
        value.facts.align_n.is_some()
            || value.provenance.as_ref().is_some_and(|p| {
                p.offset_kind.is_none()
                    && self.alloc(p.alloc_id).align.simplify().as_u64() != Some(1)
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
                        if api_classify::is_maybe_uninit_type(adt.did()))))
            && {
                let a = self.alloc(alloc_id);
                !a.is_external()
                    && a.element_ty.as_ty().is_some_and(|ty| {
                        if let TyKind::Adt(adt, _) = ty.kind() {
                            api_classify::is_maybe_uninit_type(adt.did())
                        } else {
                            false
                        }
                    })
            }
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
        if let Some(value) =
            self.contract_target_value_at(ContractTargetContext::Callsite(checkpoint), property)
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
        if VmState::term_involves(terms, &value.z3_term) {
            return true;
        }
        value.provenance.as_ref().is_some_and(|p| {
            VmState::term_involves(terms, &p.offset)
                || matches!(
                    &p.offset_kind,
                    Some(OffsetKind::Element { index, .. }) if VmState::term_involves(terms, index)
                )
        })
    }
}
