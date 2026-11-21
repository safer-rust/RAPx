//! Contract-place lookup against VM locals or call arguments.

use crate::contract::{
    ContractExpr, ContractPlace, ContractProjection, PlaceBase, Property, place::projected_field_ty,
};
use crate::util::mir_utils;
use crate::vm::{VmExecutor, state::VmValue};
use rustc_middle::mir::{Local, Operand};
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::Int;

#[derive(Clone, Copy)]
pub(crate) enum ContractTargetContext<'a, 'tcx> {
    Bound,
    Callsite(&'a [Operand<'tcx>]),
}

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// The key of a bounded span. A slice or `str` also needs its length, since
    /// the length decides the size of the object; without a known length there
    /// is no span.
    pub(crate) fn bounded_span(
        &self,
        value: &VmValue<'z3, 'tcx>,
        ty: Ty<'tcx>,
    ) -> Option<(Int<'z3>, Ty<'tcx>, Option<Int<'z3>>)> {
        let len = if matches!(ty.kind(), TyKind::Slice(_) | TyKind::Str) {
            Some(self.slice_len_from_value(value)?)
        } else {
            None
        };
        Some((value.z3_term.clone(), ty, len))
    }


    fn bound_field_value(&self, local: Local, path: &[usize]) -> Option<VmValue<'z3, 'tcx>> {
        if path.is_empty() {
            self.local_value(local).cloned()
        } else {
            self.field_value(local, path).cloned()
        }
    }

    /// Resolve a property's target in its contract binding context.
    pub(crate) fn contract_target_value_at(
        &self,
        context: ContractTargetContext<'_, 'tcx>,
        property: &Property<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let cp = match property.args().first()?.expr()? {
            ContractExpr::Const(n) => {
                let idx = usize::try_from(*n).ok()?;
                ContractPlace {
                    base: PlaceBase::Arg(idx),
                    projections: vec![],
                }
            }
            ContractExpr::Place(cp) => cp.clone(),
            ContractExpr::IndexAccess { slice, .. } => match slice.as_ref() {
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
        cp: &ContractPlace,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let call_args = match context {
            ContractTargetContext::Bound => None,
            ContractTargetContext::Callsite(call_args) => Some(call_args),
        };
        if cp.projections.is_empty() {
            return match cp.base {
                PlaceBase::Return => self.local_value(Local::from_usize(0)).cloned(),
                PlaceBase::Arg(n) => match call_args {
                    Some(call_args) => call_args.get(n).map(|op| self.value_of_operand(op)),
                    None => self.local_value(cp.base.to_local()).cloned(),
                },
                PlaceBase::Local(n) => self.local_value(Local::from_usize(n)).cloned(),
            };
        }
        let base_local = match cp.base {
            PlaceBase::Return => Local::from_usize(0),
            PlaceBase::Arg(n) if call_args.is_some() => {
                let call_args = call_args?;
                let operand = call_args.get(n)?;
                match operand {
                    Operand::Copy(place) | Operand::Move(place) => place.local,
                    _ => return None,
                }
            }
            PlaceBase::Arg(_) => cp.base.to_local(),
            PlaceBase::Local(n) => Local::from_usize(n),
        };
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                ContractProjection::Field { index } => field_path.push(*index),
                ContractProjection::Downcast { variant_index } => {
                    if call_args.is_none() {
                        return self.bound_field_value(base_local, &field_path);
                    }
                    let base_val = self
                        .field_value(base_local, &field_path)
                        .cloned()
                        .or_else(|| self.local_value(base_local).cloned());
                    let base_val = base_val?;

                    let enum_ty = if field_path.is_empty() {
                        base_val.ty
                    } else {
                        let root_ty = match cp.base {
                            PlaceBase::Arg(n) => match call_args?.get(n)? {
                                Operand::Copy(place) | Operand::Move(place) => place.ty(self.body(), self.tcx).ty,
                                _ => return None,
                            },
                            _ => self.body().local_decls[base_local].ty,
                        };
                        projected_field_ty(self.tcx, root_ty, &field_path).unwrap_or(base_val.ty)
                    };
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
                    if call_args.is_none() {
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
        if call_args.is_none() {
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

}
