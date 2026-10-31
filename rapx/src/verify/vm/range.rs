//! Range indexing and range effects in the symbolic VM.

use rustc_middle::mir::Local;
use rustc_middle::ty::TyKind;
use z3::ast::{Ast, Bool, Int};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn try_simulate_builtin_index(
        &mut self,
        callee: Option<rustc_hir::def_id::DefId>,
        args: &[VmValue<'z3, 'tcx>],
        arg_locals: &[Option<Local>],
        dest: Local,
    ) -> bool {
        use crate::def_ids::lang_api::{self, LangItem};

        let Some(callee) = callee else {
            return false;
        };
        let Some(trait_id) = self.tcx.trait_of_assoc(callee) else {
            return false;
        };
        if !lang_api::matches(self.tcx, trait_id, LangItem::Index)
            && !lang_api::matches(self.tcx, trait_id, LangItem::IndexMut)
        {
            return false;
        }
        let [base, index] = args else {
            return false;
        };
        let TyKind::Ref(_, base_pointee, _) = base.ty.kind() else {
            return false;
        };
        let (TyKind::Array(_, _) | TyKind::Slice(_)) = base_pointee.kind() else {
            return false;
        };
        let TyKind::Ref(..) = self.body().local_decls[dest].ty.kind() else {
            return false;
        };
        let is_scalar = matches!(index.ty.kind(), TyKind::Uint(rustc_middle::ty::UintTy::Usize));
        let Some(index_local) = arg_locals.get(1).copied().flatten() else {
            return false;
        };
        let Some(start) = self.slice_index_start(index, index_local) else {
            return false;
        };
        let Some(base_len) = self.slice_len_from_value(base) else {
            return false;
        };
        let output_len = if is_scalar {
            None
        } else {
            let Some(len) = self.slice_index_output_len(base, index, index_local) else {
                return false;
            };
            Some(len)
        };
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(start.ge(&zero));
        if let Some(len) = output_len {
            self.constraints.assertions.push(len.ge(&zero));
            self.constraints.assertions.push((&start + &len).le(&base_len));
            self.apply_slice_offset(dest, base, index, index_local);
            if let Some(mut value) = self.local_value(dest).cloned() {
                value.source = ValueSource::SliceLen(len);
                self.set_local(dest, value);
            }
            self.materialize_slice_ref_return(dest);
        } else {
            self.constraints.assertions.push(start.lt(&base_len));
            self.apply_slice_offset(dest, base, index, index_local);
        }
        true
    }

    pub(crate) fn slice_index_start(
        &self,
        index: &VmValue<'z3, 'tcx>,
        index_local: Local,
    ) -> Option<Int<'z3>> {
        let start_field = || {
            self.field_value(index_local, &[0])
                .map(|value| value.z3_term.clone())
        };
        match index.ty.kind() {
            TyKind::Uint(rustc_middle::ty::UintTy::Usize) => Some(index.z3_term.clone()),
            TyKind::Adt(def, _) => match mir_utils::range_kind(self.tcx, def.did()) {
                mir_utils::RangeKind::RangeTo => Some(Int::from_u64(self.z3_ctx, 0)),
                mir_utils::RangeKind::RangeFrom
                | mir_utils::RangeKind::Range
                | mir_utils::RangeKind::RangeInclusive => start_field(),
                mir_utils::RangeKind::Other => {
                    use crate::def_ids::lang_api::{self, LangItem};
                    if api_classify::is_index_range(def.did()) {
                        start_field()
                    } else {
                        (lang_api::matches(self.tcx, def.did(), LangItem::RangeToInclusive)
                            || lang_api::matches(self.tcx, def.did(), LangItem::RangeFull))
                        .then(|| Int::from_u64(self.z3_ctx, 0))
                    }
                }
            },
            _ => None,
        }
    }

    pub(crate) fn slice_index_output_len(
        &self,
        base: &VmValue<'z3, 'tcx>,
        index: &VmValue<'z3, 'tcx>,
        index_local: Local,
    ) -> Option<Int<'z3>> {
        let TyKind::Adt(def, _) = index.ty.kind() else {
            return None;
        };
        let start = self.slice_index_start(index, index_local)?;
        let one = Int::from_u64(self.z3_ctx, 1);
        let end = match mir_utils::range_kind(self.tcx, def.did()) {
            mir_utils::RangeKind::Range => self.field_value(index_local, &[1])?.z3_term.clone(),
            mir_utils::RangeKind::RangeInclusive => {
                self.field_value(index_local, &[1])?.z3_term.clone() + &one
            }
            mir_utils::RangeKind::RangeTo => self.field_value(index_local, &[0])?.z3_term.clone(),
            mir_utils::RangeKind::RangeFrom => self.slice_len_from_value(base)?,
            mir_utils::RangeKind::Other if api_classify::is_index_range(def.did()) => {
                self.field_value(index_local, &[1])?.z3_term.clone()
            }
            mir_utils::RangeKind::Other => {
                use crate::def_ids::lang_api::{self, LangItem};
                if lang_api::matches(self.tcx, def.did(), LangItem::RangeToInclusive) {
                    self.field_value(index_local, &[0])?.z3_term.clone() + &one
                } else if lang_api::matches(self.tcx, def.did(), LangItem::RangeFull) {
                    self.slice_len_from_value(base)?
                } else {
                    return None;
                }
            }
        };
        Some(end - &start)
    }

    pub(crate) fn apply_slice_offset(
        &mut self,
        dest: Local,
        base: &VmValue<'z3, 'tcx>,
        index: &VmValue<'z3, 'tcx>,
        index_local: Local,
    ) -> bool {
        let start = if let Some(start) = self.slice_index_start(index, index_local) {
            start
        } else {
            let Some(len) = self.slice_len_from_value(base) else {
                return false;
            };
            let start = self.fresh_int("slice_offset_index");
            let zero = Int::from_u64(self.z3_ctx, 0);
            self.constraints.assertions.push(start.ge(&zero));
            let dest_ty = self.body().local_decls[dest].ty;
            let is_slice = mir_utils::pointee_ty(dest_ty)
                .is_some_and(|ty| matches!(ty.kind(), TyKind::Slice(_) | TyKind::Str));
            self.constraints.assertions.push(if is_slice {
                start.le(&len)
            } else {
                start.lt(&len)
            });
            start
        };
        let offset = VmValue::new(start, self.tcx.types.usize);
        self.apply_pointer_add(dest, base, &offset, None, base.facts.in_bounds);
        true
    }

    pub(crate) fn apply_range_next_effect(&mut self, args: &[VmValue<'z3, 'tcx>], dest: Local) {
        if args.is_empty() {
            return;
        }
        let self_val = &args[0];
        let TyKind::Ref(_, pointee, _) = self_val.ty.kind() else {
            return;
        };
        let TyKind::Adt(adt_def, _) = pointee.kind() else {
            return;
        };
        let Some(alloc_id) = self_val.provenance_alloc_id() else {
            return;
        };
        let range_view_ty = self.units[alloc_id.0]
            .content
            .values
            .keys()
            .map(|(t, _)| *t)
            .find(|t| matches!(t.kind(), TyKind::Adt(adt, _) if adt.did() == adt_def.did()));
        let Some(range_view_ty) = range_view_ty else {
            return;
        };
        let Some(start) = self.load_value(alloc_id, range_view_ty, &[0]).cloned() else {
            return;
        };
        let Some(end) = self.load_value(alloc_id, range_view_ty, &[1]).cloned() else {
            return;
        };
        let dest_ty = self.body().local_decls[dest].ty;
        let zero = Int::from_u64(self.z3_ctx, 0);
        let one = Int::from_u64(self.z3_ctx, 1);
        let start_term = start.z3_term.clone();
        let end_term = end.z3_term.clone();
        let inclusive = matches!(
            mir_utils::range_kind(self.tcx, adt_def.did()),
            mir_utils::RangeKind::RangeInclusive
        );
        let is_empty = if inclusive {
            let exhausted = self
                .load_value(alloc_id, range_view_ty, &[2])
                .map(|value| value.z3_term._eq(&one))
                .unwrap_or_else(|| {
                    let term = self.fresh_int("range_inclusive_exhausted");
                    self.constraints.assertions.push(Bool::or(
                        self.z3_ctx,
                        &[&term._eq(&zero), &term._eq(&one)],
                    ));
                    term._eq(&one)
                });
            Bool::or(self.z3_ctx, &[&start_term.gt(&end_term), &exhausted])
        } else {
            start_term.ge(&end_term)
        };
        let result_val = VmValue {
            z3_term: is_empty.ite(&zero, &start_term),
            ty: dest_ty,
            provenance: None,
            facts: ValueFacts::default(),
            source: ValueSource::Discriminant(is_empty.ite(&zero, &one)),
        };
        self.set_local(dest, result_val);
        self.set_field_value(dest, vec![0], start.clone());
        let mut advanced = start;
        let next = Int::add(self.z3_ctx, &[&start_term, &one]);
        if inclusive {
            let last = start_term.ge(&end_term);
            let exhausted = Bool::or(self.z3_ctx, &[&is_empty, &last]);
            self.store_value(
                alloc_id,
                range_view_ty,
                vec![2],
                VmValue::new(exhausted.ite(&one, &zero), self.tcx.types.bool),
            );
            advanced.z3_term = exhausted.ite(&start_term, &next);
        } else {
            advanced.z3_term = is_empty.ite(&start_term, &next);
        }
        self.store_value(alloc_id, range_view_ty, vec![0], advanced);
    }
}
