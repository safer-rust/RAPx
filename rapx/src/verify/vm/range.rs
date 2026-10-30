//! Range indexing and range effects in the symbolic VM.

use rustc_middle::mir::Local;
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Bool, Int};

use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
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

    pub(crate) fn apply_range_effect(
        &mut self,
        bounds_arg: usize,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) {
        let dest_ty = self.body().local_decls[dest].ty;
        let TyKind::Adt(adt, substs) = dest_ty.kind() else {
            return;
        };
        let variant = adt.non_enum_variant();
        let field_ty = |idx: usize| -> Ty<'tcx> {
            variant
                .fields
                .iter()
                .nth(idx)
                .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                .unwrap_or(dest_ty)
        };
        let mut len_term = None;
        if let Some(l) = caller_arg_locals.get(bounds_arg).copied().flatten()
            && let Some(fv) = self.field_value(l, &[0])
        {
            len_term = Some(fv.z3_term.clone());
        }
        let len_term = len_term.or_else(|| args.get(bounds_arg).map(|v| v.z3_term.clone()));
        let Some(len_term) = len_term else {
            return;
        };

        let start = self.fresh_int(&format!("range_start_{}", dest.as_usize()));
        let end = self.fresh_int(&format!("range_end_{}", dest.as_usize()));
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(start.ge(&zero));
        self.constraints.assertions.push(start.le(&end));
        self.constraints.assertions.push(end.le(&len_term));

        let start_val = VmValue::new(start, field_ty(0));
        let end_val = VmValue::new(end, field_ty(1));
        self.set_field_value(dest, vec![0], start_val);
        self.set_field_value(dest, vec![1], end_val);
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
    pub(crate) fn apply_slice_range_index_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) {
        if args.len() < 2 {
            return;
        }
        let dest_ty = self.body().local_decls[dest].ty;
        let is_slice = matches!(dest_ty.kind(), TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), TyKind::Slice(_)));
        let range_kind = args.get(1).and_then(|v| match v.ty.kind() {
            TyKind::Adt(adt_def, _) => Some(mir_utils::range_kind(self.tcx, adt_def.did())),
            _ => None,
        });
        if !is_slice && range_kind.is_none() {
            return;
        }
        let Some(prov) = args[0].provenance.clone() else {
            return;
        };
        let array_term = args[0].z3_term.clone();
        let elem_ty = match args[0].ty.kind() {
            TyKind::Ref(_, inner, _) => match inner.kind() {
                TyKind::Array(e, _) | TyKind::Slice(e) => *e,
                _ => args[0].ty,
            },
            _ => args[0].ty,
        };
        let elem_align = self.align_sym(elem_ty);
        let elem_size = self.size_sym(elem_ty);
        let range_local = caller_arg_locals.get(1).copied().flatten();
        let range_field = |idx: usize| -> Option<Int<'z3>> {
            range_local.and_then(|l| self.field_value(l, &[idx]).map(|v| v.z3_term.clone()))
        };
        let zero = Int::from_u64(self.z3_ctx, 0);
        let one = Int::from_u64(self.z3_ctx, 1);
        let total_len = self
            .slice_len_of_alloc(prov.alloc_id)
            .unwrap_or_else(|| self.alloc(prov.alloc_id).size.div(&elem_size));
        let (start, len) = match range_kind {
            Some(mir_utils::RangeKind::RangeTo) => (
                zero.clone(),
                range_field(0).unwrap_or_else(|| total_len.clone()),
            ),
            Some(mir_utils::RangeKind::RangeFrom) => {
                let s = range_field(0).unwrap_or_else(|| zero.clone());
                (s.clone(), Int::sub(self.z3_ctx, &[&total_len, &s]))
            }
            Some(mir_utils::RangeKind::Range) => {
                let s = range_field(0).unwrap_or_else(|| zero.clone());
                let e = range_field(1).unwrap_or_else(|| total_len.clone());
                (s.clone(), Int::sub(self.z3_ctx, &[&e, &s]))
            }
            Some(mir_utils::RangeKind::RangeInclusive) => {
                let s = range_field(0).unwrap_or_else(|| zero.clone());
                let e = range_field(1).unwrap_or_else(|| total_len.clone());
                let l = Int::sub(self.z3_ctx, &[&e, &s]);
                (s.clone(), Int::add(self.z3_ctx, &[&l, &one]))
            }
            _ => (zero.clone(), total_len.clone()),
        };
        let start_bytes = Int::mul(self.z3_ctx, &[&start, &elem_size]);
        let dest_term = Int::add(self.z3_ctx, &[&array_term, &start_bytes]);
        let (alloc_id, _) = self.allocate_slice(len, elem_size, elem_align, Some(elem_ty));
        self.alloc_mut(alloc_id).parent = Some(prov.alloc_id);
        self.set_local(
            dest,
            VmValue {
                z3_term: dest_term,
                ty: dest_ty,
                provenance: Some(Provenance {
                    alloc_id,
                    offset: Int::from_u64(self.z3_ctx, 0),
                    offset_kind: None,
                }),
                facts: ValueFacts {
                    non_null: true,
                    init: true,
                    in_bounds: true,
                    ..Default::default()
                },
                source: ValueSource::None,
            },
        );
    }
}
