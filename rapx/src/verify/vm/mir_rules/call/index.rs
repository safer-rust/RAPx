use rustc_middle::{mir::Local, ty::TyKind};
use z3::ast::Int;

use crate::def_ids::lang_api::{self, LangItem};

use super::super::super::state::{ValueSource, VmState, VmValue};

pub(super) struct BuiltinIndexPlan<'z3, 'tcx> {
    base: VmValue<'z3, 'tcx>,
    index: VmValue<'z3, 'tcx>,
    index_local: Local,
    start: Int<'z3>,
    base_len: Int<'z3>,
    output_len: Option<Int<'z3>>,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(super) fn prepare_builtin_index(
        &self,
        callee: Option<rustc_hir::def_id::DefId>,
        args: &[VmValue<'z3, 'tcx>],
        arg_locals: &[Option<Local>],
        dest: Local,
    ) -> Option<BuiltinIndexPlan<'z3, 'tcx>> {
        let Some(callee) = callee else {
            return None;
        };
        let Some(trait_id) = self.tcx.trait_of_assoc(callee) else {
            return None;
        };
        if !lang_api::matches(self.tcx, trait_id, LangItem::Index)
            && !lang_api::matches(self.tcx, trait_id, LangItem::IndexMut)
        {
            return None;
        }
        let [base, index] = args else {
            return None;
        };
        let TyKind::Ref(_, base_pointee, _) = base.ty.kind() else {
            return None;
        };
        let (TyKind::Array(_, _) | TyKind::Slice(_)) = base_pointee.kind() else {
            return None;
        };
        let TyKind::Ref(..) = self.body().local_decls[dest].ty.kind() else {
            return None;
        };
        let is_scalar = matches!(
            index.ty.kind(),
            TyKind::Uint(rustc_middle::ty::UintTy::Usize)
        );
        let Some(index_local) = arg_locals.get(1).copied().flatten() else {
            return None;
        };
        let Some(start) = self.slice_index_start(index, index_local) else {
            return None;
        };
        let Some(base_len) = self.slice_len_from_value(base) else {
            return None;
        };
        let output_len = if is_scalar {
            None
        } else {
            let Some(len) = self.slice_index_output_len(base, index, index_local) else {
                return None;
            };
            Some(len)
        };
        Some(BuiltinIndexPlan {
            base: base.clone(),
            index: index.clone(),
            index_local,
            start,
            base_len,
            output_len,
        })
    }

    pub(super) fn apply_builtin_index(&mut self, plan: BuiltinIndexPlan<'z3, 'tcx>, dest: Local) {
        let BuiltinIndexPlan {
            base,
            index,
            index_local,
            start,
            base_len,
            output_len,
        } = plan;
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(start.ge(&zero));
        if let Some(len) = output_len {
            self.constraints.assertions.push(len.ge(&zero));
            self.constraints
                .assertions
                .push((&start + &len).le(&base_len));
            self.apply_slice_offset(dest, &base, &index, index_local);
            if let Some(mut value) = self.local_value(dest).cloned() {
                value.source = ValueSource::SliceLen(len);
                self.set_local(dest, value);
            }
            self.materialize_slice_ref_return(dest);
        } else {
            self.constraints.assertions.push(start.lt(&base_len));
            self.apply_slice_offset(dest, &base, &index, index_local);
        }
    }
}
