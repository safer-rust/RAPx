use rustc_middle::mir::Local;

use super::contracts::{
    bind_call_property, index_access_locals, rebind_property_place, slice_offset_locals,
};
use super::state::{VmState, VmValue};
use crate::verify::contract::{ContractKind, PropertyKind};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn assert_call_result_invariants(&mut self, destination: Local) {
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
        let invariants =
            crate::verify::type_invariants::build_type_invariants_for_ty(self.tcx, callee, ty);
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
        let ensures = crate::verify::target::get_call_ensures(self.tcx, callee);
        if ensures.is_empty() {
            return;
        }
        if self.tcx.is_foreign_item(callee) && self.local_value(destination).is_none() {
            let ty = self.body().local_decls[destination].ty;
            let term = self.fresh_int("ffi_return");
            self.set_local(destination, VmValue::new(term, ty));
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
                let bounded_result =
                    slice_offset_locals(&property).is_some_and(|(_, base, index)| {
                        bound_index_requires.contains(&(base, index))
                            && self
                                .local_value(base)
                                .zip(self.local_value(index))
                                .is_some_and(|(base_value, index_value)| {
                                    self.slice_index_start(index_value, index).is_some()
                                        || self.slice_len_from_value(base_value).is_some()
                                })
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
}
