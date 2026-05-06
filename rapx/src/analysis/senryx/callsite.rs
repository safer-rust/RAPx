//! Unsafe call-site contract dispatch and reporting helpers.
//!
//! This module bridges MIR calls and safety-property checkers. It also owns the
//! built-in unsafe-API matcher and a tiny MIR operand helper because both are
//! only needed when identifying and instantiating call-site obligations.

use crate::analysis::{
    core::alias_analysis::FnAliasPairs,
    senryx::{contract::PropertyContract, visitor::BodyVisitor},
    utils::fn_info::{
        generate_contract_from_std_annotation_json, get_cleaned_def_path_name, get_sp_tags_json,
        reflect_generic,
    },
};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Const, Operand, Place},
    ty::Ty,
};
use rustc_span::{Span, source_map::Spanned};
/// Return true when a cleaned function path has built-in unsafe API metadata.
pub(crate) fn has_unsafe_api_contract(func_name: &str) -> bool {
    get_sp_tags_json().get(func_name).is_some()
}

/// Convert a MIR operand into either a constant value or a local place index.
///
/// Returns `(is_const, value_or_local)`.
pub(crate) fn get_arg_place(arg: &Operand) -> (bool, usize) {
    match arg {
        Operand::Move(place) | Operand::Copy(place) => (false, place.local.as_usize()),
        Operand::Constant(constant) => {
            let mut val = 0;
            match constant.const_ {
                Const::Ty(_ty, _const_value) => {
                    rap_warn!("const ty found!");
                }
                Const::Unevaluated(_unevaluated, _ty) => {}
                Const::Val(const_value, _ty) => {
                    if let Some(scalar) = const_value.try_to_scalar_int() {
                        val = scalar.to_uint(scalar.size()) as usize;
                    }
                }
            }
            (true, val)
        }
    }
}

impl<'tcx> BodyVisitor<'tcx> {
    /// Instantiate and verify contracts at a standard-library unsafe API callsite.
    pub fn handle_std_unsafe_call(
        &mut self,
        _dst_place: &Place<'_>,
        def_id: &DefId,
        args: &[Spanned<Operand>],
        _path_index: usize,
        _fn_map: &FxHashMap<DefId, FnAliasPairs>,
        fn_span: Span,
        generic_mapping: FxHashMap<String, Ty<'tcx>>,
    ) {
        let func_name = get_cleaned_def_path_name(self.tcx, *def_id);
        let args_with_contracts = generate_contract_from_std_annotation_json(self.tcx, *def_id);

        for (idx, (base, fields, contract)) in args_with_contracts.iter().enumerate() {
            rap_debug!("Find contract for {:?}, {base}: {:?}", def_id, contract);
            if *base >= args.len() {
                continue;
            }

            let arg_tuple = get_arg_place(&args[*base].node);
            if arg_tuple.0 {
                continue;
            }

            let arg_place = self.chains.find_var_id_with_fields_seq(arg_tuple.1, fields);
            self.check_contract(
                arg_place,
                args,
                contract.clone(),
                &generic_mapping,
                func_name.clone(),
                fn_span,
                idx,
            );
        }
    }

    /// Dispatch one instantiated contract to the checker for that safety tag.
    pub fn check_contract(
        &mut self,
        arg: usize,
        _args: &[Spanned<Operand>],
        contract: PropertyContract<'tcx>,
        generic_mapping: &FxHashMap<String, Ty<'tcx>>,
        func_name: String,
        fn_span: Span,
        idx: usize,
    ) -> bool {
        rap_debug!("Check contract {:?} for {:?}.", contract, func_name);
        let (sp_name, check_result) = match contract {
            PropertyContract::Align(ty) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                ("Align", self.check_align(arg, contract_required_ty))
            }
            PropertyContract::InBound(ty, contract_len) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                (
                    "Inbound",
                    self.check_inbound(arg, contract_len, contract_required_ty),
                )
            }
            PropertyContract::NonNull => ("NonNull", self.check_non_null(arg)),
            PropertyContract::Typed(_ty) => ("Typed", self.check_typed(arg)),
            PropertyContract::ValidPtr(ty, contract_len) => {
                let contract_required_ty = reflect_generic(generic_mapping, &func_name, ty);
                (
                    "ValidPtr",
                    self.check_valid_ptr(arg, contract_len, contract_required_ty),
                )
            }
            PropertyContract::ValidNum(predicates) => {
                ("ValidNum", self.check_valid_num(&predicates))
            }
            _ => ("Unknown", false),
        };

        self.insert_checking_result(sp_name, check_result, func_name, fn_span, idx);
        true
    }
}
