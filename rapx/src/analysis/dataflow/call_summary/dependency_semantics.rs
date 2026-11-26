//! Verifier-specific call semantics supplied to the MIR dataflow analysis.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Body, Operand},
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::analysis::dataflow::{
    call::{CallDependencies, CallSemantics},
    call_write::WriteSemantics,
    pointer_copy, pointer_flow, pointer_offset,
};
use crate::compat::Spanned;
use crate::def_ids::{self, intrinsic_api, other_api};
use crate::util::mir_utils as helpers;
use crate::util::resolve;

use super::{CallEffect, effects, function_var};

pub(crate) struct VerifierCallSemantics;

impl CallSemantics for VerifierCallSemantics {
    fn special_dependencies<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        callee: DefId,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        body: &Body<'tcx>,
    ) -> Option<CallDependencies> {
        function_var::estimate(tcx, callee, args, body)
            .or_else(|| intrinsic_dependency_summary(tcx, caller, callee, func, args.len()))
    }

    fn skip_mir_dependencies(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool {
        helpers::is_drop_in_place(tcx, callee)
    }

    fn preserve_all_return_args(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool {
        other_api::is_box_new(tcx, callee)
    }
}

impl WriteSemantics for VerifierCallSemantics {
    fn traces_base_pointer<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        func: &Operand<'tcx>,
    ) -> bool {
        let callee = helpers::dep_callee_def_id(func);
        pointer_flow::return_traces_first_arg(tcx, callee)
            || callee.is_some_and(|id| pointer_offset::pointer_offset_direction(tcx, id).is_some())
            || resolve::resolve_callee_def_id(tcx, caller, func).and_then(|resolved| {
                pointer_flow::interior_mutable_borrow_source_arg(tcx, resolved)
            }) == Some(0)
    }

    fn direct_write_arg(&self, tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<usize> {
        let callee = helpers::dep_callee_def_id(func);
        if def_ids::is_ptr_write(tcx, callee) {
            Some(0)
        } else if let Some(flow) = callee.and_then(|id| pointer_copy::copy_flow(tcx, id)) {
            Some(flow.destination_arg)
        } else {
            None
        }
    }

    fn special_write_args<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        caller: DefId,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        body: &Body<'tcx>,
    ) -> Option<Vec<usize>> {
        let callee = helpers::dep_callee_def_id(func)?;
        self.special_dependencies(tcx, caller, callee, func, args, body)
            .map(|summary| summary.write_args)
    }

    fn skip_mir_write(&self, tcx: TyCtxt<'_>, callee: DefId) -> bool {
        intrinsic_api::is_intrinsic(tcx, callee) || self.skip_mir_dependencies(tcx, callee)
    }
}

/// Derive backward dependencies from a registered intrinsic effect.
fn intrinsic_dependency_summary<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: DefId,
    callee: DefId,
    func: &Operand<'tcx>,
    arg_count: usize,
) -> Option<CallDependencies> {
    let is_ptr_copy = pointer_copy::direct_copy_flow(tcx, callee).is_some();
    if !intrinsic_api::is_intrinsic(tcx, callee) && !is_ptr_copy {
        return None;
    }
    let modeled = effects::lookup_effect(tcx, caller, Some(callee), func);
    if is_ptr_copy && modeled.is_none() {
        return Some(CallDependencies {
            return_depends_on_args: (0..arg_count).collect(),
            write_args: (arg_count > 1).then_some(1).into_iter().collect(),
            write_inputs: (0..arg_count.min(3)).collect(),
        });
    }
    let write_args: Vec<usize> = if let Some(ref effects) = modeled {
        effects
            .iter()
            .flat_map(CallEffect::written_args)
            .filter(|arg| *arg < arg_count)
            .collect()
    } else {
        tcx.fn_sig(callee)
            .skip_binder()
            .inputs()
            .skip_binder()
            .iter()
            .take(arg_count)
            .enumerate()
            .filter_map(|(index, ty)| {
                matches!(
                    ty.kind(),
                    TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut)
                )
                .then_some(index)
            })
            .collect()
    };
    let write_inputs = if let Some(ref effects) = modeled {
        effects
            .iter()
            .flat_map(CallEffect::write_inputs)
            .filter(|arg| *arg < arg_count)
            .collect()
    } else {
        write_args.clone()
    };
    Some(CallDependencies {
        return_depends_on_args: (0..arg_count).collect(),
        write_args,
        write_inputs,
    })
}
