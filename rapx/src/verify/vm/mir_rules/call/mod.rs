mod callback;
mod comparison;
mod constructor;
mod effect;
mod index;

use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{Local, Operand},
    ty::{Instance, InstanceKind, TyKind},
};
use z3::ast::Int;

use super::super::state::{VmState, VmValue};
use super::RuleFlow;
use self::comparison::ComparisonPlan;
use self::index::BuiltinIndexPlan;
use crate::compat::Spanned;
use crate::helpers::mir_utils;
use crate::verify::call_summary::CallEffect;
use crate::verify::{api_classify, call_summary};

#[derive(Clone, Copy)]
struct CallSite<'a, 'z3, 'tcx> {
    func: &'a Operand<'tcx>,
    args: &'a [Spanned<Operand<'tcx>>],
    arg_values: &'a [VmValue<'z3, 'tcx>],
    arg_locals: &'a [Option<Local>],
    callee: Option<DefId>,
    destination: Local,
    caller_def_id: DefId,
}

enum CallModel<'z3, 'tcx> {
    Comparison(ComparisonPlan<'z3>),
    UbCheck,
    Drop(DropCall),
    UnsupportedIntrinsic,
    BuiltinIndex(BuiltinIndexPlan<'z3, 'tcx>),
    PostconditionsOnly,
    Summary(Vec<CallEffect>),
    Constructor(DefId),
    Inline(DefId),
    Unknown,
}

#[derive(Clone, Copy)]
enum DropCall {
    Value,
    Pointee,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CallFinish {
    None,
    MethodOnly,
    Full,
}

impl CallModel<'_, '_> {
    fn finish_policy(&self) -> CallFinish {
        match self {
            Self::Comparison(_) => CallFinish::MethodOnly,
            Self::UbCheck | Self::Drop(_) | Self::UnsupportedIntrinsic => CallFinish::None,
            _ => CallFinish::Full,
        }
    }

    fn uses_summary_invariants(&self) -> bool {
        match self {
            Self::Summary(effects) => !effects.is_empty(),
            Self::Constructor(_) => true,
            _ => false,
        }
    }
}

pub(super) fn exec_call<'z3, 'tcx>(
    state: &mut VmState<'z3, 'tcx>,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
    caller_def_id: DefId,
) -> RuleFlow {
    let prior_result = state
        .local_value(destination)
        .map(|value| value.z3_term.clone());
    let arg_values: Vec<VmValue<'z3, 'tcx>> = args
        .iter()
        .map(|arg| state.value_of_operand(&arg.node))
        .collect();
    let caller_arg_locals: Vec<Option<Local>> = args
        .iter()
        .map(|a| a.node.place().map(|p| p.local))
        .collect();
    let callee = mir_utils::dep_callee_resolved_def_id(state.tcx, caller_def_id, func);
    if let Some((source, owner)) = callee
        .and_then(|id| super::super::alias_hazard::reconstructed_owner(state.tcx, id))
        && let Some(value) = arg_values.get(source)
    {
        state.consume_ownership_share(value, owner, false);
    }
    let site = CallSite {
        func,
        args,
        arg_values: &arg_values,
        arg_locals: &caller_arg_locals,
        callee,
        destination,
        caller_def_id,
    };
    let drop_call = if api_classify::is_std_drop(state.tcx, callee)
        || callee.is_some_and(|id| state.tcx.def_path_str(id).contains("::ptr::drop_glue"))
    {
        Some(DropCall::Value)
    } else if callee.is_some_and(|id| mir_utils::is_drop_in_place(state.tcx, id))
        || api_classify::is_manually_drop_drop(state.tcx, callee)
    {
        Some(DropCall::Pointee)
    } else {
        None
    };
    if drop_call.is_none() {
        for (arg, value) in args.iter().zip(&arg_values) {
            if let Some(local) = arg.node.place().map(|place| place.local)
                && let Some(alloc_id) = value.provenance_alloc_id()
            {
                state.record_memory_use(alloc_id, local);
            }
        }
    }
    if callee.is_some_and(|c| {
        matches!(state.tcx.def_kind(c), DefKind::Fn | DefKind::AssocFn)
            && matches!(
                state
                    .tcx
                    .fn_sig(c)
                    .skip_binder()
                    .output()
                    .skip_binder()
                    .kind(),
                TyKind::Never
            )
    }) {
        return RuleFlow::Pruned;
    }
    let method_call = callee.and_then(|method| {
        arg_values.first().and_then(|receiver| {
            state.begin_method_call(
                method,
                receiver,
                caller_arg_locals.first().copied().flatten(),
            )
        })
    });

    let model = state.select_call_model(&site, drop_call);
    let finish_policy = model.finish_policy();
    let diagnostics_before_call = (finish_policy == CallFinish::Full
        && state.safedrop_events.is_enabled())
    .then(|| state.diagnostics.clone());
    let summary_used = model.uses_summary_invariants();
    if state.execute_call_model(model, &site) == RuleFlow::Pruned {
        return RuleFlow::Pruned;
    }
    if finish_policy == CallFinish::None {
        return RuleFlow::Continue;
    }
    if finish_policy == CallFinish::MethodOnly {
        let result = state.local_value(destination).cloned();
        state.finish_method_call(method_call, result.as_ref());
        return RuleFlow::Continue;
    }
    if let Some(before) = diagnostics_before_call.as_ref()
        && state
            .diagnostics
            .only_copy_memory_target_unavailable_since(before)
        && matches!(state.body().local_decls[destination].ty.kind(), TyKind::Adt(def, _) if api_classify::is_std_string(def.did()))
    {
        let ty = state.body().local_decls[destination].ty;
        let mut facts = Default::default();
        if state.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts) {
            state.diagnostics.recover_copy_memory_target(before);
        }
    }
    if let Some(before) = diagnostics_before_call.as_ref()
        && state.diagnostics.only_missing_mir_since(before)
        && arg_values.iter().all(|value| {
            value.provenance.is_none()
                && !matches!(value.ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..))
        })
    {
        let ty = state.body().local_decls[destination].ty;
        let mut facts = Default::default();
        if !state.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts) {
            let term = state.fresh_int("safedrop_opaque_result");
            state.set_local(destination, VmValue::new(term, ty));
        }
        state.diagnostics.recover_missing_mir(before);
    }
    state.finish_call(&site, prior_result.as_ref(), summary_used, method_call);
    RuleFlow::Continue
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    fn select_call_model(
        &self,
        site: &CallSite<'_, 'z3, 'tcx>,
        drop_call: Option<DropCall>,
    ) -> CallModel<'z3, 'tcx> {
        let CallSite {
            func,
            arg_values: args,
            arg_locals,
            callee,
            destination,
            caller_def_id,
            ..
        } = *site;
        if let Some(plan) = self.prepare_comparison(callee, args, destination) {
            return CallModel::Comparison(plan);
        }
        if callee.is_some_and(|id| crate::def_ids::other_api::is_ub_check(self.tcx, id)) {
            return CallModel::UbCheck;
        }
        if let Some(drop_call) = drop_call {
            return CallModel::Drop(drop_call);
        }
        if call_summary::effects::is_unmodeled_intrinsic(self.tcx, callee) {
            return CallModel::UnsupportedIntrinsic;
        }
        let force_inline = callee.is_some_and(|id| {
            crate::verify::options::force_inline_constructor(self.tcx, id)
                && self.tcx.is_mir_available(id)
        });
        if !force_inline {
            if let Some(plan) = self.prepare_builtin_index(callee, args, arg_locals, destination) {
                return CallModel::BuiltinIndex(plan);
            }
            if callee
                .is_some_and(|id| crate::verify::target::has_slice_offset_ensures(self.tcx, id))
            {
                return CallModel::PostconditionsOnly;
            }
            if args.first().is_some_and(|value| {
                matches!(
                    value.ty.kind(),
                    TyKind::Ref(_, inner, rustc_middle::mir::Mutability::Mut)
                        if inner.ty_adt_def().is_some_and(|adt| api_classify::is_std_vec(adt.did()))
                )
            }) && call_summary::callsite_replaces_pointer_field(self.tcx, func) {
                return CallModel::Summary(vec![CallEffect::ReallocateVec { arg: 0 }]);
            }
            if let Some(effects) = call_summary::effects::lookup_effect(
                self.tcx, caller_def_id, callee, func,
            ) {
                return CallModel::Summary(effects);
            }
            if let Some(effects) = call_summary::effects::effect_summary(self.tcx, func) {
                return CallModel::Summary(effects);
            }
        }
        if let Some(callee) = callee
            && !crate::verify::options::should_inline_constructor(self.tcx, callee)
        {
            CallModel::Constructor(callee)
        } else if let Some(callee) = callee
            && self.tcx.is_mir_available(callee)
        {
            CallModel::Inline(callee)
        } else {
            CallModel::Unknown
        }
    }

    fn execute_call_model(
        &mut self,
        model: CallModel<'z3, 'tcx>,
        site: &CallSite<'_, 'z3, 'tcx>,
    ) -> RuleFlow {
        let CallSite {
            func,
            args,
            arg_values,
            arg_locals,
            callee,
            destination,
            caller_def_id,
        } = *site;
        match model {
            CallModel::Comparison(plan) => {
                self.apply_comparison(plan, destination);
                RuleFlow::Continue
            }
            CallModel::UbCheck => {
                let ty = self.body().local_decls[destination].ty;
                self.set_local(destination, VmValue::new(Int::from_u64(self.z3_ctx, 0), ty));
                RuleFlow::Continue
            }
            CallModel::Drop(DropCall::Value) => {
                if let Some(Operand::Move(place)) = args.first().map(|arg| &arg.node) {
                    super::terminator::exec_drop(self, place);
                }
                RuleFlow::Continue
            }
            CallModel::Drop(DropCall::Pointee) => {
                let event_count = self.safedrop_events.len();
                if let Some(pointer) = arg_values.first()
                    && let Some(local) = self.find_local_by_address(&pointer.z3_term)
                {
                    super::terminator::exec_drop(self, &rustc_middle::mir::Place::from(local));
                }
                if self.safedrop_events.len() == event_count
                    && let Some(pointer) = arg_values.first()
                    && let Some(alloc_id) = pointer.provenance_alloc_id()
                {
                    let local = arg_locals.first().copied().flatten().unwrap_or(destination);
                    self.record_memory_drop(alloc_id, local);
                }
                RuleFlow::Continue
            }
            CallModel::UnsupportedIntrinsic => {
                let name = callee
                    .map(|id| self.tcx.def_path_str(id))
                    .unwrap_or_else(|| "<unresolved>".to_string());
                self.record_unsupported(&format!("intrinsic {name}"));
                RuleFlow::Continue
            }
            CallModel::BuiltinIndex(plan) => {
                self.apply_builtin_index(plan, destination);
                RuleFlow::Continue
            }
            CallModel::PostconditionsOnly => RuleFlow::Continue,
            CallModel::Summary(effects) => {
                for effect in &effects {
                    self.apply_call_effect(
                        effect,
                        arg_values,
                        arg_locals,
                        destination,
                        func,
                    );
                }
                RuleFlow::Continue
            }
            CallModel::Constructor(callee) => {
                let has_invariant =
                    crate::verify::options::constructor_has_invariant(self.tcx, callee);
                self.materialize_constructor_result(
                    destination,
                    arg_values,
                    args.first().map(|arg| &arg.node),
                    callee,
                    has_invariant,
                );
                RuleFlow::Continue
            }
            CallModel::Inline(callee) => {
                let instance = mir_utils::resolve_callee_instance(self.tcx, caller_def_id, func)
                    .or_else(|| {
                        let Operand::Constant(constant) = func else {
                            return None;
                        };
                        let TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
                            return None;
                        };
                        #[cfg(rapx_ge_99)]
                        let args = args.skip_binder();
                        (*def_id == callee && self.tcx.trait_of_assoc(callee).is_none()).then_some(
                            Instance {
                                def: InstanceKind::Item(callee),
                                args,
                            },
                        )
                    })
                    .filter(|instance| {
                        matches!(instance.def, InstanceKind::Item(_))
                            && instance.def_id() == callee
                            && (instance
                                .args
                                .types()
                                .all(|ty| !mir_utils::ty_has_type_param(ty))
                                || self.inline.symbolic_generic_const_inline
                                || mir_utils::has_generic_const_call_argument(self.tcx, callee))
                    });
                if self.exec_inline_call(
                    callee,
                    instance,
                    args,
                    arg_values,
                    arg_locals,
                    destination,
                ) {
                    RuleFlow::Continue
                } else {
                    RuleFlow::Pruned
                }
            }
            CallModel::Unknown => {
                if let Some(callee) = callee {
                    if self.tcx.trait_of_assoc(callee).is_some_and(|trait_id| {
                        crate::def_ids::lang_api::is_fn_trait(self.tcx, trait_id)
                    }) {
                        self.apply_callback_effect(arg_values, arg_locals, destination, callee);
                    } else if !crate::def_ids::lang_api::is_panic_exit(self.tcx, callee) {
                        self.record_missing_mir(callee);
                    }
                }
                RuleFlow::Continue
            }
        }
    }

    fn finish_call(
        &mut self,
        site: &CallSite<'_, 'z3, 'tcx>,
        prior_result: Option<&Int<'z3>>,
        summary_used: bool,
        method_call: Option<super::super::method_cache::MethodSnapshot<'z3, 'tcx>>,
    ) {
        self.finish_call_state(site, prior_result, summary_used, method_call.clone());
        let mut alternatives = std::mem::take(&mut self.inline.pending_states);
        for state in &mut alternatives {
            state.finish_call_state(site, prior_result, summary_used, method_call.clone());
        }
        self.inline.pending_states = alternatives;
    }

    fn finish_call_state(
        &mut self,
        site: &CallSite<'_, 'z3, 'tcx>,
        prior_result: Option<&Int<'z3>>,
        summary_used: bool,
        method_call: Option<super::super::method_cache::MethodSnapshot<'z3, 'tcx>>,
    ) {
        let callee = site.callee;
        if let Some(owner) = callee
            .and_then(|id| crate::verify::pointer_origin::shared_raw_owner_type(self.tcx, id))
        {
            self.begin_ownership_transfer(site.destination, owner);
        }
        let arg_locals = site.arg_locals;
        let destination = site.destination;
        if let Some(callee) = callee {
            self.assert_call_postconditions(callee, arg_locals, destination);
            if self
                .local_value(destination)
                .is_some_and(|value| prior_result != Some(&value.z3_term))
            {
                self.assert_call_result_invariants(destination);
                if summary_used {
                    self.assert_summary_result_type_invariants(callee, destination);
                }
            }
        }
        let result = self.local_value(destination).cloned();
        self.finish_method_call(method_call, result.as_ref());
    }
}
