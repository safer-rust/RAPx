//! Call handling for the symbolic VM.
//!
//! Bridges the existing call summary infrastructure (`call_summary`)
//! with the symbolic VM state. The `Call` terminator rule invokes `exec_call`.
//!
//! When the callee has MIR available, the VM recursively inlines the
//! callee's body to achieve context-sensitive precision, unless a
//! effects summary provides more precise hand-crafted invariants.
//! Otherwise it falls back to the summary-based approach.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    BasicBlock, Local, Operand, Rvalue, StatementKind, Terminator, TerminatorKind,
};
use rustc_middle::ty::{EarlyBinder, Instance, InstanceKind, TyKind, TypingEnv};
use z3::ast::{Ast, Bool, Int};
use z3::{SatResult, Solver};

use super::state::{AllocId, MemoryContent, VmState, VmValue};
use crate::compat::{FxHashSet, Spanned};
use crate::helpers::mir_utils;
use crate::limit::MAX_INLINE_DEPTH;
use crate::verify::api_classify;
use crate::verify::call_summary;

type InlineWorkItem<'z3, 'tcx> = (VmState<'z3, 'tcx>, BasicBlock, FxHashSet<BasicBlock>);

enum InlineStep<'z3, 'tcx> {
    Complete(bool),
    Fork(Vec<InlineWorkItem<'z3, 'tcx>>),
    Incomplete,
}

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn eval_contract_method(
        &self,
        method: DefId,
        receiver: VmValue<'z3, 'tcx>,
        receiver_local: Option<Local>,
        args: Vec<Int<'z3>>,
    ) -> Option<Int<'z3>> {
        if !super::method_cache::stable_contract_query(self.tcx, method) {
            return None;
        }
        let sig = self.tcx.fn_sig(method).skip_binder();
        let inputs = sig.inputs().skip_binder();
        if inputs.len() != args.len() + 1 {
            return None;
        }
        let mut values = vec![receiver];
        values.extend(
            args.into_iter()
                .zip(inputs[1..].iter())
                .map(|(term, ty)| VmValue::new(term, *ty)),
        );
        self.eval_contract_method_paths(method, &values, receiver_local)
    }

    fn eval_contract_method_paths(
        &self,
        method: DefId,
        values: &[VmValue<'z3, 'tcx>],
        receiver_local: Option<Local>,
    ) -> Option<Int<'z3>> {
        let mut state = self.clone();
        let frame = state.save_frame();
        state.current_frame.current_def_id = method;
        for (index, value) in values.iter().enumerate() {
            let local = Local::from_usize(index + 1);
            state.ensure_local_allocation(local);
            state.set_local(local, value.clone());
        }
        if let Some(source) = receiver_local {
            for path in self.frame_field_paths(&frame, source) {
                if let Some(value) = self.frame_field_value(&frame, source, &path) {
                    state.set_field_value(Local::from_usize(1), path, value.clone());
                }
            }
        }
        let baseline = state.constraints.assertions.len();
        let body = self.tcx.optimized_mir(method);
        let mut pending = vec![(state, BasicBlock::from_usize(0), FxHashSet::default())];
        let mut returns = Vec::new();
        let mut explored = 0;
        while let Some((mut state, block, mut visited)) = pending.pop() {
            if explored >= 128 || !visited.insert(block) {
                return None;
            }
            explored += 1;
            let data = &body.basic_blocks[block];
            for statement in &data.statements {
                crate::verify::vm::rules::exec_statement(&mut state, statement);
                if let StatementKind::Assign(assign) = &statement.kind
                    && assign.0.projection.is_empty()
                    && let Rvalue::Use(Operand::Constant(constant), ..) = &assign.1
                    && let Ok(value) = constant.const_.eval(
                        self.tcx,
                        rustc_middle::ty::TypingEnv::fully_monomorphized(),
                        rustc_span::DUMMY_SP,
                    )
                    && let Some(scalar) = value.try_to_scalar_int()
                    && let Ok(bits) = u64::try_from(scalar.to_bits(scalar.size()))
                {
                    state.set_local(
                        assign.0.local,
                        VmValue::new(Int::from_u64(self.z3_ctx, bits), constant.const_.ty()),
                    );
                }
            }
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Return => {
                    if state.unsupported_mir || state.incomplete_inline_branch {
                        return None;
                    }
                    let term = state.local_value(Local::from_usize(0))?.z3_term.clone();
                    let constraints = &state.constraints.assertions[baseline..];
                    let guard = Bool::and(self.z3_ctx, &constraints.iter().collect::<Vec<_>>());
                    returns.push((guard, term));
                }
                TerminatorKind::Goto { target, .. } => pending.push((state, *target, visited)),
                TerminatorKind::SwitchInt { targets, .. } => {
                    for target in targets.all_targets().iter().copied() {
                        let mut branch = state.clone();
                        crate::verify::vm::rules::exec_terminator(
                            &mut branch,
                            terminator,
                            Some(target),
                        );
                        if !branch.path_infeasible {
                            pending.push((branch, target, visited.clone()));
                        }
                    }
                }
                TerminatorKind::Unreachable => {}
                _ => return None,
            }
        }
        if returns.is_empty() {
            return None;
        }
        let guards: Vec<&Bool<'z3>> = returns.iter().map(|(guard, _)| guard).collect();
        let coverage = Bool::or(self.z3_ctx, &guards);
        let solver = Solver::new(self.z3_ctx);
        self.assert_all(&solver);
        solver.assert(&coverage.not());
        if solver.check() != SatResult::Unsat {
            return None;
        }
        let mut result = None;
        for (guard, term) in returns.into_iter().rev() {
            result = Some(match result {
                Some(other) => guard.ite(&term, &other),
                None => term,
            });
        }
        result
    }

    /// Execute a call terminator, dispatching by precision:
    ///
    ///  1. an exact simulator for supported calls;
    ///  2. a registry / transparent-deref summary effect;
    ///  3. inline of the callee's MIR when there is no summary.
    ///
    /// A call with neither a summary nor inlinable MIR leaves `destination`
    /// unset.
    pub(crate) fn exec_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
        caller_def_id: DefId,
    ) {
        let prior_result = self.local_value(destination).map(|value| value.z3_term.clone());
        let arg_values: Vec<VmValue<'z3, 'tcx>> = args
            .iter()
            .map(|arg| self.value_of_operand(&arg.node))
            .collect();
        let caller_arg_locals: Vec<Option<Local>> = args
            .iter()
            .map(|a| a.node.place().map(|p| p.local))
            .collect();
        let callee = mir_utils::dep_callee_resolved_def_id(self.tcx, caller_def_id, func);
        if callee.is_some_and(|c| {
            matches!(
                self.tcx.fn_sig(c).skip_binder().output().skip_binder().kind(),
                TyKind::Never
            )
        }) {
            self.path_infeasible = true;
            return;
        }
        let method_call = callee.and_then(|method| {
            arg_values.first().and_then(|receiver| {
                self.begin_method_call(
                    method,
                    receiver,
                    caller_arg_locals.first().copied().flatten(),
                )
            })
        });

        if self.try_simulate_comparison(callee, &arg_values, destination) {
            let result = self.local_value(destination).cloned();
            self.finish_method_call(method_call, result.as_ref());
            return;
        }

        // `assert_unsafe_precondition!` gates are disabled under release
        // semantics; bind them to `false` so their branchy panic bodies are not
        // inlined (which would otherwise recurse to the depth limit).
        if let Some(c) = callee
            && crate::def_ids::other_api::is_ub_check(self.tcx, c)
        {
            let dest_ty = self.body().local_decls[destination].ty;
            self.set_local(
                destination,
                VmValue::new(Int::from_u64(self.z3_ctx, 0), dest_ty),
            );
            return;
        }

        if call_summary::effects::is_unmodeled_intrinsic(self.tcx, callee) {
            let name = callee
                .map(|id| self.tcx.def_path_str(id))
                .unwrap_or_else(|| "<unresolved>".to_string());
            self.record_unsupported(&format!("intrinsic {name}"));
            return;
        }

        // Registry summary, else the transparent-deref / unknown fallback.
        let summary = if callee.is_some_and(|id| {
            crate::verify::options::force_inline_constructor(self.tcx, id)
                && self.tcx.is_mir_available(id)
        }) {
            None
        } else if self.try_simulate_builtin_index(
            callee,
            &arg_values,
            &caller_arg_locals,
            destination,
        ) {
            Some(Vec::new())
        } else if callee.is_some_and(|id| {
            crate::verify::target::has_slice_offset_ensures(self.tcx, id)
        }) {
            Some(Vec::new())
        } else {
            crate::verify::call_summary::effects::lookup_effect(
                self.tcx,
                caller_def_id,
                callee,
                func,
            )
            .or_else(|| call_summary::effects::effect_summary(self.tcx, func))
        };
        let ctor_summarized = summary.is_none()
            && callee.is_some_and(|id| {
                !crate::verify::options::should_inline_constructor(self.tcx, id)
            });
        let summary_used = summary.as_ref().is_some_and(|effects| !effects.is_empty())
            || ctor_summarized;

        if let Some(effects) = summary {
            for effect in &effects {
                self.apply_call_effect(
                    effect,
                    &arg_values,
                    &caller_arg_locals,
                    destination,
                    callee,
                    func,
                );
            }
        } else if ctor_summarized {
            let callee = callee.unwrap();
            let has_invariant =
                crate::verify::options::constructor_has_invariant(self.tcx, callee);
            self.materialize_constructor_result(
                destination,
                &arg_values,
                callee,
                has_invariant,
            );
        } else if let Some(c) = callee
            && self.tcx.is_mir_available(c)
        {
            let instance = self.frame_body.is_some()
                .then(|| mir_utils::resolve_callee_instance(self.tcx, caller_def_id, func))
                .flatten()
                .or_else(|| {
                    let Operand::Constant(constant) = func else {
                        return None;
                    };
                    let TyKind::FnDef(def_id, args) = constant.const_.ty().kind() else {
                        return None;
                    };
                    #[cfg(rapx_ge_99)]
                    let args = args.skip_binder();
                    (*def_id == c && self.tcx.trait_of_assoc(c).is_none())
                    .then_some(Instance {
                        def: InstanceKind::Item(c),
                        args,
                    })
                })
                .filter(|instance| {
                    matches!(instance.def, InstanceKind::Item(_))
                        && instance.def_id() == c
                        && (instance.args.types().all(|ty| !mir_utils::ty_has_type_param(ty))
                            || self.inline.symbolic_generic_const_inline
                            || mir_utils::has_generic_const_call_argument(self.tcx, c))
                });
            self.exec_inline_call(c, instance, args, &arg_values, &caller_arg_locals, destination);
        } else if let Some(c) = callee {
            // `assert!` panic exits contain this diverging call. It cannot
            // change the caller's state before the unwind invariant check.
            if self.tcx.trait_of_assoc(c).is_some_and(|trait_id| {
                crate::def_ids::lang_api::is_fn_trait(self.tcx, trait_id)
            }) {
                self.apply_callback_effect(&arg_values, &caller_arg_locals, destination, c);
            } else if !crate::def_ids::lang_api::is_panic_exit(self.tcx, c) {
                self.record_missing_mir(c);
            }
        }
        if let Some(callee) = callee {
            self.assert_call_postconditions(callee, &caller_arg_locals, destination);
            if self.local_value(destination).is_some_and(|value| {
                prior_result.as_ref() != Some(&value.z3_term)
            }) {
                self.assert_call_result_invariants(destination);
                if summary_used {
                    self.assert_summary_result_type_invariants(callee, destination);
                }
            }
        }
        let result = self.local_value(destination).cloned();
        self.finish_method_call(method_call.clone(), result.as_ref());
        let mut alternatives = std::mem::take(&mut self.inline.pending_states);
        for state in &mut alternatives {
            if let Some(callee) = callee {
                state.assert_call_postconditions(callee, &caller_arg_locals, destination);
                if state.local_value(destination).is_some_and(|value| {
                    prior_result.as_ref() != Some(&value.z3_term)
                }) {
                    state.assert_call_result_invariants(destination);
                    if summary_used {
                        state.assert_summary_result_type_invariants(callee, destination);
                    }
                }
            }
            let result = state.local_value(destination).cloned();
            state.finish_method_call(method_call.clone(), result.as_ref());
        }
        self.inline.pending_states = alternatives;
    }

    /// Recursively execute a callee's MIR body inline.
    ///
    /// Binds the caller's argument values to the callee's parameters,
    /// executes the callee's MIR, and writes the return value to
    /// the caller's destination local. Returns `false` if inline
    /// is not possible (e.g., recursion limit reached or a branch cannot
    /// be resolved).
    fn exec_inline_call(
        &mut self,
        callee_def_id: DefId,
        instance: Option<Instance<'tcx>>,
        call_args: &[Spanned<Operand<'tcx>>],
        arg_values: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
    ) -> bool {
        if self.inline.inline_depth >= MAX_INLINE_DEPTH {
            // Leave a distinguishable symbolic value in `dest` so the checker
            // can detect that this result depends on a truncated inline and
            // report `Unknown` instead of failing on an unconstrained term.
            let dest_ty = self.body().local_decls[dest].ty;
            let truncated_term = self.fresh_int("inline_truncated");
            self.inline
                .inline_truncated_terms
                .insert(truncated_term.clone());
            self.set_local(dest, VmValue::new(truncated_term, dest_ty));
            return false;
        }
        let before_inline = self.clone();
        self.inline.inline_depth += 1;
        self.inline.symbolic_generic_const_inline |= instance.as_ref().is_some_and(|instance| {
            instance.args.types().any(mir_utils::ty_has_type_param)
                && mir_utils::has_generic_const_call_argument(self.tcx, callee_def_id)
        });

        // Resolve each arg's referent local (for `&self`/`&mut self` reborrow
        // temps) *before* the caller's address map is saved away, so that
        // `exec_assign` can resolve `(*self).field = val` writes back to the
        // caller's referent while the callee executes.
        let inline_arg_referents: Vec<Option<Local>> = arg_values
            .iter()
            .map(|v| self.find_local_by_address(&v.z3_term))
            .collect();
        let caller_referents = inline_arg_referents.clone();
        // Whole-place reborrow referents, resolved from the *caller's* MIR
        // before the body is switched to the callee (used to propagate the
        // referent's struct fields into the callee for `old = self.ptr`).
        let reborrow_referents: Vec<Option<Local>> = caller_arg_locals
            .iter()
            .map(|arg_opt| arg_opt.and_then(|a| self.find_whole_reborrow_referent(a)))
            .collect();
        let frame = self.save_frame();
        let saved_inline_arg_referents =
            std::mem::replace(&mut self.inline.arg_referents, inline_arg_referents);
        let saved_deferred_field_writes = std::mem::take(&mut self.inline.deferred_field_writes);

        let caller_def_id = self.current_frame.current_def_id;
        self.current_frame.current_def_id = callee_def_id;
        if let Some(instance) = instance {
            let body = self.tcx.optimized_mir(callee_def_id).clone();
            let body = instance.instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                TypingEnv::post_analysis(self.tcx, caller_def_id),
                EarlyBinder::bind(self.tcx, body),
            );
            self.frame_body = Some(&*self.tcx.arena.alloc(body));
        }

        for (i, arg_val) in arg_values.iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            self.ensure_local_allocation(callee_local);
            self.set_local(callee_local, arg_val.clone());
            if let Some(Operand::Constant(constant)) = call_args.get(i).map(|arg| &arg.node) {
                self.materialize_const_adt(callee_local, &constant.const_);
            }
        }

        // Propagate the caller arg locals' field values into the callee context
        // so that the inline body can access struct fields (e.g. Iter::ptr /
        // end_or_len for len/is_empty computations).
        for (i, caller_arg_opt) in caller_arg_locals.iter().enumerate() {
            let callee_param = Local::from_usize(i + 1);
            let Some(caller_arg) = caller_arg_opt else {
                continue;
            };
            // A whole-place reborrow (`_7 = &mut (*_1)`) shares the referent's
            // struct fields; when the reborrow temp's own assignment was pruned,
            // propagate the referent's fields so `self.ptr` resolves in the
            // callee (Iter::next).  Excludes field reborrows.
            let mut source_locals = vec![*caller_arg];
            if let Some(r) = reborrow_referents.get(i).copied().flatten()
                && r != *caller_arg
            {
                source_locals.push(r);
            }
            for src in source_locals {
                let caller_field_keys: Vec<Vec<usize>> = self.frame_field_paths(&frame, src);
                for fields in caller_field_keys {
                    if let Some(fv) = self.frame_field_value(&frame, src, &fields).cloned() {
                        self.set_field_value(callee_param, fields, fv);
                    }
                }
            }
        }

        let pre_uninit: Vec<AllocId> = caller_referents
            .iter()
            .flatten()
            .filter(|local| {
                api_classify::is_maybe_uninit_ty(before_inline.body().local_decls[**local].ty)
            })
            .filter_map(|local| before_inline.current_frame.local_alloc.get(local).copied())
            .filter(|id| !before_inline.content(*id).facts.initialized)
            .collect();
        let may_recurse = self.body().basic_blocks.iter().any(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return false;
            };
            mir_utils::dep_callee_resolved_def_id(self.tcx, callee_def_id, func)
                == Some(callee_def_id)
        });
        let returns = self.inline_execute_body(&pre_uninit);
        if returns.as_ref().is_none_or(|states| {
            states
                .iter()
                .any(|state| state.local_value(Local::from_usize(0)).is_none())
        }) {
            let witnessed = self.possible_uninit_allocs.clone();
            *self = before_inline;
            self.possible_uninit_allocs.extend(witnessed);
            self.incomplete_inline_branch = true;
            let dest_ty = self.body().local_decls[dest].ty;
            let unknown_term = self.fresh_int("inline_branch_unknown");
            self.inline.inline_branch_terms.insert(unknown_term.clone());
            if may_recurse {
                self.inline
                    .inline_truncated_terms
                    .insert(unknown_term.clone());
            }
            self.set_local(dest, VmValue::new(unknown_term, dest_ty));
            let mut unknown_effect =
                self.tcx.fn_sig(callee_def_id).skip_binder().safety() == rustc_hir::Safety::Unsafe;
            for (arg, referent) in arg_values.iter().zip(&caller_referents) {
                match arg.ty.kind() {
                    TyKind::Bool
                    | TyKind::Char
                    | TyKind::Int(_)
                    | TyKind::Uint(_)
                    | TyKind::Float(_) => {}
                    TyKind::Ref(..) | TyKind::RawPtr(..) => {
                        if let Some(local) = referent {
                            self.forget_inline_referent(*local);
                        } else {
                            unknown_effect = true;
                        }
                    }
                    _ => unknown_effect = true,
                }
            }
            self.unsupported_mir |= unknown_effect;
            return false;
        }
        let mut completed = Vec::new();
        for mut state in returns.unwrap() {
            let return_val = state.local_value(Local::from_usize(0)).cloned();
            let return_fields: Vec<_> = state
                .field_paths(Local::from_usize(0))
                .into_iter()
                .filter_map(|path| {
                    state.field_value(Local::from_usize(0), &path)
                        .cloned()
                        .map(|val| (path, val))
                })
                .collect();
            state.restore_frame(frame.clone());
            let writes = std::mem::take(&mut state.inline.deferred_field_writes);
            state.inline.arg_referents = saved_inline_arg_referents.clone();
            state.inline.deferred_field_writes = saved_deferred_field_writes.clone();
            state.replay_deferred_writes(writes);
            let mut val = return_val.unwrap();
            let dest_ty = state.body().local_decls[dest].ty;
            val.ty = dest_ty;
            if val
                .provenance
                .as_ref()
                .is_some_and(|p| p.offset.as_u64() == Some(0))
            {
                val.facts.non_null = true;
            }
            state.set_local(dest, val);
            for (path, fv) in return_fields {
                state.set_field_value(dest, path, fv);
            }
            state.materialize_slice_ref_return(dest);
            if let Some(dest_alloc_id) = state.current_frame.local_alloc.get(&dest).copied() {
                state.content_mut(dest_alloc_id).facts.initialized = true;
            }
            state.inline.inline_depth -= 1;
            state.inline.symbolic_generic_const_inline =
                before_inline.inline.symbolic_generic_const_inline;
            completed.push(state);
        }
        if completed.is_empty() {
            *self = before_inline;
            self.path_infeasible = true;
            return true;
        }
        *self = completed.remove(0);
        self.inline.pending_states.extend(completed.into_iter().map(Box::new));
        true
    }

    fn forget_inline_referent(&mut self, local: Local) {
        let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied() else {
            self.unsupported_mir = true;
            return;
        };
        if self.possible_uninit_allocs.contains(&alloc_id) {
            return;
        }
        let prior = self.local_value(local).cloned();
        *self.content_mut(alloc_id) = MemoryContent::default();
        let ty = self.body().local_decls[local].ty;
        let unknown_term = self.fresh_int("inline_write_unknown");
        self.inline.inline_branch_terms.insert(unknown_term.clone());
        let mut unknown = VmValue::new(unknown_term, ty);
        if let Some(prior) = prior
            && prior.provenance_alloc_id() == Some(alloc_id)
        {
            unknown.provenance = prior.provenance;
        }
        self.set_local(local, unknown);
    }

    /// Resolve a `SwitchInt` discriminant to a constant `u64`, following a
    /// single local-assignment chain (a `cfg!`-style runtime-check flag) or a
    /// call to an `assert_unsafe_precondition!` gate (`check_language_ub`),
    /// which is disabled under release semantics.
    fn switch_discr_const(
        &self,
        body: &rustc_middle::mir::Body<'tcx>,
        discr: &Operand<'tcx>,
    ) -> Option<u64> {
        if let Some(v) = mir_utils::operand_const_u64(discr) {
            return Some(v);
        }
        // A `UbChecks`/`ContractChecks`/`OverflowChecks` discriminant folds to
        // the no-check edge (`0` = false), mirroring release-mode const-folding.
        #[cfg(rapx_ge_95)]
        if let Operand::RuntimeChecks(_) = discr {
            return Some(0);
        }
        // `T::IS_ZST` for a generic `T` is unevaluated; fold it to `false`
        // (non-ZST).  The `IS_ZST` guard in pointer arithmetic (`add`/`sub`/
        // `offset`) only skips redundant arithmetic: `offset` on a ZST pointee
        // is a no-op (stride 0), so the non-ZST path is correct for ZST too and
        // avoids the ZST branch returning `self` with a stale element offset.
        if let Operand::Constant(constant) = discr
            && let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_
            && mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
        {
            return Some(0);
        }
        let (Operand::Copy(p) | Operand::Move(p)) = discr else {
            return None;
        };
        for bbd in body.basic_blocks.iter() {
            for stmt in bbd.statements.iter() {
                let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                    continue;
                };
                let (dest, rvalue) = &**assign;
                if dest != p {
                    continue;
                }
                if let Some(v) = mir_utils::rvalue_runtime_checks_value(rvalue) {
                    return Some(v);
                }
                // `_4 = const <T as SizedTypeProperties>::IS_ZST` (generic `T`):
                // fold to non-ZST, mirroring the direct-const case above.
                if let rustc_middle::mir::Rvalue::Use(operand, ..) = rvalue
                    && let Operand::Constant(constant) = operand
                    && let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_
                    && mir_utils::is_sized_type_property(self.tcx, uneval.def, "IS_ZST")
                {
                    return Some(0);
                }
            }
        }
        // `check_language_ub` is a function *call* (not an assignment), whose
        // destination is the discriminant.  It gates the precondition check
        // behind `debug_assertions`/`ub_checks` and is `false` under the release
        // semantics the VM models.
        for bbd in body.basic_blocks.iter() {
            let terminator = bbd.terminator();
            if let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
                && destination.local == p.local
                && destination.projection.is_empty()
                && let Some(callee) = mir_utils::dep_callee_def_id(func)
                && crate::def_ids::other_api::is_ub_check(self.tcx, callee)
            {
                return Some(0);
            }
        }
        None
    }

    /// Execute the callee's MIR body.
    fn inline_execute_body(&mut self, pre_uninit: &[AllocId]) -> Option<Vec<Self>> {
        match self.inline_execute_single() {
            InlineStep::Complete(true) => Some(vec![self.clone()]),
            InlineStep::Complete(false) => Some(Vec::new()),
            InlineStep::Fork(pending) => self.inline_execute_branches(pre_uninit, pending),
            InlineStep::Incomplete => None,
        }
    }

    fn inline_execute_single(&mut self) -> InlineStep<'z3, 'tcx> {
        let mut visited = FxHashSet::default();
        let mut queue = vec![BasicBlock::from_usize(0)];
        let mut returned = false;
        while let Some(block) = queue.pop() {
            if self.path_infeasible || !visited.insert(block) {
                continue;
            }
            let bb_data = &self.body().basic_blocks[block];
            for stmt in &bb_data.statements {
                crate::verify::vm::rules::exec_statement(self, stmt);
            }
            let terminator = bb_data.terminator();
            match &terminator.kind {
                TerminatorKind::Goto { target, .. } => queue.push(*target),
                TerminatorKind::Return => returned = true,
                TerminatorKind::Assert { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    queue.push(*target);
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    if let Some(value) = self.switch_discr_const(self.body(), discr) {
                        let target = targets
                            .iter()
                            .find(|(candidate, _)| *candidate == value as u128)
                            .map(|(_, target)| target)
                            .unwrap_or_else(|| targets.otherwise());
                        queue.push(target);
                        continue;
                    }
                    if mir_utils::switch_targets_unreachable(self.tcx, self.body(), targets) {
                        queue.push(targets.otherwise());
                        continue;
                    }
                    let mut feasible = Vec::new();
                    for target in targets.all_targets().iter().copied() {
                        let mut candidate = self.clone();
                        crate::verify::vm::rules::exec_terminator(
                            &mut candidate,
                            terminator,
                            Some(target),
                        );
                        if candidate.path_infeasible {
                            continue;
                        }
                        let solver = Solver::new(self.z3_ctx);
                        if candidate.inline.symbolic_generic_const_inline {
                            candidate.assert_path_constraints(&solver);
                        } else {
                            candidate.assert_all(&solver);
                        }
                        match solver.check() {
                            SatResult::Sat => feasible.push((target, candidate)),
                            SatResult::Unknown => return InlineStep::Incomplete,
                            SatResult::Unsat => {}
                        }
                    }
                    if feasible.is_empty() {
                        return InlineStep::Complete(false);
                    }
                    if feasible.len() > 1 {
                        return InlineStep::Fork(feasible
                            .into_iter()
                            .map(|(target, state)| (state, target, visited.clone()))
                            .collect());
                    }
                    let (target, state) = feasible.pop().unwrap();
                    *self = state;
                    queue.push(target);
                }
                TerminatorKind::Call { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    if !self.inline.pending_states.is_empty() {
                        let Some(target) = target else {
                            return InlineStep::Complete(false);
                        };
                        let mut states = std::mem::take(&mut self.inline.pending_states)
                            .into_iter()
                            .map(|state| (*state, *target, visited.clone()))
                            .collect::<Vec<_>>();
                        states.push((self.clone(), *target, visited));
                        return InlineStep::Fork(states);
                    }
                    if let Some(target) = target {
                        queue.push(*target);
                    }
                }
                TerminatorKind::Drop { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(self, terminator, None);
                    queue.push(*target);
                }
                _ => crate::verify::vm::rules::exec_terminator(self, terminator, None),
            }
        }
        InlineStep::Complete(returned)
    }

    fn inline_execute_branches(
        &mut self,
        pre_uninit: &[AllocId],
        mut pending: Vec<InlineWorkItem<'z3, 'tcx>>,
    ) -> Option<Vec<Self>> {
        let mut returns = Vec::new();
        while let Some((mut state, block, mut visited)) = pending.pop() {
            if state.path_infeasible || !visited.insert(block) {
                continue;
            }
            let bb_data = &state.body().basic_blocks[block];
            for stmt in &bb_data.statements {
                crate::verify::vm::rules::exec_statement(&mut state, stmt);
            }
            let terminator = bb_data.terminator();
            match &terminator.kind {
                TerminatorKind::Goto { target, .. } => pending.push((state, *target, visited)),
                TerminatorKind::Return => {
                    let solver = Solver::new(self.z3_ctx);
                    if state.inline.symbolic_generic_const_inline {
                        state.assert_path_constraints(&solver);
                    } else {
                        state.assert_all(&solver);
                    }
                    match solver.check() {
                        SatResult::Sat => returns.push(state),
                        SatResult::Unknown => return None,
                        SatResult::Unsat => {}
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                    pending.push((state, *target, visited));
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    if let Some(v) = state.switch_discr_const(state.body(), discr) {
                        let target = targets
                            .iter()
                            .find(|(val, _)| *val == v as u128)
                            .map(|(_, target)| target)
                            .unwrap_or_else(|| targets.otherwise());
                        pending.push((state, target, visited));
                        continue;
                    }
                    if mir_utils::switch_targets_unreachable(state.tcx, state.body(), targets) {
                        pending.push((state, targets.otherwise(), visited));
                        continue;
                    }
                    for target in targets.all_targets().iter().copied() {
                        let mut candidate = state.clone();
                        crate::verify::vm::rules::exec_terminator(
                            &mut candidate,
                            terminator,
                            Some(target),
                        );
                        if candidate.path_infeasible {
                            continue;
                        }
                        let solver = Solver::new(self.z3_ctx);
                        if candidate.inline.symbolic_generic_const_inline {
                            candidate.assert_path_constraints(&solver);
                        } else {
                            candidate.assert_all(&solver);
                        }
                        match solver.check() {
                            SatResult::Sat => pending.push((candidate, target, visited.clone())),
                            SatResult::Unknown => return None,
                            SatResult::Unsat => {}
                        }
                    }
                    if pre_uninit.iter().any(|id| !state.content(*id).facts.initialized) {
                        let witness = state.find_uninit_witness(terminator, pre_uninit);
                        if !witness.is_empty() {
                            self.possible_uninit_allocs.extend(witness);
                            return None;
                        }
                    }
                }
                TerminatorKind::Call { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                    if let Some(target) = target {
                        for alternative in std::mem::take(&mut state.inline.pending_states) {
                            pending.push((*alternative, *target, visited.clone()));
                        }
                        pending.push((state, *target, visited));
                    }
                }
                TerminatorKind::Drop { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                    pending.push((state, *target, visited));
                }
                _ => crate::verify::vm::rules::exec_terminator(&mut state, terminator, None),
            }
        }
        Some(returns)
    }

    fn find_uninit_witness(
        &self,
        switch: &Terminator<'tcx>,
        candidates: &[AllocId],
    ) -> FxHashSet<AllocId> {
        let TerminatorKind::SwitchInt { targets, .. } = &switch.kind else {
            return FxHashSet::default();
        };
        if candidates.is_empty() {
            return FxHashSet::default();
        }
        let mut found = FxHashSet::default();
        let mut stack = Vec::new();
        for target in targets.all_targets().iter().copied() {
            let mut state = self.clone();
            crate::verify::vm::rules::exec_terminator(&mut state, switch, Some(target));
            stack.push((state, target, FxHashSet::default()));
        }
        let mut explored = 0;
        while let Some((mut state, block, mut visited)) = stack.pop() {
            if state.path_infeasible || explored >= 512 || !visited.insert(block) {
                continue;
            }
            explored += 1;
            let data = &state.body().basic_blocks[block];
            for statement in &data.statements {
                crate::verify::vm::rules::exec_statement(&mut state, statement);
            }
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Return => {
                    let solver = Solver::new(state.z3_ctx);
                    state.assert_all(&solver);
                    if solver.check() == SatResult::Sat {
                        for id in candidates {
                            if !state.content(*id).facts.initialized {
                                found.insert(*id);
                            }
                        }
                    }
                    if found.len() == candidates.len() {
                        break;
                    }
                }
                TerminatorKind::Goto { target, .. } => stack.push((state, *target, visited)),
                TerminatorKind::SwitchInt { targets, .. } => {
                    for target in targets.all_targets().iter().copied() {
                        let mut branch = state.clone();
                        crate::verify::vm::rules::exec_terminator(
                            &mut branch,
                            terminator,
                            Some(target),
                        );
                        stack.push((branch, target, visited.clone()));
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                    stack.push((state, *target, visited));
                }
                TerminatorKind::Call {
                    func,
                    target: Some(target),
                    ..
                } => {
                    let callee = mir_utils::dep_callee_resolved_def_id(
                        state.tcx,
                        state.current_frame.current_def_id,
                        func,
                    );
                    if callee.is_some_and(|def_id| state.tcx.is_mir_available(def_id)) {
                        let incomplete = state.incomplete_inline_branch;
                        let truncated = state.inline.inline_truncated_terms.len();
                        crate::verify::vm::rules::exec_terminator(&mut state, terminator, None);
                        if !state.unsupported_mir
                            && state.incomplete_inline_branch == incomplete
                            && state.inline.inline_truncated_terms.len() == truncated
                        {
                            stack.push((state, *target, visited));
                        }
                    }
                }
                _ => {}
            }
        }
        found
    }

    /// Find the local whose symbolic address matches `term` (the address a
    /// reference value points at). Used to resolve a `&self`/`&mut self`
    /// receiver (often a reborrow temp) back to the referent local that carries
    /// the materialized field values.
    pub(crate) fn find_local_by_address(&self, term: &Int<'z3>) -> Option<Local> {
        for (local, id) in &self.current_frame.local_alloc {
            if self.units[id.0].allocation.base == *term {
                return Some(*local);
            }
        }
        None
    }

    pub(crate) fn write_through_pointer(
        &mut self,
        pointer: &VmValue<'z3, 'tcx>,
        path: Vec<usize>,
        value: VmValue<'z3, 'tcx>,
    ) -> bool {
        let full_inner_write = pointer.provenance.as_ref().and_then(|prov| {
            let ty = self.alloc(prov.alloc_id).element_ty.as_ty()?;
            match ty.kind() {
                TyKind::Adt(def, args)
                    if crate::verify::api_classify::is_maybe_uninit_type(def.did())
                        && path.is_empty()
                        && prov.offset.simplify().as_u64() == Some(0)
                        && value.facts.init =>
                {
                    args.first()
                        .and_then(|arg| arg.as_type())
                        .filter(|inner| *inner == value.ty)
                        .map(|inner| (prov.alloc_id, inner))
                }
                _ => None,
            }
        });
        if let Some(prov) = &pointer.provenance {
            self.clear_write_evidence(prov.alloc_id);
        }
        let caller_referent =
            self.inline
                .arg_referents
                .iter()
                .enumerate()
                .find_map(|(i, referent)| {
                    let param = Local::from_usize(i + 1);
                    self.local_value(param)
                        .filter(|arg| arg.z3_term == pointer.z3_term)
                        .and_then(|_| *referent)
                });
        if let Some(local) = caller_referent {
            let wrote_object = path.is_empty()
                && pointer.provenance.as_ref().is_some_and(|prov| {
                    self.alloc(prov.alloc_id).is_external()
                        && self.alloc(prov.alloc_id).element_ty.as_ty() != Some(value.ty)
                })
                && self.write_provenance_allocation(pointer, value.clone());
            self.inline.deferred_field_writes.push((local, path, value));
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
            }
            return wrote_object;
        }
        if path.is_empty() && self.write_provenance_allocation(pointer, value.clone()) {
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
                self.content_mut(id).facts.inner_uninit = false;
            }
            return true;
        }
        if let Some(local) = self.find_local_by_address(&pointer.z3_term) {
            self.write_local_path(local, path, value);
            if let Some((id, ty)) = full_inner_write {
                self.content_mut(id).facts.written_pointee_ty = Some(ty);
                self.content_mut(id).facts.inner_uninit = false;
            }
            true
        } else if path.is_empty() {
            self.invalidate_provenance_allocation(pointer);
            false
        } else {
            false
        }
    }

    pub(crate) fn replay_deferred_writes(
        &mut self,
        writes: Vec<(Local, Vec<usize>, VmValue<'z3, 'tcx>)>,
    ) {
        for (local, path, value) in writes {
            let arg_idx = local.as_usize().checked_sub(1);
            let outer_referent = arg_idx
                .and_then(|i| self.inline.arg_referents.get(i).copied().flatten())
                .filter(|_| {
                    matches!(
                        self.body().local_decls[local].ty.kind(),
                        TyKind::Ref(..) | TyKind::RawPtr(..)
                    )
                });
            if let Some(referent) = outer_referent {
                self.inline
                    .deferred_field_writes
                    .push((referent, path, value));
            } else {
                self.write_local_path(local, path, value);
            }
        }
    }

    /// Resolve a *whole-place* reborrow (`_7 = &mut (*_1)` / `_7 = &(*_1)`,
    /// projection exactly `[Deref]`) back to its referent local.  Used to
    /// propagate the referent's materialized field values into an inlined
    /// callee when the reborrow temp's own forward assignment was pruned from
    /// the slice (so its value is still the stack-address default and
    /// `find_local_by_address` can only self-match).  Deliberately excludes
    /// field reborrows (`&mut (*_x).field`) — those address a subfield, whose
    /// value is tracked separately, so propagating the whole struct's fields
    /// would be wrong (BTreeMap's `NodeRef` handles).
    pub(crate) fn find_whole_reborrow_referent(&self, local: Local) -> Option<Local> {
        use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local
                        && dest.projection.is_empty()
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                        && place.projection.len() == 1
                        && matches!(place.projection[0].kind(), ProjectionElem::Deref)
                    {
                        return Some(place.local);
                    }
                }
            }
        }
        None
    }

    /// Resolve a *field* reborrow (`_7 = &mut (*_x).field`, projection
    /// `[Deref, Field(..)*]`) back to its referent local plus the field path.
    pub(crate) fn find_field_reborrow_referent(&self, local: Local) -> Option<(Local, Vec<usize>)> {
        use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local
                        && dest.projection.is_empty()
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                    {
                        let mut proj = place.projection.iter();
                        if !matches!(proj.next().map(|p| p.kind()), Some(ProjectionElem::Deref)) {
                            continue;
                        }
                        let mut fields = Vec::new();
                        for p in proj {
                            if let ProjectionElem::Field(f, _) = p.kind() {
                                fields.push(f.as_usize());
                            } else {
                                fields.clear();
                                break;
                            }
                        }
                        if !fields.is_empty() {
                            return Some((place.local, fields));
                        }
                    }
                }
            }
        }
        None
    }

    /// Resolve a whole-place copy root: `_x = copy _y` / `_x = move _y` (no
    /// projection) traces `_x` back to `_y`. Used to recover a value parameter's
    /// materialized fields when the optimizer inserted a copy temporary between
    /// the caller's argument and the inlined callee's parameter (e.g.
    /// `get_ext`'s `_2 = copy _1` before `NonZero::get(move _2)`), so that
    /// `handle_callee_entry`'s field collection can follow the copy chain to the
    /// local that actually carries the fields.
    pub(crate) fn find_copy_root(&self, local: Local) -> Option<Local> {
        use rustc_middle::mir::{Rvalue, StatementKind};
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local && dest.projection.is_empty() {
                        let op = match rvalue {
                            Rvalue::Use(op, ..) => Some(op),
                            _ => None,
                        };
                        if let Some(Operand::Copy(p) | Operand::Move(p)) = op
                            && p.projection.is_empty()
                        {
                            return Some(p.local);
                        }
                    }
                }
            }
        }
        None
    }


}
