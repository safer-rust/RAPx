use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::{
    mir::{
        BasicBlock, Local, Operand, ProjectionElem, Rvalue, StatementKind, Terminator,
        TerminatorKind,
    },
    ty::{EarlyBinder, Instance, TyKind, TypingEnv},
};
use z3::ast::{Bool, Int};
use z3::{SatResult, Solver};

use super::state::{AllocId, MemoryContent, VmState, VmValue};
use crate::compat::{FxHashSet, Spanned};
use crate::helpers::mir_utils;
use crate::limit::MAX_INLINE_DEPTH;
use crate::verify::api_classify;

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
        let frame = state.enter_frame(method, None);
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
                crate::verify::vm::mir_rules::exec_contract_method_statement(&mut state, statement);
            }
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Return => {
                    if state.diagnostics.is_unsupported() || state.diagnostics.has_incomplete_inline_branch() {
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
                        if crate::verify::vm::mir_rules::exec_terminator(
                            &mut branch,
                            terminator,
                            Some(target),
                        ).continues() {
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

    /// Recursively execute a callee's MIR body inline.
    ///
    /// Binds the caller's argument values to the callee's parameters,
    /// executes the callee's MIR, and writes the return value to
    /// the caller's destination local. Returns whether the call may return.
    pub(super) fn exec_inline_call(
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
            return true;
        }
        let instantiated_body = if let Some(instance) = instance {
            let caller_def_id = self.current_frame.current_def_id;
            if mir_utils::has_unresolved_const_args(self.tcx, caller_def_id, instance.args) {
                self.record_missing_mir(callee_def_id);
                return true;
            }
            let body = self.tcx.optimized_mir(callee_def_id).clone();
            let Ok(body) = instance.try_instantiate_mir_and_normalize_erasing_regions(
                self.tcx,
                TypingEnv::post_analysis(self.tcx, caller_def_id),
                EarlyBinder::bind(self.tcx, body),
            ) else {
                self.record_missing_mir(callee_def_id);
                return true;
            };
            Some(&*self.tcx.arena.alloc(body))
        } else {
            None
        };
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
        let caller_local_count = self.body().local_decls.len();
        let resolved_arg_referents: Vec<Option<Local>> = arg_values
            .iter()
            .enumerate()
            .map(|(index, value)| {
                if let super::state::ValueSource::FieldBorrow { base, .. } = &value.source {
                    return Some(*base);
                }
                let arg_local = caller_arg_locals.get(index).copied().flatten();
                let address_referent = self.find_local_by_address(&value.z3_term);
                let borrow_referent =
                    arg_local.and_then(|local| self.find_whole_borrow_referent(local));
                let referent = if address_referent == arg_local {
                    borrow_referent.or(address_referent)
                } else {
                    address_referent.or(borrow_referent)
                };
                referent.or_else(|| {
                    let local = caller_arg_locals.get(index).copied().flatten()?;
                    local
                        .as_usize()
                        .checked_sub(1)
                        .and_then(|index| self.inline.arg_referents.get(index))
                        .copied()
                        .flatten()?;
                    let provenance = value.provenance_alloc_id()?;
                    (self
                        .local_value(local)
                        .and_then(VmValue::provenance_alloc_id)
                        == Some(provenance))
                    .then_some(local)
                })
            })
            .collect();
        if resolved_arg_referents
            .iter()
            .flatten()
            .any(|local| local.as_usize() >= caller_local_count)
        {
            self.diagnostics.mark_unsupported();
        }
        let inline_arg_referents: Vec<Option<Local>> = resolved_arg_referents
            .into_iter()
            .map(|local| local.filter(|local| local.as_usize() < caller_local_count))
            .collect();
        let caller_referents = inline_arg_referents.clone();
        // Whole-place reborrow referents, resolved from the *caller's* MIR
        // before the body is switched to the callee (used to propagate the
        // referent's struct fields into the callee for `old = self.ptr`).
        let reborrow_referents: Vec<Option<Local>> = caller_arg_locals
            .iter()
            .map(|arg_opt| arg_opt.and_then(|a| self.find_whole_borrow_referent(a)))
            .collect();
        let arg_inner_uninit: Vec<bool> = caller_arg_locals
            .iter()
            .map(|arg| {
                arg.and_then(|local| self.current_frame.local_alloc.get(&local))
                    .is_some_and(|id| self.content(*id).facts.inner_uninit)
            })
            .collect();
        let frame = self.enter_frame(callee_def_id, instantiated_body);
        let saved_inline_arg_referents =
            std::mem::replace(&mut self.inline.arg_referents, inline_arg_referents);
        let saved_deferred_field_writes = std::mem::take(&mut self.inline.deferred_field_writes);

        for (i, arg_val) in arg_values.iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            self.ensure_local_allocation(callee_local);
            let mut arg_val = arg_val.clone();
            if let super::state::ValueSource::FieldBorrow { base, .. } = &mut arg_val.source {
                *base = callee_local;
            }
            self.set_local(callee_local, arg_val);
            if arg_inner_uninit.get(i) == Some(&true)
                && let Some(&id) = self.current_frame.local_alloc.get(&callee_local)
            {
                self.content_mut(id).facts.inner_uninit = true;
            }
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
            .filter(|id| before_inline.allocation_needs_write(*id))
            .collect();
        let may_recurse = self.body().basic_blocks.iter().any(|block| {
            let TerminatorKind::Call { func, .. } = &block.terminator().kind else {
                return false;
            };
            mir_utils::dep_callee_resolved_def_id(self.tcx, callee_def_id, func)
                == Some(callee_def_id)
        });
        let mut returns = self.inline_execute_body(&pre_uninit);
        let return_ty = self.body().local_decls[Local::from_usize(0)].ty;
        if crate::helpers::mir_utils::layout_of_ty(self.tcx, callee_def_id, return_ty)
            .is_some_and(|layout| layout.size.bytes() == 0)
            && let Some(states) = returns.as_mut()
        {
            for state in states {
                if state.local_value(Local::from_usize(0)).is_none() {
                    let term = state.fresh_int("zst_return");
                    state.set_local(Local::from_usize(0), VmValue::new(term, return_ty));
                }
            }
        }
        if returns.as_ref().is_none_or(|states| {
            states
                .iter()
                .any(|state| state.local_value(Local::from_usize(0)).is_none())
        }) {
            let witnessed: Vec<_> = self
                .units
                .iter()
                .enumerate()
                .filter_map(|(index, unit)| {
                    unit.content.facts.may_be_uninit.then_some(AllocId(index))
                })
                .collect();
            let explored_diagnostics = self.diagnostics.clone();
            *self = before_inline;
            for id in witnessed {
                if let Some(unit) = self.units.get_mut(id.0) {
                    unit.content.facts.may_be_uninit = true;
                }
            }
            self.diagnostics.merge_inline_fallback(&explored_diagnostics);
            let dest_ty = self.body().local_decls[dest].ty;
            let unknown_term = self.fresh_int("inline_branch_unknown");
            self.inline.inline_branch_terms.insert(unknown_term.clone());
            if may_recurse {
                self.inline
                    .inline_truncated_terms
                    .insert(unknown_term.clone());
            }
            self.set_local(dest, VmValue::new(unknown_term, dest_ty));
            let mut unknown_effect = matches!(
                self.tcx.def_kind(callee_def_id),
                DefKind::Fn | DefKind::AssocFn
            ) && self.tcx.fn_sig(callee_def_id).skip_binder().safety()
                == rustc_hir::Safety::Unsafe;
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
            self.diagnostics.mark_unsupported_if(unknown_effect);
            return true;
        }
        let mut completed = Vec::new();
        for mut state in returns.unwrap() {
            state.recover_leaked_owner_shares(callee_def_id);
            let return_val = state.local_value(Local::from_usize(0)).cloned();
            let return_inner_uninit = state
                .current_frame
                .local_alloc
                .get(&Local::from_usize(0))
                .is_some_and(|id| state.content(*id).facts.inner_uninit);
            let return_fields: Vec<_> = state
                .field_paths(Local::from_usize(0))
                .into_iter()
                .filter_map(|path| {
                    state
                        .field_value(Local::from_usize(0), &path)
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
            if return_inner_uninit
                && let Some(&dest_id) = state.current_frame.local_alloc.get(&dest)
            {
                state.content_mut(dest_id).facts.inner_uninit = true;
            }
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
            return false;
        }
        *self = completed.remove(0);
        self.inline
            .pending_states
            .extend(completed.into_iter().map(Box::new));
        true
    }

    fn forget_inline_referent(&mut self, local: Local) {
        let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied() else {
            self.diagnostics.mark_unsupported();
            return;
        };
        if self.content(alloc_id).facts.may_be_uninit {
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
            if !visited.insert(block) {
                continue;
            }
            let bb_data = &self.body().basic_blocks[block];
            for stmt in &bb_data.statements {
                crate::verify::vm::mir_rules::exec_statement(self, stmt);
            }
            let terminator = bb_data.terminator();
            match &terminator.kind {
                TerminatorKind::Goto { target, .. } => queue.push(*target),
                TerminatorKind::Return => returned = true,
                TerminatorKind::Assert { target, .. } => {
                    if crate::verify::vm::mir_rules::exec_terminator(self, terminator, None).continues() {
                        queue.push(*target);
                    }
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    if let Some(target) = super::mir_rules::forced_inline_switch_target(
                        self,
                        self.body(),
                        discr,
                        targets,
                    ) {
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
                        if !crate::verify::vm::mir_rules::exec_terminator(
                            &mut candidate,
                            terminator,
                            Some(target),
                        ).continues() {
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
                        return InlineStep::Fork(
                            feasible
                                .into_iter()
                                .map(|(target, state)| (state, target, visited.clone()))
                                .collect(),
                        );
                    }
                    let (target, state) = feasible.pop().unwrap();
                    *self = state;
                    queue.push(target);
                }
                TerminatorKind::Call { target, .. } => {
                    let viable = crate::verify::vm::mir_rules::exec_terminator(self, terminator, None).continues();
                    if !self.inline.pending_states.is_empty() {
                        let Some(target) = target else {
                            return InlineStep::Complete(false);
                        };
                        let mut states = std::mem::take(&mut self.inline.pending_states)
                            .into_iter()
                            .map(|state| (*state, *target, visited.clone()))
                            .collect::<Vec<_>>();
                        if viable {
                            states.push((self.clone(), *target, visited));
                        }
                        return InlineStep::Fork(states);
                    }
                    if !viable {
                        return InlineStep::Complete(false);
                    }
                    if let Some(target) = target {
                        queue.push(*target);
                    }
                }
                TerminatorKind::Drop { target, .. } => {
                    if crate::verify::vm::mir_rules::exec_terminator(self, terminator, None).continues() {
                        queue.push(*target);
                    }
                }
                _ => {
                    if !crate::verify::vm::mir_rules::exec_terminator(self, terminator, None).continues() {
                        return InlineStep::Complete(false);
                    }
                }
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
            if !visited.insert(block) {
                continue;
            }
            let bb_data = &state.body().basic_blocks[block];
            for stmt in &bb_data.statements {
                crate::verify::vm::mir_rules::exec_statement(&mut state, stmt);
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
                    if crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None).continues() {
                        pending.push((state, *target, visited));
                    }
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    if let Some(target) = super::mir_rules::forced_inline_switch_target(
                        &state,
                        state.body(),
                        discr,
                        targets,
                    ) {
                        pending.push((state, target, visited));
                        continue;
                    }
                    if mir_utils::switch_targets_unreachable(state.tcx, state.body(), targets) {
                        pending.push((state, targets.otherwise(), visited));
                        continue;
                    }
                    for target in targets.all_targets().iter().copied() {
                        let mut candidate = state.clone();
                        if !crate::verify::vm::mir_rules::exec_terminator(
                            &mut candidate,
                            terminator,
                            Some(target),
                        ).continues() {
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
                    if pre_uninit
                        .iter()
                        .any(|id| state.allocation_needs_write(*id))
                    {
                        let witness = state.find_uninit_witness(terminator, pre_uninit);
                        if !witness.is_empty() {
                            for id in witness {
                                self.content_mut(id).facts.may_be_uninit = true;
                            }
                            return None;
                        }
                    }
                }
                TerminatorKind::Call { target, .. } => {
                    let viable =
                        crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None).continues();
                    if let Some(target) = target {
                        for alternative in std::mem::take(&mut state.inline.pending_states) {
                            pending.push((*alternative, *target, visited.clone()));
                        }
                        if viable {
                            pending.push((state, *target, visited));
                        }
                    }
                }
                TerminatorKind::Drop { target, .. } => {
                    if crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None).continues() {
                        pending.push((state, *target, visited));
                    }
                }
                _ => {
                    let _ = crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None);
                }
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
            if crate::verify::vm::mir_rules::exec_terminator(&mut state, switch, Some(target)).continues() {
                stack.push((state, target, FxHashSet::default()));
            }
        }
        let mut explored = 0;
        while let Some((mut state, block, mut visited)) = stack.pop() {
            if explored >= 512 || !visited.insert(block) {
                continue;
            }
            explored += 1;
            let data = &state.body().basic_blocks[block];
            for statement in &data.statements {
                crate::verify::vm::mir_rules::exec_statement(&mut state, statement);
            }
            let terminator = data.terminator();
            match &terminator.kind {
                TerminatorKind::Return => {
                    let solver = Solver::new(state.z3_ctx);
                    state.assert_all(&solver);
                    if solver.check() == SatResult::Sat {
                        for id in candidates {
                            if state.allocation_needs_write(*id) {
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
                        if crate::verify::vm::mir_rules::exec_terminator(
                            &mut branch,
                            terminator,
                            Some(target),
                        ).continues() {
                            stack.push((branch, target, visited.clone()));
                        }
                    }
                }
                TerminatorKind::Assert { target, .. } => {
                    if crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None).continues() {
                        stack.push((state, *target, visited));
                    }
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
                        let incomplete = state.diagnostics.has_incomplete_inline_branch();
                        let truncated = state.inline.inline_truncated_terms.len();
                        let viable =
                            crate::verify::vm::mir_rules::exec_terminator(&mut state, terminator, None).continues();
                        if viable
                            && !state.diagnostics.is_unsupported()
                            && state.diagnostics.has_incomplete_inline_branch() == incomplete
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

    fn allocation_needs_write(&self, id: AllocId) -> bool {
        let facts = &self.content(id).facts;
        !facts.initialized || (facts.inner_uninit && facts.written_pointee_ty.is_none())
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

    /// Resolve a direct mutable borrow or a whole-place reborrow back to its
    /// referent local. Used to
    /// propagate the referent's materialized field values into an inlined
    /// callee when the reborrow temp's own forward assignment was pruned from
    /// the slice (so its value is still the stack-address default and
    /// `find_local_by_address` can only self-match).  Deliberately excludes
    /// field reborrows (`&mut (*_x).field`) — those address a subfield, whose
    /// value is tracked separately, so propagating the whole struct's fields
    /// would be wrong (BTreeMap's `NodeRef` handles).
    pub(crate) fn find_whole_borrow_referent(&self, local: Local) -> Option<Local> {
        for bb in self.body().basic_blocks.iter() {
            for stmt in &bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local == local
                        && dest.projection.is_empty()
                        && let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = rvalue
                        && ((place.projection.is_empty()
                            && matches!(
                                self.body().local_decls[local].ty.kind(),
                                TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
                                    | TyKind::RawPtr(_, rustc_middle::ty::Mutability::Mut)
                            ))
                            || (place.projection.len() == 1
                                && matches!(place.projection[0].kind(), ProjectionElem::Deref)))
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
