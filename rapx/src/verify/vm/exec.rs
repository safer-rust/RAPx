//! Execute retained path items in the symbolic VM.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Local, TerminatorKind, UnwindAction};
use z3::ast::Int;

use crate::{analysis::path::CallArg, compat::FxHashSet, verify::slicer::RelevantItem};

use super::state::{ActiveMirItem, ActiveMirLocation, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Execute all retained MIR items in path order.
    pub(crate) fn execute_items(mut self, items: &[RelevantItem<'tcx>]) -> Vec<Self> {
        self.init_parameters();
        Self::execute_items_after(vec![self], items)
    }

    pub(crate) fn execute_items_after(
        mut states: Vec<Self>,
        items: &[RelevantItem<'tcx>],
    ) -> Vec<Self> {
        for item in items {
            let mut next = Vec::new();
            for mut state in states {
                let viable = if state.diagnostics.is_unsupported() {
                    true
                } else {
                    let viable = state.execute_item(item);
                    next.extend(
                        std::mem::take(&mut state.inline.pending_states)
                            .into_iter()
                            .map(|state| *state),
                    );
                    viable
                };
                if viable {
                    next.push(state);
                }
            }
            states = next;
        }
        states
    }

    fn execute_item(&mut self, item: &RelevantItem<'tcx>) -> bool {
        match item {
            RelevantItem::Statement {
                def_id,
                block,
                statement_index,
                ..
            } => {
                let body = self.body_for(*def_id);
                let statement = &body.basic_blocks[*block].statements[*statement_index];
                self.active_mir = Some(ActiveMirLocation {
                    def_id: *def_id,
                    block: block.as_usize(),
                    item: ActiveMirItem::Statement(*statement_index),
                    span: statement.source_info.span,
                });
                crate::verify::vm::rules::exec_statement(self, statement);
                true
            }
            RelevantItem::Terminator {
                def_id,
                block,
                switch_succ,
                ..
            } => {
                let body = self.body_for(*def_id);
                let terminator = body.basic_blocks[*block].terminator();
                self.active_mir = Some(ActiveMirLocation {
                    def_id: *def_id,
                    block: block.as_usize(),
                    item: ActiveMirItem::Terminator,
                    span: terminator.source_info.span,
                });
                let viable =
                    crate::verify::vm::rules::exec_terminator(self, terminator, *switch_succ);
                viable || (self.memory_events.is_enabled()
                    && matches!(&terminator.kind, TerminatorKind::Call { unwind: UnwindAction::Cleanup(target), .. } if Some(*target) == *switch_succ)
                )
            }
            RelevantItem::CalleeEntry { callee, body, args } => {
                self.active_mir = None;
                self.handle_callee_entry(*callee, *body, args);
                true
            }
            RelevantItem::CalleeExit { dest } => {
                self.active_mir = None;
                self.handle_callee_exit(*dest);
                true
            }
            RelevantItem::ContractFact { property } => {
                self.active_mir = None;
                self.assert_contract_fact(property);
                true
            }
        }
    }

    /// Enter an inlined callee during path execution: save the caller context,
    /// switch to the callee body, and bind the caller's argument locals to the
    /// callee's parameters.
    fn handle_callee_entry(
        &mut self,
        callee: DefId,
        body: Option<&'tcx rustc_middle::mir::Body<'tcx>>,
        args: &[CallArg],
    ) {
        let method_call = args.first().and_then(|arg| {
            let CallArg::Local(local) = arg else {
                return None;
            };
            self.local_value(Local::from_usize(*local))
                .and_then(|receiver| {
                    self.begin_method_call(callee, receiver, Some(Local::from_usize(*local)))
                })
        });
        let param_count = body
            .map(|body| body.arg_count)
            .unwrap_or_else(|| self.tcx.optimized_mir(callee).arg_count);
        let param_sources: Vec<Option<Local>> = (1..=param_count)
            .map(|param| match args.get(param - 1) {
                Some(CallArg::Local(local)) => Some(Local::from_usize(*local)),
                _ => None,
            })
            .collect();
        let arg_referents: Vec<Option<Local>> = param_sources
            .iter()
            .map(|arg| {
                let arg_local = (*arg)?;
                self.local_value(arg_local).and_then(|value| {
                    let address_referent = self.find_local_by_address(&value.z3_term);
                    let borrow_referent = self.find_whole_borrow_referent(arg_local);
                    let referent = if address_referent == Some(arg_local) {
                        borrow_referent.or(address_referent)
                    } else {
                        address_referent.or(borrow_referent)
                    };
                    referent
                        .or_else(|| {
                            self.find_copy_root(arg_local).filter(|root| {
                                self.local_value(*root).is_some_and(|source| {
                                    value
                                        .provenance_alloc_id()
                                        .is_some_and(|id| source.provenance_alloc_id() == Some(id))
                                }) && self.field_value(*root, &[0]).is_some()
                            })
                        })
                        .or_else(|| {
                            let outer = arg_local
                                .as_usize()
                                .checked_sub(1)
                                .and_then(|index| self.inline.arg_referents.get(index))
                                .copied()
                                .flatten()?;
                            let parent_alloc =
                                self.caller_frames.last()?.frame.local_alloc.get(&outer)?;
                            (value.provenance_alloc_id() == Some(*parent_alloc))
                                .then_some(arg_local)
                        })
                })
            })
            .collect();
        let saved_referents = std::mem::replace(&mut self.inline.arg_referents, arg_referents);
        let saved_writes = std::mem::take(&mut self.inline.deferred_field_writes);
        let frame = self.enter_frame(callee, body);

        // Collect the caller argument fields from the saved map, so the callee's
        // parameters inherit them (e.g. NonZero's non-zero inner value, and an
        // iterator's `ptr`/`end_or_len`). A whole-place reborrow
        // (`_7 = &mut (*_1)`) carries its referent's fields, so resolve it too;
        // likewise a whole-place copy temporary (`_2 = copy _1`) that the
        // optimizer inserted between the caller's argument and the inlined
        // callee's parameter — follow both chains so the local that actually
        // materialized the fields is found.
        let mut arg_fields: Vec<(usize, Vec<usize>, VmValue<'z3, 'tcx>)> = Vec::new();
        let mut bound_fields: FxHashSet<(usize, Vec<usize>)> = FxHashSet::default();
        for (i, caller_local) in param_sources.iter().enumerate() {
            let Some(caller_local) = caller_local else {
                continue;
            };
            let caller_local = *caller_local;
            let mut source_locals: Vec<(Local, Vec<usize>)> = Vec::new();
            let mut seen: FxHashSet<(Local, Vec<usize>)> = FxHashSet::default();
            let mut stack = vec![(caller_local, Vec::new())];
            while let Some((cur, prefix)) = stack.pop() {
                if !seen.insert((cur, prefix.clone())) {
                    continue;
                }
                source_locals.push((cur, prefix.clone()));
                if let Some(r) = self.find_whole_borrow_referent(cur) {
                    stack.push((r, prefix.clone()));
                }
                if let Some((r, fields)) = self.find_field_reborrow_referent(cur) {
                    let mut new_prefix = prefix.clone();
                    new_prefix.extend(fields);
                    stack.push((r, new_prefix));
                }
                if let Some(c) = self.find_copy_root(cur) {
                    stack.push((c, prefix.clone()));
                }
            }
            for (src, prefix) in source_locals {
                let keys: Vec<Vec<usize>> = self
                    .frame_field_paths(&frame, src)
                    .into_iter()
                    .filter(|f| {
                        prefix.is_empty()
                            || (f.len() >= prefix.len() && f[..prefix.len()] == prefix[..])
                    })
                    .collect();
                for fields in keys {
                    if let Some(fv) = self.frame_field_value(&frame, src, &fields).cloned() {
                        let stripped = if prefix.is_empty() {
                            fields
                        } else {
                            fields[prefix.len()..].to_vec()
                        };
                        if bound_fields.insert((i + 1, stripped.clone())) {
                            arg_fields.push((i + 1, stripped, fv));
                        }
                    }
                }
            }
        }

        for (i, arg) in param_sources.iter().enumerate() {
            if let Some(v) = arg
                .and_then(|local| self.frame_local_value(&frame, local))
                .cloned()
            {
                let inner_uninit = arg
                    .and_then(|local| frame.local_alloc.get(&local))
                    .is_some_and(|id| self.content(*id).facts.inner_uninit);
                let param = Local::from_usize(i + 1);
                self.set_local(param, v);
                if inner_uninit && let Some(&id) = self.current_frame.local_alloc.get(&param) {
                    self.content_mut(id).facts.inner_uninit = true;
                }
            }
        }

        for (index, arg) in args.iter().enumerate().take(param_count) {
            let local = Local::from_usize(index + 1);
            let ty = self.body().local_decls[local].ty;
            let (term, source) = match arg {
                CallArg::Local(_) => continue,
                CallArg::Literal(value) => {
                    let width = self.size_of_ty(ty).saturating_mul(8);
                    let text = if matches!(ty.kind(), rustc_middle::ty::TyKind::Int(_))
                        && (1..=128).contains(&width)
                    {
                        let shift = 128 - width as u32;
                        (((*value << shift) as i128) >> shift).to_string()
                    } else {
                        value.to_string()
                    };
                    (
                        Int::from_str(self.z3_ctx, &text).expect("valid integer literal"),
                        ValueSource::CallsiteConst,
                    )
                }
                CallArg::Symbol(text) => (self.symbolic_const_term_text(text), ValueSource::None),
                CallArg::FieldOffset => (self.fresh_int("field_offset"), ValueSource::FieldOffset),
                CallArg::Opaque => (self.fresh_int("opaque_call_arg"), ValueSource::None),
            };
            let mut value = VmValue::new(term, ty);
            value.source = source;
            self.set_local(local, value);
        }

        for (callee_param, fields, fv) in arg_fields {
            self.set_field_value(Local::from_usize(callee_param), fields, fv);
        }
        self.caller_frames.push(super::state::SavedCallerFrame {
            frame,
            method_call,
            postcondition_args: param_sources,
            arg_referents: saved_referents,
            deferred_writes: saved_writes,
        });
    }

    /// Exit an inlined callee: capture the callee's return value, restore the
    /// caller context, and write the return value to the caller's destination.
    fn handle_callee_exit(&mut self, dest: usize) {
        let callee = self.current_frame.current_def_id;
        let ret = self.local_value(Local::from_usize(0)).cloned();
        let ret_inner_uninit = self
            .current_frame
            .local_alloc
            .get(&Local::from_usize(0))
            .is_some_and(|id| self.content(*id).facts.inner_uninit);
        let ret_fields: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = self
            .field_paths(Local::from_usize(0))
            .into_iter()
            .filter_map(|f| {
                self.field_value(Local::from_usize(0), &f)
                    .cloned()
                    .map(|v| (f, v))
            })
            .collect();
        let writes = std::mem::take(&mut self.inline.deferred_field_writes);
        let (method_call, postcondition_args) = match self.caller_frames.pop() {
            Some(saved) => {
                self.restore_frame(saved.frame);
                self.inline.arg_referents = saved.arg_referents;
                self.inline.deferred_field_writes = saved.deferred_writes;
                (saved.method_call, Some(saved.postcondition_args))
            }
            None => {
                self.inline.arg_referents.clear();
                (None, None)
            }
        };
        self.replay_deferred_writes(writes);
        if let Some(mut v) = ret.clone() {
            let dest_ty = self.body().local_decls[Local::from_usize(dest)].ty;
            v.ty = dest_ty;
            let at_base = v
                .provenance
                .as_ref()
                .is_some_and(|p| p.offset.as_u64() == Some(0));
            if at_base {
                v.facts.non_null = true;
            }
            self.set_local(Local::from_usize(dest), v);
            if ret_inner_uninit
                && let Some(&dest_id) = self.current_frame.local_alloc.get(&Local::from_usize(dest))
            {
                self.content_mut(dest_id).facts.inner_uninit = true;
            }
            if let Some(dest_alloc_id) = self
                .current_frame
                .local_alloc
                .get(&Local::from_usize(dest))
                .copied()
            {
                self.content_mut(dest_alloc_id).facts.initialized = true;
            }
        }
        for (fields, fv) in ret_fields {
            self.set_field_value(Local::from_usize(dest), fields, fv);
        }
        self.materialize_slice_ref_return(Local::from_usize(dest));
        if let Some(args) = postcondition_args
            && self.local_value(Local::from_usize(dest)).is_some()
        {
            self.assert_call_postconditions(callee, &args, Local::from_usize(dest));
            self.assert_call_result_invariants(Local::from_usize(dest));
        }
        self.finish_method_call(method_call, ret.as_ref());
    }
}
