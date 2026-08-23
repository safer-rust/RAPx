//! Call handling for the symbolic VM.
//!
//! Bridges the existing call summary infrastructure (`call_summary`)
//! with the new symbolic VM state. The `exec_call` method is called
//! from `exec.rs` when a `Call` terminator is encountered.
//!
//! When the callee has MIR available, the VM recursively inlines the
//! callee's body to achieve context-sensitive precision. Otherwise it
//! falls back to the summary-based approach.

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{BasicBlock, Local, Operand, TerminatorKind};
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::{Ast, Bool, Int};

use crate::compat::{FxHashSet, Spanned};
use crate::verify::call_summary::{self, CallEffect};
use crate::verify::def_use::{PlaceBaseKey, PlaceKey};
use crate::helpers::mir_utils::operand_place;
use crate::helpers::api_classify;

use super::state::{AllocId, Provenance, VmState, VmValue, ValueInvariants};

/// Classification of a call site for dispatch prioritization.
const MAX_INLINE_DEPTH: usize = 5;

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Execute a call terminator. Summary takes priority (fn_simulator →
    /// interprocedural) for their hand-crafted invariants. Inline execution
    /// is tried as a fallback when the summary is unsupported and the callee
    /// has available MIR (including dependency crates).
    pub fn exec_call(
        &mut self,
        func: &Operand<'tcx>,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
        _target: Option<BasicBlock>,
        _cleanup: Option<BasicBlock>,
        caller_def_id: DefId,
    ) {
        let arg_values: Vec<VmValue<'ctx, 'tcx>> = args
            .iter()
            .map(|arg| self.value_of_operand(&arg.node))
            .collect();

        let name = crate::helpers::mir_utils::call_name(self.tcx, func);

        // ── select_unpredictable: result ∈ {x, y} ─────────────────────
        if self.try_select_unpredictable(&name, &arg_values, args, destination) {
            return;
        }

        // Slice range indexing: `<[T]>::index(range)` / `::index_mut(range)`
        // returns a sub-slice whose length is the range's extent.
        if self.try_slice_index(&name, &arg_values, args, destination) {
            return;
        }

        // Iter::len() / Iter::is_empty(): compute from struct fields.
        if self.try_iter_len_is_empty(&name, &arg_values, args, destination) {
            return;
        }

        // Iter::next() / IterMut::next(): advance ptr by 1 and return old.
        if self.try_iter_next(&name, &arg_values, args, destination) {
            return;
        }

        // post_inc_start / pre_dec_end on Iter/IterMut: apply the ptr/end
        // update as a side effect, then fall through to normal handling.
        // These callees have SwitchInt (ZST branch) exceeding inline limits,
        // so the ptr update would otherwise be lost.
        let callee = crate::helpers::mir_utils::dep_callee_def_id(func);
        let caller_arg_locals: Vec<Local> = args.iter()
            .filter_map(|a| a.node.place().map(|p| p.local))
            .collect();
        if let Some(c) = callee {
            if self.tcx.is_mir_available(c) {
                let cname = self.tcx.def_path_str(c);
                if (api_classify::is_iter_ptr_adj(&cname))
                    && arg_values.len() >= 2
                {
                    self.apply_iter_ptr_update(c, &cname, &arg_values, &caller_arg_locals);
                    // Continue to normal handling (return value is () , ignored).
                }
            }
        }

        // Try inline for callees with available MIR, unless fn_simulator
        // has a precise summary (memory allocation, intrinsics, known ptr
        // arithmetic, etc.). The summary path handles these with
        // hand-crafted invariants that are more precise than BFS inline.
        let callee = crate::helpers::mir_utils::dep_callee_def_id(func);
        let mut tried_inline = false;
        // Extract caller arg locals for field_value propagation into inline.
        let caller_arg_locals: Vec<Local> = args.iter()
            .filter_map(|a| a.node.place().map(|p| p.local))
            .collect();
        if let Some(c) = callee {
            if self.tcx.is_mir_available(c) {
                let has_fn_sim = crate::verify::call_summary::fn_simulator::lookup_effect(
                    self.tcx, caller_def_id, Some(c), &name, func, destination,
                ).is_some();
                if !has_fn_sim {
                    if self.exec_inline_call(c, &arg_values, &caller_arg_locals, destination, 0) {
                        self.materialize_const_bytes_after_call(args, destination);
                        return;
                    }
                    tried_inline = true;
                }
            }
        }

        let summary = call_summary::effect_summary(
            self.tcx,
            caller_def_id,
            func,
            destination,
        );

        self.last_call_name = summary.name.clone();

        if !summary.unsupported {
            for effect in &summary.effects {
                self.apply_call_effect(effect, &arg_values, &caller_arg_locals, destination);
            }
        } else {
            if !tried_inline {
                let callee = crate::helpers::mir_utils::dep_callee_def_id(func);
                let inlined = callee
                    .and_then(|c| {
                        if self.tcx.is_mir_available(c) {
                            Some(self.exec_inline_call(c, &arg_values, &caller_arg_locals, destination, 0))
                        } else {
                            None
                        }
                    })
                    .unwrap_or(false);
                if inlined {
                    self.materialize_const_bytes_after_call(args, destination);
                    return;
                }
            }
            self.notes.push(format!("unsupported call: {}", summary.name));
            let dest_ty = self.body.local_decls[destination].ty;
            let term = self.fresh_int(&format!("callret_{}", destination.as_usize()));
            if let TyKind::Adt(adt_def, _) = dest_ty.kind() {
                let path = self.tcx.def_path_str(adt_def.did());
                if api_classify::is_std_ordering(&path) {
                    let minus_one = Int::from_i64(self.ctx, -1);
                    let one = Int::from_i64(self.ctx, 1);
                    self.path_conditions.push(term.ge(&minus_one));
                    self.path_conditions.push(term.le(&one));
                }
            }
            // bool return (bool, Result::ok/err, etc.) — constrain to {0, 1}
            if dest_ty.is_bool() {
                let zero = Int::from_u64(self.ctx, 0);
                let one = Int::from_u64(self.ctx, 1);
                self.path_conditions.push(term.ge(&zero));
                self.path_conditions.push(term.le(&one));
            }
            self.set_local(
                destination,
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                },
            );
            return;
        }

        self.materialize_const_bytes_after_call(args, destination);
    }

    /// `select_unpredictable`: result ∈ {x, y}.
    fn try_select_unpredictable(
        &mut self,
        name: &str,
        arg_values: &[VmValue<'ctx, 'tcx>],
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) -> bool {
        if !api_classify::is_select_unpredictable(name) || arg_values.len() < 3 {
            return false;
        }
        let term = self.fresh_int(&format!("selunpred_{}", destination.as_usize()));
        let dest_ty = self.body.local_decls[destination].ty;
        let eq1 = term._eq(&arg_values[1].term);
        let eq2 = term._eq(&arg_values[2].term);
        self.path_conditions.push(Bool::or(self.ctx, &[&eq1, &eq2]));
        let prov = arg_values[1].provenance.clone()
            .or_else(|| arg_values[2].provenance.clone());
        // Track operand chain for inject_div_axioms_for_term so that
        // division axioms reachable through select_unpredictable
        // can be found even across Use / Cast chains.
        let dest_pk = PlaceKey { base: PlaceBaseKey::Local(destination.as_usize()), fields: vec![] };
        let lhs_pk = args.get(1).and_then(|a| operand_place(&a.node));
        let rhs_pk = args.get(2).and_then(|a| operand_place(&a.node));
        self.other_op_sources.insert(dest_pk, (lhs_pk, rhs_pk));
        self.set_local(destination, VmValue {
            term,
            ty: dest_ty,
            provenance: prov,
            invariants: ValueInvariants::default(),
        });
        true
    }

    /// Slice range indexing `<[T]>::index(range)` / `::index_mut(range)`:
    /// returns a sub-slice whose length is the range's extent. Model it as a
    /// sub-allocation of the array so downstream `into_iter`/`next()` see the
    /// correct element count (empty for `..0`). Single-element indexing
    /// (`index(usize)`) has a non-slice destination and keeps the plain
    /// alias behaviour from the summary table.
    fn try_slice_index(
        &mut self,
        name: &str,
        arg_values: &[VmValue<'ctx, 'tcx>],
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) -> bool {
        let is_index = name.ends_with("::Index::index") || name.ends_with("::IndexMut::index_mut");
        if !is_index || arg_values.len() < 2 {
            return false;
        }
        let dest_ty = self.body.local_decls[destination].ty;
        let is_slice = matches!(dest_ty.kind(), TyKind::Ref(_, inner, _)
            if matches!(inner.kind(), TyKind::Slice(_)));
        if !is_slice {
            return false;
        }
        let Some(prov) = arg_values[0].provenance.clone() else {
            return false;
        };
        let array_term = arg_values[0].term.clone();
        let (elem_ty, elem_size) = match arg_values[0].ty.kind() {
            TyKind::Ref(_, inner, _) => match inner.kind() {
                TyKind::Array(e, _) | TyKind::Slice(e) => {
                    (*e, self.size_of_ty(*e).max(1) as u64)
                }
                _ => (arg_values[0].ty, 1),
            },
            _ => (arg_values[0].ty, 1),
        };
        let elem_align = self.align_of_ty(elem_ty).max(1);
        // The range argument (RangeTo/RangeFrom/Range) is an aggregate; its
        // field 0 is the end bound (for RangeTo this is the slice length).
        let range_local = args.get(1).and_then(|a| match &a.node {
            Operand::Copy(p) | Operand::Move(p) => Some(p.local),
            _ => None,
        });
        let range_len = match range_local.and_then(|l| self.field_value(l, &[0]).map(|v| v.term.clone())) {
            Some(end) => end,
            None => {
                // RangeFull or unknown: fall back to the array's full length.
                self.alloc(prov.alloc_id).size.clone()
                    .div(&Int::from_u64(self.ctx, elem_size))
            }
        };
        let size_bytes = Int::mul(self.ctx, &[&range_len, &Int::from_u64(self.ctx, elem_size)]);
        let (alloc_id, _) = self.allocate(size_bytes, elem_align, Some(elem_ty));
        self.alloc_mut(alloc_id).parent = Some(prov.alloc_id);
        self.set_local(destination, VmValue {
            term: array_term,
            ty: dest_ty,
            provenance: Some(Provenance {
                alloc_id,
                offset: Int::from_u64(self.ctx, 0),
                is_field_offset: false,
            }),
            invariants: ValueInvariants {
                non_null: true, aligned: true, init: true, in_bounds: true,
                ..Default::default()
            },
        });
        true
    }

    /// `Iter::len()` / `Iter::is_empty()`: compute from struct fields
    /// (ptr + end_or_len share the same allocation with per-field offsets).
    /// The generic fn_simulator would return sizeof(Iter)/sizeof(T), which is
    /// wrong for generic T.
    fn try_iter_len_is_empty(
        &mut self,
        name: &str,
        arg_values: &[VmValue<'ctx, 'tcx>],
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) -> bool {
        if !((name.contains("::Iter<") || name.contains("::IterMut<")
            || name.ends_with("::Iter::len") || name.ends_with("::IterMut::len")
            || name.ends_with("::Iter::is_empty") || name.ends_with("::IterMut::is_empty"))
            && (name.ends_with("::len") || name.ends_with("::is_empty"))
            && arg_values.len() >= 1)
        {
            return false;
        }
        let receiver_local = args.first().and_then(|a| a.node.place()).map(|p| p.local);
        let Some(local) = receiver_local else { return false; };
        // len() = (end_or_len - ptr) / sizeof(T)   (non-ZST)
        // is_empty() = ptr == end_or_len           (non-ZST)
        let (Some(ptr), Some(end)) = (self.field_value(local, &[0]), self.field_value(local, &[1])) else {
            return false;
        };
        let (Some(pp), Some(ep)) = (&ptr.provenance, &end.provenance) else {
            return false;
        };
        if pp.alloc_id != ep.alloc_id {
            return false;
        }
        let dest_ty = self.body.local_decls[destination].ty;
        if name.ends_with("::len") {
            let diff = Int::sub(self.ctx, &[&ep.offset, &pp.offset]);
            let sz = Int::from_u64(self.ctx, self.iter_elem_size(ptr));
            let val = VmValue::new(diff.div(&sz), dest_ty);
            self.set_local(destination, val);
        } else {
            // is_empty(): ptr == end_or_len  (non-ZST branch)
            let eq = pp.offset._eq(&ep.offset);
            let zero = Int::from_u64(self.ctx, 0);
            let one = Int::from_u64(self.ctx, 1);
            let val = VmValue {
                term: eq.ite(&one, &zero),
                ty: dest_ty,
                provenance: None,
                invariants: ValueInvariants::default(),
            };
            self.set_local(destination, val);
        }
        true
    }

    /// `Iter::next()` / `IterMut::next()`: advance ptr by 1 and return old.
    /// The MIR calls the `Iterator::next` trait method, so also match the
    /// trait path (`std::iter::Iterator::next`) in addition to the concrete
    /// `Iter`/`IterMut` method names.
    fn try_iter_next(
        &mut self,
        name: &str,
        arg_values: &[VmValue<'ctx, 'tcx>],
        _args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) -> bool {
        let is_next = name.contains("::next")
            && (name.starts_with("Iter::") || name.starts_with("IterMut::")
                || name.contains("::Iter::") || name.contains("::IterMut::")
                || name.contains("::Iter<") || name.contains("::IterMut<")
                || name.contains("::Iterator::next"));
        if !is_next || arg_values.len() < 1 {
            return false;
        }
        let self_val = &arg_values[0];
        let Some(local) = self.find_iter_self_local(self_val) else {
            return false;
        };
        let (Some(ptr), Some(end)) = (self.field_value(local, &[0]), self.field_value(local, &[1])) else {
            return false;
        };
        let (Some(pp), Some(ep)) = (&ptr.provenance, &end.provenance) else {
            return false;
        };
        if pp.alloc_id != ep.alloc_id {
            return false;
        }
        let dest_ty = self.body.local_decls[destination].ty;
        // Compute is_empty from fields/tracked offset (same as is_empty()).
        let sz = Int::from_u64(self.ctx, self.iter_elem_size(ptr));
        let ep_offset = ep.offset.clone();
        let remaining = if let Some(off) = self.iter_ptr_offset.get(&local) {
            let base_len = ep_offset.div(&sz);
            let zero = Int::from_u64(self.ctx, 0);
            off.gt(&base_len).ite(&zero, &Int::sub(self.ctx, &[&base_len, off]))
        } else {
            let diff = Int::sub(self.ctx, &[&ep_offset, &pp.offset]);
            diff.div(&sz)
        };
        let is_empty = remaining._eq(&Int::from_u64(self.ctx, 0));
        // The returned element is the *current* position: the tracked element
        // index (iter_ptr_offset) scaled by the element stride, or the base
        // ptr offset on the first call.
        let zero = Int::from_u64(self.ctx, 0);
        let cur_off = match self.iter_ptr_offset.get(&local) {
            Some(prev) => Int::mul(self.ctx, &[prev, &sz]),
            None => pp.offset.clone(),
        };
        let old_ptr_val = VmValue {
            term: cur_off.clone(),
            ty: ptr.ty,
            provenance: Some(Provenance {
                alloc_id: pp.alloc_id,
                offset: cur_off,
                is_field_offset: false,
            }),
            invariants: ValueInvariants { non_null: true, init: true, ..Default::default() },
        };
        // Advance ptr when not empty
        let one_term = Int::from_u64(self.ctx, 1);
        let new_offset = match self.iter_ptr_offset.get(&local) {
            Some(prev) => Int::add(self.ctx, &[prev, &one_term]),
            None => one_term.clone(),
        };
        // Assert !is_empty as path condition (remaining > 0)
        self.path_conditions.push(remaining.gt(&zero));
        // Push: base_len >= tracked_offset
        let base_len = ep_offset.div(&sz);
        self.path_conditions.push(new_offset.le(&base_len));
        self.iter_ptr_offset.insert(local, new_offset);
        // Return None or old ptr
        let result_val = VmValue {
            term: is_empty.ite(&zero, &old_ptr_val.term),
            ty: dest_ty,
            provenance: if is_empty.as_bool().unwrap_or(false) { None } else { old_ptr_val.provenance.clone() },
            invariants: ValueInvariants::default(),
        };
        self.set_local(destination, result_val);
        // Tie the Option's discriminant to the emptiness condition so
        // `switchInt(discriminant(_n))` only takes the `Some` branch when the
        // iterator was non-empty (and the `None` branch when empty).
        let discr_term = is_empty.ite(&zero, &one_term);
        self.discriminant_terms.insert(destination, discr_term);
        true
    }

    fn materialize_const_bytes_after_call(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
        destination: Local,
    ) {
        if let Some(mut dv) = self.locals.get(&destination).cloned() {
            let dest_ty = dv.ty;
            let pointee_is_byte_like = match dest_ty.kind() {
                rustc_middle::ty::TyKind::RawPtr(inner, _)
                | rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                    match inner.kind() {
                        rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                        | rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8) => true,
                        rustc_middle::ty::TyKind::Array(elem_ty, _)
                        | rustc_middle::ty::TyKind::Slice(elem_ty) => {
                            matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8))
                        }
                        _ => false,
                    }
                }
                _ => false,
            };
            if pointee_is_byte_like {
                for arg in args {
                    self.try_materialize_const_bytes(&mut dv, &arg.node);
                    if dv.provenance.is_some() {
                        self.set_local(destination, dv);
                        break;
                    }
                }
            }
        }
    }

    /// Recursively execute a callee's MIR body inline.
    ///
    /// Binds the caller's argument values to the callee's parameters,
    /// executes the callee's MIR, and writes the return value to
    /// the caller's destination local. Returns `false` if inline
    /// is not possible (e.g., recursion limit reached, callee has
    /// branches, or the callee is too large).
    fn exec_inline_call(
        &mut self,
        callee_def_id: DefId,
        arg_values: &[VmValue<'ctx, 'tcx>],
        caller_arg_locals: &[Local],
        dest: Local,
        _depth: usize,
    ) -> bool {
        // The `depth` argument is always 0 at the call sites; use the stateful
        // counter to actually bound nested inlining (otherwise a callee that
        // itself inlines another callee recurses without limit).
        if self.inline_depth >= MAX_INLINE_DEPTH {
            return false;
        }
        self.inline_depth += 1;

        // Only inline small, branch-free functions. `inline_execute_body`
        // follows every `SwitchInt` target without forking state, so a real
        // branch (e.g. a `match` that returns different pointers per arm)
        // would have its arms merged and lose precision — which silently marks
        // unsound callers sound. Keep rejecting `SwitchInt` bodies; branch-free
        // bodies that merely exceed a small block count are still safe to
        // inline, so the cap must cover the Box construction helpers used by
        // constructors (`from_new_internal` is 9 blocks) so the fresh heap
        // allocation's provenance reaches the returned `NonNull`.
        let callee_body = self.tcx.optimized_mir(callee_def_id);
        let n_return = callee_body
            .basic_blocks
            .iter()
            .filter(|bb| matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::Return))
            .count();
        // Reject a *semantic* branch (a `SwitchInt` reachable on the normal
        // path): `inline_execute_body` merges its arms and loses precision.
        // A `SwitchInt` that only appears in a cleanup block (the drop-flag
        // dispatch) is dead on the normal path and is safe to ignore.
        // Likewise, a `debug_assert!`/`assert!`-style `SwitchInt` whose every
        // non-otherwise target leads to `panic`/`unreachable` is dead on the
        // normal path — inlining it and taking only the `otherwise` edge keeps
        // the field-level provenance of wrapper casts (`cast_to_internal_unchecked`).
        let has_switch = callee_body.basic_blocks.iter_enumerated().any(|(idx, bb)| {
            !bb.is_cleanup
                && matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::SwitchInt { .. })
                && !Self::switch_is_debug_assert(self.tcx, &callee_body, idx)
        });
        if arg_values.len() > 4 || callee_body.basic_blocks.len() > 16 || n_return > 1 || has_switch {
            self.inline_depth -= 1;
            return false;
        }

        // ── Save caller context ──
        let saved_body = self.body;
        let saved_caller = self.caller_def_id;
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_field_values = std::mem::take(&mut self.field_values);
        let saved_local_addresses = std::mem::take(&mut self.local_addresses);
        let saved_local_alloc_ids = std::mem::take(&mut self.local_alloc_ids);
        let saved_binary_op_sources = std::mem::take(&mut self.binary_op_sources);
        let saved_other_op_sources = std::mem::take(&mut self.other_op_sources);

        // ── Switch to callee context ──
        self.body = callee_body;
        self.caller_def_id = callee_def_id;

        // Bind args to callee locals (local_1..local_N are function params)
        for (i, arg_val) in arg_values.iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            self.ensure_local_allocation(callee_local);
            self.set_local(callee_local, arg_val.clone());
        }

        // Propagate field_values from caller arg locals into the callee
        // context so that inline body can access struct fields (e.g.
        // Iter::ptr / end_or_len for len/is_empty computations).
        for (i, caller_arg) in caller_arg_locals.iter().enumerate() {
            let callee_param = Local::from_usize(i + 1);
            if *caller_arg == callee_param {
                continue; // same local; field_values already present
            }
            let caller_field_keys: Vec<Vec<usize>> = saved_field_values.keys()
                .filter(|(l, _)| *l == *caller_arg)
                .map(|(_, f)| f.clone())
                .collect();
            for fields in caller_field_keys {
                if let Some(fv) = saved_field_values.get(&(*caller_arg, fields.clone())).cloned() {
                    self.set_field_value(callee_param, fields, fv);
                }
            }
        }

        // ── BFS execution of callee MIR ──
        self.inline_execute_body();

        // ── Capture return value and its per-field values ──
        let return_val = self.locals.get(&Local::from_usize(0)).cloned();
        let return_fields: Vec<(Vec<usize>, VmValue<'ctx, 'tcx>)> = self
            .field_values
            .iter()
            .filter(|((l, _), _)| *l == Local::from_usize(0))
            .map(|((_, path), val)| (path.clone(), val.clone()))
            .collect();

        // ── Restore caller context ──
        self.body = saved_body;
        self.caller_def_id = saved_caller;
        self.locals = saved_locals;
        self.field_values = saved_field_values;
        self.local_addresses = saved_local_addresses;
        self.local_alloc_ids = saved_local_alloc_ids;
        self.binary_op_sources = saved_binary_op_sources;
        self.other_op_sources = saved_other_op_sources;

        // ── Write return value to caller destination ──
        let dest_ty = self.body.local_decls[dest].ty;
        match return_val {
            Some(mut val) => {
                val.ty = dest_ty;
                // Infer invariants: a non-null provenance with offset=0
                // means the return value is valid and initialized.
                if let Some(ref prov) = val.provenance {
                    if prov.offset.as_u64() == Some(0) {
                        val.invariants.non_null = true;
                        val.invariants.init = true;
                        val.invariants.aligned = true;
                        self.alloc_mut(prov.alloc_id).initialized = true;
                    }
                }
                self.set_local(dest, val);
                // Propagate the callee's per-field return values (e.g. a
                // tuple `(NonNull<T>, A)`'s field 0) to the caller's
                // destination so subsequent field projections resolve.
                for (path, fv) in return_fields {
                    self.set_field_value(dest, path, fv);
                }
                // The callee returned a fully-constructed value, so the
                // caller's destination stack slot is initialized.  This matters
                // for ADT returns (struct/enum) whose aggregate value carries
                // no provenance: a later `&raw const (*&field)` + `ptr::read`
                // must be able to discharge `Init` against the field.
                if let Some(dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                    self.alloc_mut(dest_alloc_id).initialized = true;
                }
            }
            None => {
                self.inline_depth -= 1;
                return false;
            }
        }

        self.inline_depth -= 1;
        true
    }

    /// Whether a `SwitchInt`'s non-`otherwise` targets all lead straight to
    /// `panic`/`unreachable` (a `debug_assert!`/`assert!` dispatch).  Such a
    /// switch is dead on the normal path and can be inlined by following only
    /// the `otherwise` edge.
    fn switch_targets_unreachable(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
    ) -> bool {
        targets.iter().all(|(_, target)| {
            let mut cur = target;
            let mut seen = FxHashSet::default();
            loop {
                if !seen.insert(cur) {
                    return false;
                }
                let bb = &body.basic_blocks[cur];
                let term = bb.terminator();
                match &term.kind {
                    rustc_middle::mir::TerminatorKind::Unreachable => return true,
                    rustc_middle::mir::TerminatorKind::Call { func, .. } => {
                        let name = crate::helpers::mir_utils::call_name(tcx, func);
                        return name.contains("panic") || name.contains("unreachable") || name.contains("abort");
                    }
                    rustc_middle::mir::TerminatorKind::Goto { target: next } => {
                        cur = *next;
                    }
                    // A bare `return` with no statements is a drop-flag skip
                    // (dead on the normal path); a `return` preceded by real
                    // statements computes a different value, so it is a semantic
                    // branch and must not be ignored.
                    rustc_middle::mir::TerminatorKind::Return => return bb.statements.is_empty(),
                    _ => return false,
                }
            }
        })
    }

    /// Whether a block's `SwitchInt` is a `debug_assert!`-style dispatch (all
    /// non-`otherwise` targets are `panic`/`unreachable`).
    fn switch_is_debug_assert(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        bb: BasicBlock,
    ) -> bool {
        let rustc_middle::mir::TerminatorKind::SwitchInt { discr, targets } =
            &body.basic_blocks[bb].terminator().kind
        else {
            return false;
        };
        // A constant discriminant (e.g. `_3 = const true` for a no-drop flag)
        // folds to a single live edge; the other edges are dead and can be
        // ignored when inlining.  This includes a `move _3` whose `_3` is
        // assigned a constant earlier in the body.
        let discr_is_const = match discr {
            rustc_middle::mir::Operand::Constant(_) => true,
            rustc_middle::mir::Operand::Copy(p) | rustc_middle::mir::Operand::Move(p) => {
                body.basic_blocks.iter().any(|bbd| {
                    bbd.statements.iter().any(|stmt| {
                        let rustc_middle::mir::StatementKind::Assign(assign) = &stmt.kind else {
                            return false;
                        };
                        let (dest, rvalue) = &**assign;
                        let is_const = match rvalue {
                            #[cfg(rapx_rvalue_use_with_retag)]
                            rustc_middle::mir::Rvalue::Use(rustc_middle::mir::Operand::Constant(_), _) => true,
                            #[cfg(not(rapx_rvalue_use_with_retag))]
                            rustc_middle::mir::Rvalue::Use(rustc_middle::mir::Operand::Constant(_)) => true,
                            _ => false,
                        };
                        dest == p && is_const
                    })
                })
            }
            #[allow(unreachable_patterns)]
            _ => false,
        };
        if discr_is_const {
            return true;
        }
        Self::switch_targets_unreachable(tcx, body, targets)
    }

    /// BFS-execute the callee's MIR body.
    fn inline_execute_body(&mut self) {
        let mut visited = FxHashSet::default();
        let mut queue: Vec<BasicBlock> = Vec::new();
        queue.push(BasicBlock::from_usize(0));

        while let Some(block) = queue.pop() {
            if !visited.insert(block) {
                continue;
            }

            let bb_data = &self.body.basic_blocks[block];

            // Execute statements
            for (si, stmt) in bb_data.statements.iter().enumerate() {
                self.exec_statement(block, si, stmt);
            }

            // Process terminator
            let terminator = bb_data.terminator();

            match &terminator.kind {
                TerminatorKind::Goto { target } => {
                    queue.push(*target);
                }
                TerminatorKind::Return => {
                    // Return value captured in local_0
                }
                TerminatorKind::Assert { cond, expected, target, .. } => {
                    let cond_val = self.value_of_operand(cond);
                    if *expected {
                        let zero = Int::from_u64(self.ctx, 0);
                        self.path_conditions.push(cond_val.term._eq(&zero).not());
                    } else {
                        let zero = Int::from_u64(self.ctx, 0);
                        self.path_conditions.push(cond_val.term._eq(&zero));
                    }
                    // Guard inference for inline callee
                    self.infer_guard_non_null(cond, *expected);
                    self.infer_guard_align(cond, *expected);
                    queue.push(*target);
                }
                TerminatorKind::SwitchInt { discr, targets } => {
                    // A constant discriminant folds to a single live edge.
                    if let rustc_middle::mir::Operand::Constant(c) = discr {
                        let text = format!("{:?}", c.const_);
                        if let Some(v) = crate::verify::vm::state::const_int_from_debug(&text) {
                            let t = targets.iter().find(|(val, _)| *val == v as u128)
                                .map(|(_, t)| t)
                                .unwrap_or_else(|| targets.otherwise());
                            queue.push(t);
                            continue;
                        }
                    }
                    // A `debug_assert!`/`assert!` switch or a drop-flag dispatch
                    // has its non-otherwise edges dead on the normal path, so
                    // follow only `otherwise`.
                    let trivial = Self::switch_targets_unreachable(self.tcx, &self.body, targets);
                    if trivial {
                        queue.push(targets.otherwise());
                        continue;
                    }
                    // Conservative: add path conditions for all branches,
                    // but since we don't fork state, we follow all targets.
                    // This loses precision for overwritten locals but is sound.
                    for (value, target) in targets.iter() {
                        let discr_val = self.value_of_operand(discr);
                        let val_term = Int::from_u64(self.ctx, value as u64);
                        self.path_conditions.push(discr_val.term._eq(&val_term));
                        queue.push(target);
                    }
                    let otherwise = targets.otherwise();
                    queue.push(otherwise);
                }
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    self.exec_call(
                        func,
                        args,
                        destination.local,
                        *target,
                        None,
                        self.caller_def_id,
                    );
                    if let Some(t) = target {
                        queue.push(*t);
                    }
                }
                TerminatorKind::Drop { place, target, .. } => {
                    self.exec_drop(place);
                    queue.push(*target);
                }
                TerminatorKind::Unreachable
                | TerminatorKind::UnwindResume
                | TerminatorKind::UnwindTerminate(_)
                | TerminatorKind::Yield { .. }
                | TerminatorKind::CoroutineDrop
                | TerminatorKind::FalseEdge { .. }
                | TerminatorKind::FalseUnwind { .. }
                | TerminatorKind::InlineAsm { .. }
                | TerminatorKind::TailCall { .. } => {
                    // Dead-end or unsupported — stop traversal at this block.
                }
            }
        }
    }

    /// Apply a single call effect to the VM state.
    fn apply_call_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'ctx, 'tcx>],
        caller_arg_locals: &[Local],
        dest: Local,
    ) {
        match effect {
            CallEffect::ReturnAliasArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.non_null = true;
                    val.invariants.aligned = true;
                    val.invariants.init = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnTransparentDeref { arg, peel } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.non_null = true;
                    val.invariants.aligned = true;
                    val.invariants.init = true;
                    self.set_local(dest, val);
                    // Peel `peel` leading field-0 hops off the argument's
                    // pointee field values (ManuallyDrop.value → MaybeDangling.0)
                    // and expose them as the deref result's pointee fields.
                    if let Some(arg_local) = caller_arg_locals.get(*arg).copied() {
                        let keys: Vec<Vec<usize>> = self
                            .field_values
                            .keys()
                            .filter(|(l, _)| *l == arg_local)
                            .map(|(_, p)| p.clone())
                            .collect();
                        for path in keys {
                            if path.len() > *peel
                                && path[..*peel].iter().all(|&f| f == 0)
                            {
                                if let Some(v) =
                                    self.field_values.get(&(arg_local, path.clone())).cloned()
                                {
                                    self.set_field_value(dest, path[*peel..].to_vec(), v);
                                }
                            }
                        }
                    }
                }
            }
            CallEffect::ReturnTupleFieldLength { field: _field, from_arg: _from_arg } => {
                if args.len() < 2 {
                    return;
                }
                let self_val = &args[0]; // &[T]
                let mid_val = &args[1];  // usize

                let dest_ty = self.body.local_decls[dest].ty;
                if let TyKind::Tuple(elem_tys) = dest_ty.kind() {
                    // Look up the source allocation from self's provenance.
                    let src_alloc_id = self_val.provenance.as_ref().map(|p| p.alloc_id);
                    let _src_offset = self_val.provenance.as_ref()
                        .map(|p| p.offset.clone())
                        .unwrap_or_else(|| Int::from_u64(self.ctx, 0));

                    let (elem_ty, elem_sz, alloc_size) = src_alloc_id
                        .map(|id| self.alloc(id))
                        .map(|a| {
                            let ty = a.element_ty;
                            let sz = self.size_of_ty(ty.unwrap_or(self_val.ty)).max(1) as u64;
                            (ty, sz, a.size.clone())
                        })
                        .unwrap_or((None, 1, Int::from_u64(self.ctx, 1)));

                    let elem_sz_term = Int::from_u64(self.ctx, elem_sz);
                    let total_len = alloc_size.div(&elem_sz_term); // self.len()

                    let zero = Int::from_u64(self.ctx, 0);
                    self.path_conditions.push(mid_val.term.ge(&zero));
                    self.path_conditions.push(mid_val.term.le(&total_len));

                    // mid (field 0 length)
                    let mid = mid_val.term.clone();
                    // self.len() - mid (field 1 length)
                    let rest_len = Int::sub(self.ctx, &[&total_len, &mid]);

                    // mid byte offset for field 1 pointer
                    let mid_bytes = Int::mul(self.ctx, &[&mid, &elem_sz_term]);
                    let ptr1 = Int::add(self.ctx, &[&self_val.term, &mid_bytes]);

                    for f in 0..elem_tys.len() {
                        let field_ty = elem_tys[f];
                        let (field_len, field_ptr) = if f == 0 {
                            (mid.clone(), self_val.term.clone())
                        } else {
                            (rest_len.clone(), ptr1.clone())
                        };
                        let field_size = Int::mul(self.ctx, &[&field_len, &elem_sz_term]);
                        let field_alloc_align = self_val.provenance.as_ref()
                            .map(|p| self.alloc(p.alloc_id).align)
                            .unwrap_or(1);

                        let (alloc_id, _base) = self.allocate(
                            field_size.clone(), field_alloc_align, elem_ty,
                        );
                        let src_bytes = Int::mul(self.ctx, &[&total_len, &elem_sz_term]);
                        if f == 0 {
                            self.path_conditions.push(field_size._eq(&mid_bytes));
                        } else {
                            let remaining = Int::sub(self.ctx, &[&src_bytes, &mid_bytes]);
                            self.path_conditions.push(field_size._eq(&remaining));
                        }
                        self.alloc_mut(alloc_id).initialized = true;
                        if let Some(ref source_prov) = self_val.provenance {
                            self.alloc_mut(alloc_id).parent = Some(source_prov.alloc_id);
                        }
                        if let Some(ref_dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                            self.alloc_mut(ref_dest_alloc_id).slice_data = Some(alloc_id);
                        }

                        let field_offset = Int::from_u64(self.ctx, 0);

                        let field_prov = Provenance {
                            alloc_id,
                            offset: field_offset,
                            is_field_offset: false,
                        };

                        let field_val = VmValue {
                            term: field_ptr,
                            ty: field_ty,
                            provenance: Some(field_prov),
                            invariants: ValueInvariants {
                                init: true,
                                non_null: true,
                                aligned: true,
                                in_bounds: true,
                                align_n: Some(field_alloc_align),
                                is_field_offset: false,
                            },
                        };
                        self.set_field_value(dest, vec![f], field_val);
                    }
                }
            }
            CallEffect::ReturnIter { receiver_arg } => {
                let Some(self_val) = args.get(*receiver_arg).cloned() else { return };
                let Some(src_prov) = self_val.provenance.clone() else { return };
                // `array[..i]` may be a `from_raw_parts` sub-allocation of the
                // array's backing storage. Follow the sub-allocation chain to the
                // root so the iterator's `ptr`/`end_or_len` fields point at live,
                // init-tracked storage (the array itself), not the transient
                // slice allocation.
                let root_alloc_id = {
                    let mut id = src_prov.alloc_id;
                    while let Some(parent) = self.alloc(id).parent {
                        id = parent;
                    }
                    id
                };
                let slice_len = self.alloc(src_prov.alloc_id).size.clone();

                // The Iter/IterMut struct has `ptr` (field 0) and `end_or_len`
                // (field 1), both raw pointers into the source slice allocation.
                // Derive the pointee type so `next()` can compute the stride.
                let field_ty = match self_val.ty.kind() {
                    TyKind::Ref(_, inner, _) => match inner.kind() {
                        TyKind::Slice(t) => *t,
                        _ => self_val.ty,
                    },
                    _ => self_val.ty,
                };

                let start_off = Int::from_u64(self.ctx, 0);
                let end_term = Int::add(self.ctx, &[&self_val.term, &slice_len]);

                let start_val = VmValue {
                    term: self_val.term.clone(),
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: root_alloc_id,
                        offset: start_off,
                        is_field_offset: false,
                    }),
                    invariants: ValueInvariants { init: true, non_null: true, ..Default::default() },
                };
                let end_val = VmValue {
                    term: end_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: root_alloc_id,
                        offset: slice_len,
                        is_field_offset: false,
                    }),
                    invariants: ValueInvariants { init: true, non_null: true, ..Default::default() },
                };
                self.set_field_value(dest, vec![0], start_val);
                self.set_field_value(dest, vec![1], end_val);
            }
            CallEffect::ReturnAlignTo { receiver_arg } => {
                let Some(self_val) = args.get(*receiver_arg).cloned() else { return };
                let dest_ty = self.body.local_decls[dest].ty;
                let TyKind::Tuple(elem_tys) = dest_ty.kind() else { return };
                if elem_tys.len() < 3 { return; }

                // Body element type U is the pointee of field 1 (`&[U]`).
                let body_elem_ty = match elem_tys[1].kind() {
                    TyKind::Ref(_, inner, _) => match inner.kind() {
                        TyKind::Slice(u) => *u,
                        _ => return,
                    },
                    _ => return,
                };
                let size_u = self.size_of_ty(body_elem_ty).max(1) as u64;
                let align_u = self.align_of_ty(body_elem_ty).max(1);

                let Some(src_prov) = self_val.provenance.clone() else { return };
                let alloc = self.alloc(src_prov.alloc_id);
                let (elem_ty, elem_sz, len_bytes) = {
                    let ty = alloc.element_ty;
                    let sz = self.size_of_ty(ty.unwrap_or(self_val.ty)).max(1) as u64;
                    (ty, sz, alloc.size.clone())
                };

                let elem_sz_term = Int::from_u64(self.ctx, elem_sz);
                let size_u_term = Int::from_u64(self.ctx, size_u);
                let align_u_term = Int::from_u64(self.ctx, align_u);

                // Fresh aligned offset: (ptr + offset) % align_u == 0 and
                // 0 <= offset < align_u.
                let offset = self.fresh_int(&format!("align_to_offset_{}", dest.as_usize()));
                let zero = Int::from_u64(self.ctx, 0);
                let ptr_plus_offset = Int::add(self.ctx, &[&self_val.term, &offset]);
                self.path_conditions.push(ptr_plus_offset.rem(&align_u_term)._eq(&zero));
                self.path_conditions.push(offset.ge(&zero));
                self.path_conditions.push(offset.lt(&align_u_term));

                // body = len_bytes - offset bytes split into size_u chunks; the
                // remainder is the suffix. Record the Euclidean identity so that
                // `len - offset - suffix = body_len * size_u` (a multiple of
                // align_u) is derivable downstream.
                let body_bytes = Int::sub(self.ctx, &[&len_bytes, &offset]);
                let body_len = body_bytes.div(&size_u_term);
                let suffix_bytes = body_bytes.rem(&size_u_term);
                let mul_term = Int::mul(self.ctx, &[&body_len, &size_u_term]);
                let sum_term = Int::add(self.ctx, &[&mul_term, &suffix_bytes]);
                self.path_conditions.push(body_bytes._eq(&sum_term));
                self.path_conditions.push(suffix_bytes.ge(&zero));
                self.path_conditions.push(suffix_bytes.lt(&size_u_term));

                // Field lengths in elements.
                let prefix_len = offset.div(&elem_sz_term);
                let suffix_len = suffix_bytes.div(&elem_sz_term);

                let body_byte_len = Int::mul(self.ctx, &[&body_len, &size_u_term]);
                let suffix_ptr = Int::add(self.ctx, &[&ptr_plus_offset, &body_byte_len]);

                let base_align = self.alloc(src_prov.alloc_id).align;

                let fields: Vec<(Int<'ctx>, Int<'ctx>, Ty<'tcx>, u64, u64)> = vec![
                    (prefix_len, self_val.term.clone(), elem_tys[0], elem_sz, base_align),
                    (body_len, ptr_plus_offset, elem_tys[1], size_u, align_u),
                    (suffix_len, suffix_ptr, elem_tys[2], elem_sz, base_align),
                ];

                for (f, (f_len, f_ptr, f_ty, f_elem_sz, f_align)) in fields.into_iter().enumerate() {
                    let f_size = Int::mul(self.ctx, &[&f_len, &Int::from_u64(self.ctx, f_elem_sz)]);
                    let f_elem_ty = if f == 1 { Some(body_elem_ty) } else { elem_ty };
                    let (alloc_id, _) = self.allocate(f_size.clone(), f_align, f_elem_ty);
                    self.alloc_mut(alloc_id).initialized = true;
                    self.alloc_mut(alloc_id).parent = Some(src_prov.alloc_id);
                    if let Some(ref_dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                        self.alloc_mut(ref_dest_alloc_id).slice_data = Some(alloc_id);
                    }
                    let field_val = VmValue {
                        term: f_ptr,
                        ty: f_ty,
                        provenance: Some(Provenance {
                            alloc_id,
                            offset: Int::from_u64(self.ctx, 0),
                            is_field_offset: false,
                        }),
                        invariants: ValueInvariants {
                            init: true, non_null: true, aligned: true, in_bounds: true,
                            align_n: if f_align > 1 { Some(f_align) } else { None },
                            is_field_offset: false,
                        },
                    };
                    self.set_field_value(dest, vec![f], field_val);
                }
            }
            CallEffect::ReturnPointerFromArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let mut val = arg_val.clone();
                    let dest_ty = self.body.local_decls[dest].ty;
                    val.ty = dest_ty;
                    val.invariants.non_null = true;
                    val.invariants.aligned = true;
                    // Pointer-returning APIs expose the backing allocation;
                    // mark it init-accessible for raw pointer types.
                    if matches!(dest_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)) {
                        val.invariants.init = true;
                    }
                    // For locally-created Vec: redirect as_ptr() from the
                    // struct allocation to the heap data allocation.
                    let is_vec = api_classify::is_vec_or_cstring_call(&self.last_call_name);
                    if is_vec {
                        if let Some(ref prov) = val.provenance {
                            if let Some(data_alloc) = self.alloc(prov.alloc_id).slice_data {
                                if let Some(data_base) = self.allocation_base(data_alloc).cloned() {
                                    val.term = data_base;
                                    val.provenance = Some(Provenance {
                                        alloc_id: data_alloc,
                                        offset: Int::from_u64(self.ctx, 0),
                                        is_field_offset: false,
                                    });
                                }
                            }
                        }
                    }
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerAdd { base_arg, offset_arg, stride } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let adjusted_offset = if stride_bytes == 1 {
                        Int::add(self.ctx, &[&offset.term])
                    } else {
                        let stride_term = Int::from_u64(self.ctx, stride_bytes);
                        Int::mul(self.ctx, &[&offset.term, &stride_term])
                    };
                    let new_term = Int::add(self.ctx, &[&base.term, &adjusted_offset]);
                    // A field offset (`offset_of!`) added to a container base
                    // keeps the pointer within the container allocation.
                    let is_field_offset = offset.invariants.is_field_offset
                        && base
                            .provenance
                            .as_ref()
                            .is_some_and(|p| p.offset.as_u64() == Some(0));
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| {
                        Provenance {
                            alloc_id: prov.alloc_id,
                            offset: Int::add(self.ctx, &[&prov.offset, &adjusted_offset]),
                            is_field_offset,
                        }
                    });
                    // Preserve alignment if the added offset is compatible
                    let align_n = self.compute_pointer_add_align(base, offset, stride_bytes);
                    let val = VmValue {
                        term: new_term,
                        ty: self.body.local_decls[dest].ty,
                        provenance: adjusted_provenance,
                        invariants: ValueInvariants {
                            non_null: base.invariants.non_null,
                            aligned: align_n.is_some() && base.invariants.aligned,
                            in_bounds: base.invariants.in_bounds,
                            align_n,
                            init: base.invariants.init,
                            is_field_offset: false,
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerSub { base_arg, offset_arg, stride } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let stride_term = Int::from_u64(self.ctx, stride_bytes);
                    let scaled = Int::mul(self.ctx, &[&offset.term, &stride_term]);
                    let new_term = Int::sub(self.ctx, &[&base.term, &scaled]);
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| {
                        Provenance {
                            alloc_id: prov.alloc_id,
                            offset: Int::sub(self.ctx, &[&prov.offset, &scaled]),
                            is_field_offset: false,
                        }
                    });
                    let align_n = self.compute_pointer_add_align(base, offset, stride_bytes);
                    let val = VmValue {
                        term: new_term,
                        ty: self.body.local_decls[dest].ty,
                        provenance: adjusted_provenance,
                        invariants: ValueInvariants {
                            non_null: base.invariants.non_null,
                            aligned: align_n.is_some() && base.invariants.aligned,
                            in_bounds: base.invariants.in_bounds,
                            align_n,
                            init: base.invariants.init,
                            is_field_offset: false,
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::CleanSliceDataLinks { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(ref prov) = arg_val.provenance {
                        self.alloc_mut(prov.alloc_id).slice_data = None;
                    }
                }
            }
            CallEffect::ReturnNonZero => {
                let zero = Int::from_u64(self.ctx, 0);
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.non_null = true;
                    // Record the non-zero fact as a path condition so that a
                    // downstream `ValidNum(result != 0)` obligation (e.g.
                    // `NonZero::new_unchecked` after a bit-preserving operation)
                    // discharges against it.
                    self.path_conditions.push(existing.term._eq(&zero).not());
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_nz_{}", dest.as_usize()));
                    self.path_conditions.push(term._eq(&zero).not());
                    self.set_local(dest, VmValue {
                        term, ty: dest_ty, provenance: None,
                        invariants: ValueInvariants { non_null: true, ..Default::default() },
                    });
                }
            }
            CallEffect::ReturnTupleFieldNonZero { field } => {
                let dest_ty = self.body.local_decls[dest].ty;
                if let TyKind::Tuple(elem_tys) = dest_ty.kind() {
                    if let Some(field_ty) = elem_tys.get(*field) {
                        let zero = Int::from_u64(self.ctx, 0);
                        let term = self
                            .fresh_int(&format!("ret_tup_nz_{}_{}", dest.as_usize(), field));
                        self.path_conditions.push(term._eq(&zero).not());
                        self.set_field_value(dest, vec![*field], VmValue {
                            term,
                            ty: *field_ty,
                            provenance: None,
                            invariants: ValueInvariants { non_null: true, init: true, ..Default::default() },
                        });
                    }
                }
            }
            CallEffect::ReturnAligned { align: _, ty_name: _ } => {
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.aligned = true;
                    existing.invariants.non_null = true;
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_align_{}", dest.as_usize()));
                    self.set_local(dest, VmValue {
                        term, ty: dest_ty, provenance: None,
                        invariants: ValueInvariants { aligned: true, non_null: true, ..Default::default() },
                    });
                }
            }
            CallEffect::ReturnLengthOfArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    // For Iter / IterMut, compute len from struct fields
                    // (ptr + end_or_len with shared allocation) instead of
                    // the generic sizeof(Iter)/sizeof(T) heuristic.
                    if self.interpreter_iter_len(arg_val, dest) {
                        return;
                    }
                    let effective_alloc_id = arg_val.provenance_alloc_id()
                        .and_then(|pid| self.alloc(pid).slice_data)
                        .or_else(|| arg_val.provenance_alloc_id());

                    if let Some(alloc_id) = effective_alloc_id {
                        let dest_ty = self.body.local_decls[dest].ty;
                        // If the allocation has an element type, divide the
                        // byte-aligned size by the element size to return the
                        // number of elements (e.g. slice length).
                        if let Some(elem_ty) = self.alloc(alloc_id).element_ty {
                            let elem_size = self.size_of_ty(elem_ty) as u64;
                            if elem_size > 1 {
                                if let Some(size) = self.allocation_size(alloc_id) {
                                    let div = Int::from_u64(self.ctx, elem_size);
                                    let val = VmValue::new(size.div(&div), dest_ty);
                                    self.set_local(dest, val);
                                    return;
                                }
                            } else if let Some(size) = self.allocation_size(alloc_id) {
                                let val = VmValue::new(size.clone(), dest_ty);
                                self.set_local(dest, val);
                                return;
                            }
                        } else if let Some(size) = self.allocation_size(alloc_id) {
                            let val = VmValue::new(size.clone(), dest_ty);
                            self.set_local(dest, val);
                            return;
                        }
                    }
                }
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("len_{}", dest.as_usize()));
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnIsEmptyOfArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if self.interpreter_iter_is_empty(arg_val, dest) {
                        return;
                    }
                    let effective_alloc_id = arg_val.provenance_alloc_id()
                        .and_then(|pid| self.alloc(pid).slice_data)
                        .or_else(|| arg_val.provenance_alloc_id());
                    if let Some(alloc_id) = effective_alloc_id {
                        if let Some(len_term) = self.allocation_size(alloc_id).cloned() {
                            let zero = Int::from_u64(self.ctx, 0);
                            let one = Int::from_u64(self.ctx, 1);
                            let dest_ty = self.body.local_decls[dest].ty;
                            let cond = len_term._eq(&zero);
                            let val = VmValue {
                                term: cond.ite(&one, &zero),
                                ty: dest_ty,
                                provenance: None,
                                invariants: ValueInvariants::default(),
                            };
                            self.set_local(dest, val);
                            return;
                        }
                    }
                }
                let dest_ty = self.body.local_decls[dest].ty;
                let one = Int::from_u64(self.ctx, 1);
                let zero = Int::from_u64(self.ctx, 0);
                let fresh = self.fresh_int(&format!("empty_{}", dest.as_usize()));
                let val = VmValue {
                    term: fresh.le(&zero).ite(&one, &zero),
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnOffsetFromUnsigned { self_arg, origin_arg } => {
                if let (Some(self_val), Some(origin_val)) = (args.get(*self_arg), args.get(*origin_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    if let (Some(self_prov), Some(origin_prov)) = (&self_val.provenance, &origin_val.provenance) {
                        // Both pointers share provenance: the element-distance
                        // is (self_offset - origin_offset) / elem_size.
                        let elem_ty = match self_val.ty.kind() {
                            TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
                            _ => None,
                        };
                        let elem_size = elem_ty.map(|t| self.size_of_ty(t).max(1)).unwrap_or(1) as u64;
                        let diff = Int::sub(self.ctx, &[&self_prov.offset, &origin_prov.offset]);
                        let sz = Int::from_u64(self.ctx, elem_size);
                        let val = VmValue::new(diff.div(&sz), dest_ty);
                        self.set_local(dest, val);
                        return;
                    }
                    // Fallback: fresh symbolic length.
                    let term = self.fresh_int(&format!("offset_{}", dest.as_usize()));
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                    return;
                }
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("offset_{}", dest.as_usize()));
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnConst { value, label: _ } => {
                let dest_ty = self.body.local_decls[dest].ty;
                let term = Int::from_u64(self.ctx, *value);
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnAlignOffset { ptr_arg, align_arg } => {
                let dest_ty = self.body.local_decls[dest].ty;
                let offset = self.fresh_int(&format!("align_offset_{}", dest.as_usize()));
                if let (Some(ptr_val), Some(align_val)) = (args.get(*ptr_arg), args.get(*align_arg)) {
                    // `ptr.align_offset(align)` guarantees `(ptr + offset) % align == 0`
                    // with `0 <= offset < align` on the success path. Record both so a
                    // downstream `*(ptr.add(offset) as *const U)` can discharge `Align`.
                    let zero = Int::from_u64(self.ctx, 0);
                    let ptr_plus_off = Int::add(self.ctx, &[&ptr_val.term, &offset]);
                    self.path_conditions
                        .push(ptr_plus_off.rem(&align_val.term)._eq(&zero));
                    self.path_conditions.push(offset.ge(&zero));
                    self.path_conditions.push(offset.lt(&align_val.term));
                }
                let val = VmValue {
                    term: offset,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    // Build the min as a first-class `ite(lhs <= rhs, lhs, rhs)`
                    // term rather than a fresh variable plus disjunction facts.
                    // A fresh variable breaks downstream alignment/bounds
                    // reasoning: e.g. `ptr.align_offset(8)` guarantees
                    // `(ptr + offset) % 8 == 0`, but `offset.min(len)` would
                    // then become an unrelated symbol and the `Align`/`InBound`
                    // checks on `*(ptr.add(offset) as *const usize)` could no
                    // longer discharge.  With an `ite`, the path conditions
                    // (`offset < 8`, `len >= 16`) let the solver reduce
                    // `ite(offset <= len, offset, len)` back to `offset`.
                    let term = lhs.term.le(&rhs.term).ite(&lhs.term, &rhs.term);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnMax { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = lhs.term.ge(&rhs.term).ite(&lhs.term, &rhs.term);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnClamp { value_arg, min_arg, max_arg } => {
                if let (Some(v), Some(mn), Some(mx)) =
                    (args.get(*value_arg), args.get(*min_arg), args.get(*max_arg))
                {
                    let dest_ty = self.body.local_decls[dest].ty;
                    // clamp(v, mn, mx) = max(mn, min(v, mx))
                    let upper = v.term.gt(&mx.term).ite(&mx.term, &v.term);
                    let term = v.term.lt(&mn.term).ite(&mn.term, &upper);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnAbs { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let zero = Int::from_u64(self.ctx, 0);
                    let neg = Int::sub(self.ctx, &[&zero, &a.term]);
                    let term = a.term.ge(&zero).ite(&a.term, &neg);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnNeg { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let zero = Int::from_u64(self.ctx, 0);
                    let term = Int::sub(self.ctx, &[&zero, &a.term]);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnAdd { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = Int::add(self.ctx, &[&lhs.term, &rhs.term]);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnMul { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = Int::mul(self.ctx, &[&lhs.term, &rhs.term]);
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnOptionSomeAdd { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    // `checked_add` returns `Option<T>`; its `Some` payload is
                    // `lhs + rhs`. Store the payload term under field 0 so the
                    // `if let Some(payload)` projection resolves to it. The
                    // discriminant is left unconstrained, so both `Some`/`None`
                    // branches remain reachable.
                    let term = Int::add(self.ctx, &[&lhs.term, &rhs.term]);
                    self.set_field_value(dest, vec![0], VmValue {
                        term,
                        ty: lhs.ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    });
                }
            }
            CallEffect::ReturnOptionSomeMul { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let term = Int::mul(self.ctx, &[&lhs.term, &rhs.term]);
                    self.set_field_value(dest, vec![0], VmValue {
                        term,
                        ty: lhs.ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    });
                }
            }
            CallEffect::ReturnOptionSomeScanIndex { self_arg } => {
                // `Iterator::position`/`find` return `Option<usize>` whose `Some`
                // payload is a scan index into the iterator, so `0 <= i < self.len()`.
                // The receiver is `&mut iter` (a reference to the Iter/IterMut
                // struct), so resolve the reference to the iterator local it
                // points at (via its provenance = the iterator's stack alloc).
                // The iterator carries `ptr` (field 0) and `end_or_len`
                // (field 1); `len = end_or_len - ptr`.
                if let Some(&iter_ref) = caller_arg_locals.get(*self_arg) {
                    let iter_local = self
                        .locals
                        .get(&iter_ref)
                        .and_then(|v| v.provenance_alloc_id())
                        .and_then(|alloc| {
                            self.local_alloc_ids
                                .iter()
                                .find(|(_, a)| **a == alloc)
                                .map(|(l, _)| *l)
                        });
                    let ptr_term = iter_local.and_then(|l| {
                        self.field_value(l, &[0]).map(|v| v.term.clone())
                    });
                    let end_term = iter_local.and_then(|l| {
                        self.field_value(l, &[1]).map(|v| v.term.clone())
                    });
                    if let (Some(ptr), Some(end)) = (ptr_term, end_term) {
                        let len = Int::sub(self.ctx, &[&end, &ptr]);
                        let payload = self.fresh_int(&format!("scan_idx_{}", dest.as_usize()));
                        self.path_conditions.push(payload.lt(&len));
                        let dest_ty = self.body.local_decls[dest].ty;
                        let payload_ty = match dest_ty.kind() {
                            TyKind::Adt(adt, substs) if adt.is_enum() => substs.type_at(0),
                            _ => dest_ty,
                        };
                        self.set_field_value(dest, vec![0], VmValue {
                            term: payload,
                            ty: payload_ty,
                            provenance: None,
                            invariants: ValueInvariants::default(),
                        });
                    }
                }
            }
            CallEffect::ReturnScanLength { ptr_arg: _ } => {
                // `strlen(ptr)` returns the byte length before the NUL
                // terminator. The `ValidCStr` invariant guarantees the NUL is
                // within `isize::MAX` bytes, so `len < isize::MAX`, and
                // `len + 1` (the length with the terminator) fits in
                // `isize::MAX` — discharging `from_raw_parts`'s
                // `ValidNum(size_of(T)*(len+1) <= isize::MAX)`.
                let len = self.fresh_int(&format!("strlen_{}", dest.as_usize()));
                let max = Int::from_i64(self.ctx, i64::MAX);
                self.path_conditions.push(len.lt(&max));
                let dest_ty = self.body.local_decls[dest].ty;
                self.set_local(dest, VmValue {
                    term: len,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                });
            }
            CallEffect::ReturnNonZeroIff { arg } => {
                if let Some(a) = args.get(*arg) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let zero = Int::from_u64(self.ctx, 0);
                    let term = self.fresh_int(&format!("ret_nz_iff_{}", dest.as_usize()));
                    // `result == 0` iff `arg == 0`, i.e. non-zero is preserved
                    // exactly (bit-preserving ops map 0 -> 0, non-zero -> non-zero).
                    self.path_conditions
                        .push(term._eq(&zero)._eq(&a.term._eq(&zero)));
                    self.set_local(dest, VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    });
                }
            }
            CallEffect::ReturnOptionSomeNonZeroIff { arg } => {
                if let Some(a) = args.get(*arg) {
                    let zero = Int::from_u64(self.ctx, 0);
                    let term = self.fresh_int(&format!("ret_opt_nz_iff_{}", dest.as_usize()));
                    self.path_conditions
                        .push(term._eq(&zero)._eq(&a.term._eq(&zero)));
                    self.set_field_value(dest, vec![0], VmValue {
                        term,
                        ty: a.ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    });
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg) {
                    if let Some(prov) = &arg_val.provenance {
                        // For locally-created Vec-like types: create a heap data
                        // allocation on first mutation. (Param Vecs already have
                        // an external allocation set by init_parameters.)
                        let is_vec = crate::helpers::api_classify::is_vec_push(&self.last_call_name);
                        let is_external = self.alloc(prov.alloc_id).is_external;
                        if is_vec && !is_external {
                            let elem_ty = match arg_val.ty.kind() {
                                TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => self.vec_elem_ty(*inner),
                                _ => self.vec_elem_ty(arg_val.ty),
                            };
                            let heap_align = elem_ty.map(|ty| self.align_of_ty(ty)).unwrap_or(1).max(1);
                            if let Some(old_data) = self.alloc(prov.alloc_id).slice_data {
                                // Subsequent mutation: invalidate old heap data.
                                self.alloc_mut(old_data).dead = true;
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) = self.allocate_external(max_size, heap_align, elem_ty);
                                self.alloc_mut(prov.alloc_id).slice_data = Some(data_alloc);
                            } else {
                                // First mutation: create heap data allocation.
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) = self.allocate_external(max_size, heap_align, elem_ty);
                                self.alloc_mut(prov.alloc_id).slice_data = Some(data_alloc);
                            }
                        }
                        // When offset is concrete, only mark the bytes actually
                        // written. For symbolic offsets, mark entire allocation.
                        let off_u64 = prov.offset.as_u64()
                            .or_else(|| prov.offset.simplify().as_u64());
                        if let Some(off) = off_u64 {
                            if off == 0 {
                                self.alloc_mut(prov.alloc_id).initialized = true;
                            }
                            let elem_size = match arg_val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => self.size_of_ty(*inner) as usize,
                                _ => 0,
                            };
                            let write_size = if elem_size > 0 { elem_size } else {
                                self.allocation_size(prov.alloc_id).and_then(|s| s.as_u64()).unwrap_or(0) as usize
                            };
                            let end = (off as usize + write_size).min(4096);
                            for byte_off in (off as usize)..end {
                                self.mark_byte_init(prov.alloc_id, byte_off);
                            }
                        } else {
                            // Symbolic write offset: the exact written element
                            // can't be tracked per-byte. For concrete allocation
                            // sizes, mark every byte (as before). For unknown /
                            // zero sizes — generic element types such as
                            // `MaybeUninit<T>` inside `[MaybeUninit<T>; N]` —
                            // mark the whole allocation initialized so a later
                            // `assume_init_read`/`assume_init_drop` can discharge
                            // `Init` on those (fully initialized) elements.
                            let size_val = self.allocation_size(prov.alloc_id)
                                .and_then(|s| s.as_u64());
                            match size_val {
                                Some(sz) if sz > 0 => {
                                    for off in 0..(sz as usize).min(1024) {
                                        self.mark_byte_init(prov.alloc_id, off);
                                    }
                                }
                                _ => {
                                    self.alloc_mut(prov.alloc_id).initialized = true;
                                }
                            }
                        }
                    }
                }
            }
            CallEffect::ReadMemory { arg: _ } => {
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("read_{}", dest.as_usize()));
                let val = VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                };
                self.set_local(dest, val);
            }
            CallEffect::ReturnFreshAllocation { pointer_arg, size_arg, elem_size } => {
                if let (Some(ptr_val), Some(size_val)) = (args.get(*pointer_arg), args.get(*size_arg)) {
                    let elem_sz = Int::from_u64(self.ctx, *elem_size);
                    let total = Int::mul(self.ctx, &[&size_val.term, &elem_sz]);
                    let dest_ty = self.body.local_decls[dest].ty;
                    // For generic types (elem_size == 0), use external alloc
                    // so Allocated/InBound checks auto-pass.
                    let (alloc_id, base) = if *elem_size == 0 {
                        let max = Int::from_u64(self.ctx, i64::MAX as u64);
                        self.allocate_external(max, 1, None)
                    } else {
                        self.allocate(total, *elem_size, None)
                    };
                    let prov = Provenance {
                        alloc_id,
                        offset: Int::from_u64(self.ctx, 0),
                        is_field_offset: false,
                    };
                    // If return is a reference, register slice/pointee data
                    if let Some(ref dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                        self.alloc_mut(*dest_alloc_id).slice_data = Some(alloc_id);
                    }
                    // Propagate init status and byte-level tracking from the source pointer
                    // For fresh allocations, the init status is inherited from the source.
                    let is_external = self.alloc(alloc_id).is_external;
                    if is_external {
                        self.alloc_mut(alloc_id).initialized = true;
                    }
                    if let Some(ref source_prov) = ptr_val.provenance {
                        if !self.alloc(source_prov.alloc_id).dead {
                            self.alloc_mut(alloc_id).initialized = true;
                            self.alloc_mut(alloc_id).parent = Some(source_prov.alloc_id);
                        }
                        // Copy byte-level tracking (value, init, NUL knowledge).
                        self.copy_byte_tracking(source_prov.alloc_id, alloc_id);
                    }
                    let result_align_n = ptr_val.invariants.align_n.or_else(|| {
                        ptr_val.provenance.as_ref()
                            .map(|p| self.alloc(p.alloc_id).align)
                    });
                    self.set_local(dest, VmValue {
                        term: base,
                        ty: dest_ty,
                        provenance: Some(prov),
                        invariants: ValueInvariants {
                            non_null: true, init: true, in_bounds: true, aligned: true,
                            align_n: result_align_n,
                            ..ValueInvariants::default()
                        },
                    });
                }
            }
            CallEffect::ReturnNewAllocation { size_arg, elem_size } => {
                if let Some(size_val) = args.get(*size_arg) {
                    let elem_sz = Int::from_u64(self.ctx, *elem_size);
                    let total = Int::mul(self.ctx, &[&size_val.term, &elem_sz]);
                    let dest_ty = self.body.local_decls[dest].ty;
                    let elem_ty = self.vec_elem_ty(dest_ty);
                    let heap_align = elem_ty.map(|ty| self.align_of_ty(ty)).unwrap_or(1).max(1);
                    let (alloc_id, base) = self.allocate_external(total, heap_align, elem_ty);
                    let dest_alloc_id = self.local_alloc_ids.get(&dest).copied();
                    if let Some(dest_alloc_id) = dest_alloc_id {
                        self.alloc_mut(dest_alloc_id).slice_data = Some(alloc_id);
                    }
                    self.alloc_mut(alloc_id).initialized = true;
                    self.set_local(dest, VmValue {
                        term: base,
                        ty: dest_ty,
                        provenance: dest_alloc_id.map(|stack_id| Provenance {
                            alloc_id: stack_id,
                            offset: Int::from_u64(self.ctx, 0),
                            is_field_offset: false,
                        }),
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            in_bounds: true,
                            aligned: true,
                            ..ValueInvariants::default()
                        },
                    });
                }
            }
            CallEffect::ReturnNewAllocationFromBox { box_arg: _ } => {
                // Box→Vec conversion (into_vec, box_assume_init_into_vec_unsafe).
                self.ensure_local_allocation(dest);
                let dest_ty = self.body.local_decls[dest].ty;
                let elem_ty = self.vec_elem_ty(dest_ty);
                let heap_align = elem_ty.map(|ty| self.align_of_ty(ty)).unwrap_or(1).max(1);
                let max = Int::from_u64(self.ctx, i64::MAX as u64);
                let (alloc_id, base) = self.allocate_external(max, heap_align, elem_ty);
                let dest_alloc_id = self.local_alloc_ids.get(&dest).copied();
                if let Some(ref dest_alloc_id) = dest_alloc_id {
                    self.alloc_mut(*dest_alloc_id).slice_data = Some(alloc_id);
                }
                self.alloc_mut(alloc_id).initialized = true;
                self.set_local(dest, VmValue {
                    term: base,
                    ty: dest_ty,
                    provenance: dest_alloc_id.map(|stack_id| Provenance {
                        alloc_id: stack_id,
                        offset: Int::from_u64(self.ctx, 0),
                        is_field_offset: false,
                    }),
                    invariants: ValueInvariants {
                        non_null: true,
                        init: true,
                        in_bounds: true,
                        aligned: true,
                        ..ValueInvariants::default()
                    },
                });
            }
            CallEffect::ReturnBoxFromVec { arg } => {
                if let Some(vec_val) = args.get(*arg) {
                    if let Some(ref prov) = vec_val.provenance {
                        if let Some(heap_alloc_id) = self.alloc(prov.alloc_id).slice_data {
                            if let Some(heap_base) = self.allocation_base(heap_alloc_id).cloned() {
                                let dest_ty = self.body.local_decls[dest].ty;
                                self.set_local(dest, VmValue {
                                    term: heap_base,
                                    ty: dest_ty,
                                    provenance: Some(Provenance {
                                        alloc_id: heap_alloc_id,
                                        offset: Int::from_u64(self.ctx, 0),
                                        is_field_offset: false,
                                    }),
                                    invariants: ValueInvariants {
                                        non_null: true,
                                        init: true,
                                        in_bounds: true,
                                        aligned: true,
                                        ..ValueInvariants::default()
                                    },
                                });
                            }
                        }
                    }
                }
            }
            CallEffect::OwnsInitMemory { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(prov) = &arg_val.provenance {
                        self.alloc_mut(prov.alloc_id).initialized = true;
                    }
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.init = true;
                    val.invariants.non_null = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnAllocBuffer => {
                // Model `Allocator::allocate(self, layout)`'s `Ok` variant as a
                // fresh *external* allocation: the exact byte count is
                // `layout.size()`, a symbolic value, so mark the allocation
                // unbounded (`is_external`) so `NonNull`/`Allocated` checks
                // auto-pass. The `Result` downcast `((_res as Ok).0)` copies
                // this provenance into the extracted `NonNull<[u8]>`.
                let dest_ty = self.body.local_decls[dest].ty;
                let max = Int::from_u64(self.ctx, i64::MAX as u64);
                let (alloc_id, base) = self.allocate_external(max, 1, None);
                self.alloc_mut(alloc_id).initialized = true;
                self.set_local(dest, VmValue {
                    term: base,
                    ty: dest_ty,
                    provenance: Some(Provenance {
                        alloc_id,
                        offset: Int::from_u64(self.ctx, 0),
                        is_field_offset: false,
                    }),
                    invariants: ValueInvariants {
                        non_null: true,
                        init: true,
                        in_bounds: true,
                        aligned: true,
                        ..ValueInvariants::default()
                    },
                });
            }
            CallEffect::ReturnPowerOfTwo => {
                // `Layout::align()` returns the layout's alignment, which is a
                // non-zero power of two. `Layout::align` inlines to
                // `self.align.as_usize()`, whose transmute-based body drops the
                // `NonZero` provenance; re-establish the non-zero fact (and the
                // power-of-two fact) with a fresh symbol so downstream
                // `from_size_align_unchecked` can discharge `align != 0` (its
                // `(align & (align - 1)) == 0` check is otherwise vacuously
                // proved, since contract-level `BitAnd` is unsupported).
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("layout_align_{}", dest.as_usize()));
                let zero = Int::from_u64(self.ctx, 0);
                self.path_conditions.push(term.gt(&zero));
                self.set_local(dest, VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                });
            }
            CallEffect::ChecksIndexBoundsDisjoint { indices_arg, len_arg } => {
                let indices = args.get(*indices_arg);
                let len_val = args.get(*len_arg);
                if let (Some(indices_val), Some(len_val)) = (indices, len_val) {
                    let arr_ty = match indices_val.ty.kind() {
                        rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                        _ => indices_val.ty,
                    };
                    if let rustc_middle::ty::TyKind::Array(_elem_ty, _const_len) = arr_ty.kind() {
                        let alloc_id = indices_val.provenance_alloc_id()
                            .or_else(|| {
                                // Slicer may have dropped the &indices
                                // assignment, losing provenance.  Fall back
                                 let fallback = self.locals.values().find_map(|v| {
                                    if v.ty == arr_ty { v.provenance_alloc_id() }
                                    else { None }
                                });
                                fallback
                            });
                        if let Some(alloc_id) = alloc_id {
                            self.contract_flags.has_checked_bounds = true;
                            let zero = Int::from_u64(self.ctx, 0);
                            let mut byte_offsets: Vec<(usize, Int)> = self
                                .alloc_byte_values(alloc_id)
                                .into_iter()
                                .map(|(off, term)| (off, term.clone()))
                                .collect();
                            byte_offsets.sort_by_key(|(off, _)| *off);
                            for (_, term) in &byte_offsets {
                                self.path_conditions.push(term.ge(&zero));
                                self.path_conditions.push(term.lt(&len_val.term));
                            }
                            for i in 0..byte_offsets.len() {
                                for j in (i + 1)..byte_offsets.len() {
                                    let ti = &byte_offsets[i].1;
                                    let tj = &byte_offsets[j].1;
                                    self.path_conditions.push(ti._eq(tj).not());
                                }
                            }
                        }
                    }
                }
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("ck_ok_{}", dest.as_usize()));
                self.set_local( dest, VmValue { term, ty: dest_ty, provenance: None, invariants: ValueInvariants::default() });
            }
            _ => {
                self.notes.push(format!("unhandled call effect: {:?}", effect));
                let dest_ty = self.body.local_decls[dest].ty;
                let term = self.fresh_int(&format!("unk_{}", dest.as_usize()));
                self.set_local(
                    dest,
                    VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    },
                );
            }
        }
    }

    /// Compute the preserved alignment when doing `base + offset * stride`.
    /// Pointer arithmetic only ever *preserves* the base's alignment; it never
    /// creates it. When the base's alignment is unknown, we cannot conclude
    /// anything about the result (a `wrapping_add` over misaligned storage does
    /// not become aligned just because the stride is a power of two).
    fn compute_pointer_add_align(
        &self,
        base: &VmValue<'ctx, 'tcx>,
        _offset: &VmValue<'ctx, 'tcx>,
        stride_bytes: u64,
    ) -> Option<u64> {
        let base_align = base.invariants.align_n;
        let Some(n) = base_align else { return None };
        if stride_bytes > 0 && stride_bytes % n == 0 {
            return Some(n);
        }
        None
    }

    pub(crate) fn propagate_const_bytes_to_tracked(
        &mut self,
        args: &[Spanned<Operand<'tcx>>],
    ) {
        let mut const_bytes: Option<(Vec<u8>, usize)> = None;
        let mut tracked_alloc: Option<AllocId> = None;
        let mut tracked_offset: usize = 0;

        for (i, arg) in args.iter().enumerate() {
            let arg_val = self.value_of_operand(&arg.node);
            if const_bytes.is_none() {
                let bytes_opt = super::state::extract_const_bytes_from_operand(
                    self.tcx,
                    &arg.node,
                ).or_else(|| self.trace_to_const_bytes(&arg.node));
                if let Some(bytes) = bytes_opt {
                    const_bytes = Some((bytes, i));
                }
            }
            if tracked_alloc.is_none() {
                if let Some(alloc_id) = arg_val.provenance_alloc_id() {
                    tracked_alloc = Some(alloc_id);
                    if let Some(ref prov) = arg_val.provenance {
                        tracked_offset = prov.offset.as_u64().map(|v| v as usize).unwrap_or(0);
                    }
                }
            }
        }

        if let (Some((bytes, _)), Some(alloc_id)) = (const_bytes, tracked_alloc) {
            for (j, &b) in bytes.iter().enumerate() {
                let off = tracked_offset + j;
                self.record_byte_value(
                    alloc_id,
                    off,
                    Int::from_u64(self.ctx, b as u64),
                );
                if b == 0 {
                    self.mark_byte_nul(alloc_id, off);
                } else {
                    self.mark_byte_non_nul(alloc_id, off);
                }
            }
            self.alloc_mut(alloc_id).initialized = true;
        }
    }

    /// Extract the element type from a Vec<T>'s type, e.g. Vec<*mut Entry> → *mut Entry.
    fn vec_elem_ty(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        if let TyKind::Adt(adt_def, substs) = ty.kind() {
            let name = self.tcx.def_path_str(adt_def.did());
            if api_classify::is_std_vec(&name) {
                return substs.first().and_then(|s| s.as_type());
            }
        }
        None
    }

    /// Element size (bytes) of the type iterated by an Iter/IterMut pointer.
    pub(crate) fn iter_elem_size(&self, ptr: &VmValue<'ctx, 'tcx>) -> u64 {
        let elem_ty = match ptr.ty.kind() {
            TyKind::Adt(_, substs) => substs.first().and_then(|s| s.as_type()),
            _ => None,
        };
        elem_ty.map(|t| self.size_of_ty(t).max(1)).unwrap_or(1) as u64
    }

    /// Remaining element count of the Iter/IterMut backed by `local`
    /// (fields `[0]` = ptr, `[1]` = end_or_len).  When a tracked pointer
    /// offset exists (`iter_ptr_offset`), prefers the compact
    /// `base_len - offset` form; otherwise falls back to
    /// `(end.offset - ptr.offset) / elem_size`.
    fn iter_remaining_len(&self, local: Local) -> Option<Int<'ctx>> {
        let ptr = self.field_value(local, &[0])?;
        let end = self.field_value(local, &[1])?;
        let pp = ptr.provenance.as_ref()?;
        let ep = end.provenance.as_ref()?;
        if pp.alloc_id != ep.alloc_id {
            return None;
        }
        let sz = Int::from_u64(self.ctx, self.iter_elem_size(&ptr));
        if let Some(offset) = self.iter_ptr_offset.get(&local) {
            let base_len = ep.offset.div(&sz);
            let zero = Int::from_u64(self.ctx, 0);
            Some(offset.gt(&base_len).ite(&zero, &Int::sub(self.ctx, &[&base_len, offset])))
        } else {
            Some(Int::sub(self.ctx, &[&ep.offset, &pp.offset]).div(&sz))
        }
    }

    /// For Iter/IterMut types, compute len from struct fields directly
    /// instead of the generic allocation-size heuristic. Returns true
    /// if handled (value set to dest).
    fn interpreter_iter_len(&mut self, arg_val: &VmValue<'ctx, 'tcx>, dest: Local) -> bool {
        let Some(l) = self.find_iter_self_local(arg_val) else {
            return false;
        };
        let Some(len_term) = self.iter_remaining_len(l) else {
            return false;
        };
        let dest_ty = self.body.local_decls[dest].ty;
        self.set_local(dest, VmValue::new(len_term, dest_ty));
        true
    }

    /// For Iter/IterMut types, compute is_empty from struct fields. Returns
    /// true if handled (value set to dest).
    fn interpreter_iter_is_empty(&mut self, arg_val: &VmValue<'ctx, 'tcx>, dest: Local) -> bool {
        let Some(l) = self.find_iter_self_local(arg_val) else {
            return false;
        };
        let Some(remaining) = self.iter_remaining_len(l) else {
            return false;
        };
        let dest_ty = self.body.local_decls[dest].ty;
        let zero = Int::from_u64(self.ctx, 0);
        let one = Int::from_u64(self.ctx, 1);
        let val = VmValue {
            term: remaining._eq(&zero).ite(&one, &zero),
            ty: dest_ty,
            provenance: None,
            invariants: ValueInvariants::default(),
        };
        self.is_empty_len.insert(dest, remaining);
        self.set_local(dest, val);
        true
    }

    /// Apply the side effect of post_inc_start / pre_dec_end on Iter/IterMut.
    /// Only updates the tracked offset (not field values), so that the
    /// precondition check (which runs before the call executes) sees the
    /// pre-update state, while subsequent len()/is_empty() calls use
    /// `base_len - offset` via interpreter_iter_len.
    fn apply_iter_ptr_update(
        &mut self,
        _callee: DefId,
        cname: &str,
        arg_values: &[VmValue<'ctx, 'tcx>],
        _caller_arg_locals: &[Local],
    ) {
        let is_inc = api_classify::is_post_inc_start(&cname);
        if !is_inc { return; }  // pre_dec_end not yet supported
        let self_val = &arg_values[0];
        let some_local = self.find_iter_self_local(self_val);
        let Some(local) = some_local else { return };
        let offset_term = arg_values.get(1).map(|v| v.term.clone())
            .unwrap_or_else(|| Int::from_u64(self.ctx, 1));
        let new_offset = match self.iter_ptr_offset.get(&local) {
            Some(prev) => Int::add(self.ctx, &[prev, &offset_term]),
            None => offset_term,
        };
        self.iter_ptr_offset.insert(local, new_offset);
    }

    /// If arg_val is a reference to an Iter or IterMut struct, return the
    /// local index of the referent (so field values can be looked up).
    /// Since len()/is_empty() always take &self, local 1 is the receiver.
    fn find_iter_self_local(&self, arg_val: &VmValue<'ctx, 'tcx>) -> Option<Local> {
        match arg_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => {
                    let name = self.tcx.def_path_str(adt_def.did());
                    if api_classify::is_std_iter_or_itermut(&name) {
                        // Find the local holding the iterator by matching the
                        // reference's address term against known local addresses
                        // (`&mut _iter` has term `addr__iter`).  A hardcoded
                        // `Local(1)` only holds for inlined `next` bodies where
                        // the iterator is the first argument; direct trait
                        // `Iterator::next` calls keep the iterator at an
                        // arbitrary local.
                        for (local, addr) in &self.local_addresses {
                            if addr == &arg_val.term {
                                return Some(*local);
                            }
                        }
                        // Fallback for inlined `next` bodies (iter bound to arg 1).
                        return Some(Local::from_usize(1));
                    }
                    None
                }
                _ => None,
            },
            _ => None,
        }
    }
}
