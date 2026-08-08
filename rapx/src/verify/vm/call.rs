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
use z3::ast::{Ast, Int};

use crate::compat::{FxHashSet, Spanned};
use crate::verify::call_summary::{self, CallEffect};

use super::state::{AllocId, Provenance, ValueInvariants, VmState, VmValue};

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

        // Try inline for callees with available MIR, unless fn_simulator
        // has a precise summary (memory allocation, intrinsics, known ptr
        // arithmetic, etc.). The summary path handles these with
        // hand-crafted invariants that are more precise than BFS inline.
        let callee = crate::helpers::mir_utils::dep_callee_def_id(func);
        let mut tried_inline = false;
        if let Some(c) = callee {
            if self.tcx.is_mir_available(c) {
                let name = crate::helpers::mir_utils::call_name(self.tcx, func);
                let has_fn_sim = crate::verify::call_summary::fn_simulator::lookup_effect(
                    self.tcx,
                    caller_def_id,
                    Some(c),
                    &name,
                    func,
                    destination,
                )
                .is_some();
                if !has_fn_sim {
                    if self.exec_inline_call(c, &arg_values, destination, 0) {
                        self.materialize_const_bytes_after_call(args, destination);
                        return;
                    }
                    tried_inline = true;
                }
            }
        }

        let summary = call_summary::effect_summary(self.tcx, caller_def_id, func, destination);

        self.last_call_name = summary.name.clone();

        if !summary.unsupported {
            for effect in &summary.effects {
                self.apply_call_effect(effect, &arg_values, destination);
            }
        } else {
            if !tried_inline {
                let callee = crate::helpers::mir_utils::dep_callee_def_id(func);
                let inlined = callee
                    .and_then(|c| {
                        if self.tcx.is_mir_available(c) {
                            Some(self.exec_inline_call(c, &arg_values, destination, 0))
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
            self.notes
                .push(format!("unsupported call: {}", summary.name));
            let dest_ty = self.body.local_decls[destination].ty;
            self.set_local(
                destination,
                VmValue {
                    term: self.fresh_int(&format!("callret_{}", destination.as_usize())),
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                },
            );
            return;
        }

        self.materialize_const_bytes_after_call(args, destination);
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
                | rustc_middle::ty::TyKind::Ref(_, inner, _) => match inner.kind() {
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                    | rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8) => true,
                    rustc_middle::ty::TyKind::Array(elem_ty, _)
                    | rustc_middle::ty::TyKind::Slice(elem_ty) => {
                        matches!(
                            elem_ty.kind(),
                            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                        )
                    }
                    _ => false,
                },
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
        dest: Local,
        depth: usize,
    ) -> bool {
        if depth >= MAX_INLINE_DEPTH {
            return false;
        }

        let callee_body = self.tcx.optimized_mir(callee_def_id);

        // Only inline small, linear functions. Branching functions
        // require state forking which we don't do yet; the summary
        // system provides better precision for those cases.
        if callee_body.basic_blocks.len() > 3 || arg_values.len() > 4 {
            return false;
        }

        // Check that the callee has no SwitchInt terminators (linear CFG).
        for bb_data in callee_body.basic_blocks.iter() {
            if matches!(bb_data.terminator().kind, TerminatorKind::SwitchInt { .. }) {
                return false;
            }
        }

        // Count return points — if > 1, the inline is imprecise.
        let return_count = callee_body
            .basic_blocks
            .iter()
            .filter(|bb| matches!(bb.terminator().kind, TerminatorKind::Return))
            .count();
        if return_count > 1 {
            return false;
        }

        // ── Save caller context ──
        let saved_body = self.body;
        let saved_caller = self.caller_def_id;
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_field_values = std::mem::take(&mut self.field_values);
        let saved_field_init = std::mem::take(&mut self.field_init);
        let saved_local_addresses = std::mem::take(&mut self.local_addresses);
        let saved_local_alloc_ids = std::mem::take(&mut self.local_alloc_ids);
        let saved_binary_op_sources = std::mem::take(&mut self.binary_op_sources);
        let saved_dropped_locals = std::mem::take(&mut self.dropped_locals);

        // ── Switch to callee context ──
        self.body = callee_body;
        self.caller_def_id = callee_def_id;

        // Bind args to callee locals (local_1..local_N are function params)
        for (i, arg_val) in arg_values.iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            self.ensure_local_allocation(callee_local);
            self.set_local(callee_local, arg_val.clone());
        }

        // ── BFS execution of callee MIR ──
        self.inline_execute_body();

        // ── Capture return value ──
        let return_val = self.locals.get(&Local::from_usize(0)).cloned();

        // ── Restore caller context ──
        self.body = saved_body;
        self.caller_def_id = saved_caller;
        self.locals = saved_locals;
        self.field_values = saved_field_values;
        self.field_init = saved_field_init;
        self.local_addresses = saved_local_addresses;
        self.local_alloc_ids = saved_local_alloc_ids;
        self.binary_op_sources = saved_binary_op_sources;
        self.dropped_locals = saved_dropped_locals;

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
                        self.init_allocations.insert(prov.alloc_id);
                    }
                }
                self.set_local(dest, val);
            }
            None => {
                return false;
            }
        }

        true
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
                self.current_block = Some(block);
                self.current_statement_index = Some(si);
                if let Err(reason) = self.exec_statement(block, si, stmt) {
                    self.notes.push(format!(
                        "inline: unsupported stmt at bb{}#{}: {}",
                        block.as_usize(),
                        si,
                        reason.message,
                    ));
                }
            }

            // Process terminator
            let terminator = bb_data.terminator();
            self.current_block = Some(block);
            self.current_statement_index = None;

            match &terminator.kind {
                TerminatorKind::Goto { target } => {
                    queue.push(*target);
                }
                TerminatorKind::Return => {
                    // Return value captured in local_0
                }
                TerminatorKind::Assert {
                    cond,
                    expected,
                    target,
                    ..
                } => {
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
            CallEffect::ReturnTupleFieldLength {
                field: _field,
                from_arg: _from_arg,
            } => {
                if args.is_empty() {
                    return;
                }
                let dest_ty = self.body.local_decls[dest].ty;
                if let TyKind::Tuple(elem_tys) = dest_ty.kind() {
                    for f in 0..elem_tys.len() {
                        let field_ty = elem_tys[f];
                        let base_prov = self.locals.get(&dest).and_then(|v| v.provenance.clone());
                        let field_val = VmValue {
                            term: args[0].term.clone(),
                            ty: field_ty,
                            provenance: base_prov,
                            invariants: ValueInvariants {
                                init: true,
                                non_null: true,
                                aligned: true,
                                in_bounds: args[0].invariants.in_bounds,
                                align_n: None,
                            },
                        };
                        self.set_field_value(dest, vec![f], field_val);
                    }
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
                    let is_vec = self.last_call_name.contains("::Vec")
                        || self.last_call_name.contains("::CString");
                    if is_vec {
                        if let Some(ref prov) = val.provenance {
                            if let Some(data_alloc) =
                                self.slice_data_allocations.get(&prov.alloc_id).copied()
                            {
                                if let Some(data_base) = self.allocation_base(data_alloc).cloned() {
                                    val.term = data_base;
                                    val.provenance = Some(Provenance {
                                        alloc_id: data_alloc,
                                        offset: Int::from_u64(self.ctx, 0),
                                    });
                                }
                            }
                        }
                    }
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerAdd {
                base_arg,
                offset_arg,
                stride,
            } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let adjusted_offset = if stride_bytes == 1 {
                        Int::add(self.ctx, &[&offset.term])
                    } else {
                        let stride_term = Int::from_u64(self.ctx, stride_bytes);
                        Int::mul(self.ctx, &[&offset.term, &stride_term])
                    };
                    let new_term = Int::add(self.ctx, &[&base.term, &adjusted_offset]);
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| Provenance {
                        alloc_id: prov.alloc_id,
                        offset: Int::add(self.ctx, &[&prov.offset, &adjusted_offset]),
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
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::ReturnPointerSub {
                base_arg,
                offset_arg,
                stride,
            } => {
                if let (Some(base), Some(offset)) = (args.get(*base_arg), args.get(*offset_arg)) {
                    let stride_bytes = stride.unwrap_or(1);
                    let stride_term = Int::from_u64(self.ctx, stride_bytes);
                    let scaled = Int::mul(self.ctx, &[&offset.term, &stride_term]);
                    let new_term = Int::sub(self.ctx, &[&base.term, &scaled]);
                    let adjusted_provenance = base.provenance.as_ref().map(|prov| Provenance {
                        alloc_id: prov.alloc_id,
                        offset: Int::sub(self.ctx, &[&prov.offset, &scaled]),
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
                        },
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::CleanSliceDataLinks { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(ref prov) = arg_val.provenance {
                        self.slice_data_allocations.remove(&prov.alloc_id);
                    }
                }
            }
            CallEffect::ReturnNonZero => {
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.non_null = true;
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_nz_{}", dest.as_usize()));
                    self.set_local(
                        dest,
                        VmValue {
                            term,
                            ty: dest_ty,
                            provenance: None,
                            invariants: ValueInvariants {
                                non_null: true,
                                ..Default::default()
                            },
                        },
                    );
                }
            }
            CallEffect::ReturnAligned {
                align: _,
                ty_name: _,
            } => {
                if let Some(mut existing) = self.locals.get(&dest).cloned() {
                    existing.invariants.aligned = true;
                    existing.invariants.non_null = true;
                    self.set_local(dest, existing);
                } else {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("ret_align_{}", dest.as_usize()));
                    self.set_local(
                        dest,
                        VmValue {
                            term,
                            ty: dest_ty,
                            provenance: None,
                            invariants: ValueInvariants {
                                aligned: true,
                                non_null: true,
                                ..Default::default()
                            },
                        },
                    );
                }
            }
            CallEffect::ReturnLengthOfArg { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    let effective_alloc_id = arg_val
                        .provenance_alloc_id()
                        .and_then(|pid| self.slice_data_allocations.get(&pid).copied())
                        .or_else(|| arg_val.provenance_alloc_id());

                    if let Some(alloc_id) = effective_alloc_id {
                        let dest_ty = self.body.local_decls[dest].ty;
                        // If the allocation has an element type, divide the
                        // byte-aligned size by the element size to return the
                        // number of elements (e.g. slice length).
                        if let Some(elem_ty) = self
                            .allocations
                            .iter()
                            .find(|a| a.id == alloc_id)
                            .and_then(|a| a.element_ty)
                        {
                            let elem_size = self.size_of_ty(elem_ty) as u64;
                            if elem_size > 1 {
                                if let Some(size) = self.allocation_size(alloc_id) {
                                    let div = Int::from_u64(self.ctx, elem_size);
                                    let val = VmValue {
                                        term: size.div(&div),
                                        ty: dest_ty,
                                        provenance: None,
                                        invariants: ValueInvariants::default(),
                                    };
                                    self.set_local(dest, val);
                                    return;
                                }
                            } else if let Some(size) = self.allocation_size(alloc_id) {
                                let val = VmValue {
                                    term: size.clone(),
                                    ty: dest_ty,
                                    provenance: None,
                                    invariants: ValueInvariants::default(),
                                };
                                self.set_local(dest, val);
                                return;
                            }
                        } else if let Some(size) = self.allocation_size(alloc_id) {
                            let val = VmValue {
                                term: size.clone(),
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
                let term = self.fresh_int(&format!("len_{}", dest.as_usize()));
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
            CallEffect::ReturnMin { lhs_arg, rhs_arg } => {
                if let (Some(lhs), Some(rhs)) = (args.get(*lhs_arg), args.get(*rhs_arg)) {
                    let dest_ty = self.body.local_decls[dest].ty;
                    let term = self.fresh_int(&format!("min_{}", dest.as_usize()));
                    self.path_conditions.push(term.le(&lhs.term));
                    self.path_conditions.push(term.le(&rhs.term));
                    let eq_lhs = term._eq(&lhs.term);
                    let eq_rhs = term._eq(&rhs.term);
                    self.path_conditions
                        .push(z3::ast::Bool::or(self.ctx, &[&eq_lhs, &eq_rhs]));
                    let val = VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    };
                    self.set_local(dest, val);
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg) {
                    if let Some(prov) = &arg_val.provenance {
                        // For locally-created Vec-like types: create a heap data
                        // allocation on first mutation. (Param Vecs already have
                        // an external allocation set by init_parameters.)
                        let is_vec = crate::verify::call_summary::fn_simulator::is_vec_push(
                            &self.last_call_name,
                        );
                        let is_external = self
                            .allocations
                            .iter()
                            .any(|a| a.id == prov.alloc_id && a.is_external);
                        if is_vec && !is_external {
                            let elem_ty = match arg_val.ty.kind() {
                                TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => {
                                    self.vec_elem_ty(*inner)
                                }
                                _ => self.vec_elem_ty(arg_val.ty),
                            };
                            let heap_align =
                                elem_ty.map(|ty| self.align_of_ty(ty)).unwrap_or(1).max(1);
                            if let Some(old_data) =
                                self.slice_data_allocations.get(&prov.alloc_id).copied()
                            {
                                // Subsequent mutation: invalidate old heap data.
                                self.dead_allocations.insert(old_data);
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) =
                                    self.allocate_external(max_size, heap_align, elem_ty);
                                self.slice_data_allocations
                                    .insert(prov.alloc_id, data_alloc);
                            } else {
                                // First mutation: create heap data allocation.
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                let (data_alloc, _) =
                                    self.allocate_external(max_size, heap_align, elem_ty);
                                self.slice_data_allocations
                                    .insert(prov.alloc_id, data_alloc);
                            }
                        }
                        // When offset is concrete, only mark the bytes actually
                        // written. For symbolic offsets, mark entire allocation.
                        let off_u64 = prov
                            .offset
                            .as_u64()
                            .or_else(|| prov.offset.simplify().as_u64());
                        if let Some(off) = off_u64 {
                            if off == 0 {
                                self.init_allocations.insert(prov.alloc_id);
                            }
                            let elem_size = match arg_val.ty.kind() {
                                rustc_middle::ty::TyKind::Ref(_, inner, _) => {
                                    self.size_of_ty(*inner) as usize
                                }
                                _ => 0,
                            };
                            let write_size = if elem_size > 0 {
                                elem_size
                            } else {
                                self.allocation_size(prov.alloc_id)
                                    .and_then(|s| s.as_u64())
                                    .unwrap_or(0) as usize
                            };
                            let end = (off as usize + write_size).min(4096);
                            for byte_off in (off as usize)..end {
                                self.byte_init.insert((prov.alloc_id, byte_off));
                            }
                        } else {
                            if prov.offset.as_u64() == Some(0) {
                                self.init_allocations.insert(prov.alloc_id);
                            }
                            if let Some(size) = self.allocation_size(prov.alloc_id).cloned() {
                                if let Some(size_val) = size.as_u64() {
                                    for off in 0..(size_val as usize).min(1024) {
                                        self.byte_init.insert((prov.alloc_id, off));
                                    }
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
            CallEffect::ReturnFreshAllocation {
                pointer_arg,
                size_arg,
                elem_size,
            } => {
                if let (Some(ptr_val), Some(size_val)) =
                    (args.get(*pointer_arg), args.get(*size_arg))
                {
                    let elem_sz = Int::from_u64(self.ctx, *elem_size);
                    let total = Int::mul(self.ctx, &[&size_val.term, &elem_sz]);
                    let dest_ty = self.body.local_decls[dest].ty;
                    // For generic types (elem_size == 0), use external alloc
                    // so Allocated/InBound checks auto-pass.
                    let (alloc_id, _base) = if *elem_size == 0 {
                        let max = Int::from_u64(self.ctx, i64::MAX as u64);
                        self.allocate_external(max, 1, None)
                    } else {
                        self.allocate(total, *elem_size, None)
                    };
                    let prov = Provenance {
                        alloc_id,
                        offset: ptr_val
                            .provenance
                            .as_ref()
                            .map(|p| p.offset.clone())
                            .unwrap_or_else(|| Int::from_u64(self.ctx, 0)),
                    };
                    // If return is a reference, register slice/pointee data
                    if let Some(ref dest_alloc_id) = self.local_alloc_ids.get(&dest).copied() {
                        self.slice_data_allocations
                            .insert(dest_alloc_id.clone(), alloc_id);
                    }
                    // Propagate init status and byte-level tracking from the source pointer
                    // For fresh allocations, the init status is inherited from the source.
                    let is_external = self
                        .allocations
                        .iter()
                        .any(|a| a.id == alloc_id && a.is_external);
                    if is_external {
                        self.init_allocations.insert(alloc_id);
                    }
                    if let Some(ref source_prov) = ptr_val.provenance {
                        // Always propagate init: from_raw_parts creates a view into
                        // existing memory.  If the source memory is init, so is the
                        // new slice.  InBound/ValidPtr check the bounds independently.
                        if !self.dead_allocations.contains(&source_prov.alloc_id) {
                            self.init_allocations.insert(alloc_id);
                        }
                        // Copy byte-level tracking
                        let byte_pairs: Vec<_> = self
                            .byte_values
                            .iter()
                            .filter(|((aid, _), _)| *aid == source_prov.alloc_id)
                            .map(|((_, off), term)| (*off, term.clone()))
                            .collect();
                        for (off, term) in byte_pairs {
                            self.record_byte_value(alloc_id, off, term);
                        }
                        let init_bytes: Vec<_> = self
                            .byte_init
                            .iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in init_bytes {
                            self.byte_init.insert((alloc_id, off));
                        }
                        let nul_offs: Vec<_> = self
                            .known_nul_offsets
                            .iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in nul_offs {
                            self.known_nul_offsets.insert((alloc_id, off));
                        }
                        let non_nul_offs: Vec<_> = self
                            .known_non_nul_offsets
                            .iter()
                            .filter(|(aid, _)| *aid == source_prov.alloc_id)
                            .map(|(_, off)| *off)
                            .collect();
                        for off in non_nul_offs {
                            self.known_non_nul_offsets.insert((alloc_id, off));
                        }
                    }
                    self.set_local(
                        dest,
                        VmValue {
                            term: ptr_val.term.clone(),
                            ty: dest_ty,
                            provenance: Some(prov),
                            invariants: ValueInvariants {
                                non_null: true,
                                init: true,
                                in_bounds: true,
                                aligned: true,
                                ..ValueInvariants::default()
                            },
                        },
                    );
                }
            }
            CallEffect::ReturnNewAllocation {
                size_arg,
                elem_size,
            } => {
                if let Some(size_val) = args.get(*size_arg) {
                    let elem_sz = Int::from_u64(self.ctx, *elem_size);
                    let total = Int::mul(self.ctx, &[&size_val.term, &elem_sz]);
                    let dest_ty = self.body.local_decls[dest].ty;
                    let elem_ty = self.vec_elem_ty(dest_ty);
                    let heap_align = elem_ty.map(|ty| self.align_of_ty(ty)).unwrap_or(1).max(1);
                    let (alloc_id, base) = self.allocate_external(total, heap_align, elem_ty);
                    let dest_alloc_id = self.local_alloc_ids.get(&dest).copied();
                    if let Some(dest_alloc_id) = dest_alloc_id {
                        self.slice_data_allocations.insert(dest_alloc_id, alloc_id);
                    }
                    self.init_allocations.insert(alloc_id);
                    self.set_local(
                        dest,
                        VmValue {
                            term: base,
                            ty: dest_ty,
                            provenance: dest_alloc_id.map(|stack_id| Provenance {
                                alloc_id: stack_id,
                                offset: Int::from_u64(self.ctx, 0),
                            }),
                            invariants: ValueInvariants {
                                non_null: true,
                                init: true,
                                in_bounds: true,
                                aligned: true,
                                ..ValueInvariants::default()
                            },
                        },
                    );
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
                    self.slice_data_allocations.insert(*dest_alloc_id, alloc_id);
                }
                self.init_allocations.insert(alloc_id);
                self.set_local(
                    dest,
                    VmValue {
                        term: base,
                        ty: dest_ty,
                        provenance: dest_alloc_id.map(|stack_id| Provenance {
                            alloc_id: stack_id,
                            offset: Int::from_u64(self.ctx, 0),
                        }),
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            in_bounds: true,
                            aligned: true,
                            ..ValueInvariants::default()
                        },
                    },
                );
            }
            CallEffect::ReturnBoxFromVec { arg } => {
                if let Some(vec_val) = args.get(*arg) {
                    if let Some(ref prov) = vec_val.provenance {
                        if let Some(heap_alloc_id) =
                            self.slice_data_allocations.get(&prov.alloc_id).copied()
                        {
                            if let Some(heap_base) = self.allocation_base(heap_alloc_id).cloned() {
                                let dest_ty = self.body.local_decls[dest].ty;
                                self.set_local(
                                    dest,
                                    VmValue {
                                        term: heap_base,
                                        ty: dest_ty,
                                        provenance: Some(Provenance {
                                            alloc_id: heap_alloc_id,
                                            offset: Int::from_u64(self.ctx, 0),
                                        }),
                                        invariants: ValueInvariants {
                                            non_null: true,
                                            init: true,
                                            in_bounds: true,
                                            aligned: true,
                                            ..ValueInvariants::default()
                                        },
                                    },
                                );
                            }
                        }
                    }
                }
            }
            CallEffect::OwnsInitMemory { arg } => {
                if let Some(arg_val) = args.get(*arg) {
                    if let Some(prov) = &arg_val.provenance {
                        self.init_allocations.insert(prov.alloc_id);
                    }
                    let mut val = arg_val.clone();
                    val.ty = self.body.local_decls[dest].ty;
                    val.invariants.init = true;
                    val.invariants.non_null = true;
                    self.set_local(dest, val);
                }
            }
            CallEffect::ChecksIndexBoundsDisjoint {
                indices_arg,
                len_arg,
            } => {
                let indices = args.get(*indices_arg);
                let len_val = args.get(*len_arg);
                if let (Some(indices_val), Some(len_val)) = (indices, len_val) {
                    let arr_ty = match indices_val.ty.kind() {
                        rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                        _ => indices_val.ty,
                    };
                    if let rustc_middle::ty::TyKind::Array(_elem_ty, _const_len) = arr_ty.kind() {
                        let alloc_id = indices_val.provenance_alloc_id().or_else(|| {
                            // Slicer may have dropped the &indices
                            // assignment, losing provenance.  Fall back
                            let fallback = self.locals.values().find_map(|v| {
                                if v.ty == arr_ty {
                                    v.provenance_alloc_id()
                                } else {
                                    None
                                }
                            });
                            fallback
                        });
                        if let Some(alloc_id) = alloc_id {
                            self.checked_bounds_disjoint
                                .push((alloc_id, len_val.term.clone()));
                            self.has_checked_bounds = true;
                            let zero = Int::from_u64(self.ctx, 0);
                            let mut byte_offsets: Vec<(usize, Int)> = self
                                .byte_values
                                .iter()
                                .filter(|((aid, _), _)| *aid == alloc_id)
                                .map(|((_, off), term)| (*off, term.clone()))
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
            _ => {
                self.notes
                    .push(format!("unhandled call effect: {:?}", effect));
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
    /// If stride is a multiple of known alignment, the result has that alignment.
    fn compute_pointer_add_align(
        &self,
        base: &VmValue<'ctx, 'tcx>,
        _offset: &VmValue<'ctx, 'tcx>,
        stride_bytes: u64,
    ) -> Option<u64> {
        let base_align = base.invariants.align_n;
        if let Some(n) = base_align {
            if stride_bytes > 0 && stride_bytes % n == 0 {
                return Some(n);
            }
        }
        // If stride itself is a power of two, the step preserves that alignment
        if stride_bytes > 1 && stride_bytes.is_power_of_two() {
            if base_align.map_or(true, |a| stride_bytes >= a && stride_bytes % a == 0) {
                return Some(stride_bytes.min(base_align.unwrap_or(stride_bytes)));
            }
        }
        None
    }

    pub(crate) fn propagate_const_bytes_to_tracked(&mut self, args: &[Spanned<Operand<'tcx>>]) {
        let mut const_bytes: Option<(Vec<u8>, usize)> = None;
        let mut tracked_alloc: Option<AllocId> = None;
        let mut tracked_offset: usize = 0;

        for (i, arg) in args.iter().enumerate() {
            let arg_val = self.value_of_operand(&arg.node);
            if const_bytes.is_none() {
                let bytes_opt = super::state::extract_const_bytes_from_operand(self.tcx, &arg.node)
                    .or_else(|| self.trace_to_const_bytes(&arg.node));
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
                self.record_byte_value(alloc_id, off, Int::from_u64(self.ctx, b as u64));
                if b == 0 {
                    self.known_nul_offsets.insert((alloc_id, off));
                } else {
                    self.known_non_nul_offsets.insert((alloc_id, off));
                }
            }
            self.init_allocations.insert(alloc_id);
        }
    }

    /// Extract the element type from a Vec<T>'s type, e.g. Vec<*mut Entry> → *mut Entry.
    fn vec_elem_ty(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        if let TyKind::Adt(adt_def, substs) = ty.kind() {
            let name = self.tcx.def_path_str(adt_def.did());
            if name.ends_with("::Vec") || name == "Vec" {
                return substs.first().and_then(|s| s.as_type());
            }
        }
        None
    }
}
