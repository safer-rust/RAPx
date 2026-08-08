//! MIR statement and terminator executors for the symbolic VM.
//!
//! Each executor is a transfer function that updates `VmState` based on
//! the semantics of a MIR construct. The VM walks retained MIR items
//! in forward path order, calling these executors.

use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Local, Operand, Place, Rvalue,
        Statement, StatementKind, Terminator, TerminatorKind, UnOp,
    },
    ty::Ty,
};
#[cfg(not(rapx_has_skip_norm_wip))]
use crate::compat::SkipNormWip;
use rustc_hir::def_id::DefId;
use z3::ast::{Ast, Bool, Int};

use crate::{
    compat::FxHashSet,
    verify::{
        contract::{ContractExpr, PlaceBase, Property, PropertyArg, PropertyKind},
        def_use::PlaceKey,
        path_extractor::{Path, PathStep},
        slicer::BackwardItem,
    },
};

use super::state::{AllocId, Provenance, VmState, VmValue, ValueInvariants};

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Execute all retained MIR items in path order.
    pub fn execute_items(
        &mut self,
        items: &[BackwardItem<'tcx>],
    ) -> Result<(), super::state::UnsupportedReason> {
        // Initialize function parameters as fresh symbolic values.
        // Parameters are _1.._N (excluding _0 return value).
        self.init_parameters();

        for item in items {
            match item {
                BackwardItem::Statement {
                    block,
                    statement_index,
                    kind: _,
                } => {
                    let statement =
                        &self.body.basic_blocks[*block].statements[*statement_index];
                    self.current_block = Some(*block);
                    self.current_statement_index = Some(*statement_index);
                    self.exec_statement(*block, *statement_index, statement)?;
                }
                BackwardItem::Terminator { block, kind: _ } => {
                    let occ = self
                        .block_occurrences
                        .get(block)
                        .map(|c| c + 1)
                        .unwrap_or(1);
                    self.block_occurrences.insert(*block, occ);
                    let terminator = self.body.basic_blocks[*block].terminator();
                    self.current_block = Some(*block);
                    self.current_statement_index = None;
                    self.exec_terminator(*block, terminator, occ)?;
                }
                BackwardItem::PathStep { step, kind } => {
                    self.notes.push(format!(
                        "path step {:?} kept for {:?}",
                        step, kind
                    ));
                }
                BackwardItem::ContractFact { property } => {
                    self.assert_contract_fact(property);
                }
                BackwardItem::Forget { reason } => {
                    self.notes.push(format!("forget: {:?}", reason));
                }
                BackwardItem::CalleeEntry { callee, args } => {
                    self.handle_callee_entry(*callee, args);
                }
                BackwardItem::CalleeExit { dest } => {
                    self.handle_callee_exit(*dest);
                }
            }
        }
        Ok(())
    }

    /// Enter a callee's function context during sliced inline execution.
    /// Saves the caller's locals state, pushes the callee body onto the
    /// context stack, and binds caller args to callee parameters.
    fn handle_callee_entry(
        &mut self,
        callee_def_id: DefId,
        arg_locals: &[Local],
    ) {
        let callee_body = self.tcx.optimized_mir(callee_def_id);

        // Save caller's locals
        let saved_locals = std::mem::take(&mut self.locals);

        // Clone the arg values we need before pushing context
        let arg_vals: Vec<Option<VmValue<'ctx, 'tcx>>> = arg_locals.iter()
            .map(|&local| saved_locals.get(&local).cloned())
            .collect();

        self.saved_caller_locals = Some(saved_locals);

        // Push callee context
        self.body_stack.push((self.body, self.caller_def_id));
        self.body = callee_body;
        self.caller_def_id = callee_def_id;

        // Bind args from saved caller state
        for (i, arg_val) in arg_vals.into_iter().enumerate() {
            let callee_local = Local::from_usize(i + 1);
            if let Some(val) = arg_val {
                self.ensure_local_allocation(callee_local);
                self.set_local(callee_local, val);
            }
        }
    }

    /// Exit a callee's function context. Captures the return value from
    /// callee's local_0, restores the caller's locals and body, and writes
    /// the return value to the caller's dest local.
    fn handle_callee_exit(
        &mut self,
        dest: Local,
    ) {
        let return_val = self.locals.get(&Local::from_usize(0)).cloned();

        // Restore caller context
        if let Some((saved_body, saved_caller)) = self.body_stack.pop() {
            self.body = saved_body;
            self.caller_def_id = saved_caller;
        }

        // Restore caller's locals
        if let Some(saved) = self.saved_caller_locals.take() {
            self.locals = saved;
        }

        // Write return value
        if let Some(mut val) = return_val {
            let dest_ty = self.body.local_decls[dest].ty;
            val.ty = dest_ty;
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
    }

    // ── Initialization ──────────────────────────────────────────

    fn init_parameters(&mut self) {
        let arg_count = self.body.arg_count;
        let local_count = self.body.local_decls.len();

        // Pre-allocate ALL locals and set initial values
        for local_idx in 1..local_count {
            let local = Local::from_usize(local_idx);
            if self.locals.contains_key(&local) {
                continue;
            }
            let decl = &self.body.local_decls[local];
            let ty = decl.ty;

            self.ensure_local_allocation(local);

            let mut invariants = ValueInvariants::default();
            if local_idx <= arg_count {
                // ── Box / Vec parameter: heap-allocated pointee ──
                if let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() {
                    let def_path = self.tcx.def_path_str(adt_def.did());
                    let is_vec = def_path.ends_with("::Vec") || def_path == "Vec";
                    if def_path.ends_with("::Box") || def_path == "Box"
                        || is_vec
                        || def_path.ends_with("::CString") || def_path == "CString"
                        || def_path.ends_with("::c_str::CString")
                    {
                        let heap_ty = if let rustc_middle::ty::TyKind::Adt(_, substs) = ty.kind() {
                            if let Some(first) = substs.first() {
                                first.as_type()
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        let heap_ty = heap_ty.unwrap_or(ty);
                        let heap_size = self.size_of_ty(heap_ty) as u64;
                        let heap_align = self.align_of_ty(heap_ty);
                        let heap_size_term = Int::from_u64(self.ctx, heap_size.max(1));
                        // Vec/CString can hold many elements — use an external
                        // allocation so Allocated checks can pass for arbitrary
                        // capacity queries.
                        let (heap_alloc_id, heap_base) = if is_vec {
                            let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                            let (id, base) = self.allocate_external(max_size, heap_align, Some(heap_ty));
                            (id, base)
                        } else {
                            self.allocate(heap_size_term, heap_align, Some(heap_ty))
                        };
                        invariants.non_null = true;
                        invariants.init = true;
                        invariants.aligned = true;
                        self.init_allocations.insert(heap_alloc_id);
                        self.set_local(local, VmValue {
                            term: heap_base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id: heap_alloc_id,
                                offset: Int::from_u64(self.ctx, 0),
                            }),
                            invariants,
                        });
                        continue;
                    }
                }
                // ── Struct/tuple/enum parameter (non-Box/Vec ADT) ──
                // Decompose into per-field symbolic values for field-level checking.
                if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() {
                    if adt_def.is_enum() {
                        let term = self.fresh_int(&format!("param_{}", local_idx));
                        self.set_local(local, VmValue {
                            term, ty, provenance: None, invariants,
                        });
                        continue;
                    }
                    let variant = adt_def.non_enum_variant();
                    for (idx, field_def) in variant.fields.iter().enumerate() {
                        let field_ty: Ty<'tcx> = field_def.ty(self.tcx, substs).skip_norm_wip();
                        let field_term = self.fresh_int(
                            &format!("field_{}_{}", local_idx, idx)
                        );
                        self.set_field_value(local, vec![idx], VmValue {
                            term: field_term,
                            ty: field_ty,
                            provenance: None,
                            invariants: ValueInvariants { init: true, ..Default::default() },
                        });
                        self.mark_field_init(local, vec![idx]);
                    }
                    let term = self.fresh_int(&format!("param_{}", local_idx));
                    self.set_local(local, VmValue {
                        term,
                        ty,
                        provenance: None,
                        invariants: ValueInvariants { init: true, ..Default::default() },
                    });
                    continue;
                }
                // ── Reference parameter (&T, &mut T) ──
                // Create a symbolic allocation for the pointee and attach
                // provenance so that pointer-deriving operations (as_ptr,
                // add, etc.) propagate correctly.
                if let rustc_middle::ty::TyKind::Ref(..) = ty.kind() {
                    invariants.non_null = true;
                    invariants.init = true;
                    invariants.aligned = true;

                    let pointee_ty = if let rustc_middle::ty::TyKind::Ref(_, inner_ty, _) = ty.kind() {
                        *inner_ty
                    } else {
                        ty
                    };

                    if let rustc_middle::ty::TyKind::Slice(elem_ty) = pointee_ty.kind() {
                        let elem_size = self.size_of_ty(*elem_ty) as u64;
                        let len = self.fresh_int(&format!("slice_len_{}", local_idx));
                        let zero = Int::from_u64(self.ctx, 0);
                        self.path_conditions.push(len.ge(&zero));
                        let isize_max = Int::from_i64(self.ctx, i64::MAX);
                        let elem_sz = if elem_size > 0 {
                            elem_size
                        } else {
                            self.size_of_generic_param(*elem_ty).max(1)
                        };
                        let elem_sz_term = Int::from_u64(self.ctx, elem_sz);
                        self.path_conditions.push(
                            Int::mul(self.ctx, &[&len, &elem_sz_term]).le(&isize_max));
                        let data_size = Int::mul(self.ctx, &[
                            &len,
                            &Int::from_u64(self.ctx, elem_size.max(1)),
                        ]);
                        let (data_alloc_id, data_base) = self.allocate(
                            data_size,
                            self.align_of_ty(*elem_ty),
                            Some(*elem_ty),
                        );
                        if let Some(ref_alloc_id) = self.alloc_for_local(local) {
                            self.slice_data_allocations.insert(ref_alloc_id, data_alloc_id);
                        }
                        self.init_allocations.insert(data_alloc_id);
                        self.set_local(local, VmValue {
                            term: data_base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id: data_alloc_id,
                                offset: Int::from_u64(self.ctx, 0),
                            }),
                            invariants,
                        });
                        continue;
                    }

                    // Non-slice reference: allocate pointee
                    let pointee_size = self.size_of_ty(pointee_ty) as u64;
                    let pointee_align = self.align_of_ty(pointee_ty);
                    let pointee_size_term = Int::from_u64(self.ctx, pointee_size.max(1));
                    let (pointee_alloc_id, pointee_base) = self.allocate(
                        pointee_size_term,
                        pointee_align,
                        Some(pointee_ty),
                    );
                    self.init_allocations.insert(pointee_alloc_id);
                    self.set_local(local, VmValue {
                        term: pointee_base,
                        ty,
                        provenance: Some(Provenance {
                            alloc_id: pointee_alloc_id,
                            offset: Int::from_u64(self.ctx, 0),
                        }),
                        invariants,
                    });

                    // Decompose struct fields for pointer-field access.
                    // E.g. &RawBuf → (*self).ptr should yield a valid raw ptr.
                    if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = pointee_ty.kind() {
                        if !adt_def.is_enum() {
                            let variant = adt_def.non_enum_variant();
                            for (idx, field_def) in variant.fields.iter().enumerate() {
                                let field_ty: Ty<'tcx> = field_def.ty(self.tcx, substs).skip_norm_wip();
                                if let rustc_middle::ty::TyKind::RawPtr(inner, _) = field_ty.kind() {
                                    let field_align = 1u64.max(self.align_of_ty(*inner));
                                    let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                    let (field_alloc_id, field_base) = self.allocate_external(
                                        max_size, field_align, Some(*inner),
                                    );
                                    self.init_allocations.insert(field_alloc_id);
                                    self.set_field_value(local, vec![idx], VmValue {
                                        term: field_base,
                                        ty: field_ty,
                                        provenance: Some(Provenance {
                                            alloc_id: field_alloc_id,
                                            offset: Int::from_u64(self.ctx, 0),
                                        }),
                                        invariants: ValueInvariants {
                                            non_null: true, init: true, ..Default::default()
                                        },
                                    });
                                    self.mark_field_init(local, vec![idx]);
                                } else if let Some(pointee) = self.find_nn_pointee(field_ty) {
                                    // Field contains NonNull<T> (possibly wrapped in Option):
                                    // create an external allocation for the pointee and
                                    // set field value with provenance so that subsequent
                                    // as_ptr() / as_ref() / as_mut() propagate correctly.
                                    let pointee_align = 1u64.max(self.align_of_ty(pointee));
                                    let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                    let (field_alloc_id, _field_base) = self.allocate_external(
                                        max_size, pointee_align, Some(pointee),
                                    );
                                    self.init_allocations.insert(field_alloc_id);
                                    let field_term = self.fresh_int(
                                        &format!("ref_field_{}_{}", local_idx, idx)
                                    );
                                    self.set_field_value(local, vec![idx], VmValue {
                                        term: field_term,
                                        ty: field_ty,
                                        provenance: Some(Provenance {
                                            alloc_id: field_alloc_id,
                                            offset: Int::from_u64(self.ctx, 0),
                                        }),
                                        invariants: ValueInvariants { init: true, ..Default::default() },
                                    });
                                    self.mark_field_init(local, vec![idx]);
                                }
                            }
                        }
                    }
                    continue;
                }
                // ── Scalar parameter ──
                let is_scalar = matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                );
                if is_scalar {
                    let val = self.fresh_int(&format!("arg_{}", local_idx));
                    self.set_local(local, VmValue {
                        term: val,
                        ty,
                        provenance: None,
                        invariants,
                    });
                    continue;
                }
                // ── Raw pointer parameter (*const T, *mut T) ──
                // Create a symbolic external allocation for provenance
                // tracking. No invariants are set — callers must provide
                // contracts (NonNull, ValidPtr, etc.) via assert_contract_fact
                // to make property checks pass.
                if let rustc_middle::ty::TyKind::RawPtr(pointee, _mutbl) = ty.kind() {
                    let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                    let pointee_align = self.align_of_ty(*pointee);
                    let (alloc_id, base) = self.allocate_external(max_size, pointee_align, Some(*pointee));
                    self.set_local(local, VmValue {
                        term: base,
                        ty,
                        provenance: Some(Provenance {
                            alloc_id,
                            offset: Int::from_u64(self.ctx, 0),
                        }),
                        invariants,
                    });
                    continue;
                }
                // ── Scalar parameter ──
                let is_scalar = matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Bool
                        | rustc_middle::ty::TyKind::Char
                );
                if is_scalar {
                    let val = self.fresh_int(&format!("arg_{}", local_idx));
                    self.set_local(local, VmValue {
                        term: val,
                        ty,
                        provenance: None,
                        invariants,
                    });
                    continue;
                }
                // ── Array parameter ([usize; N], etc.) ──
                // Give every array parameter a real allocation with provenance so
                // that downstream call effects (e.g. ChecksIndexBoundsDisjoint)
                // can record the alloc_id and property checker can match it later.
                if let rustc_middle::ty::TyKind::Array(elem_ty, const_len) = ty.kind() {
                    let n: Option<usize> =
                        super::state::const_int_from_debug(&format!("{:?}", const_len))
                            .map(|v| v as usize);
                    let elem_size = self.size_of_ty(*elem_ty) as u64;
                    let step = (elem_size.max(1)) as usize;
                    let align = self.align_of_ty(*elem_ty);
                    let (alloc_id, base) = if let Some(n) = n {
                        let total = Int::from_u64(self.ctx, (step as u64).saturating_mul(n as u64));
                        self.allocate(total, align, Some(*elem_ty))
                    } else {
                        // Generic N: unbounded external allocation
                        let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                        self.allocate_external(max_size, align, Some(*elem_ty))
                    };
                    self.init_allocations.insert(alloc_id);
                    self.local_alloc_ids.insert(local, alloc_id);
                    if let Some(n) = n {
                        for i in 0..n {
                            let off = i * step;
                            let elem_term = self.fresh_int(&format!(
                                "array_{}_idx_{}",
                                local_idx, i
                            ));
                            self.record_byte_value(alloc_id, off, elem_term);
                        }
                    } else {
                        // Generic N: create placeholder byte_values so that
                        // downstream Index projection ITE chains and
                        // assert_in_bound_for_each can add constraints.
                        let m = 16usize;
                        for i in 0..m {
                            let off = i * step;
                            let elem_term = self.fresh_int(&format!(
                                "array_{}_idx_{}",
                                local_idx, i
                            ));
                            self.record_byte_value(alloc_id, off, elem_term);
                        }
                    }
                    self.set_local(
                        local,
                        VmValue {
                            term: base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.ctx, 0),
                            }),
                            invariants: ValueInvariants {
                                init: true,
                                ..invariants
                            },
                        },
                    );
                    continue;
                }
                // ── Struct / other parameter ──
                let term = self.fresh_int(&format!("param_{}", local_idx));
                self.set_local(local, VmValue {
                    term,
                    ty,
                    provenance: None,
                    invariants,
                });
                continue;
            }
            // ── Non-parameter local: use stack address with own-allocation
            // provenance as a fallback (overwritten by actual assignments).
            let addr = self.local_address(local);
            self.set_local(local, VmValue {
                term: addr,
                ty,
                provenance: None,
                invariants,
            });
        }

        // Entry-block provenance propagation: scan the first basic block
        // for simple assignments that propagate parameter values.  This
        // helps when the backward slicer omits same-block definitions
        // (e.g. `_tmp = _1 as *const T`).  Limiting to the entry block
        // ensures only unconditionally-executed assignments are covered.
        if let Some(entry_bb) = self.body.basic_blocks.iter().next() {
            for stmt in &entry_bb.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    let dest_local = dest.local;
                    let src = match rvalue {
                        #[cfg(rapx_rvalue_use_with_retag)]
                        Rvalue::Use(operand, _) => Some(operand),
                        #[cfg(not(rapx_rvalue_use_with_retag))]
                        Rvalue::Use(operand) => Some(operand),
                        Rvalue::Cast(_, operand, _) => Some(operand),
                        _ => None,
                    }.and_then(|operand| {
                        match operand {
                            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                                Some(place.local)
                            }
                            _ => None,
                        }
                    });
                    if let Some(src_local) = src {
                        if let Some(src_val) = self.locals.get(&src_local) {
                            let has_better_prov = src_val.provenance.is_some()
                                && src_val.invariants.non_null
                                && self.locals.get(&dest_local).map_or(true, |d| {
                                    d.provenance.is_none() || !d.invariants.non_null
                                });
                            if has_better_prov {
                                self.set_local(dest_local, VmValue {
                                    term: src_val.term.clone(),
                                    ty: dest.ty(self.body, self.tcx).ty,
                                    provenance: src_val.provenance.clone(),
                                    invariants: src_val.invariants,
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    /// Replay same-block assignment chains that the backward slicer may omit.
    /// Walks backwards through the CFG from the checkpoint block, propagating
    /// provenance and invariants through Use/Cast/RawPtr/CopyForDeref chains.
    /// Uses the current path to avoid cross-branch contamination.
    pub(crate) fn propagate_from_checkpoint(&mut self, checkpoint_block: BasicBlock) {
        let path_blocks: FxHashSet<BasicBlock> = self.path.as_ref()
            .map(|p| {
                let mut blocks: FxHashSet<BasicBlock> = p.steps.iter()
                    .filter_map(|s| match s {
                        crate::verify::path_extractor::PathStep::Block(b) => Some(*b),
                        _ => None,
                    })
                    .collect();
                blocks.insert(checkpoint_block);
                blocks
            })
            .unwrap_or_default();

        if path_blocks.is_empty() {
            self.propagate_pass(checkpoint_block, None, false);
            return;
        }

        // Detect SCC (loop) paths: if any block appears more than once
        // in the block steps, the path is unrolled and path-filtering
        // may exclude needed blocks.
        let block_steps: Vec<BasicBlock> = self.path.as_ref()
            .map(|p| p.steps.iter()
                .filter_map(|s| match s {
                    crate::verify::path_extractor::PathStep::Block(b) => Some(*b),
                    _ => None,
                })
                .collect())
            .unwrap_or_default();
        let has_duplicates = {
            let mut seen = FxHashSet::default();
            block_steps.iter().any(|b| !seen.insert(*b))
        };

        if has_duplicates {
            self.propagate_pass(checkpoint_block, Some(&path_blocks), false);
            return;
        }

        self.propagate_pass(checkpoint_block, Some(&path_blocks), false);
        self.propagate_pass(checkpoint_block, Some(&path_blocks), true);
    }

    fn propagate_pass(&mut self, checkpoint_block: BasicBlock,
        path_blocks: Option<&FxHashSet<BasicBlock>>, use_only: bool) {
        // Walk backwards through all reachable predecessors to fill in
        // provenance chains the slicer may have omitted (e.g. `_tmp = self.ptr`).
        let mut visited = FxHashSet::default();
        let mut worklist: Vec<BasicBlock> = vec![checkpoint_block];
        let mut max_depth = 32usize;
        while let Some(block) = worklist.pop() {
            if max_depth == 0 { break; }
            max_depth -= 1;
            if !visited.insert(block) { continue; }
            if let Some(blocks) = path_blocks {
                if !blocks.contains(&block) {
                    continue;
                }
            }
            for pred in self.body.basic_blocks.predecessors()[block].to_vec() {
                if path_blocks.map_or(true, |b| b.contains(&pred)) {
                    worklist.push(pred);
                }
            }
            for stmt in &self.body.basic_blocks[block].statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.projection.is_empty() {
                        if use_only && !Self::is_propagate_use_kind(rvalue) {
                            continue;
                        }
                        self.propagate_single_assign(dest.local, rvalue);
                    }
                }
            }
            // In use_only pass, skip terminator handling
            if use_only {
                continue;
            }
            // Also try to materialize constant bytes from call terminators
            // (e.g. as_ptr() on a constant byte array). The backward slicer
            // may prune these calls, so we fill them in here.
            let terminator = self.body.basic_blocks[block].terminator();
            if let TerminatorKind::Call { destination, args, func, .. } = &terminator.kind {
                let dest = destination.local;
                // Check if the destination needs provenance (as_ptr/as_mut_ptr fallback).
                let needs_fallback = match self.locals.get(&dest) {
                    Some(dv) => dv.provenance.is_none(),
                    None => true,
                };
                let mut fallback_applied = false;
                // Try constant byte materialization first
                if let Some(mut dv) = self.locals.get(&dest).cloned() {
                    let mut found = false;
                    for arg in args {
                        self.try_materialize_const_bytes(&mut dv, &arg.node);
                        if dv.provenance.is_some() {
                            self.set_local(dest, dv);
                            found = true;
                            break;
                        }
                    }
                    if !found && needs_fallback {
                        if let Some(first) = args.first() {
                            fallback_applied = self.try_as_ptr_fallback(dest, func, self.value_of_operand(&first.node), &first.node);
                        }
                    }
                }
                if !fallback_applied && needs_fallback && self.locals.get(&dest).is_none() {
                    if let Some(first) = args.first() {
                        self.try_as_ptr_fallback(dest, func, self.value_of_operand(&first.node), &first.node);
                    }
                }
                // For comparison calls (e.g. <[u8]>::eq), propagate
                // constant bytes from a literal operand to the tracked
                // operand's allocation so ValidCStr checks succeed.
                if self.locals.contains_key(&dest) {
                    let cmpr_name = crate::helpers::mir_utils::call_name(self.tcx, func);
                    if cmpr_name.contains("::eq") || cmpr_name.contains("PartialEq") {
                        self.propagate_const_bytes_to_tracked(args);
                    }
                }
            }
        }
    }

    /// Check if an rvalue kind should be re-propagated in the use-only pass
    /// (Use/Cast/CopyForDeref — forward-propagate existing provenance).
    fn is_propagate_use_kind(rvalue: &Rvalue<'tcx>) -> bool {
        matches!(rvalue,
            Rvalue::Use(..) | Rvalue::Cast(..) | Rvalue::CopyForDeref(..))
    }

    /// Propagate a single MIR assignment to fill in provenance for previously
    /// uninitialised locals.
    fn propagate_single_assign(&mut self, dest_local: Local, rvalue: &Rvalue<'tcx>) {
        // Don't overwrite a value that was already set by forward execution.
        if self.locals.contains_key(&dest_local) {
            return;
        }

        let src_local = match rvalue {
            #[cfg(rapx_rvalue_use_with_retag)]
            Rvalue::Use(operand, _) => extract_local(operand),
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(operand) => extract_local(operand),
            Rvalue::Cast(_, operand, _) => extract_local(operand),
            Rvalue::CopyForDeref(place) if place.projection.is_empty() => Some(place.local),
            _ => None,
        };

        if let Some(src) = src_local {
            if let Some(src_val) = self.locals.get(&src).cloned() {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let is_cast = matches!(rvalue, Rvalue::Cast(..));
                let is_ptr_arith = matches!(
                    rvalue,
                    Rvalue::BinaryOp(BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked
                        | BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked
                        | BinOp::Offset, _)
                );
                self.set_local(dest_local, VmValue {
                    term: src_val.term,
                    ty: dest_ty,
                    provenance: src_val.provenance,
                    invariants: ValueInvariants {
                        aligned: src_val.invariants.aligned,
                        in_bounds: false,
                        align_n: if is_cast || is_ptr_arith { src_val.invariants.align_n } else { None },
                        ..src_val.invariants
                    },
                });
            }
            return;
        }

        // Handle projected-places: Use/CopyForDeref of a place with projections
        // (e.g. `_2 = (*_1).0` or `_2 = _1.ptr`).  Trace through field and deref
        // projections to find the ultimate source local and its provenance.
        let src_place = match rvalue {
            #[cfg(rapx_rvalue_use_with_retag)]
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p), _) => Some(p),
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => Some(p),
            Rvalue::CopyForDeref(p) => Some(p),
            _ => None,
        };
        if let Some(place) = src_place {
            if !place.projection.is_empty() {
                if let Some(val) = self.value_of_place(place) {
                    if val.provenance.is_some() || val.invariants.non_null {
                        let dest_ty = self.body.local_decls[dest_local].ty;
                        self.set_local(dest_local, VmValue {
                            term: val.term,
                            ty: dest_ty,
                            provenance: val.provenance,
                            invariants: val.invariants,
                        });
                    }
                }
            }
            return;
        }

        // Ref: &place → propagate address + provenance
        if let Rvalue::Ref(_, _, place) = rvalue {
            if let Some(addr) = self.address_of_place(place) {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let alloc_align = addr.provenance.as_ref()
                    .and_then(|p| self.allocations.iter().find(|a| a.id == p.alloc_id))
                    .map(|a| a.align)
                    .filter(|&a| a > 1);
                self.set_local(dest_local, VmValue {
                    term: addr.term,
                    ty: dest_ty,
                    provenance: addr.provenance,
                    invariants: ValueInvariants {
                        non_null: true, aligned: true, init: true, in_bounds: false,
                        align_n: alloc_align,
                    },
                });
            }
            return;
        }

        // RawPtr: &raw place → propagate address + provenance
        if let Rvalue::RawPtr(_, place) = rvalue {
            if let Some(addr) = self.address_of_place(place) {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let alloc_align = addr.provenance.as_ref()
                    .and_then(|p| self.allocations.iter().find(|a| a.id == p.alloc_id))
                    .map(|a| a.align)
                    .filter(|&a| a > 1);
                self.set_local(dest_local, VmValue {
                    term: addr.term,
                    ty: dest_ty,
                    provenance: addr.provenance,
                    invariants: ValueInvariants {
                        non_null: true, in_bounds: false, align_n: alloc_align, ..Default::default()
                    },
                });
            }
            return;
        }

        // BinaryOp Add/Sub/Offset: lhs provenance → dest
        if let Rvalue::BinaryOp(op, pair) = rvalue {
            let (lhs_op, _rhs_op) = &**pair;
            if matches!(op,
                BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked
                | BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked
                | BinOp::Offset)
            {
                let lhs = extract_local(lhs_op);
                if let Some(src) = lhs {
                    if let Some(src_val) = self.locals.get(&src).cloned() {
                        let dest_ty = self.body.local_decls[dest_local].ty;
                        self.set_local(dest_local, VmValue {
                            term: src_val.term,
                            ty: dest_ty,
                            provenance: src_val.provenance,
                            invariants: ValueInvariants {
                                aligned: src_val.invariants.aligned,
                                in_bounds: false,
                                align_n: src_val.invariants.align_n,
                                ..src_val.invariants
                            },
                        });
                    }
                }
            }
        }
    }

    // ── Statement executors ──────────────────────────────────────

    pub(crate) fn exec_statement(
        &mut self,
        block: BasicBlock,
        statement_index: usize,
        statement: &Statement<'tcx>,
    ) -> Result<(), super::state::UnsupportedReason> {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                self.exec_assign(place, rvalue)?;
            }
            StatementKind::StorageLive(local) => {
                self.exec_storage_live(*local);
            }
            StatementKind::StorageDead(local) => {
                self.exec_storage_dead(*local);
            }
            StatementKind::FakeRead(..)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(..)
            | StatementKind::PlaceMention(..)
            | StatementKind::Intrinsic(..)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop => {}
            #[cfg(not(rapx_rustc_ge_198))]
            StatementKind::Retag(..) => {}
            _ => {
                self.notes.push(format!(
                    "unsupported statement at bb{}#{}",
                    block.as_usize(),
                    statement_index
                ));
            }
        }
        Ok(())
    }

    fn exec_assign(
        &mut self,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Result<(), super::state::UnsupportedReason> {
        let value = self.eval_rvalue(place, rvalue)?;
        let place_key = PlaceKey::from_mir_place(place);

        let has_deref = place.projection.iter().any(|p| {
            matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref)
        });

        if !place.projection.is_empty() {
            self.record_projected_store(place, &value);
            self.record_indexed_store_for_vm(place, &value);
        }

        self.record_definition(place_key, &value);

        if place.projection.is_empty() {
            let mut value = value;
            value.invariants.init = true;
            self.set_local(place.local, value);
        } else if !has_deref {
            // Field projection (no Deref): update field_values for the base local.
            let field_indices: Vec<usize> = place.projection.iter()
                .filter_map(|p| match p.kind() {
                    rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                    _ => None,
                })
                .collect();
            if !field_indices.is_empty() {
                let mut write_value = value;
                write_value.invariants.init = true;
                self.set_field_value(place.local, field_indices, write_value);
            }
        }
        // For deref projections (`*ptr = val`): do NOT overwrite the base local.
        // Writing through a pointer should not reassign the pointer variable.

        Ok(())
    }

    /// Record byte-level values when assigning to a place with projections.
    /// This handles patterns like `buf[i] = 0u8` (nul-store) and `arr[i] = val`.
    fn record_projected_store(
        &mut self,
        place: &Place<'tcx>,
        value: &VmValue<'ctx, 'tcx>,
    ) {
        // Prefer the value's provenance (pointee alloc) over local_alloc_ids
        // (reference alloc) for ref/ptr parameters.
        let Some(alloc_id) = self.locals.get(&place.local)
            .and_then(|v| v.provenance_alloc_id())
            .or_else(|| self.local_alloc_ids.get(&place.local).copied())
        else {
            return;
        };

        let value_ty = value.ty;
        let value_size = self.size_of_ty(value_ty) as usize;

        let mut byte_offset: usize = 0;
        let mut concrete = true;

        let base_ty = self.body.local_decls[place.local].ty;
        let mut cur_ty = base_ty;

        for proj in place.projection.iter() {
            match proj.kind() {
                rustc_middle::mir::ProjectionElem::Field(field_idx, _) => {
                    let off = self.field_offset_in_bytes(cur_ty, field_idx.as_usize()) as usize;
                    byte_offset += off;
                    if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = cur_ty.kind() {
                        if !adt_def.is_enum() {
                            let variant = adt_def.non_enum_variant();
                            if let Some(field_def) = variant.fields.get(field_idx) {
                                let unnorm = field_def.ty(self.tcx, substs);
                                cur_ty = unnorm.skip_norm_wip();
                            }
                        }
                    }
                }
                rustc_middle::mir::ProjectionElem::Deref => {
                    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = cur_ty.kind() {
                        cur_ty = *inner;
                    }
                }
                rustc_middle::mir::ProjectionElem::Index(_local) => {
                    concrete = false;
                    break;
                }
                rustc_middle::mir::ProjectionElem::Subslice { from, to: _, from_end: _ } => {
                    byte_offset += from as usize;
                }
                _ => {}
            }
        }

        if concrete && value_size > 0 {
            self.init_allocations.insert(alloc_id);

            let is_u8_write = matches!(value_ty.kind(),
                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8));

            if is_u8_write {
                self.record_byte_value(alloc_id, byte_offset, value.term.clone());
                if let Some(term_val) = value.term.as_u64() {
                    if term_val == 0 {
                        self.known_nul_offsets.insert((alloc_id, byte_offset));
                    } else {
                        self.known_non_nul_offsets.insert((alloc_id, byte_offset));
                    }
                }
            }
        }
    }

    /// Track byte-level values for index-based stores (e.g. `buf[i] = 0u8`)
    /// that `record_projected_store` skips due to Index projections.
    fn record_indexed_store_for_vm(
        &mut self,
        place: &Place<'tcx>,
        value: &VmValue<'ctx, 'tcx>,
    ) {
        let is_u8 = matches!(value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8));
        if !is_u8 {
            return;
        }
        let has_index_with_concrete = place.projection.iter().any(|p| {
            if let rustc_middle::mir::ProjectionElem::Index(local) = p {
                self.locals.get(&local)
                    .and_then(|v| v.term.simplify().as_u64())
                    .is_some()
            } else {
                false
            }
        });
        if !has_index_with_concrete {
            return;
        }
        if let Some(addr) = self.address_of_place(place) {
            if let Some(ref prov) = addr.provenance {
                let alloc_id = prov.alloc_id;
                let byte_offset = prov.offset.as_u64().map(|v| v as usize).unwrap_or(0);
                self.init_allocations.insert(alloc_id);
                self.record_byte_value(alloc_id, byte_offset, value.term.clone());
                if let Some(term_val) = value.term.as_u64() {
                    if term_val == 0 {
                        self.known_nul_offsets.insert((alloc_id, byte_offset));
                    } else {
                        self.known_non_nul_offsets.insert((alloc_id, byte_offset));
                    }
                }
            }
        }
    }

    /// Inject layout constraints (>= 1) for generic AlignOf/SizeOf constants.
    fn inject_layout_constraints(&mut self, operand: &Operand<'tcx>, val: &VmValue<'ctx, 'tcx>) {
        if let Operand::Constant(constant) = operand {
            let text = format!("{:?}", constant.const_);
            if super::state::const_int_from_debug(&text).is_none() {
                let is_align_or_size = text.starts_with("AlignOf(") || text.starts_with("SizeOf(");
                if is_align_or_size {
                    let one = Int::from_u64(self.ctx, 1);
                    self.path_conditions.push(val.term.ge(&one));
                }
            }
        }
    }

    /// Evaluate an Rvalue into a VmValue.
    fn eval_rvalue(
        &mut self,
        dest_place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> Result<VmValue<'ctx, 'tcx>, super::state::UnsupportedReason> {
        let dest_ty = dest_place.ty(self.body, self.tcx).ty;

        match rvalue {
            #[cfg(rapx_rvalue_use_with_retag)]
            Rvalue::Use(operand, _retag) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                Ok(val)
            }
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(operand) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                Ok(val)
            }
            Rvalue::Ref(_, _borrow_kind, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr.provenance.as_ref()
                        .and_then(|p| self.allocations.iter().find(|a| a.id == p.alloc_id))
                        .map(|a| a.align)
                        .filter(|&a| a > 1);
                    let val = VmValue {
                        term: addr.term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            aligned: self.check_place_alignment(place),
                            init: true,
                            in_bounds: false,
                            align_n: alloc_align,
                        },
                    };
                    self.propagate_byte_values_to_ref(place, &val);
                    Ok(val)
                } else {
                    let term = self.fresh_int("ref_addr");
                    Ok(VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            ..Default::default()
                        },
                    })
                }
            }
            Rvalue::RawPtr(_, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr.provenance.as_ref()
                        .and_then(|p| self.allocations.iter().find(|a| a.id == p.alloc_id))
                        .map(|a| a.align)
                        .filter(|&a| a > 1);
                    let source_in_bounds = self.locals.get(&place.local)
                        .map_or(false, |v| v.invariants.in_bounds);
                    let val = VmValue {
                        term: addr.term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            in_bounds: source_in_bounds,
                            align_n: alloc_align,
                            ..Default::default()
                        },
                    };
                    Ok(val)
                } else {
                    let term = self.fresh_int("rawptr_addr");
                    Ok(VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            ..Default::default()
                        },
                    })
                }
            }
            Rvalue::BinaryOp(op, pair) => {
                let (lhs_op, rhs_op) = &**pair;
                let lhs = self.value_of_operand(lhs_op);
                let rhs = self.value_of_operand(rhs_op);
                let term = self.eval_binary_op(*op, &lhs.term, &rhs.term);
                let provenance = self.provenance_for_binary_op(*op, &lhs, &rhs);
                let invariants = self.invariants_for_binary_op(*op, &lhs, &rhs, &provenance);
                let dest_pk = PlaceKey::from_mir_place(dest_place);
                let lhs_pk = operand_to_place_key(lhs_op);
                let rhs_pk = operand_to_place_key(rhs_op);
                self.binary_op_sources.insert(dest_pk, (lhs_pk, rhs_pk));
                // Add Euclidean division identity for Div and Rem:
                //   lhs == (lhs/rhs)*rhs + lhs%rhs  ∧  lhs%rhs >= 0
                // Also add (lhs/rhs)*rhs <= lhs directly for Div for robustness.
                // This lets later checks prove (x/N)*N <= x and x%N >= 0.
                if matches!(*op, BinOp::Div | BinOp::Rem) {
                    let quot = lhs.term.div(&rhs.term);
                    let rem = lhs.term.rem(&rhs.term);
                    let mul_term = Int::mul(self.ctx, &[&quot, &rhs.term]);
                    let sum_term = Int::add(self.ctx, &[&mul_term, &rem]);
                    self.path_conditions.push(lhs.term._eq(&sum_term));
                    let zero = Int::from_u64(self.ctx, 0);
                    self.path_conditions.push(rem.ge(&zero));
                    // Direct inequality: (lhs/rhs)*rhs <= lhs
                    self.path_conditions.push(mul_term.le(&lhs.term));
                }
                // For tuple-returning binary ops (AddWithOverflow, MulWithOverflow),
                // populate field_values so that .0 (result) and .1 (overflow flag)
                // are properly tracked. Without this, field access falls through
                // to cloning the base term, mixing the arithmetic result with the
                // boolean overflow flag and corrupting path conditions.
                if let rustc_middle::ty::TyKind::Tuple(fields) = dest_ty.kind() {
                    if fields.len() == 2 {
                        let result_val = VmValue {
                            term: term.clone(),
                            ty: fields[0],
                            provenance: provenance.clone(),
                            invariants,
                        };
                        self.set_field_value(dest_place.local, vec![0], result_val);
                        let overflow_term = self.fresh_int("overflow_flag");
                        let overflow_val = VmValue {
                            term: overflow_term,
                            ty: fields[1],
                            provenance: None,
                            invariants: ValueInvariants::default(),
                        };
                        self.set_field_value(dest_place.local, vec![1], overflow_val);
                        self.mark_field_init(dest_place.local, vec![0]);
                        self.mark_field_init(dest_place.local, vec![1]);
                    }
                }
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance,
                    invariants,
                })
            }
            Rvalue::UnaryOp(op, operand) => {
                let val = self.value_of_operand(operand);
                let term = self.eval_unary_op(*op, &val.term);
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                })
            }
            Rvalue::Cast(_kind, operand, cast_ty) => {
                let src_val = self.value_of_operand(operand);
                let src_ty = src_val.ty;
                let is_src_ref = matches!(src_ty.kind(),
                    rustc_middle::ty::TyKind::Ref(..));
                let dest_is_ptr = matches!(cast_ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(..));
                let aligned = if dest_is_ptr && is_src_ref {
                    true
                } else {
                    src_val.invariants.aligned
                };
                Ok(VmValue {
                    term: src_val.term,
                    ty: *cast_ty,
                    provenance: src_val.provenance,
                    invariants: ValueInvariants {
                        non_null: src_val.invariants.non_null,
                        init: src_val.invariants.init,
                        aligned,
                        in_bounds: src_val.invariants.in_bounds,
                        align_n: src_val.invariants.align_n,
                    },
                })
            }
            Rvalue::Aggregate(_kind, operands) => {
                let term = self.fresh_int("aggregate");
                let dest_local = dest_place.local;
                let dest_alloc_id = self.local_alloc_ids.get(&dest_local).copied();
                let is_byte_array = self.is_u8_array_or_slice(dest_ty);
                let field_types: Vec<_> = self.aggregate_field_tys(dest_ty);
                let mut byte_offset = 0usize;
                for (i, operand) in operands.iter().enumerate() {
                    let field_val = self.value_of_operand(operand);
                    let field_sz = field_types.get(i).copied()
                        .map(|ty| self.size_of_ty(ty) as usize)
                        .unwrap_or(1);
                    let field_term = field_val.term.clone();
                    self.set_field_value(dest_local, vec![i], field_val);
                    self.mark_field_init(dest_local, vec![i]);
                    if let Some(alloc_id) = dest_alloc_id {
                        self.init_allocations.insert(alloc_id);
                        if is_byte_array && field_sz == 1 {
                            self.record_byte_value(alloc_id, byte_offset, field_term.clone());
                        }
                        // Record known_nul / known_non_nul from constant operands
                        if let Some(int_val) = extract_operand_const(operand) {
                            if field_sz == 1 {
                                if int_val == 0 {
                                    self.known_nul_offsets.insert((alloc_id, byte_offset));
                                    if !is_byte_array {
                                        self.record_byte_value(alloc_id, byte_offset,
                                            Int::from_u64(self.ctx, 0));
                                    }
                                } else {
                                    self.known_non_nul_offsets.insert((alloc_id, byte_offset));
                                    if !is_byte_array {
                                        self.record_byte_value(alloc_id, byte_offset,
                                            Int::from_u64(self.ctx, int_val));
                                    }
                                }
                            }
                            // For multi-byte fields: track each constituent byte
                            for b in 0..field_sz.min(8) {
                                let byte_off = byte_offset + b;
                                let byte_val = (int_val >> (b * 8)) & 0xFF;
                                if byte_val == 0 {
                                    self.known_nul_offsets.insert((alloc_id, byte_off));
                                } else {
                                    self.known_non_nul_offsets.insert((alloc_id, byte_off));
                                }
                                self.record_byte_value(alloc_id, byte_off,
                                    Int::from_u64(self.ctx, byte_val));
                            }
                        }
                    }
                    byte_offset += field_sz;
                }
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            Rvalue::Discriminant(_place) => {
                let term = self.fresh_int("discriminant");
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::ShallowInitBox(operand, _ty) => {
                let val = self.value_of_operand(operand);
                Ok(VmValue {
                    term: val.term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                })
            }
            Rvalue::CopyForDeref(place) => {
                if let Some(val) = self.value_of_place(place) {
                    Ok(val)
                } else {
                    let term = self.fresh_int("copy_for_deref");
                    Ok(VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    })
                }
            }
            Rvalue::Repeat(operand, _count) => {
                let _val = self.value_of_operand(operand);
                let term = self.fresh_int("repeat");
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            Rvalue::ThreadLocalRef(_) => {
                let term = self.fresh_int("thread_local");
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            #[cfg(not(rapx_rustc_ge_196))]
            Rvalue::NullaryOp(_op) => {
                let term = self.fresh_int("nullary");
                let op_debug = format!("{:?}", _op);
                let is_align_of = op_debug.contains("AlignOf") || op_debug.contains("min_align_of");
                let is_size_of = op_debug.contains("SizeOf");
                if is_align_of || is_size_of {
                    let one = Int::from_u64(self.ctx, 1);
                    self.path_conditions.push(term.ge(&one));
                }
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            Rvalue::WrapUnsafeBinder(_operand, _ty) => {
                let term = self.fresh_int("wrap_unsafe_binder");
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                })
            }
            #[cfg(rapx_rvalue_has_reborrow)]
            Rvalue::Reborrow(_ty, _mutability, _place) => {
                let term = self.fresh_int("reborrow");
                Ok(VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants { non_null: true, ..Default::default() },
                })
            }
        }
    }

    // ── Arithmetic ────────────────────────────────────────────────

    fn eval_binary_op(&self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Int<'ctx> {
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                Int::add(self.ctx, &[lhs, rhs])
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                Int::sub(self.ctx, &[lhs, rhs])
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                Int::mul(self.ctx, &[lhs, rhs])
            }
            BinOp::Div => lhs.div(rhs),
            BinOp::Rem => lhs.rem(rhs),
            BinOp::Eq => {
                let cond = lhs._eq(rhs);
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Ne => {
                let cond = lhs._eq(rhs).not();
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Lt => {
                let cond = lhs.lt(rhs);
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Le => {
                let cond = lhs.le(rhs);
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Gt => {
                let cond = lhs.gt(rhs);
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Ge => {
                let cond = lhs.ge(rhs);
                cond.ite(&Int::from_u64(self.ctx, 1), &Int::from_u64(self.ctx, 0))
            }
            BinOp::Offset => Int::add(self.ctx, &[lhs, rhs]),
            _ => self.fresh_int("binop"),
        }
    }

    fn eval_unary_op(&self, op: UnOp, val: &Int<'ctx>) -> Int<'ctx> {
        match op {
            UnOp::Not => {
                let zero = Int::from_u64(self.ctx, 0);
                let one = Int::from_u64(self.ctx, 1);
                val._eq(&zero).ite(&one, &zero)
            }
            UnOp::Neg => {
                let zero = Int::from_u64(self.ctx, 0);
                Int::sub(self.ctx, &[&zero, val])
            }
            UnOp::PtrMetadata => self.fresh_int("ptr_metadata"),
        }
    }

    /// Compute provenance for a binary operation on pointer values.
    /// Propagates provenance with adjusted offset for pointer arithmetic
    /// (`ptr + offset`, `ptr - offset`, `Offset`).
    fn provenance_for_binary_op(
        &self,
        op: BinOp,
        lhs: &VmValue<'ctx, 'tcx>,
        rhs: &VmValue<'ctx, 'tcx>,
    ) -> Option<Provenance<'ctx>> {
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked
            | BinOp::Offset => {
                // ptr + scalar → propagate with adjusted offset
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.ctx, &[&prov.offset, &rhs.term]),
                })
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                if rhs.provenance.is_some() {
                    // ptr - ptr → integer (difference), no provenance
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::sub(self.ctx, &[&prov.offset, &rhs.term]),
                })
            }
            _ => None,
        }
    }

    /// Compute invariants for a binary operation.
    /// Propagates non_null from pointer arithmetic and align_n from compatible ops.
    fn invariants_for_binary_op(
        &self,
        op: BinOp,
        lhs: &VmValue<'ctx, 'tcx>,
        rhs: &VmValue<'ctx, 'tcx>,
        provenance: &Option<Provenance<'ctx>>,
    ) -> ValueInvariants {
        let non_null = provenance.is_some() && lhs.invariants.non_null;

        let align_n = match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked
            | BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked
            | BinOp::Offset => {
                // If both LHS and RHS are known to be n-aligned, sum/diff is n-aligned
                match (lhs.invariants.align_n, rhs.invariants.align_n) {
                    (Some(a), Some(b)) if a == b => Some(a),
                    // LHS has alignment, RHS is a constant multiple of it
                    (Some(a), None) => {
                        let c = rhs.term.as_u64().unwrap_or(1);
                        if c % a == 0 { Some(a) } else { None }
                    }
                    // LHS has alignment, RHS is the result of Mul by constant factor
                    (Some(a), _) if self.rhs_is_aligned_multiple(rhs, a) => Some(a),
                    _ => None,
                }
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                if let Some(c) = rhs.term.as_u64() {
                    if c > 0 && c.is_power_of_two() {
                        Some(c)
                    } else if c > 0 {
                        let factor = 1u64 << c.trailing_zeros();
                        if factor > 1 { Some(factor) } else { None }
                    } else {
                        None
                    }
                } else if let Some(c) = lhs.term.as_u64() {
                    if c > 0 && c.is_power_of_two() {
                        Some(c)
                    } else if c > 0 {
                        let factor = 1u64 << c.trailing_zeros();
                        if factor > 1 { Some(factor) } else { None }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => lhs.invariants.align_n,
        };

        ValueInvariants { non_null, align_n, ..Default::default() }
    }

    /// Check if a value is known to be a multiple of `align` (e.g. the result
    /// of a Mul by a constant factor of `align`).
    fn rhs_is_aligned_multiple(&self, val: &VmValue<'ctx, 'tcx>, align: u64) -> bool {
        // If the value itself has align_n >= align, it's a multiple
        if let Some(a) = val.invariants.align_n {
            if a >= align && a % align == 0 { return true; }
        }
        // If the value is a constant, check directly
        if let Some(c) = val.term.as_u64() {
            if c % align == 0 { return true; }
        }
        false
    }

    // ── Storage ──────────────────────────────────────────────────

    fn exec_storage_live(&mut self, local: Local) {
        self.local_address(local);
        if let Some(alloc_id) = self.local_alloc_ids.get(&local).copied() {
            self.dead_allocations.remove(&alloc_id);
        }
    }

    fn exec_storage_dead(&mut self, local: Local) {
        self.dropped_locals.insert(local);
        if let Some(alloc_id) = self.local_alloc_ids.get(&local).copied() {
            self.dead_allocations.insert(alloc_id);
            if let Some(block) = self.current_block {
                self.dead_alloc_blocks.insert(alloc_id, block);
            }
        }
    }

    pub(crate) fn exec_drop(&mut self, place: &Place<'tcx>) {
        self.dropped_locals.insert(place.local);
        if let Some(alloc_id) = self.local_alloc_ids.get(&place.local).copied() {
            self.dead_allocations.insert(alloc_id);
            if let Some(block) = self.current_block {
                self.dead_alloc_blocks.insert(alloc_id, block);
            }
            // Cascade to heap data allocations (see exec_storage_dead).
            let mut worklist: Vec<AllocId> = vec![alloc_id];
            while let Some(id) = worklist.pop() {
                if let Some(data_id) = self.slice_data_allocations.get(&id).copied() {
                    self.dead_allocations.insert(data_id);
                    if let Some(block) = self.current_block {
                        self.dead_alloc_blocks.insert(data_id, block);
                    }
                    worklist.push(data_id);
                }
            }
        }
        self.notes.push(format!("drop: {:?}", place));
    }

    // ── Terminator executors ─────────────────────────────────────

    fn exec_terminator(
        &mut self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        occurrence: usize,
    ) -> Result<(), super::state::UnsupportedReason> {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let caller_id = self.caller_def_id;
                self.exec_call(
                    func,
                    args,
                    destination.local,
                    *target,
                    None,
                    caller_id,
                );
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.exec_switchint(block, discr, targets, occurrence);
            }
            TerminatorKind::Assert { cond, expected, .. } => {
                self.exec_assert(cond, *expected, block, occurrence);
            }
            TerminatorKind::Goto { .. }
            | TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::Yield { .. }
            | TerminatorKind::CoroutineDrop
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::InlineAsm { .. }
            | TerminatorKind::TailCall { .. } => {}
            TerminatorKind::Drop { place, .. } => {
                self.exec_drop(place);
            }
        }
        Ok(())
    }

    /// Execute a SwitchInt terminator.
    ///
    /// Uses the path to determine which branch is taken, then adds
    /// a path condition asserting the discriminant equals that value.
    fn exec_switchint(
        &mut self,
        block: BasicBlock,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        occurrence: usize,
    ) {
        let discr_val = self.value_of_operand(discr);

        // Determine which target block is taken along the path.
        if let Some(ref path) = self.path {
            if let Some(chosen) = chosen_successor(path, block, occurrence) {
                for (value, target) in targets.iter() {
                    if target == chosen {
                        let val_term = Int::from_u64(self.ctx, value as u64);
                        self.path_conditions.push(discr_val.term._eq(&val_term));
                        if value != 0 {
                            self.infer_switch_guard(discr);
                        }
                        return;
                    }
                }
                // Otherwise branch with single value → the remaining value
                if targets.otherwise() == chosen && targets.iter().count() == 1 {
                    let explicit = targets.iter().next().unwrap().0;
                    let other = if explicit == 0 { 1 } else { 0 };
                    let val_term = Int::from_u64(self.ctx, other);
                    self.path_conditions.push(discr_val.term._eq(&val_term));
                    if other != 0 {
                        self.infer_switch_guard(discr);
                    }
                    return;
                }
            }
        }

        // Conservative fallback: note it but don't add path condition
        self.notes.push(format!(
            "SwitchInt at bb{} occ{}: discr is symbolic, branch unknown",
            block.as_usize(),
            occurrence
        ));
    }

    /// Execute an Assert terminator.
    fn exec_assert(
        &mut self,
        cond: &Operand<'tcx>,
        expected: bool,
        _block: BasicBlock,
        _occurrence: usize,
    ) {
        let cond_val = self.value_of_operand(cond);
        if expected {
            let zero = Int::from_u64(self.ctx, 0);
            self.path_conditions
                .push(cond_val.term._eq(&zero).not());
        } else {
            let zero = Int::from_u64(self.ctx, 0);
            self.path_conditions.push(cond_val.term._eq(&zero));
        }

        // Guard inference: trace the assert condition back to find non_null sources
        self.infer_guard_non_null(cond, expected);
        // Infer alignment from == 0 guards on Rem expressions
        self.infer_guard_align(cond, expected);
    }

    /// Infer alignment constraints from guards of the form `(x % n) == 0`.
    pub(crate) fn infer_guard_align(&mut self, cond: &Operand<'tcx>, expected: bool) {
        if !expected { return; }
        let place = match cond {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return,
        };
        let cond_pk = PlaceKey::from_mir_place(place);

        // Check if cond is a Ne/Eq comparison of (x % n) against 0
        if let Some((lhs_pk, rhs_pk)) = self.binary_op_sources.get(&cond_pk).cloned() {
            // The lhs is (x % n), rhs is constant 0
            let rem_pk = match (&lhs_pk, &rhs_pk) {
                (Some(pk), None) => pk.clone(),
                (None, Some(pk)) => pk.clone(),
                _ => return,
            };
            // Trace the Rem operand
            if let Some((div_lhs, div_rhs)) = self.binary_op_sources.get(&rem_pk).cloned() {
                // div_rhs is the divisor constant
                if let Some(divisor) = resolve_u64_from_place_key(&div_rhs, self) {
                    if divisor > 0 {
                        // Mark div_lhs as having align_n = divisor
                        if let Some(src_pk) = &div_lhs {
                            if let Some(local) = src_pk.local() {
                                if let Some(mut val) = self.locals.get(&local).cloned() {
                                    val.invariants.align_n = Some(divisor);
                                    self.set_local(local, val);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    /// Infer non_null invariants from branch guards.
    pub(crate) fn infer_guard_non_null(&mut self, cond: &Operand<'tcx>, expected: bool) {
        if !expected { return; }
        let place = match cond {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return,
        };
        let cond_pk = PlaceKey::from_mir_place(place);

        // Check if cond was defined by BinaryOp(Ne, (ptr, 0)) or similar
        if let Some((lhs_pk, rhs_pk)) = self.binary_op_sources.get(&cond_pk).cloned() {
            // lhs is pointer, rhs is None (constant zero) → mark lhs as non_null
            if rhs_pk.is_none() {
                if let Some(ptr_pk) = &lhs_pk {
                    if let Some(local) = ptr_pk.local() {
                        if let Some(mut val) = self.locals.get(&local).cloned() {
                            val.invariants.non_null = true;
                            self.set_local(local, val);
                        }
                    }
                }
            }
            // rhs is pointer, lhs is None (constant zero) → mark rhs as non_null
            if lhs_pk.is_none() {
                if let Some(ptr_pk) = &rhs_pk {
                    if let Some(local) = ptr_pk.local() {
                        if let Some(mut val) = self.locals.get(&local).cloned() {
                            val.invariants.non_null = true;
                            self.set_local(local, val);
                        }
                    }
                }
            }
        }
    }

    /// Infer non_null from SwitchInt discriminant.
    fn infer_switch_guard(&mut self, discr: &Operand<'tcx>) {
        let place = match discr {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return,
        };
        let pk = PlaceKey::from_mir_place(place);
        if let Some((lhs_pk, rhs_pk)) = self.binary_op_sources.get(&pk).cloned() {
            self.mark_guard_pointer(&lhs_pk, &rhs_pk);
        }
    }

    fn mark_guard_pointer(&mut self, lhs: &Option<PlaceKey>, rhs: &Option<PlaceKey>) {
        for ptr_pk in [lhs, rhs] {
            if let Some(pk) = ptr_pk {
                if let Some(local) = pk.local() {
                    if let Some(mut val) = self.locals.get(&local).cloned() {
                        val.invariants.non_null = true;
                        self.set_local(local, val);
                    }
                }
            }
        }
    }

    /// Check if a MIR place's type alignment is statically known.
    fn check_place_alignment(&self, place: &Place<'tcx>) -> bool {
        let ty = place.ty(self.body, self.tcx).ty;
        self.align_of_ty(ty) > 0
    }

    /// Assert a contract fact as VM state invariants.
    fn assert_contract_fact(&mut self, property: &Property<'tcx>) {
        let kind = &property.kind;
        match kind {
            PropertyKind::NonNull => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_non_null_for_value(property, val);
                }
            }
            PropertyKind::Align => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_align_for_value(property, val);
                }
            }
            PropertyKind::Init => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_init_for_value(property, val);
                }
            }
            PropertyKind::Owning => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_owning_for_value(val);
                }
            }
            PropertyKind::Alive => {
                if let Some(val) = self.contract_target_value(property) {
                    if let Some(id) = val.provenance_alloc_id() {
                        self.alive_assumed.insert(id);
                    }
                }
            }
            PropertyKind::ValidPtr => {
                // ValidPtr is composed of Allocated+InBound+Init+Align.
                if let Some(val) = self.contract_target_value(property) {
                    self.set_init_for_value(property, val.clone());
                    self.set_in_bounds_for_value(property, val.clone());
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        self.dead_allocations.remove(&alloc_id);
                    }
                    // The alignment from the contract type
                    if let Some(ty) = property.args.get(1).and_then(|a| {
                        if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None }
                    }) {
                        let mut v = val;
                        v.invariants.aligned = true;
                        let align = self.align_of_ty(ty);
                        if align > 1 {
                            v.invariants.align_n = Some(align);
                        }
                        if let Some(l) = self.contract_target_local(property) {
                            self.set_local(l, v);
                        }
                    }
                }
            }
            PropertyKind::InBound => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_in_bounds_for_value(property, val);
                }
                if let Some(ref fe_place) = property.for_each {
                    self.assert_in_bound_for_each(property, fe_place);
                    self.has_checked_bounds = true;
                }
            }
            PropertyKind::Allocated => {
                if let Some(local) = self.contract_target_local(property) {
                    if let Some(val) = self.locals.get(&local).cloned() {
                        if let Some(alloc_id) = val.provenance_alloc_id() {
                            self.dead_allocations.remove(&alloc_id);
                        }
                        // For raw-pointer parameters with Allocated contracts,
                        // create a proper external allocation matching the contract
                        // size (count * sizeof(T)). The stack allocation created by
                        // init_parameters is only sizeof(ptr) bytes — too small for
                        // pointer arithmetic like x.add(i).
                        let elem_ty = property.args.get(1)
                            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None });
                        let count_term = property.args.get(2).and_then(|a| self.resolve_contract_count(a));
                        if let (Some(elem_ty), Some(count_term)) = (elem_ty, count_term) {
                            let elem_sz_raw = self.size_of_ty(elem_ty);
                            let heap_align = self.align_of_ty(elem_ty).max(1);
                            let (heap_id, heap_base) = if elem_sz_raw == 0 {
                                // Generic type param: size unknown. Use a large external
                                // alloc so bounds checks auto-pass.
                                let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                self.allocate_external(max_size, heap_align, Some(elem_ty))
                            } else {
                                let elem_sz = Int::from_u64(self.ctx, elem_sz_raw as u64);
                                let total = Int::mul(self.ctx, &[&count_term, &elem_sz]);
                                self.allocate_external(total, heap_align, Some(elem_ty))
                            };
                            self.init_allocations.insert(heap_id);
                            let v = VmValue {
                                term: heap_base,
                                ty: val.ty,
                                provenance: Some(Provenance {
                                    alloc_id: heap_id,
                                    offset: Int::from_u64(self.ctx, 0),
                                }),
                                invariants: ValueInvariants {
                                    non_null: true,
                                    init: true,
                                    in_bounds: true,
                                    aligned: true,
                                    align_n: if heap_align > 1 { Some(heap_align) } else { None },
                                },
                            };
                            self.set_local(local, v);
                        }
                    }
                }
            }
            PropertyKind::Typed => {
                if let Some(val) = self.contract_target_value(property) {
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        if let Some(expected_ty) = property.args.get(1)
                            .and_then(|a| if let PropertyArg::Ty(ty) = a { Some(*ty) } else { None })
                        {
                            if let Some(alloc) = self.allocations.iter_mut().find(|a| a.id == alloc_id) {
                                alloc.element_ty = Some(expected_ty);
                            }
                        }
                    }
                }
            }
            PropertyKind::SplitTransmute => {
                self.split_transmute_asserted = true;
            }
            PropertyKind::ValidNum => {
                if let Some(PropertyArg::Predicates(predicates)) = property.args.first() {
                    for pred in predicates {
                        if let Some(condition) = self.eval_predicate_as_bool(pred) {
                            self.path_conditions.push(condition);
                        }
                    }
                }
            }
            _ => {
                self.notes.push(format!(
                    "contract fact {:?} not directly asserted",
                    kind
                ));
            }
        }
    }

    /// Get the local referenced by a contract property's target.
    fn contract_target_local(&self, property: &Property<'tcx>) -> Option<Local> {
        let cp = match property.args.first()? {
            PropertyArg::Place(cp) => cp,
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp,
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => cp,
                    _ => return None,
                }
            }
            _ => return None,
        };
        match cp.base {
            PlaceBase::Local(n) => Some(Local::from_usize(n)),
            PlaceBase::Arg(n) => {
                Some(Local::from_usize(n + 1))
            }
            PlaceBase::Return => Some(Local::from_usize(0)),
        }
    }

    /// Get the VmValue for a contract property's target.
    fn contract_target_value(&mut self, property: &Property<'tcx>) -> Option<VmValue<'ctx, 'tcx>> {
        let local = self.contract_target_local(property)?;
        self.locals.get(&local).cloned()
    }

    /// Resolve a contract count argument to a Z3 term by looking up
    /// the corresponding function parameter in the VM state.
    fn resolve_contract_count(&self, arg: &PropertyArg<'tcx>) -> Option<Int<'ctx>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) => {
                Some(Int::from_u64(self.ctx, *n as u64))
            }
            PropertyArg::Expr(ContractExpr::Place(cp)) | PropertyArg::Place(cp) => {
                let local = match cp.base {
                    PlaceBase::Local(n) => Local::from_usize(n),
                    PlaceBase::Arg(n) => Local::from_usize(n + 1),
                    PlaceBase::Return => return None,
                };
                self.locals.get(&local).map(|v| v.term.clone())
            }
            _ => None,
        }
    }

    /// Evaluate a numeric predicate to a Z3 Bool for path-condition assertion.
    fn eval_predicate_as_bool(&self, pred: &crate::verify::contract::NumericPredicate<'tcx>) -> Option<Bool<'ctx>> {
        use crate::verify::contract::{ContractExpr, RelOp};
        let ContractExpr::Const(rhs_val) = &pred.rhs else { return None };
        let lhs = self.eval_contract_expr_simple(&pred.lhs)?;
        let rhs = Int::from_u64(self.ctx, *rhs_val as u64);
        Some(match pred.op {
            RelOp::Le => lhs.le(&rhs),
            RelOp::Lt => lhs.lt(&rhs),
            RelOp::Ge => lhs.ge(&rhs),
            RelOp::Gt => lhs.gt(&rhs),
            _ => return None,
        })
    }

    fn eval_contract_expr_simple(&self, expr: &crate::verify::contract::ContractExpr<'tcx>) -> Option<Int<'ctx>> {
        use crate::verify::contract::{ContractExpr, NumericOp, PlaceBase};
        match expr {
            ContractExpr::SizeOf(ty) => {
                let size = self.size_of_ty(*ty).max(1);
                Some(Int::from_u64(self.ctx, size as u64))
            }
            ContractExpr::Place(cp) => {
                match cp.base {
                    PlaceBase::Local(n) => {
                        self.local_value(Local::from_usize(n)).map(|v| v.term.clone())
                    }
                    _ => None,
                }
            }
            ContractExpr::Binary { op: NumericOp::Mul, lhs, rhs } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(Int::mul(self.ctx, &[&l, &r]))
            }
            ContractExpr::Const(n) => Some(Int::from_u64(self.ctx, *n as u64)),
            _ => None,
        }
    }

    /// Set non_null invariant on the target value.
    fn set_non_null_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'ctx, 'tcx>) {
        val.invariants.non_null = true;
        if let Some(local) = self.contract_target_local(property) {
            self.set_local(local, val);
        }
    }

    fn set_in_bounds_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'ctx, 'tcx>) {
        val.invariants.in_bounds = true;
        if let Some(local) = self.contract_target_local(property) {
            self.set_local(local, val);
        }
    }

    fn assert_in_bound_for_each(&mut self, property: &Property<'tcx>, fe_place: &crate::verify::contract::ContractPlace<'tcx>) {
        let fe_local = match fe_place.base {
            PlaceBase::Arg(n) => Local::from_usize(n + 1),
            PlaceBase::Local(n) => Local::from_usize(n),
            _ => return,
        };
        let fe_val = match self.locals.get(&fe_local).cloned() {
            Some(v) => v,
            None => return,
        };
        let fe_alloc_id = match fe_val.provenance_alloc_id() {
            Some(id) => id,
            None => return,
        };
        let byte_vals: Vec<(usize, Int<'ctx>)> = self
            .alloc_byte_values(fe_alloc_id)
            .into_iter()
            .map(|(off, term)| (off, term.clone()))
            .collect();
        if byte_vals.is_empty() {
            return;
        }
        let slice_local = match property.args.first() {
            Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. })) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => match cp.base {
                        PlaceBase::Arg(n) => Some(Local::from_usize(n + 1)),
                        PlaceBase::Local(n) => Some(Local::from_usize(n)),
                        _ => None,
                    },
                    _ => None,
                }
            }
            Some(PropertyArg::Place(cp)) => match cp.base {
                PlaceBase::Arg(n) => Some(Local::from_usize(n + 1)),
                PlaceBase::Local(n) => Some(Local::from_usize(n)),
                _ => None,
            },
            _ => None,
        };
        let data_size = slice_local
            .and_then(|loc| self.locals.get(&loc))
            .and_then(|sl_val| sl_val.provenance_alloc_id())
            .and_then(|da_id| self.allocations.iter().find(|a| a.id == da_id))
            .map(|da| da.size.clone());
        let elem_sz = slice_local
            .and_then(|loc| self.locals.get(&loc))
            .and_then(|sl_val| sl_val.provenance_alloc_id())
            .and_then(|da_id| self.allocations.iter().find(|a| a.id == da_id))
            .and_then(|da| da.element_ty)
            .map(|ty| self.size_of_ty(ty) as u64)
            .unwrap_or(1)
            .max(1);
        let Some(data_size) = data_size else { return };
        let elem_sz_term = Int::from_u64(self.ctx, elem_sz);
        let len = data_size.div(&elem_sz_term);
        let zero = Int::from_u64(self.ctx, 0);
        for (_, term) in &byte_vals {
            self.path_conditions.push(term.ge(&zero));
            self.path_conditions.push(term.lt(&len));
        }
    }

    /// Set align invariant on the target value.
    fn set_align_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'ctx, 'tcx>) {
        val.invariants.aligned = true;
        if let Some(PropertyArg::Ty(ty)) = property.args.get(1) {
            let align = self.align_of_ty(*ty);
            if align > 1 {
                val.invariants.align_n = Some(align);
            }
        }
        if let Some(local) = self.contract_target_local(property) {
            self.set_local(local, val);
        }
    }

    /// Set init invariant on the target value and its allocation.
    fn set_init_for_value(&mut self, property: &Property<'tcx>, val: VmValue<'ctx, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.init_allocations.insert(prov.alloc_id);
        }
        if let Some(local) = self.contract_target_local(property) {
            if let Some(mut existing) = self.locals.get(&local).cloned() {
                existing.invariants.init = true;
                if let Some(prov) = &existing.provenance {
                    self.init_allocations.insert(prov.alloc_id);
                }
                self.set_local(local, existing);
            }
        }
    }

    /// Set owning invariant on the target value.
    fn set_owning_for_value(&mut self, val: VmValue<'ctx, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.init_allocations.insert(prov.alloc_id);
        }
    }

    /// Extract the pointee type if `ty` is `NonNull<P>` or wrapped in
    /// `Option<NonNull<P>>`. Returns `Some(P)`.
    fn find_nn_pointee(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use rustc_middle::ty::TyKind;
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                let def_path = self.tcx.def_path_str(adt_def.did());
                let is_nn = def_path.ends_with("::NonNull") || def_path == "NonNull"
                    || def_path.contains("::NonNull");
                if is_nn {
                    substs.first().and_then(|s| s.as_type())
                } else if def_path.ends_with("::Option") || def_path == "Option"
                    || def_path.contains("::Option")
                {
                    if let Some(inner) = substs.first().and_then(|s| s.as_type()) {
                        match inner.kind() {
                            TyKind::Adt(ia, is_) => {
                                let ip = self.tcx.def_path_str(ia.did());
                                let is_nn_inner = ip.ends_with("::NonNull") || ip == "NonNull"
                                    || ip.contains("::NonNull");
                                if is_nn_inner {
                                    is_.first().and_then(|s| s.as_type())
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Check whether a type is a `u8` array (`[u8; N]`) or `u8` slice (`[u8]`).
    fn is_u8_array_or_slice(&self, ty: Ty<'tcx>) -> bool {
        match ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _) => {
                matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8))
            }
            rustc_middle::ty::TyKind::Slice(elem_ty) => {
                matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8))
            }
            _ => false,
        }
    }

    /// Try to propagate provenance from pointer-extracting calls
    /// (e.g. as_ptr, as_mut_ptr). Returns true if applied.
    /// Try to propagate provenance from pointer-extracting calls
    /// (e.g. as_ptr, as_mut_ptr). Returns true if applied.
    fn try_as_ptr_fallback(
        &mut self,
        dest: Local,
        func: &Operand<'tcx>,
        first_arg_val: VmValue<'ctx, 'tcx>,
        first_arg_op: &Operand<'tcx>,
    ) -> bool {
        let name = crate::helpers::mir_utils::call_name(self.tcx, func);
        if !crate::verify::call_summary::fn_simulator::is_as_ptr(&name)
            && !name.contains("::as_ptr")
        {
            return false;
        }
        let dest_ty = self.body.local_decls[dest].ty;
        let prov = first_arg_val.provenance.clone().or_else(|| {
            if let Operand::Move(place) | Operand::Copy(place) = first_arg_op {
                self.local_alloc_ids.get(&place.local).map(|&id| {
                    Provenance { alloc_id: id, offset: Int::from_u64(self.ctx, 0) }
                })
            } else {
                None
            }
        });
        if let Some(ref prov) = prov {
            self.init_allocations.insert(prov.alloc_id);
            self.set_local(dest, VmValue {
                term: first_arg_val.term.clone(),
                ty: dest_ty,
                provenance: Some(prov.clone()),
                invariants: ValueInvariants {
                    non_null: true, aligned: true, init: true,
                    in_bounds: first_arg_val.invariants.in_bounds,
                    align_n: first_arg_val.invariants.align_n,
                },
            });
            return true;
        }
        false
    }

    /// If `operand` is a constant reference to a byte array (e.g. `b"hello\0"`),
    /// extract the raw bytes and create a tracked allocation. Updates `val`
    /// in-place with the proper provenance and invariants.
    pub(crate) fn try_materialize_const_bytes(
        &mut self,
        val: &mut VmValue<'ctx, 'tcx>,
        operand: &Operand<'tcx>,
    ) {
        // Use the operand's type (before any pointer cast) to check for byte arrays.
        let operand_val = self.value_of_operand(operand);
        let op_ty = operand_val.ty;
        let (pointee_ty, _is_ref) = match op_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner_ty, _) => (*inner_ty, true),
            rustc_middle::ty::TyKind::RawPtr(inner_ty, _) => (*inner_ty, false),
            _ => {
                // Fallback: use val's type
                let val_ty = val.ty;
                match val_ty.kind() {
                    rustc_middle::ty::TyKind::Ref(_, inner_ty, _) => (*inner_ty, true),
                    rustc_middle::ty::TyKind::RawPtr(inner_ty, _) => (*inner_ty, false),
                    _ => return,
                }
            }
        };
        match pointee_ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _)
            | rustc_middle::ty::TyKind::Slice(elem_ty) => {
                let is_byte = match elem_ty.kind() {
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8) => true,
                    rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8) => true,
                    _ => false,
                };
                if is_byte {
                    let bytes_opt = super::state::extract_const_bytes_from_operand(self.tcx, operand)
                        .or_else(|| self.trace_to_const_bytes(operand));
                    if let Some(bytes) = bytes_opt {
                        let size = z3::ast::Int::from_u64(self.ctx, bytes.len() as u64);
                        let (alloc_id, base) = self.allocate(
                            size,
                            self.align_of_ty(pointee_ty),
                            Some(pointee_ty),
                        );
                        self.init_allocations.insert(alloc_id);
                        for (i, &b) in bytes.iter().enumerate() {
                            self.record_byte_value(alloc_id, i,
                                z3::ast::Int::from_u64(self.ctx, b as u64));
                            if b == 0 {
                                self.known_nul_offsets.insert((alloc_id, i));
                            } else {
                                self.known_non_nul_offsets.insert((alloc_id, i));
                            }
                        }
                        val.term = base;
                        val.provenance = Some(super::state::Provenance {
                            alloc_id,
                            offset: z3::ast::Int::from_u64(self.ctx, 0),
                        });
                        val.invariants = ValueInvariants {
                            non_null: true, init: true, aligned: true, in_bounds: false,
                            align_n: None,
                        };
                    }
                }
            }
            _ => {}
        }
    }

    pub(crate) fn trace_to_const_bytes(&self, operand: &Operand<'tcx>) -> Option<Vec<u8>> {
        let place = match operand {
            Operand::Copy(p) | Operand::Move(p) => p,
            _ => return None,
        };
        let base_local = if place.projection.len() == 1
            && matches!(place.projection.first().map(|p| p.kind()),
                Some(rustc_middle::mir::ProjectionElem::Deref))
        {
            place.local
        } else if place.projection.is_empty() {
            place.local
        } else {
            return None;
        };
        for block in self.body.basic_blocks.iter() {
            for stmt in &block.statements {
                if let StatementKind::Assign(assign) = &stmt.kind {
                    let (dest, rvalue) = &**assign;
                    if dest.local != base_local || !dest.projection.is_empty() {
                        continue;
                    }
                    match rvalue {
                        #[cfg(rapx_rvalue_use_with_retag)]
                        Rvalue::Use(op, _) => {
                            return super::state::extract_const_bytes_from_operand(self.tcx, op)
                                .or_else(|| self.trace_to_const_bytes(op));
                        }
                        #[cfg(not(rapx_rvalue_use_with_retag))]
                        Rvalue::Use(op) => {
                            return super::state::extract_const_bytes_from_operand(self.tcx, op)
                                .or_else(|| self.trace_to_const_bytes(op));
                        }
                        Rvalue::Ref(_, _, p) => {
                            let op = Operand::Copy(*p);
                            return self.trace_to_const_bytes(&op);
                        }
                        _ => return None,
                    }
                }
            }
        }
        None
    }

    /// Propagate byte values from a source place's allocation to the
    /// provenance allocation of a reference. This ensures that when we
    /// create `&bytes` from an aggregate, the byte-level tracking follows.
    fn propagate_byte_values_to_ref(
        &mut self,
        source_place: &Place<'tcx>,
        ref_val: &VmValue<'ctx, 'tcx>,
    ) {
        let Some(src_alloc_id) = self.local_alloc_ids.get(&source_place.local).copied() else {
            return;
        };
        let Some(ref_alloc_id) = ref_val.provenance_alloc_id() else {
            return;
        };
        if src_alloc_id == ref_alloc_id {
            return; // same allocation, bytes already there
        }
        // Copy byte values from source alloc to ref's alloc
        let byte_pairs: Vec<_> = self.byte_values.iter()
            .filter(|((aid, _), _)| *aid == src_alloc_id)
            .map(|((_, off), term)| (*off, term.clone()))
            .collect();
        for (off, term) in byte_pairs {
            self.record_byte_value(ref_alloc_id, off, term);
        }
        // Also copy known_nul / known_non_nul
        let nul_offsets: Vec<_> = self.known_nul_offsets.iter()
            .filter(|(aid, _)| *aid == src_alloc_id)
            .map(|(_, off)| *off)
            .collect();
        for off in nul_offsets {
            self.known_nul_offsets.insert((ref_alloc_id, off));
        }
        let non_nul_offsets: Vec<_> = self.known_non_nul_offsets.iter()
            .filter(|(aid, _)| *aid == src_alloc_id)
            .map(|(_, off)| *off)
            .collect();
        for off in non_nul_offsets {
            self.known_non_nul_offsets.insert((ref_alloc_id, off));
        }
    }

    /// Return the per-field types for an aggregate's operands.
    fn aggregate_field_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _len) => {
                // We don't need the exact count — just the element type for size
                vec![*elem_ty]
            }
            rustc_middle::ty::TyKind::Tuple(elems) => {
                elems.iter().collect()
            }
            rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                if adt_def.is_enum() { return vec![]; }
                let variant = adt_def.non_enum_variant();
                variant.fields.iter()
                    .map(|f| {
                        let unnorm = f.ty(self.tcx, substs);
                        unnorm.skip_norm_wip()
                    })
                    .collect()
            }
            _ => vec![],
        }
    }
}

/// Return the next MIR block after `block` in a finite verification path.
fn chosen_successor(path: &Path, block: BasicBlock, occurrence: usize) -> Option<BasicBlock> {
    let mut count = 0;
    let mut previous = None;
    for step in path.steps.iter() {
        match step {
            PathStep::Block(current) => {
                if previous == Some(block) {
                    count += 1;
                    if count == occurrence {
                        return Some(*current);
                    }
                }
                previous = Some(*current);
            }
            PathStep::Checkpoint(_) => return None,
        }
    }
    None
}

/// Convert an operand to a PlaceKey (if it's a place operand).
fn operand_to_place_key(operand: &Operand<'_>) -> Option<PlaceKey> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(PlaceKey::from_mir_place(place)),
        _ => None,
    }
}

/// Try to resolve a u64 constant from a PlaceKey's source in the VM state.
fn resolve_u64_from_place_key<'ctx, 'tcx>(
    pk: &Option<PlaceKey>,
    state: &VmState<'ctx, 'tcx>,
) -> Option<u64> {
    let pk = pk.as_ref()?;
    let local = pk.local()?;
    let val = state.local_value(local)?;
    val.term.as_u64()
}

/// Extract the bare local from a Copy/Move operand.
fn extract_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() => Some(place.local),
        _ => None,
    }
}

/// Extract a constant u64 value from an operand, if it's a known constant.
fn extract_operand_const(operand: &Operand<'_>) -> Option<u64> {
    match operand {
        Operand::Constant(constant) => {
            let text = format!("{:?}", constant.const_);
            super::state::const_int_from_debug(&text)
        }
        _ => None,
    }
}
