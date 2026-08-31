//! MIR statement and terminator executors for the symbolic VM.
//!
//! Each executor is a transfer function that updates `VmState` based on
//! the semantics of a MIR construct. The VM walks retained MIR items
//! in forward path order, calling these executors.

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Local, Operand, Place, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind, UnOp,
    },
    ty::Ty,
};
use z3::ast::{Ast, Bool, Int};

use crate::{
    compat::{FxHashMap, FxHashSet},
    verify::{
        contract::{ContractExpr, ContractKind, PlaceBase, Property, PropertyArg, PropertyKind},
        def_use::PlaceKey,
        path_extractor::{Path, PathStep},
        slicer::RelevantItem,
    },
};

use super::state::{AllocId, InlineFrame, Provenance, ValueInvariants, VmState, VmValue};

use crate::verify::api_classify;

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Execute all retained MIR items in path order.
    pub(crate) fn execute_items(&mut self, items: &[RelevantItem<'tcx>]) {
        // Initialize function parameters as fresh symbolic values.
        // Parameters are _1.._N (excluding _0 return value).
        self.init_parameters();

        for item in items {
            match item {
                RelevantItem::Statement {
                    def_id,
                    block,
                    statement_index,
                } => {
                    let body = self.tcx.optimized_mir(*def_id);
                    let statement = &body.basic_blocks[*block].statements[*statement_index];
                    let saved = self.body;
                    self.body = body;
                    self.exec_statement(*block, *statement_index, statement);
                    self.body = saved;
                }
                RelevantItem::Terminator { def_id, block } => {
                    let body = self.tcx.optimized_mir(*def_id);
                    let occ = self
                        .block_occurrences
                        .get(block)
                        .map(|c| c + 1)
                        .unwrap_or(1);
                    self.block_occurrences.insert(*block, occ);
                    let terminator = body.basic_blocks[*block].terminator();
                    let saved = self.body;
                    self.body = body;
                    self.exec_terminator(*block, terminator, occ);
                    self.body = saved;
                }
                RelevantItem::CalleeEntry { callee, args } => {
                    self.handle_callee_entry(*callee, args);
                }
                RelevantItem::CalleeExit { dest } => {
                    self.handle_callee_exit(*dest);
                }
                RelevantItem::ContractFact { property } => {
                    self.assert_contract_fact(property);
                }
                RelevantItem::Forget => {
                    self.notes.push("forget: unsupported call".to_string());
                }
            }
        }
    }

    /// Enter an inlined callee during path execution: save the caller context,
    /// switch to the callee body, and bind the caller's argument locals to the
    /// callee's parameters.
    fn handle_callee_entry(&mut self, callee: DefId, arg_locals: &[usize]) {
        let saved_body = self.body;
        let saved_def_id = self.caller_def_id;
        let saved_locals = std::mem::take(&mut self.locals);
        let saved_field_values = std::mem::take(&mut self.field_values);

        // Collect the caller argument fields from the saved map, so the callee's
        // parameters inherit them (e.g. NonZero's non-zero inner value).
        let mut arg_fields: Vec<(usize, Vec<usize>, VmValue<'ctx, 'tcx>)> = Vec::new();
        for (i, arg) in arg_locals.iter().enumerate() {
            let caller_local = Local::from_usize(*arg);
            let keys: Vec<Vec<usize>> = saved_field_values
                .keys()
                .filter(|(l, _)| *l == caller_local)
                .map(|(_, f)| f.clone())
                .collect();
            for fields in keys {
                if let Some(fv) = saved_field_values
                    .get(&(caller_local, fields.clone()))
                    .cloned()
                {
                    arg_fields.push((i + 1, fields, fv));
                }
            }
        }

        self.body = self.tcx.optimized_mir(callee);
        self.caller_def_id = callee;

        for (i, arg) in arg_locals.iter().enumerate() {
            if let Some(v) = saved_locals.get(&Local::from_usize(*arg)).cloned() {
                self.set_local(Local::from_usize(i + 1), v);
            }
        }
        for (callee_param, fields, fv) in arg_fields {
            self.set_field_value(Local::from_usize(callee_param), fields, fv);
        }

        self.inline_frames.push(InlineFrame {
            body: saved_body,
            def_id: saved_def_id,
            saved_locals,
            saved_field_values,
        });
    }

    /// Exit an inlined callee: capture the callee's return value, restore the
    /// caller context, and write the return value to the caller's destination.
    fn handle_callee_exit(&mut self, dest: usize) {
        let ret = self.locals.get(&Local::from_usize(0)).cloned();
        let ret_fields: Vec<(Vec<usize>, VmValue<'ctx, 'tcx>)> = self
            .field_values
            .iter()
            .filter(|((l, _), _)| *l == Local::from_usize(0))
            .map(|((_, f), v)| (f.clone(), v.clone()))
            .collect();
        if let Some(frame) = self.inline_frames.pop() {
            self.body = frame.body;
            self.caller_def_id = frame.def_id;
            self.locals = frame.saved_locals;
            self.field_values = frame.saved_field_values;
        }
        if let Some(mut v) = ret {
            let dest_ty = self.body.local_decls[Local::from_usize(dest)].ty;
            v.ty = dest_ty;
            // Infer invariants: a non-null provenance with offset 0 means the
            // return value is valid and initialized.
            if let Some(ref prov) = v.provenance {
                if prov.offset.as_u64() == Some(0) {
                    v.invariants.non_null = true;
                    v.invariants.init = true;
                    v.invariants.aligned = true;
                    self.alloc_mut(prov.alloc_id).initialized = true;
                }
            }
            self.set_local(Local::from_usize(dest), v);
            // The callee returned a fully-constructed value, so the caller's
            // destination stack slot is initialized.
            if let Some(dest_alloc_id) = self.local_alloc_ids.get(&Local::from_usize(dest)).copied()
            {
                self.alloc_mut(dest_alloc_id).initialized = true;
            }
        }
        for (fields, fv) in ret_fields {
            self.set_field_value(Local::from_usize(dest), fields, fv);
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
                    let is_vec = api_classify::is_std_vec(adt_def.did());
                    if api_classify::is_std_box(adt_def.did())
                        || is_vec
                        || api_classify::is_std_cstring(adt_def.did())
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
                            let (id, base) =
                                self.allocate_external(max_size, heap_align, Some(heap_ty));
                            (id, base)
                        } else {
                            self.allocate(heap_size_term, heap_align, Some(heap_ty))
                        };
                        invariants.non_null = true;
                        invariants.init = true;
                        invariants.aligned = true;
                        self.alloc_mut(heap_alloc_id).initialized = true;
                        // Also expose the box's inner `Unique<T>.pointer` field
                        // (a `NonNull<T>` at path [0, 0]) so that inlined bodies
                        // like `Box::into_non_null_with_allocator` — which reads
                        // `(_1.0).0` and transmutes it to `NonNull<T>` — inherit
                        // the heap pointer's non-null/aligned/allocated facts.
                        self.set_field_value(
                            local,
                            vec![0, 0],
                            VmValue {
                                term: heap_base.clone(),
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: heap_alloc_id,
                                    offset: Int::from_u64(self.ctx, 0),
                                    is_field_offset: false,
                                }),
                                invariants: ValueInvariants {
                                    non_null: true,
                                    init: true,
                                    aligned: true,
                                    ..Default::default()
                                },
                            },
                        );
                        // For Vec: materialize `buf.cap` ([0, 1]) and `len`
                        // ([1]) as fresh symbolic fields with `0 <= len <= cap`,
                        // so `len()`/`capacity()` become plain field reads rather
                        // than recomputing `size / elem_size` from the external
                        // (unbounded) buffer allocation.
                        if is_vec {
                            let cap = self.fresh_int(&format!("vec_cap_{}", local_idx));
                            let len = self.fresh_int(&format!("vec_len_{}", local_idx));
                            let zero = Int::from_u64(self.ctx, 0);
                            self.path_conditions.push(len.ge(&zero));
                            self.path_conditions.push(len.le(&cap));
                            self.path_conditions.push(cap.ge(&zero));
                            // Language invariant: byte length fits in isize::MAX.
                            let isize_max = Int::from_u64(self.ctx, isize::MAX as u64);
                            let elem_term = Int::from_u64(self.ctx, heap_size.max(1));
                            self.path_conditions
                                .push(Int::mul(self.ctx, &[&cap, &elem_term]).le(&isize_max));
                            let usize_ty = self.tcx.types.usize;
                            self.set_field_value(local, vec![0, 1], VmValue::new(cap, usize_ty));
                            self.set_field_value(local, vec![1], VmValue::new(len, usize_ty));
                        }
                        self.set_local(
                            local,
                            VmValue {
                                term: heap_base,
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: heap_alloc_id,
                                    offset: Int::from_u64(self.ctx, 0),
                                    is_field_offset: false,
                                }),
                                invariants,
                            },
                        );
                        continue;
                    }
                }
                // ── Struct/tuple/enum parameter (non-Box/Vec ADT) ──
                // Decompose into per-field symbolic values for field-level checking.
                if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() {
                    if adt_def.is_enum() {
                        let term = self.fresh_int(&format!("param_{}", local_idx));
                        self.set_local(
                            local,
                            VmValue {
                                term,
                                ty,
                                provenance: None,
                                invariants,
                            },
                        );
                        continue;
                    }
                    let variant = adt_def.non_enum_variant();
                    let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'ctx>)> =
                        FxHashMap::default();
                    for (idx, field_def) in variant.fields.iter().enumerate() {
                        let field_ty: Ty<'tcx> =
                            crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
                        if let rustc_middle::ty::TyKind::RawPtr(inner, _) = field_ty.kind() {
                            self.init_ptr_field(
                                local,
                                vec![idx],
                                field_ty,
                                *inner,
                                local_idx,
                                idx,
                                &mut elem_alloc,
                                true,
                                "field_nn",
                            );
                        } else if let Some(pointee) = self.find_nn_pointee(field_ty) {
                            self.init_ptr_field(
                                local,
                                vec![idx],
                                field_ty,
                                pointee,
                                local_idx,
                                idx,
                                &mut elem_alloc,
                                false,
                                "field_nn",
                            );
                        } else if let rustc_middle::ty::TyKind::Adt(inner_adt, _) = field_ty.kind()
                        {
                            if !inner_adt.is_enum() {
                                self.decompose_adt_fields(
                                    local,
                                    vec![idx],
                                    field_ty,
                                    local_idx,
                                    &mut elem_alloc,
                                    1,
                                );
                            } else {
                                let field_term =
                                    self.fresh_int(&format!("field_{}_{}", local_idx, idx));
                                self.set_field_value(
                                    local,
                                    vec![idx],
                                    VmValue {
                                        term: field_term,
                                        ty: field_ty,
                                        provenance: None,
                                        invariants: ValueInvariants {
                                            init: true,
                                            ..Default::default()
                                        },
                                    },
                                );
                            }
                        } else {
                            let field_term =
                                self.fresh_int(&format!("field_{}_{}", local_idx, idx));
                            self.set_field_value(
                                local,
                                vec![idx],
                                VmValue {
                                    term: field_term,
                                    ty: field_ty,
                                    provenance: None,
                                    invariants: ValueInvariants {
                                        init: true,
                                        ..Default::default()
                                    },
                                },
                            );
                        }
                    }
                    // A single-raw-pointer wrapper (e.g. `NonNull<T>`) *is* its
                    // pointer, so carry the field's provenance onto the whole local —
                    // otherwise alias/ownership reasoning can't trace a deref of
                    // `self.pointer` back to "owned" (the local's provenance would
                    // be `None`).
                    if crate::helpers::mir_utils::is_raw_ptr_wrapper(self.tcx, adt_def.did()) {
                        if let Some(f0) = self.field_value(local, &vec![0]).cloned() {
                            let prov = f0.provenance.clone();
                            self.set_local(
                                local,
                                VmValue {
                                    term: f0.term,
                                    ty,
                                    provenance: prov,
                                    invariants: ValueInvariants {
                                        init: true,
                                        ..Default::default()
                                    },
                                },
                            );
                            continue;
                        }
                    }
                    let term = self.fresh_int(&format!("param_{}", local_idx));
                    self.set_local(
                        local,
                        VmValue {
                            term,
                            ty,
                            provenance: None,
                            invariants: ValueInvariants {
                                init: true,
                                ..Default::default()
                            },
                        },
                    );
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

                    let pointee_ty =
                        if let rustc_middle::ty::TyKind::Ref(_, inner_ty, _) = ty.kind() {
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
                            crate::helpers::mir_utils::size_of_generic_param(
                                self.tcx,
                                self.caller_def_id,
                                *elem_ty,
                            )
                            .max(1)
                        };
                        let elem_sz_term = Int::from_u64(self.ctx, elem_sz);
                        self.path_conditions
                            .push(Int::mul(self.ctx, &[&len, &elem_sz_term]).le(&isize_max));
                        let data_size = Int::mul(
                            self.ctx,
                            &[&len, &Int::from_u64(self.ctx, elem_size.max(1))],
                        );
                        let (data_alloc_id, data_base) =
                            self.allocate(data_size, self.align_of_ty(*elem_ty), Some(*elem_ty));
                        if let Some(ref_alloc_id) = self.alloc_for_local(local) {
                            self.alloc_mut(ref_alloc_id).slice_data = Some(data_alloc_id);
                        }
                        self.alloc_mut(data_alloc_id).initialized = true;
                        self.set_local(
                            local,
                            VmValue {
                                term: data_base,
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: data_alloc_id,
                                    offset: Int::from_u64(self.ctx, 0),
                                    is_field_offset: false,
                                }),
                                invariants,
                            },
                        );
                        continue;
                    }

                    // Non-slice reference: allocate pointee
                    let pointee_size = self.size_of_ty(pointee_ty) as u64;
                    let pointee_align = self.align_of_ty(pointee_ty);
                    let pointee_size_term = Int::from_u64(self.ctx, pointee_size.max(1));
                    let (pointee_alloc_id, pointee_base) =
                        self.allocate(pointee_size_term, pointee_align, Some(pointee_ty));
                    self.alloc_mut(pointee_alloc_id).initialized = true;
                    self.set_local(
                        local,
                        VmValue {
                            term: pointee_base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id: pointee_alloc_id,
                                offset: Int::from_u64(self.ctx, 0),
                                is_field_offset: false,
                            }),
                            invariants,
                        },
                    );

                    // Decompose struct fields for pointer-field access.
                    // E.g. &RawBuf → (*self).ptr should yield a valid raw ptr.
                    if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = pointee_ty.kind() {
                        if !adt_def.is_enum() {
                            let variant = adt_def.non_enum_variant();
                            // Track the first data allocation per element type.
                            // Subsequent RawPtr / NonNull fields with the same
                            // pointee type reuse the allocation with per-field
                            // symbolic offsets, preserving the field relationships
                            // (e.g. ptr=start, end_or_len=start+len).
                            let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'ctx>)> =
                                FxHashMap::default();
                            for (idx, field_def) in variant.fields.iter().enumerate() {
                                let field_ty: Ty<'tcx> = crate::helpers::mir_utils::field_ty(
                                    self.tcx, field_def, substs,
                                );
                                if let rustc_middle::ty::TyKind::RawPtr(inner, _) = field_ty.kind()
                                {
                                    self.init_ptr_field(
                                        local,
                                        vec![idx],
                                        field_ty,
                                        *inner,
                                        local_idx,
                                        idx,
                                        &mut elem_alloc,
                                        true,
                                        "field_nn",
                                    );
                                } else if let Some(pointee) = self.find_nn_pointee(field_ty) {
                                    // Field contains NonNull<T> (possibly wrapped in Option):
                                    // create/reuse an external allocation for the pointee.
                                    self.init_ptr_field(
                                        local,
                                        vec![idx],
                                        field_ty,
                                        pointee,
                                        local_idx,
                                        idx,
                                        &mut elem_alloc,
                                        false,
                                        "ref_field",
                                    );
                                } else if let rustc_middle::ty::TyKind::Ref(_, pointee, _) =
                                    field_ty.kind()
                                {
                                    // Field contains a reference (&T, &mut T, &[T], etc.).
                                    // Give it provenance so that as_ptr() / as_mut_ptr()
                                    // on the field propagates the allocation info.
                                    if let rustc_middle::ty::TyKind::Slice(elem_ty) = pointee.kind()
                                    {
                                        let elem_align = 1u64.max(self.align_of_ty(*elem_ty));
                                        let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                        let (data_alloc_id, data_base) = self.allocate_external(
                                            max_size,
                                            elem_align,
                                            Some(*elem_ty),
                                        );
                                        self.alloc_mut(data_alloc_id).initialized = true;
                                        self.alloc_mut(data_alloc_id).alive_assumed = true;
                                        self.set_field_value(
                                            local,
                                            vec![idx],
                                            VmValue {
                                                term: data_base,
                                                ty: field_ty,
                                                provenance: Some(Provenance {
                                                    alloc_id: data_alloc_id,
                                                    offset: Int::from_u64(self.ctx, 0),
                                                    is_field_offset: false,
                                                }),
                                                invariants: ValueInvariants {
                                                    non_null: true,
                                                    init: true,
                                                    ..Default::default()
                                                },
                                            },
                                        );
                                    } else {
                                        let pointee_align = 1u64.max(self.align_of_ty(*pointee));
                                        let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
                                        let (field_alloc_id, field_base) = self.allocate_external(
                                            max_size,
                                            pointee_align,
                                            Some(*pointee),
                                        );
                                        self.alloc_mut(field_alloc_id).initialized = true;
                                        self.alloc_mut(field_alloc_id).alive_assumed = true;
                                        self.set_field_value(
                                            local,
                                            vec![idx],
                                            VmValue {
                                                term: field_base,
                                                ty: field_ty,
                                                provenance: Some(Provenance {
                                                    alloc_id: field_alloc_id,
                                                    offset: Int::from_u64(self.ctx, 0),
                                                    is_field_offset: false,
                                                }),
                                                invariants: ValueInvariants {
                                                    non_null: true,
                                                    init: true,
                                                    ..Default::default()
                                                },
                                            },
                                        );
                                    }
                                } else if matches!(
                                    field_ty.kind(),
                                    rustc_middle::ty::TyKind::Uint(_)
                                        | rustc_middle::ty::TyKind::Int(_)
                                        | rustc_middle::ty::TyKind::Float(_)
                                        | rustc_middle::ty::TyKind::Bool
                                        | rustc_middle::ty::TyKind::Char
                                ) {
                                    // Scalar field (e.g. `size: usize`) inside a
                                    // referenced struct. Materialize a fresh
                                    // symbolic value so that field reads return
                                    // the correct term instead of the whole
                                    // struct term. Non-scalar, non-pointer ADT
                                    // fields (Box/Vec/etc.) are left unset so
                                    // they keep their pre-existing heap modeling.
                                    let field_term =
                                        self.fresh_int(&format!("ref_field_{}_{}", local_idx, idx));
                                    self.set_field_value(
                                        local,
                                        vec![idx],
                                        VmValue {
                                            term: field_term,
                                            ty: field_ty,
                                            provenance: None,
                                            invariants: ValueInvariants {
                                                init: true,
                                                ..Default::default()
                                            },
                                        },
                                    );
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
                    self.set_local(
                        local,
                        VmValue {
                            term: val,
                            ty,
                            provenance: None,
                            invariants,
                        },
                    );
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
                    let (alloc_id, base) =
                        self.allocate_external(max_size, pointee_align, Some(*pointee));
                    self.set_local(
                        local,
                        VmValue {
                            term: base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.ctx, 0),
                                is_field_offset: false,
                            }),
                            invariants,
                        },
                    );
                    continue;
                }
                // ── Array parameter ([usize; N], etc.) ──
                // Give every array parameter a real allocation with provenance so
                // that downstream call effects (e.g. ChecksIndexBoundsDisjoint)
                // can record the alloc_id and property checker can match it later.
                if let rustc_middle::ty::TyKind::Array(elem_ty, const_len) = ty.kind() {
                    let n: Option<usize> =
                        const_len.try_to_target_usize(self.tcx).map(|v| v as usize);
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
                    self.alloc_mut(alloc_id).initialized = true;
                    self.local_alloc_ids.insert(local, alloc_id);
                    if let Some(n) = n {
                        for i in 0..n {
                            let off = i * step;
                            let elem_term =
                                self.fresh_int(&format!("array_{}_idx_{}", local_idx, i));
                            self.record_byte_value(alloc_id, off, elem_term);
                        }
                    } else {
                        // Generic N: create placeholder byte tracking so that
                        // downstream Index projection ITE chains and
                        // assert_in_bound_for_each can add constraints.
                        let m = 16usize;
                        for i in 0..m {
                            let off = i * step;
                            let elem_term =
                                self.fresh_int(&format!("array_{}_idx_{}", local_idx, i));
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
                                is_field_offset: false,
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
                self.set_local(
                    local,
                    VmValue {
                        term,
                        ty,
                        provenance: None,
                        invariants,
                    },
                );
                continue;
            }
            // ── Non-parameter local: fallback value (overwritten by actual
            // assignments). For reference/raw-pointer locals the value *is* the
            // stack address; for scalar locals use a fresh symbolic value so a
            // stale stack address never leaks into scalar arithmetic (e.g. the
            // `offset <= len` bound check in memchr-style loops).
            let term = match ty.kind() {
                rustc_middle::ty::TyKind::Ref(..) | rustc_middle::ty::TyKind::RawPtr(..) => {
                    self.local_address(local)
                }
                _ => self.fresh_int(&format!("local_{}", local_idx)),
            };
            self.set_local(
                local,
                VmValue {
                    term,
                    ty,
                    provenance: None,
                    invariants,
                },
            );
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
                    }
                    .and_then(|operand| match operand {
                        Operand::Copy(place) | Operand::Move(place)
                            if place.projection.is_empty() =>
                        {
                            Some(place.local)
                        }
                        _ => None,
                    });
                    if let Some(src_local) = src {
                        if let Some(src_val) = self.locals.get(&src_local) {
                            let has_better_prov = src_val.provenance.is_some()
                                && src_val.invariants.non_null
                                && self.locals.get(&dest_local).map_or(true, |d| {
                                    d.provenance.is_none() || !d.invariants.non_null
                                });
                            if has_better_prov {
                                self.set_local(
                                    dest_local,
                                    VmValue {
                                        term: src_val.term.clone(),
                                        ty: dest.ty(self.body, self.tcx).ty,
                                        provenance: src_val.provenance.clone(),
                                        invariants: src_val.invariants,
                                    },
                                );
                            }
                        }
                    }
                }
            }
        }
    }

    /// Initialize one pointer-like field (raw pointer or `NonNull<T>`) of a
    /// decomposed struct/ref parameter. The first field with a given pointee
    /// type creates a shared external allocation; later fields with the same
    /// pointee reuse it with a symbolic offset, preserving relationships like
    /// `ptr = start, end_or_len = start + len`.
    #[allow(clippy::too_many_arguments)]
    fn init_ptr_field(
        &mut self,
        local: Local,
        path: Vec<usize>,
        field_ty: Ty<'tcx>,
        pointee: Ty<'tcx>,
        local_idx: usize,
        idx: usize,
        elem_alloc: &mut FxHashMap<Ty<'tcx>, (AllocId, Int<'ctx>)>,
        is_raw_ptr: bool,
        nn_fresh_prefix: &str,
    ) {
        let invariants = if is_raw_ptr {
            ValueInvariants {
                non_null: true,
                init: true,
                ..Default::default()
            }
        } else {
            ValueInvariants {
                init: true,
                ..Default::default()
            }
        };
        if let Some(&(existing_alloc, ref base)) = elem_alloc.get(&pointee) {
            let elem_size = self.size_of_ty(pointee).max(1) as u64;
            let len_term = self.fresh_int(&format!("field_len_{}_{}", local_idx, idx));
            self.path_conditions
                .push(len_term.ge(&Int::from_u64(self.ctx, 0)));
            let prost_offset =
                Int::mul(self.ctx, &[&len_term, &Int::from_u64(self.ctx, elem_size)]);
            let field_term = Int::add(self.ctx, &[base, &prost_offset]);
            self.set_field_value(
                local,
                path.clone(),
                VmValue {
                    term: field_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: existing_alloc,
                        offset: prost_offset.clone(),
                        is_field_offset: false,
                    }),
                    invariants,
                },
            );
        } else {
            let field_align = 1u64.max(self.align_of_ty(pointee));
            let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
            let (field_alloc_id, field_base) =
                self.allocate_external(max_size, field_align, Some(pointee));
            self.alloc_mut(field_alloc_id).initialized = true;
            elem_alloc.insert(pointee, (field_alloc_id, field_base.clone()));
            let field_term = if is_raw_ptr {
                field_base
            } else {
                self.fresh_int(&format!("{}_{}_{}", nn_fresh_prefix, local_idx, idx))
            };
            self.set_field_value(
                local,
                path.clone(),
                VmValue {
                    term: field_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: field_alloc_id,
                        offset: Int::from_u64(self.ctx, 0),
                        is_field_offset: false,
                    }),
                    invariants,
                },
            );
        }
    }

    /// Recursively decompose a (possibly nested) struct parameter into per-field
    /// symbolic values.  Nested ADT fields (e.g. `Handle { node: NodeRef { node:
    /// NonNull<LeafNode>, .. }, .. }`) are descended into so their `NonNull` /
    /// raw-pointer leaves get external-allocation provenance — otherwise a
    /// `NonNull` buried two levels deep loses its provenance and downstream
    /// `Allocated`/`Init` checks (e.g. `descend`'s `edges.get_unchecked`) fail.
    fn decompose_adt_fields(
        &mut self,
        local: Local,
        prefix: Vec<usize>,
        ty: Ty<'tcx>,
        local_idx: usize,
        elem_alloc: &mut FxHashMap<Ty<'tcx>, (AllocId, Int<'ctx>)>,
        depth: usize,
    ) {
        if depth > 4 {
            return;
        }
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return;
        };
        if adt_def.is_enum() {
            return;
        }
        let variant = adt_def.non_enum_variant();
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty: Ty<'tcx> =
                crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
            let mut path = prefix.clone();
            path.push(idx);
            if let rustc_middle::ty::TyKind::RawPtr(inner, _) = field_ty.kind() {
                self.init_ptr_field(
                    local, path, field_ty, *inner, local_idx, idx, elem_alloc, true, "field_nn",
                );
            } else if let Some(pointee) = self.find_nn_pointee(field_ty) {
                self.init_ptr_field(
                    local, path, field_ty, pointee, local_idx, idx, elem_alloc, false, "field_nn",
                );
            } else if matches!(field_ty.kind(), rustc_middle::ty::TyKind::Adt(_, _)) {
                self.decompose_adt_fields(local, path, field_ty, local_idx, elem_alloc, depth + 1);
            } else {
                let field_term = self.fresh_int(&format!("field_{}_{}", local_idx, idx));
                self.set_field_value(
                    local,
                    path.clone(),
                    VmValue {
                        term: field_term,
                        ty: field_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            init: true,
                            ..Default::default()
                        },
                    },
                );
            }
        }
    }

    /// Replay same-block assignment chains that the backward slicer may omit.
    /// Walks backwards through the CFG from the checkpoint block, propagating
    /// provenance and invariants through Use/Cast/RawPtr/CopyForDeref chains.
    /// Uses the current path to avoid cross-branch contamination.
    pub(crate) fn propagate_from_checkpoint(&mut self, checkpoint_block: BasicBlock) {
        let path_blocks: FxHashSet<BasicBlock> = self
            .path
            .as_ref()
            .map(|p| {
                let mut blocks: FxHashSet<BasicBlock> = p
                    .steps
                    .iter()
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
        let block_steps: Vec<BasicBlock> = self
            .path
            .as_ref()
            .map(|p| {
                p.steps
                    .iter()
                    .filter_map(|s| match s {
                        crate::verify::path_extractor::PathStep::Block(b) => Some(*b),
                        _ => None,
                    })
                    .collect()
            })
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

    fn propagate_pass(
        &mut self,
        checkpoint_block: BasicBlock,
        path_blocks: Option<&FxHashSet<BasicBlock>>,
        use_only: bool,
    ) {
        // Walk backwards through all reachable predecessors to fill in
        // provenance chains the slicer may have omitted (e.g. `_tmp = self.ptr`).
        let mut visited = FxHashSet::default();
        let mut worklist: Vec<BasicBlock> = vec![checkpoint_block];
        let mut max_depth = 32usize;
        while let Some(block) = worklist.pop() {
            if max_depth == 0 {
                break;
            }
            max_depth -= 1;
            if !visited.insert(block) {
                continue;
            }
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
            if let TerminatorKind::Call {
                destination,
                args,
                func,
                ..
            } = &terminator.kind
            {
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
                            fallback_applied = self.try_as_ptr_fallback(
                                dest,
                                func,
                                self.value_of_operand(&first.node),
                                &first.node,
                            );
                        }
                    }
                }
                if !fallback_applied && needs_fallback && self.locals.get(&dest).is_none() {
                    if let Some(first) = args.first() {
                        self.try_as_ptr_fallback(
                            dest,
                            func,
                            self.value_of_operand(&first.node),
                            &first.node,
                        );
                    }
                }
                // For comparison calls (e.g. <[u8]>::eq), propagate
                // constant bytes from a literal operand to the tracked
                // operand's allocation so ValidCStr checks succeed.
                if self.locals.contains_key(&dest) {
                    if crate::helpers::mir_utils::is_eq_call(self.tcx, func) {
                        self.propagate_const_bytes_to_tracked(args);
                    }
                }
            }
        }
    }

    /// Check if an rvalue kind should be re-propagated in the use-only pass
    /// (Use/Cast/CopyForDeref — forward-propagate existing provenance).
    fn is_propagate_use_kind(rvalue: &Rvalue<'tcx>) -> bool {
        matches!(
            rvalue,
            Rvalue::Use(..) | Rvalue::Cast(..) | Rvalue::CopyForDeref(..)
        )
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
            Rvalue::Use(operand, _) => crate::helpers::mir_utils::extract_local(operand),
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(operand) => crate::helpers::mir_utils::extract_local(operand),
            Rvalue::Cast(_, operand, _) => crate::helpers::mir_utils::extract_local(operand),
            Rvalue::CopyForDeref(place) if place.projection.is_empty() => Some(place.local),
            _ => None,
        };

        if let Some(src) = src_local {
            if let Some(src_val) = self.locals.get(&src).cloned() {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let is_cast = matches!(rvalue, Rvalue::Cast(..));
                let is_ptr_arith = matches!(
                    rvalue,
                    Rvalue::BinaryOp(
                        BinOp::Add
                            | BinOp::AddWithOverflow
                            | BinOp::AddUnchecked
                            | BinOp::Sub
                            | BinOp::SubWithOverflow
                            | BinOp::SubUnchecked
                            | BinOp::Offset,
                        _
                    )
                );
                self.set_local(
                    dest_local,
                    VmValue {
                        term: src_val.term,
                        ty: dest_ty,
                        provenance: src_val.provenance,
                        invariants: ValueInvariants {
                            aligned: src_val.invariants.aligned,
                            in_bounds: src_val.invariants.in_bounds,
                            align_n: if is_cast || is_ptr_arith {
                                src_val.invariants.align_n
                            } else {
                                None
                            },
                            ..src_val.invariants
                        },
                    },
                );
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
                    let dest_ty = self.body.local_decls[dest_local].ty;
                    self.set_local(
                        dest_local,
                        VmValue {
                            term: val.term,
                            ty: dest_ty,
                            provenance: val.provenance,
                            invariants: val.invariants,
                        },
                    );
                }
            }
            return;
        }

        // Ref: &place → propagate address + provenance
        if let Rvalue::Ref(_, _, place) = rvalue {
            if let Some(addr) = self.address_of_place(place) {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let alloc_align = addr
                    .provenance
                    .as_ref()
                    .map(|p| self.alloc(p.alloc_id).align)
                    .filter(|&a| a > 1);
                let has_deref = place
                    .projection
                    .iter()
                    .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
                let src_ty = self.body.local_decls[place.local].ty;
                let is_from_raw_parts_like =
                    matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(_, _));
                let is_slice_ref =
                    if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                        matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
                    } else {
                        false
                    };
                let src_in_bounds = if is_slice_ref && is_from_raw_parts_like && has_deref {
                    addr.provenance.is_some()
                } else {
                    self.locals
                        .get(&place.local)
                        .map_or(false, |v| v.invariants.in_bounds)
                };
                self.set_local(
                    dest_local,
                    VmValue {
                        term: addr.term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            aligned: true,
                            init: true,
                            in_bounds: src_in_bounds,
                            align_n: alloc_align,
                            is_field_offset: false,
                        },
                    },
                );
            }
            return;
        }

        // RawPtr: &raw place → propagate address + provenance
        if let Rvalue::RawPtr(_, place) = rvalue {
            if let Some(addr) = self.address_of_place(place) {
                let dest_ty = self.body.local_decls[dest_local].ty;
                let alloc_align = addr
                    .provenance
                    .as_ref()
                    .map(|p| self.alloc(p.alloc_id).align)
                    .filter(|&a| a > 1);
                let src_in_bounds = self
                    .locals
                    .get(&place.local)
                    .map_or(false, |v| v.invariants.in_bounds);
                self.set_local(
                    dest_local,
                    VmValue {
                        term: addr.term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            in_bounds: src_in_bounds,
                            align_n: alloc_align,
                            ..Default::default()
                        },
                    },
                );
            }
            return;
        }

        // BinaryOp Add/Sub/Offset: lhs provenance → dest
        if let Rvalue::BinaryOp(op, pair) = rvalue {
            let (lhs_op, rhs_op) = &**pair;
            if matches!(
                op,
                BinOp::Add
                    | BinOp::AddWithOverflow
                    | BinOp::AddUnchecked
                    | BinOp::Sub
                    | BinOp::SubWithOverflow
                    | BinOp::SubUnchecked
                    | BinOp::Offset
            ) {
                let lhs = crate::helpers::mir_utils::extract_local(lhs_op);
                let rhs = crate::helpers::mir_utils::extract_local(rhs_op);
                if let Some(src) = lhs {
                    if let Some(src_val) = self.locals.get(&src).cloned() {
                        let rhs_val = rhs
                            .and_then(|r| self.locals.get(&r))
                            .map(|v| VmValue {
                                term: v.term.clone(),
                                ty: v.ty,
                                provenance: None,
                                invariants: ValueInvariants::default(),
                            })
                            .unwrap_or(VmValue {
                                term: Int::from_u64(self.ctx, 0),
                                ty: self.body.local_decls[dest_local].ty,
                                provenance: None,
                                invariants: ValueInvariants::default(),
                            });
                        let prov = self.provenance_for_binary_op(*op, &src_val, &rhs_val);
                        let dest_ty = self.body.local_decls[dest_local].ty;
                        self.set_local(
                            dest_local,
                            VmValue {
                                term: src_val.term,
                                ty: dest_ty,
                                provenance: prov,
                                invariants: ValueInvariants {
                                    aligned: src_val.invariants.aligned,
                                    in_bounds: false,
                                    align_n: src_val.invariants.align_n,
                                    ..src_val.invariants
                                },
                            },
                        );
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
    ) {
        match &statement.kind {
            StatementKind::Assign(assign) => {
                let (place, rvalue) = &**assign;
                self.exec_assign(place, rvalue);
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
            #[cfg(not(rapx_ge_99))]
            StatementKind::Retag(..) => {}
            _ => {
                self.notes.push(format!(
                    "unsupported statement at bb{}#{}",
                    block.as_usize(),
                    statement_index
                ));
            }
        }
    }

    fn exec_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>) {
        let value = self.eval_rvalue(place, rvalue);

        let has_deref = place
            .projection
            .iter()
            .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));

        if !place.projection.is_empty() {
            self.record_projected_store(place, &value);
            self.record_indexed_store_for_vm(place, &value);
        }

        if place.projection.is_empty() {
            let mut value = value;
            value.invariants.init = true;
            self.set_local(place.local, value);
            // Propagate field values for aggregate copies (e.g. `_4 = copy _1`)
            // so downstream field accesses (NonZero::get -> self.0) resolve to
            // the same symbolic field terms.  A projected source (`_11 = move
            // (_1.2)`) shifts the field path by its `Field` projection prefix,
            // so `(_1.2).1` becomes `_11.1` — this keeps the `NonNull` node
            // field's provenance alive across `NodeRef` moves.
            let src_place: Option<&Place<'tcx>> = match rvalue {
                #[cfg(rapx_rvalue_use_with_retag)]
                Rvalue::Use(operand, _) => match operand {
                    Operand::Copy(p) | Operand::Move(p) => Some(p),
                    _ => None,
                },
                #[cfg(not(rapx_rvalue_use_with_retag))]
                Rvalue::Use(operand) => match operand {
                    Operand::Copy(p) | Operand::Move(p) => Some(p),
                    _ => None,
                },
                Rvalue::CopyForDeref(p) => Some(p),
                _ => None,
            };
            if let Some(sp) = src_place {
                let field_prefix: Vec<usize> = sp
                    .projection
                    .iter()
                    .filter_map(|p| match p.kind() {
                        rustc_middle::mir::ProjectionElem::Field(fi, _) => Some(fi.as_usize()),
                        _ => None,
                    })
                    .collect();
                let only_field = sp
                    .projection
                    .iter()
                    .all(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Field(..)));
                if only_field {
                    let keys: Vec<Vec<usize>> = self
                        .field_values
                        .keys()
                        .filter(|(l, _)| *l == sp.local)
                        .map(|(_, f)| f.clone())
                        .collect();
                    for k in keys {
                        let rest = if field_prefix.is_empty() {
                            Some(k.clone())
                        } else if k.len() > field_prefix.len()
                            && k[..field_prefix.len()] == field_prefix[..]
                        {
                            Some(k[field_prefix.len()..].to_vec())
                        } else {
                            None
                        };
                        if let Some(rest) = rest {
                            if let Some(fv) = self.field_value(sp.local, &k).cloned() {
                                self.set_field_value(place.local, rest, fv);
                            }
                        }
                    }
                }
            }
        } else if !has_deref {
            // Field projection (no Deref): update field_values for the base local.
            let field_indices: Vec<usize> = place
                .projection
                .iter()
                .filter_map(|p| match p.kind() {
                    rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                    _ => None,
                })
                .collect();
            if !field_indices.is_empty() {
                // Track cumulative ptr offset for Iter/IterMut before moving value.
                let track_iter = field_indices == [0];
                let mut write_value = value;
                write_value.invariants.init = true;
                self.set_field_value(place.local, field_indices, write_value);
                if track_iter {
                    self.track_iter_ptr_update(place.local);
                }
            }
        }
        // For deref projections (`*ptr = val`): do NOT overwrite the base local.
        // Writing through a pointer should not reassign the pointer variable.
    }

    /// Record byte-level values when assigning to a place with projections.
    /// This handles patterns like `buf[i] = 0u8` (nul-store) and `arr[i] = val`.
    fn record_projected_store(&mut self, place: &Place<'tcx>, value: &VmValue<'ctx, 'tcx>) {
        // Prefer the value's provenance (pointee alloc) over local_alloc_ids
        // (reference alloc) for ref/ptr parameters.
        let Some(alloc_id) = self
            .locals
            .get(&place.local)
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
                                cur_ty = crate::helpers::mir_utils::field_ty(
                                    self.tcx, field_def, substs,
                                );
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
                rustc_middle::mir::ProjectionElem::Subslice {
                    from,
                    to: _,
                    from_end: _,
                } => {
                    byte_offset += from as usize;
                }
                _ => {}
            }
        }

        if concrete && value_size > 0 {
            self.alloc_mut(alloc_id).initialized = true;

            let is_u8_write = matches!(
                value_ty.kind(),
                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
            );

            if is_u8_write {
                self.record_byte_value(alloc_id, byte_offset, value.term.clone());
                if let Some(term_val) = value.term.as_u64() {
                    if term_val == 0 {
                        self.mark_byte_nul(alloc_id, byte_offset);
                    } else {
                        self.mark_byte_non_nul(alloc_id, byte_offset);
                    }
                }
            }
        }
    }

    /// Track byte-level values for index-based stores (e.g. `buf[i] = 0u8`)
    /// that `record_projected_store` skips due to Index projections.
    fn record_indexed_store_for_vm(&mut self, place: &Place<'tcx>, value: &VmValue<'ctx, 'tcx>) {
        let is_u8 = matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
        );
        if !is_u8 {
            return;
        }
        let has_index_with_concrete = place.projection.iter().any(|p| {
            if let rustc_middle::mir::ProjectionElem::Index(local) = p {
                self.locals
                    .get(&local)
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
                self.alloc_mut(alloc_id).initialized = true;
                self.record_byte_value(alloc_id, byte_offset, value.term.clone());
                if let Some(term_val) = value.term.as_u64() {
                    if term_val == 0 {
                        self.mark_byte_nul(alloc_id, byte_offset);
                    } else {
                        self.mark_byte_non_nul(alloc_id, byte_offset);
                    }
                }
            }
        }
    }

    /// Inject layout constraints (>= 1) for generic AlignOf/SizeOf constants.
    fn inject_layout_constraints(&mut self, operand: &Operand<'tcx>, val: &VmValue<'ctx, 'tcx>) {
        if let Operand::Constant(constant) = operand {
            let text = format!("{:?}", constant.const_);
            if crate::helpers::mir_utils::const_int_from_debug(&text).is_none() {
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
    ) -> VmValue<'ctx, 'tcx> {
        let dest_ty = dest_place.ty(self.body, self.tcx).ty;

        match rvalue {
            #[cfg(rapx_rvalue_use_with_retag)]
            Rvalue::Use(operand, _retag) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                val
            }
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(operand) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                val
            }
            Rvalue::Ref(_, _borrow_kind, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr
                        .provenance
                        .as_ref()
                        .map(|p| self.alloc(p.alloc_id).align)
                        .filter(|&a| a > 1);
                    // Inherit in_bounds. For &[T] created via Deref of a
                    // fat raw ptr (inlined from_raw_parts), set in_bounds
                    // like ReturnFreshAllocation does in builtin_models.
                    let has_deref = place
                        .projection
                        .iter()
                        .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
                    let src_ty = self.body.local_decls[place.local].ty;
                    let is_from_raw_parts_like =
                        matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(_, _));
                    let is_slice_ref =
                        if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                            matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
                        } else {
                            false
                        };
                    let src_in_bounds = if is_slice_ref && is_from_raw_parts_like && has_deref {
                        addr.provenance.is_some()
                    } else {
                        self.locals
                            .get(&place.local)
                            .map_or(false, |v| v.invariants.in_bounds)
                    };
                    let val = VmValue {
                        term: addr.term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            aligned: self.check_place_alignment(place),
                            init: true,
                            in_bounds: src_in_bounds,
                            align_n: alloc_align,
                            is_field_offset: false,
                        },
                    };
                    self.propagate_byte_values_to_ref(place, &val);
                    self.propagate_field_values_to_ref(place, dest_place.local);
                    val
                } else {
                    let term = self.fresh_int("ref_addr");
                    VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            ..Default::default()
                        },
                    }
                }
            }
            Rvalue::RawPtr(_, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr
                        .provenance
                        .as_ref()
                        .map(|p| self.alloc(p.alloc_id).align)
                        .filter(|&a| a > 1);
                    let source_in_bounds = self
                        .locals
                        .get(&place.local)
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
                    val
                } else {
                    let term = self.fresh_int("rawptr_addr");
                    VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            ..Default::default()
                        },
                    }
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
                let lhs_pk = crate::helpers::mir_utils::operand_place(lhs_op);
                let rhs_pk = crate::helpers::mir_utils::operand_place(rhs_op);
                self.binary_op_sources
                    .insert(dest_pk.clone(), (lhs_pk, rhs_pk));
                // Store the direct boolean condition for comparison results so
                // exec_switchint can record a precise path condition (e.g.
                // `offset <= len - 16`) instead of `ite(cond, 1, 0) != 0`, which
                // the SMT solver often fails to unfold.
                let cmp_cond = match *op {
                    BinOp::Le => Some(lhs.term.le(&rhs.term)),
                    BinOp::Lt => Some(lhs.term.lt(&rhs.term)),
                    BinOp::Ge => Some(lhs.term.ge(&rhs.term)),
                    BinOp::Gt => Some(lhs.term.gt(&rhs.term)),
                    BinOp::Eq => Some(lhs.term._eq(&rhs.term)),
                    BinOp::Ne => Some(lhs.term._eq(&rhs.term).not()),
                    _ => None,
                };
                if let Some(cond) = cmp_cond {
                    self.comparison_conds.insert(dest_pk.clone(), cond);
                }
                // Add Euclidean division identity for Div and Rem:
                //   lhs == (lhs/rhs)*rhs + lhs%rhs  ∧  lhs%rhs >= 0
                // Also add (lhs/rhs)*rhs <= lhs directly for Div for robustness.
                // This lets later checks prove (x/N)*N <= x and x%N >= 0.
                // IMPORTANT: use `term` (returned by eval_binary_op) as the
                // quotient, NOT a separate `lhs.div(&rhs)` call, so that the
                // axiom constrains the SAME Z3 term used in subsequent ops.
                if matches!(*op, BinOp::Div | BinOp::Rem) {
                    let quot = if matches!(*op, BinOp::Div) {
                        &term
                    } else {
                        &lhs.term.div(&rhs.term)
                    };
                    let rem = lhs.term.rem(&rhs.term);
                    let mul_term = Int::mul(self.ctx, &[quot, &rhs.term]);
                    let sum_term = Int::add(self.ctx, &[&mul_term, &rem]);
                    self.path_conditions.push(lhs.term._eq(&sum_term));
                    let zero = Int::from_u64(self.ctx, 0);
                    self.path_conditions.push(rem.ge(&zero));
                    // Remainder and quotient bounds help prove length constraints
                    // involving % and / in the SMT solver.
                    if rhs.term.as_u64().map_or(true, |r| r >= 1) {
                        self.path_conditions.push(rem.lt(&rhs.term));
                    }
                    self.path_conditions.push(rem.le(&lhs.term));
                    self.path_conditions.push(quot.ge(&zero));
                    // Direct inequality: (lhs/rhs)*rhs <= lhs
                    self.path_conditions.push(mul_term.le(&lhs.term));
                    // Quotient strict bound: for rhs >= 2 and lhs >= 2,
                    // quot + 1 <= lhs (hence quot < lhs). E.g. X/2 < X for X>1.
                    if rhs.term.as_u64().map_or(false, |r| r >= 2) {
                        let one = Int::from_u64(self.ctx, 1);
                        let qp1 = Int::add(self.ctx, &[quot, &one]);
                        // qp1 <= lhs is equivalent to quot < lhs for integers
                        self.path_conditions.push(qp1.le(&lhs.term));
                    } else {
                        // For rhs >= 1: quot <= lhs
                        if rhs.term.as_u64().map_or(false, |r| r >= 1) {
                            self.path_conditions.push(quot.le(&lhs.term));
                        }
                    }
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
                        let overflow_val = VmValue::new(overflow_term, fields[1]);
                        self.set_field_value(dest_place.local, vec![1], overflow_val);
                    }
                }
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance,
                    invariants,
                }
            }
            Rvalue::UnaryOp(op, operand) => {
                let val = self.value_of_operand(operand);
                let is_bool = matches!(val.ty.kind(), rustc_middle::ty::TyKind::Bool);
                let term = if matches!(op, UnOp::PtrMetadata) {
                    // `PtrMetadata` on a `&[T]` gives the slice length, which is
                    // the allocation size divided by the element size. Reuse the
                    // same symbolic term as the allocation size so downstream
                    // InBound checks (`offset <= len`) agree with the `len` used
                    // in loop guards (`offset <= len - 16`).
                    self.slice_len_from_value(&val)
                        .unwrap_or_else(|| self.fresh_int("ptr_metadata"))
                } else {
                    self.eval_unary_op(*op, &val.term, is_bool)
                };
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                }
            }
            Rvalue::Cast(_kind, operand, cast_ty) => {
                let src_val = self.value_of_operand(operand);
                let src_ty = src_val.ty;
                let is_src_ref = matches!(src_ty.kind(), rustc_middle::ty::TyKind::Ref(..));
                let dest_is_ptr = matches!(cast_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..));
                let aligned = if dest_is_ptr && is_src_ref {
                    true
                } else {
                    src_val.invariants.aligned
                };
                // Transmute-like casts of single-field newtypes (e.g.
                // NonZero::get's `_0 = copy _1 as T`) yield the underlying
                // field value, not the wrapper's own term.
                let term = crate::helpers::mir_utils::extract_local(operand)
                    .and_then(|l| self.field_value(l, &[0]).map(|v| v.term.clone()))
                    .unwrap_or(src_val.term);
                VmValue {
                    term,
                    ty: *cast_ty,
                    provenance: src_val.provenance,
                    invariants: ValueInvariants {
                        non_null: src_val.invariants.non_null,
                        init: src_val.invariants.init,
                        aligned,
                        in_bounds: src_val.invariants.in_bounds,
                        align_n: src_val.invariants.align_n,
                        is_field_offset: false,
                    },
                }
            }
            Rvalue::Aggregate(_kind, operands) => {
                // For an enum aggregate, remember whether this is the
                // data-carrying variant of `Option`/`Result` (`Some`/`Ok`), so
                // the nested-field flattening below only fires on paths that
                // actually carry a `Self` value.
                let data_variant = match &**_kind {
                    rustc_middle::mir::AggregateKind::Adt(did, variant_idx, ..) => {
                        if self.tcx.is_diagnostic_item(rustc_span::sym::Result, *did) {
                            Some(variant_idx.as_usize() == 0)
                        } else if self.tcx.is_diagnostic_item(rustc_span::sym::Option, *did) {
                            Some(variant_idx.as_usize() == 1)
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                // `NonNull::new_unchecked(ptr)` / `NonNull::from(&T)` construct a
                // repr(transparent) single-field newtype whose value *is* the
                // underlying pointer.  Model the wrapper as the pointer field
                // itself (term + provenance + invariants) so downstream checks
                // like `NonNull(node)` / `Align(node, T)` / `Allocated(node, ..)`
                // can discharge against the real pointer instead of a fresh
                // unconstrained `aggregate` symbol.
                if operands.len() == 1 && self.find_nn_pointee(dest_ty).is_some() {
                    let field_val = self.value_of_operand(operands.iter().next().unwrap());
                    let dest_local = dest_place.local;
                    self.set_field_value(dest_local, vec![0], field_val.clone());
                    if let Some(alloc_id) = self.local_alloc_ids.get(&dest_local).copied() {
                        self.alloc_mut(alloc_id).initialized = true;
                    }
                    return VmValue {
                        term: field_val.term,
                        ty: dest_ty,
                        provenance: field_val.provenance,
                        invariants: field_val.invariants,
                    };
                }
                let term = self.fresh_int("aggregate");
                let dest_local = dest_place.local;
                let dest_alloc_id = self.local_alloc_ids.get(&dest_local).copied();
                let is_byte_array = crate::helpers::mir_utils::is_u8_array_or_slice(dest_ty);
                let field_types: Vec<_> = self.aggregate_field_tys(dest_ty);
                let mut byte_offset = 0usize;
                for (i, operand) in operands.iter().enumerate() {
                    let mut field_val = self.value_of_operand(operand);
                    if let Some(field_ty) = field_types.get(i) {
                        let src_is_ref =
                            matches!(field_val.ty.kind(), rustc_middle::ty::TyKind::Ref(..));
                        let dst_is_raw =
                            matches!(field_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..));
                        if src_is_ref && dst_is_raw {
                            field_val.invariants.in_bounds = true;
                            field_val.ty = *field_ty;
                        } else if dst_is_raw && field_val.invariants.non_null {
                            field_val.invariants.in_bounds = true;
                            field_val.ty = *field_ty;
                        }
                    }
                    let field_sz = field_types
                        .get(i)
                        .copied()
                        .map(|ty| self.size_of_ty(ty) as usize)
                        .unwrap_or(1);
                    let field_term = field_val.term.clone();
                    self.set_field_value(dest_local, vec![i], field_val);
                    // Flatten a nested aggregate: if the operand is a local whose
                    // own fields are tracked (e.g. `_0 = Result::Ok(_24)` where
                    // `_24 = RawVecInner { ptr: _25, .. }`), expose the nested
                    // fields under the destination's field path so a contract
                    // place like `Return.Field(0).Field(0)` (the `Ok` variant's
                    // data, then the struct field) can resolve to `_25`.
                    // Only flatten the data-carrying variant (`Ok`/`Some`); on
                    // `Err`/`None` paths there is no `Self` and the nested place
                    // should resolve to `Unknown` instead.
                    if data_variant != Some(false) {
                        if let Some(op_place) = operand.place() {
                            if op_place.projection.is_empty() {
                                let nested: Vec<(Vec<usize>, VmValue<'ctx, 'tcx>)> = self
                                    .field_values
                                    .iter()
                                    .filter(|((l, _), _)| *l == op_place.local)
                                    .map(|((_, p), v)| (p.clone(), v.clone()))
                                    .collect();
                                for (nested_path, nested_val) in nested {
                                    let mut full = vec![i];
                                    full.extend_from_slice(&nested_path);
                                    self.set_field_value(dest_local, full, nested_val);
                                }
                            }
                        }
                    }
                    if let Some(alloc_id) = dest_alloc_id {
                        self.alloc_mut(alloc_id).initialized = true;
                        if is_byte_array && field_sz == 1 {
                            self.record_byte_value(alloc_id, byte_offset, field_term.clone());
                        }
                        // Record known_nul / known_non_nul from constant operands
                        if let Some(int_val) = crate::helpers::mir_utils::operand_const_u64(operand)
                        {
                            if field_sz == 1 {
                                if int_val == 0 {
                                    self.mark_byte_nul(alloc_id, byte_offset);
                                    if !is_byte_array {
                                        self.record_byte_value(
                                            alloc_id,
                                            byte_offset,
                                            Int::from_u64(self.ctx, 0),
                                        );
                                    }
                                } else {
                                    self.mark_byte_non_nul(alloc_id, byte_offset);
                                    if !is_byte_array {
                                        self.record_byte_value(
                                            alloc_id,
                                            byte_offset,
                                            Int::from_u64(self.ctx, int_val),
                                        );
                                    }
                                }
                            }
                            // For multi-byte fields: track each constituent byte
                            for b in 0..field_sz.min(8) {
                                let byte_off = byte_offset + b;
                                let byte_val = (int_val >> (b * 8)) & 0xFF;
                                if byte_val == 0 {
                                    self.mark_byte_nul(alloc_id, byte_off);
                                } else {
                                    self.mark_byte_non_nul(alloc_id, byte_off);
                                }
                                self.record_byte_value(
                                    alloc_id,
                                    byte_off,
                                    Int::from_u64(self.ctx, byte_val),
                                );
                            }
                        }
                    }
                    byte_offset += field_sz;
                }
                // Fat-pointer construction (inlined `from_raw_parts` /
                // `slice_from_raw_parts_mut`): the result's address and
                // provenance are those of the data pointer (field 0), so
                // downstream `Allocated`/`Owning` checks on the slice resolve
                // against the real buffer instead of a fresh `aggregate` symbol.
                let is_slice_ptr = matches!(dest_ty.kind(),
                    rustc_middle::ty::TyKind::RawPtr(inner, _) | rustc_middle::ty::TyKind::Ref(_, inner, _)
                        if matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_)));
                let (result_term, result_prov) = if is_slice_ptr {
                    match self.field_value(dest_local, &[0]).cloned() {
                        Some(data) => (data.term.clone(), data.provenance.clone()),
                        None => (term.clone(), None),
                    }
                } else {
                    (term.clone(), None)
                };
                VmValue {
                    term: result_term,
                    ty: dest_ty,
                    provenance: result_prov,
                    invariants: ValueInvariants::default(),
                }
            }
            Rvalue::Discriminant(place) => {
                // If the ADT's variant is known symbolically (e.g. `Iterator::next`
                // returns `Some` iff the iterator was non-empty), reuse that term
                // so `switchInt(discriminant)` branches stay tied to the real
                // condition instead of a fresh unconstrained symbol.
                let term = self
                    .discriminant_terms
                    .get(&place.local)
                    .cloned()
                    .unwrap_or_else(|| self.fresh_int("discriminant"));
                if self.discriminant_terms.contains_key(&place.local) {
                    self.contract_flags.saw_next_discriminant = true;
                }
                // For Ordering (repr i8, values: Less=-1 Equal=0 Greater=1),
                // the discriminant index equals the repr value + 1.
                // Connect the fresh discriminant term to the ADT value so
                // that SwitchInt constraints propagate to the stored value.
                let place_val = self
                    .value_of_place(place)
                    .or_else(|| self.local_value(place.local).cloned());
                if let Some(ref pv) = place_val {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = pv.ty.kind() {
                        if api_classify::is_std_ordering(adt_def.did()) && adt_def.is_enum() {
                            let one = Int::from_u64(self.ctx, 1);
                            let discr_minus_one = Int::sub(self.ctx, &[&term, &one]);
                            self.path_conditions.push(pv.term._eq(&discr_minus_one));
                            // Also bound the discriminant to {0, 1, 2}
                            let zero = Int::from_u64(self.ctx, 0);
                            let two = Int::from_u64(self.ctx, 2);
                            self.path_conditions.push(term.ge(&zero));
                            self.path_conditions.push(term.le(&two));
                        }
                    }
                }
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            #[cfg(not(rapx_ge_99))]
            Rvalue::ShallowInitBox(operand, _ty) => {
                let val = self.value_of_operand(operand);
                VmValue {
                    term: val.term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                }
            }
            Rvalue::CopyForDeref(place) => {
                if let Some(val) = self.value_of_place(place) {
                    val
                } else {
                    let term = self.fresh_int("copy_for_deref");
                    VmValue {
                        term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants::default(),
                    }
                }
            }
            Rvalue::Repeat(operand, _count) => {
                let _val = self.value_of_operand(operand);
                let term = self.fresh_int("repeat");
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            Rvalue::ThreadLocalRef(_) => {
                let term = self.fresh_int("thread_local");
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            #[cfg(not(rapx_ge_99))]
            Rvalue::NullaryOp(_op) => {
                let term = self.fresh_int("nullary");
                let op_debug = format!("{:?}", _op);
                let is_align_of = op_debug.contains("AlignOf") || op_debug.contains("min_align_of");
                let is_size_of = op_debug.contains("SizeOf");
                if is_align_of || is_size_of {
                    let one = Int::from_u64(self.ctx, 1);
                    self.path_conditions.push(term.ge(&one));
                }
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            Rvalue::WrapUnsafeBinder(_operand, _ty) => {
                let term = self.fresh_int("wrap_unsafe_binder");
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants::default(),
                }
            }
            #[cfg(rapx_rvalue_has_reborrow)]
            Rvalue::Reborrow(_ty, _mutability, _place) => {
                let term = self.fresh_int("reborrow");
                VmValue {
                    term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants {
                        non_null: true,
                        ..Default::default()
                    },
                }
            }
        }
    }

    // ── Arithmetic ────────────────────────────────────────────────

    fn eval_binary_op(&mut self, op: BinOp, lhs: &Int<'ctx>, rhs: &Int<'ctx>) -> Int<'ctx> {
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
            BinOp::BitAnd => {
                let result = self.fresh_int("binop");
                // BitAnd only clears bits, so it never increases a non-negative
                // value: result <= lhs.
                self.path_conditions.push(result.le(lhs));
                // When the mask (rhs) is a non-negative constant, the result is
                // also bounded by it: `x & c <= c` (e.g. `rhs & 31 <= 31`).
                // This lets `(rhs & (BITS - 1)) < BITS` be discharged. The
                // mask may be a folded expression (`SubWithOverflow(BITS, 1)`),
                // so `simplify()` is used to recover its constant value.
                if rhs.simplify().as_u64().is_some() {
                    self.path_conditions.push(result.le(rhs));
                }
                if self.not_mask_terms.contains(rhs) {
                    // rhs is a two's-complement mask `!(align-1) == -align`,
                    // so `align = -rhs`. The result of `x & !(align-1)` is
                    // `x` rounded down to a multiple of `align` (i.e. align_up
                    // of the pre-incremented value).
                    let zero = Int::from_u64(self.ctx, 0);
                    let align = Int::sub(self.ctx, &[&zero, rhs]);
                    self.path_conditions.push(result.rem(&align)._eq(&zero));
                    let one = Int::from_u64(self.ctx, 1);
                    let addr = Int::add(self.ctx, &[lhs, rhs, &one]);
                    self.path_conditions.push(result.ge(&addr));
                }
                result
            }
            BinOp::BitOr => {
                let result = self.fresh_int("binop");
                let zero = Int::from_u64(self.ctx, 0);
                // Bitwise OR only sets bits, so the result is non-zero whenever
                // either operand is non-zero.  Emit an implication (rather than
                // `result >= lhs`, which is only valid for non-negative values)
                // so `NonZero` bit-or methods discharge their `!= 0` obligation
                // for both signed and unsigned instantiations.
                self.path_conditions
                    .push(lhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                self.path_conditions
                    .push(rhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                result
            }
            _ => self.fresh_int("binop"),
        }
    }

    fn eval_unary_op(&mut self, op: UnOp, val: &Int<'ctx>, is_bool: bool) -> Int<'ctx> {
        match op {
            UnOp::Not => {
                if is_bool {
                    let zero = Int::from_u64(self.ctx, 0);
                    let one = Int::from_u64(self.ctx, 1);
                    val._eq(&zero).ite(&one, &zero)
                } else {
                    // Two's-complement bitwise NOT: !x == -x - 1.
                    let zero = Int::from_u64(self.ctx, 0);
                    let one = Int::from_u64(self.ctx, 1);
                    let neg = Int::sub(self.ctx, &[&zero, val]);
                    let result = Int::sub(self.ctx, &[&neg, &one]);
                    self.not_mask_terms.insert(result.clone());
                    result
                }
            }
            UnOp::Neg => {
                let zero = Int::from_u64(self.ctx, 0);
                Int::sub(self.ctx, &[&zero, val])
            }
            UnOp::PtrMetadata => self.fresh_int("ptr_metadata"),
        }
    }

    /// Compute the slice length for a `&[T]` / `&mut [T]` value: the allocation
    /// size divided by the element size. Reuses the allocation's size term so
    /// it agrees with InBound/`alloc.size` checks.
    fn slice_len_from_value(&self, val: &VmValue<'ctx, 'tcx>) -> Option<Int<'ctx>> {
        let alloc_id = val.provenance_alloc_id()?;
        let alloc = self.alloc(alloc_id);
        let elem_ty = alloc.element_ty?;
        let elem_size = self.size_of_ty(elem_ty).max(1) as u64;
        if elem_size == 1 {
            return Some(alloc.size.clone());
        }
        let elem_term = Int::from_u64(self.ctx, elem_size);
        Some(alloc.size.div(&elem_term))
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
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked | BinOp::Offset => {
                // ptr + scalar → propagate with adjusted offset
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.ctx, &[&prov.offset, &rhs.term]),
                    is_field_offset: false,
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
                    is_field_offset: false,
                })
            }
            BinOp::BitAnd => {
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    // Alignment rounding changes the intra-allocation offset
                    // unpredictably; use a fresh symbolic offset constrained
                    // by the BitAnd path conditions emitted in eval_binary_op.
                    offset: self.fresh_int("align_offset"),
                    is_field_offset: false,
                })
            }
            BinOp::BitXor | BinOp::Shr | BinOp::ShrUnchecked => {
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.clone()
            }
            BinOp::BitOr | BinOp::Shl | BinOp::ShlUnchecked => {
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.ctx, &[&prov.offset, &rhs.term]),
                    is_field_offset: false,
                })
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                if rhs.provenance.is_some() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::mul(self.ctx, &[&prov.offset, &rhs.term]),
                    is_field_offset: false,
                })
            }
            BinOp::Div | BinOp::Rem => lhs.provenance.clone(),
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
            BinOp::Add
            | BinOp::AddWithOverflow
            | BinOp::AddUnchecked
            | BinOp::Sub
            | BinOp::SubWithOverflow
            | BinOp::SubUnchecked
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

        ValueInvariants {
            non_null,
            align_n,
            ..Default::default()
        }
    }

    /// Check if a value is known to be a multiple of `align` (e.g. the result
    /// of a Mul by a constant factor of `align`).
    fn rhs_is_aligned_multiple(&self, val: &VmValue<'ctx, 'tcx>, align: u64) -> bool {
        // If the value itself has align_n >= align, it's a multiple
        if let Some(a) = val.invariants.align_n {
            if a >= align && a % align == 0 {
                return true;
            }
        }
        // If the value is a constant, check directly
        if let Some(c) = val.term.as_u64() {
            if c % align == 0 {
                return true;
            }
        }
        false
    }

    // ── Storage ──────────────────────────────────────────────────

    fn exec_storage_live(&mut self, local: Local) {
        self.local_address(local);
        if let Some(alloc_id) = self.local_alloc_ids.get(&local).copied() {
            self.alloc_mut(alloc_id).dead = false;
        }
    }

    fn exec_storage_dead(&mut self, local: Local) {
        if let Some(alloc_id) = self.local_alloc_ids.get(&local).copied() {
            self.alloc_mut(alloc_id).dead = true;
        }
    }

    pub(crate) fn exec_drop(&mut self, place: &Place<'tcx>) {
        if let Some(alloc_id) = self.local_alloc_ids.get(&place.local).copied() {
            self.alloc_mut(alloc_id).dead = true;
            // Cascade to heap data allocations (see exec_storage_dead).
            let mut worklist: Vec<AllocId> = vec![alloc_id];
            while let Some(id) = worklist.pop() {
                if let Some(data_id) = self.alloc(id).slice_data {
                    self.alloc_mut(data_id).dead = true;
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
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let caller_id = self.caller_def_id;
                self.exec_call(func, args, destination.local, *target, None, caller_id);
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

        // If the discriminator is a comparison result, record the direct
        // boolean condition alongside the ite-encoded `discr == value` fact,
        // so the SMT solver can reason about `offset <= len` directly.
        let cmp_cond = discr.place().and_then(|p| {
            let pk = PlaceKey::from_mir_place(&p);
            self.comparison_conds.get(&pk).cloned()
        });

        // Determine which target block is taken along the path.
        if let Some(ref path) = self.path {
            if let Some(chosen) = chosen_successor(path, block, occurrence) {
                for (value, target) in targets.iter() {
                    if target == chosen {
                        let val_term = Int::from_u64(self.ctx, value as u64);
                        self.path_conditions.push(discr_val.term._eq(&val_term));
                        if let Some(ref cond) = cmp_cond {
                            if value != 0 {
                                self.path_conditions.push(cond.clone());
                            } else {
                                self.path_conditions.push(cond.not());
                            }
                        }
                        if value != 0 {
                            self.infer_switch_guard(discr);
                        }
                        return;
                    }
                }
                // Otherwise branch: the discrim is NOT any of the explicit values.
                if targets.otherwise() == chosen {
                    // Negate every explicit target value.
                    for (value, _) in targets.iter() {
                        let val_term = Int::from_u64(self.ctx, value as u64);
                        self.path_conditions
                            .push(discr_val.term._eq(&val_term).not());
                    }
                    if let Some(ref cond) = cmp_cond {
                        // For a boolean discriminator, `otherwise` means
                        // `discr != 0`, i.e. the comparison is true.
                        if targets.iter().any(|(v, _)| v == 0) {
                            self.path_conditions.push(cond.clone());
                        }
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
            self.path_conditions.push(cond_val.term._eq(&zero).not());
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
        if !expected {
            return;
        }
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
        if !expected {
            return;
        }
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
        // A precondition with a hazard component records that the caller
        // accepts that hazard (e.g. `any(Trait(T, Copy), Alias(self, ret))` on
        // `NonNull::read`).  Inlined read/copy intrinsics whose result
        // structurally aliases the source are then treated as the accepted
        // hazard rather than a hard failure.
        if contains_hazard(property) {
            self.contract_flags.alias_hazard_accepted = true;
        }
        let Property::Atom(atom) = property else {
            return;
        };
        if atom.contract_kind == ContractKind::Hazard {
            return;
        }
        let kind = atom.kind;
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
                if let Some(id) = self.contract_alloc_id_field_aware(property) {
                    self.alloc_mut(id).alive_assumed = true;
                }
            }
            PropertyKind::InBound => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_in_bounds_for_value(property, val);
                }
                if let Some(fe_place) = property.for_each() {
                    self.assert_in_bound_for_each(property, fe_place);
                    self.contract_flags.has_checked_bounds = true;
                }
            }
            PropertyKind::Allocated => {
                self.assert_allocated_fact(property);
            }
            PropertyKind::Typed => {
                if let Some(val) = self.contract_target_value(property) {
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        if let Some(expected_ty) = property.args().get(1).and_then(|a| {
                            if let PropertyArg::Ty(ty) = a {
                                Some(*ty)
                            } else {
                                None
                            }
                        }) {
                            self.alloc_mut(alloc_id).element_ty = Some(expected_ty);
                        }
                    }
                }
            }
            PropertyKind::SplitTransmute => {
                self.contract_flags.split_transmute_asserted = true;
            }
            PropertyKind::ValidCStr => {
                // A `ValidCStr(p, n)` fact guarantees `p` points to a live,
                // initialized, null-terminated byte buffer. Mark the target
                // allocation so the checker can treat it (and any of its
                // sub-slices) as a valid C string, and so pointer reads /
                // `from_raw_parts` over it see a live, initialized allocation.
                //
                // For a `&CStr`-style target the field projection (`inner`)
                // may not be materialised for a DST, so fall back to the base
                // local's own provenance (a `&CStr` reference points directly
                // at the byte buffer it owns).
                let id = self.contract_alloc_id_field_aware(property).or_else(|| {
                    let local = self.contract_target_local(property)?;
                    self.locals.get(&local)?.provenance_alloc_id()
                });
                if let Some(id) = id {
                    self.alloc_mut(id).dead = false;
                    self.alloc_mut(id).alive_assumed = true;
                    self.alloc_mut(id).initialized = true;
                    self.alloc_mut(id).nul_terminated = true;
                    // `ValidCStr(p, n)` carries the byte length of the
                    // nul-terminated buffer.  Assert the allocation covers `n`
                    // bytes so downstream `from_raw_parts(p, n)` / InBound
                    // obligations can be discharged from the exact length
                    // (rather than a conservative `1` placeholder).
                    if let Some(n) = property
                        .args()
                        .get(1)
                        .and_then(|a| self.resolve_contract_count(a))
                    {
                        self.path_conditions.push(self.alloc(id).size.ge(&n));
                    }
                }
            }
            PropertyKind::ValidNum => {
                if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
                    for pred in predicates {
                        if let Some(condition) = self.eval_predicate_as_bool(pred) {
                            self.path_conditions.push(condition);
                            // For !self.is_empty() → self.len() != 0 on
                            // Iter/IterMut: also assert len >= 1 to help
                            // Z3 with integer division reasoning.
                            if let Some(len_term) = self.try_simple_iter_len_from_pred(pred) {
                                let one = Int::from_u64(self.ctx, 1);
                                self.path_conditions.push(len_term.ge(&one));
                            }
                        }
                    }
                }
            }
            _ => {
                self.notes
                    .push(format!("contract fact {:?} not directly asserted", kind));
            }
        }
    }

    /// Get the local referenced by a contract property's target.
    fn contract_target_local(&self, property: &Property<'tcx>) -> Option<Local> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp,
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(cp) => cp,
                _ => return None,
            },
            _ => return None,
        };
        match cp.base {
            PlaceBase::Local(n) => Some(Local::from_usize(n)),
            PlaceBase::Arg(n) => Some(Local::from_usize(n + 1)),
            PlaceBase::Return => Some(Local::from_usize(0)),
        }
    }

    /// Materialize a fresh external allocation for an `Allocated` contract
    /// fact, returning a value carrying the allocation's provenance.
    fn materialize_external_alloc(
        &mut self,
        elem_ty: Ty<'tcx>,
        count_term: Option<Int<'ctx>>,
        val_ty: Ty<'tcx>,
        huge: bool,
    ) -> VmValue<'ctx, 'tcx> {
        let elem_sz_raw = self.size_of_ty(elem_ty);
        let heap_align = self.align_of_ty(elem_ty).max(1);
        let (heap_id, heap_base) = if huge || elem_sz_raw == 0 {
            // Struct-field targets (and generic element types): use an
            // unbounded external allocation so `Allocated`/`InBound` checks
            // auto-pass regardless of the symbolic element size.
            let max_size = Int::from_u64(self.ctx, i64::MAX as u64);
            self.allocate_external(max_size, heap_align, Some(elem_ty))
        } else {
            let elem_sz = Int::from_u64(self.ctx, elem_sz_raw as u64);
            let count = count_term.unwrap_or_else(|| Int::from_u64(self.ctx, 1));
            let total = Int::mul(self.ctx, &[&count, &elem_sz]);
            self.allocate_external(total, heap_align, Some(elem_ty))
        };
        self.alloc_mut(heap_id).initialized = true;
        VmValue {
            term: heap_base,
            ty: val_ty,
            provenance: Some(Provenance {
                alloc_id: heap_id,
                offset: Int::from_u64(self.ctx, 0),
                is_field_offset: false,
            }),
            invariants: ValueInvariants {
                non_null: true,
                init: true,
                in_bounds: true,
                aligned: true,
                align_n: if heap_align > 1 {
                    Some(heap_align)
                } else {
                    None
                },
                is_field_offset: false,
            },
        }
    }

    /// Assert an `Allocated(p, T, n)` contract fact by materializing a fresh
    /// external allocation for the pointer-typed target.
    ///
    /// - For a whole pointer parameter (`src`), the allocation is sized
    ///   `n * sizeof(T)` so downstream pointer arithmetic stays in bounds.
    /// - For a plain pointer *field* (e.g. `RawVecInner::ptr`), the allocation
    ///   is written back to the field via `set_contract_target_value`, and is
    ///   unbounded so field-subrange `InBound` checks auto-pass.
    /// - For `ForEach`/`Downcast` targets (e.g. `buckets.iter()`), the
    ///   container itself is not a pointer — keep the legacy whole-local
    ///   behaviour.
    fn assert_allocated_fact(&mut self, property: &Property<'tcx>) {
        let elem_ty = property.args().get(1).and_then(|a| {
            if let PropertyArg::Ty(ty) = a {
                Some(*ty)
            } else {
                None
            }
        });
        let count_term = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a));
        let Some(elem_ty) = elem_ty else { return };

        let has_nonfield = property
            .args()
            .first()
            .and_then(|a| match a {
                PropertyArg::Expr(ContractExpr::Place(cp)) => Some(cp),
                PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => {
                    match slice.as_ref() {
                        ContractExpr::Place(cp) => Some(cp),
                        _ => None,
                    }
                }
                _ => None,
            })
            .map(|cp| {
                cp.projections.iter().any(|p| {
                    !matches!(p, crate::verify::contract::ContractProjection::Field { .. })
                })
            })
            .unwrap_or(false);

        if has_nonfield {
            // ForEach/Downcast target: legacy whole-local, exact size.
            let Some(local) = self.contract_target_local(property) else {
                return;
            };
            let Some(val) = self.locals.get(&local).cloned() else {
                return;
            };
            if let Some(alloc_id) = val.provenance_alloc_id() {
                self.alloc_mut(alloc_id).dead = false;
            }
            let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
            self.set_local(local, v);
        } else {
            let Some((local, field_path)) = self.contract_field_path(property) else {
                return;
            };
            if field_path.is_empty() {
                // Whole pointer parameter: exact size.
                let Some(val) = self.locals.get(&local).cloned() else {
                    return;
                };
                if let Some(alloc_id) = val.provenance_alloc_id() {
                    self.alloc_mut(alloc_id).dead = false;
                }
                let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
                self.set_local(local, v);
            } else {
                // Field target. Only a *direct* pointer field (`NonNull<T>` /
                // `*mut T` / `*const T`) to a *simple* element type (primitive or
                // generic param, e.g. `NonNull<u8>`) carries the allocation
                // itself without a nested field decomposition; a wrapped field
                // (`Option<NonNull>`, `Box`) or a pointer-to-ADT (`NonNull<LeafNode>`,
                // whose fields were decomposed by param init) is handled via the
                // legacy whole-local path to avoid losing those relationships.
                let is_direct_simple_ptr = self.field_value(local, &field_path)
                    .map(|val| {
                        (matches!(val.ty.kind(), rustc_middle::ty::TyKind::RawPtr(..))
                            || matches!(val.ty.kind(), rustc_middle::ty::TyKind::Adt(adt, _)
                                if api_classify::is_std_nonnull(adt.did())
                                    || crate::helpers::mir_utils::is_raw_ptr_wrapper(self.tcx, adt.did())))
                            && (elem_ty.is_primitive()
                                || matches!(elem_ty.kind(), rustc_middle::ty::TyKind::Param(_)))
                    })
                    .unwrap_or(false);
                if is_direct_simple_ptr {
                    let Some(val) = self.field_value(local, &field_path).cloned() else {
                        return;
                    };
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        self.alloc_mut(alloc_id).dead = false;
                    }
                    let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, true);
                    self.set_field_value(local, field_path, v);
                } else {
                    let Some(val) = self.locals.get(&local).cloned() else {
                        return;
                    };
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        self.alloc_mut(alloc_id).dead = false;
                    }
                    let v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
                    self.set_local(local, v);
                }
            }
        }
    }

    /// Resolve a contract place to `(local, field_path)`. Field projections
    /// are accumulated into `field_path`; `Downcast`/`ForEach` terminate
    /// the path (they unwrap the value in place).
    fn contract_field_path(&self, property: &Property<'tcx>) -> Option<(Local, Vec<usize>)> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp,
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(cp) => cp,
                _ => return None,
            },
            _ => return None,
        };
        let local = match cp.base {
            PlaceBase::Local(n) => Local::from_usize(n),
            PlaceBase::Arg(n) => Local::from_usize(n + 1),
            PlaceBase::Return => Local::from_usize(0),
        };
        let mut path = Vec::new();
        for proj in &cp.projections {
            match proj {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    path.push(*index);
                }
                _ => break,
            }
        }
        Some((local, path))
    }

    /// Get the VmValue for a contract property's target, following field
    /// projections so that `Align(self.heap, T)` resolves to the `heap` field
    /// value rather than the whole `self` reference.
    fn contract_target_value(&mut self, property: &Property<'tcx>) -> Option<VmValue<'ctx, 'tcx>> {
        let (local, path) = self.contract_field_path(property)?;
        if path.is_empty() {
            self.locals.get(&local).cloned()
        } else {
            self.field_value(local, &path).cloned()
        }
    }

    /// Write a contract target value back to its (possibly field) location.
    fn set_contract_target_value(&mut self, property: &Property<'tcx>, val: VmValue<'ctx, 'tcx>) {
        if let Some((local, path)) = self.contract_field_path(property) {
            if path.is_empty() {
                self.set_local(local, val);
            } else {
                self.set_field_value(local, path, val);
            }
        }
    }

    /// Resolve the alloc_id for a contract property target, following
    /// field projections to locate the actual field value's provenance.
    fn contract_alloc_id_field_aware(&mut self, property: &Property<'tcx>) -> Option<AllocId> {
        let cp = match property.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => cp.clone(),
            _ => return None,
        };
        let local = match cp.base {
            PlaceBase::Local(n) => Local::from_usize(n),
            PlaceBase::Arg(n) => Local::from_usize(n + 1),
            PlaceBase::Return => Local::from_usize(0),
        };
        let mut field_path: Vec<usize> = Vec::new();
        for proj in &cp.projections {
            match proj {
                crate::verify::contract::ContractProjection::Field { index, .. } => {
                    field_path.push(*index);
                }
                _ => return None,
            }
        }
        if field_path.is_empty() {
            self.locals.get(&local)?.provenance_alloc_id()
        } else {
            self.field_value(local, &field_path)?.provenance_alloc_id()
        }
    }

    /// Resolve a contract count argument to a Z3 term by looking up
    /// the corresponding function parameter in the VM state.
    fn resolve_contract_count(&self, arg: &PropertyArg<'tcx>) -> Option<Int<'ctx>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) => Some(Int::from_u64(self.ctx, *n as u64)),
            // Delegate field-projected places and arithmetic (e.g. `cap * elem_size`)
            // to the general simple evaluator.
            PropertyArg::Expr(expr) => self.eval_contract_expr_simple(expr),
            _ => None,
        }
    }

    /// Evaluate a numeric predicate to a Z3 Bool for path-condition assertion.
    fn eval_predicate_as_bool(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'ctx>> {
        use crate::verify::contract::{ContractExpr, RelOp};
        let lhs = self.eval_contract_expr_simple(&pred.lhs)?;
        let rhs = match &pred.rhs {
            ContractExpr::Const(v) => Int::from_u64(self.ctx, *v as u64),
            _ => self.eval_contract_expr_simple(&pred.rhs)?,
        };
        Some(match pred.op {
            RelOp::Eq => lhs._eq(&rhs),
            RelOp::Ne => lhs._eq(&rhs).not(),
            RelOp::Le => lhs.le(&rhs),
            RelOp::Lt => lhs.lt(&rhs),
            RelOp::Ge => lhs.ge(&rhs),
            RelOp::Gt => lhs.gt(&rhs),
        })
    }

    fn eval_contract_expr_simple(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<Int<'ctx>> {
        use crate::verify::contract::{ContractExpr, NumericBinOp, PlaceBase};
        match expr {
            ContractExpr::SizeOf(ty) => {
                let size = self.size_of_ty(*ty).max(1);
                Some(Int::from_u64(self.ctx, size as u64))
            }
            ContractExpr::Place(cp) => {
                let local = match cp.base {
                    PlaceBase::Local(n) => Local::from_usize(n),
                    PlaceBase::Arg(n) => Local::from_usize(n + 1),
                    PlaceBase::Return => Local::from_usize(0),
                };
                let mut path: Vec<usize> = Vec::new();
                for proj in &cp.projections {
                    match proj {
                        crate::verify::contract::ContractProjection::Field { index, .. } => {
                            path.push(*index);
                        }
                        // Downcast / ForEach are not scalar numeric values.
                        _ => return None,
                    }
                }
                if path.is_empty() {
                    self.local_value(local).map(|v| v.term.clone())
                } else {
                    self.field_value(local, &path).map(|v| v.term.clone())
                }
            }
            ContractExpr::Len(inner) => {
                // Try field-based len for Iter/IterMut first.
                if let Some(val) = self.eval_contract_expr_simple_value(inner) {
                    if let Some(term) = self.try_simple_iter_len(&val) {
                        return Some(term);
                    }
                }
                let val = self.eval_contract_expr_simple_value(inner)?;
                let alloc_id = val.provenance_alloc_id()?;
                let alloc = self.alloc(alloc_id);
                let elem_ty = alloc.element_ty?;
                let elem_size = self.size_of_ty(elem_ty).max(1) as u64;
                if elem_size == 1 {
                    return Some(alloc.size.clone());
                }
                let elem_term = Int::from_u64(self.ctx, elem_size);
                Some(alloc.size.div(&elem_term))
            }
            ContractExpr::Binary {
                op: NumericBinOp::Mul,
                lhs,
                rhs,
            } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(Int::mul(self.ctx, &[&l, &r]))
            }
            ContractExpr::Binary {
                op: NumericBinOp::Add,
                lhs,
                rhs,
            } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(Int::add(self.ctx, &[&l, &r]))
            }
            ContractExpr::Binary {
                op: NumericBinOp::Sub,
                lhs,
                rhs,
            } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(Int::sub(self.ctx, &[&l, &r]))
            }
            ContractExpr::Binary {
                op: NumericBinOp::Div,
                lhs,
                rhs,
            } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(l.div(&r))
            }
            ContractExpr::Const(n) => Some(Int::from_u64(self.ctx, *n as u64)),
            _ => None,
        }
    }

    fn eval_contract_expr_simple_value(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<VmValue<'ctx, 'tcx>> {
        match expr {
            ContractExpr::Place(cp) => match cp.base {
                PlaceBase::Local(n) => self.local_value(Local::from_usize(n)).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    /// Try field-based len for Iter/IterMut references (same logic as
    /// `interpreter_iter_len` in call.rs). Used by `eval_contract_expr_simple`
    /// so that ContractFact assertions use the same symbolic term as the
    /// VM execution path.
    fn try_simple_iter_len(&self, arg_val: &VmValue<'ctx, 'tcx>) -> Option<Int<'ctx>> {
        use rustc_middle::ty::TyKind;
        let is_iter = match arg_val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => api_classify::is_std_iter_or_itermut(adt_def.did()),
                _ => false,
            },
            _ => false,
        };
        if !is_iter {
            return None;
        }
        let local = Local::from_usize(1);
        let ptr = self.field_value(local, &[0])?;
        let end = self.field_value(local, &[1])?;
        let pp = ptr.provenance.as_ref()?;
        let ep = end.provenance.as_ref()?;
        if pp.alloc_id != ep.alloc_id {
            return None;
        }
        let diff = Int::sub(self.ctx, &[&ep.offset, &pp.offset]);
        let sz = Int::from_u64(self.ctx, self.iter_elem_size(ptr));
        Some(diff.div(&sz))
    }

    /// For a predicate of the form `self.len() != 0` (i.e. `!self.is_empty()`),
    /// if the self is an Iter/IterMut reference, return the field-based len term
    /// so that a `len >= 1` constraint can be added.
    fn try_simple_iter_len_from_pred(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Int<'ctx>> {
        use crate::verify::contract::{ContractExpr, RelOp};
        if !matches!(pred.op, RelOp::Ne) {
            return None;
        }
        if !matches!(&pred.rhs, ContractExpr::Const(0)) {
            return None;
        }
        let ContractExpr::Len(inner) = &pred.lhs else {
            return None;
        };
        let val = self.eval_contract_expr_simple_value(inner)?;
        self.try_simple_iter_len(&val)
    }

    /// If `local` is a reference to Iter/IterMut and field 0 (ptr)
    /// is updated, increment the cumulative ptr offset so that
    /// `interpreter_iter_len` can express `len = initial_len - offset`
    /// instead of nested `(end - (ptr + sz + sz + ...)) / sz`.
    fn track_iter_ptr_update(&mut self, local: Local) {
        let local_val = match self.locals.get(&local) {
            Some(v) => v,
            None => return,
        };
        let is_iter = match local_val.ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, pointee, _) => match pointee.kind() {
                rustc_middle::ty::TyKind::Adt(adt_def, _) => {
                    api_classify::is_std_iter_or_itermut(adt_def.did())
                }
                _ => false,
            },
            _ => false,
        };
        if !is_iter {
            return;
        }
        let one = Int::from_u64(self.ctx, 1);
        let new_offset = match self.iter_ptr_offset.get(&local) {
            Some(prev) => Int::add(self.ctx, &[prev, &one]),
            None => one,
        };
        self.iter_ptr_offset.insert(local, new_offset);
    }

    /// Set non_null invariant on the target value.
    fn set_non_null_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'ctx, 'tcx>) {
        val.invariants.non_null = true;
        self.set_contract_target_value(property, val);
    }

    fn set_in_bounds_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'ctx, 'tcx>) {
        val.invariants.in_bounds = true;
        self.set_contract_target_value(property, val);
    }

    fn assert_in_bound_for_each(
        &mut self,
        property: &Property<'tcx>,
        fe_place: &crate::verify::contract::ContractPlace<'tcx>,
    ) {
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
        let slice_local = match property.args().first() {
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
            Some(PropertyArg::Expr(ContractExpr::Place(cp))) => match cp.base {
                PlaceBase::Arg(n) => Some(Local::from_usize(n + 1)),
                PlaceBase::Local(n) => Some(Local::from_usize(n)),
                _ => None,
            },
            _ => None,
        };
        let data_size = slice_local
            .and_then(|loc| self.locals.get(&loc))
            .and_then(|sl_val| sl_val.provenance_alloc_id())
            .map(|da_id| self.alloc(da_id).size.clone());
        let elem_sz = slice_local
            .and_then(|loc| self.locals.get(&loc))
            .and_then(|sl_val| sl_val.provenance_alloc_id())
            .and_then(|da_id| self.alloc(da_id).element_ty)
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
        if let Some(PropertyArg::Ty(ty)) = property.args().get(1) {
            let align = self.align_of_ty(*ty);
            if align > 1 {
                val.invariants.align_n = Some(align);
            }
        }
        self.set_contract_target_value(property, val);
    }

    /// Set init invariant on the target value and its allocation.
    fn set_init_for_value(&mut self, property: &Property<'tcx>, val: VmValue<'ctx, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.alloc_mut(prov.alloc_id).initialized = true;
        }
        if let Some((local, path)) = self.contract_field_path(property) {
            let existing = if path.is_empty() {
                self.locals.get(&local).cloned()
            } else {
                self.field_value(local, &path).cloned()
            };
            if let Some(mut existing) = existing {
                existing.invariants.init = true;
                if let Some(prov) = &existing.provenance {
                    self.alloc_mut(prov.alloc_id).initialized = true;
                }
                if path.is_empty() {
                    self.set_local(local, existing);
                } else {
                    self.set_field_value(local, path, existing);
                }
            }
        }
    }

    /// Set owning invariant on the target value.
    fn set_owning_for_value(&mut self, val: VmValue<'ctx, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.alloc_mut(prov.alloc_id).initialized = true;
        }
    }

    /// Extract the pointee type if `ty` is a `#[repr(transparent)]`
    /// single-field raw-pointer wrapper (`NonNull<P>`) or wrapped in
    /// `Option<NonNull<P>>`. Returns `Some(P)`.
    ///
    /// Detected structurally (via `#[repr(transparent)]` + a raw-pointer field)
    /// rather than by name, so re-implemented std types in the challenge
    /// suites are modelled identically to their std counterparts.
    fn find_nn_pointee(&self, ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
        use rustc_middle::ty::TyKind;
        match ty.kind() {
            TyKind::Adt(adt_def, substs) => {
                if let Some(pointee) = self.transparent_ptr_pointee(adt_def, substs) {
                    return Some(pointee);
                }
                if self
                    .tcx
                    .is_diagnostic_item(rustc_span::sym::Option, adt_def.did())
                {
                    if let Some(inner) = substs.first().and_then(|s| s.as_type()) {
                        if let TyKind::Adt(ia, is_) = inner.kind() {
                            return self.transparent_ptr_pointee(ia, is_);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Pointee type of a `#[repr(transparent)]` single-field raw-pointer
    /// wrapper such as `NonNull<T>` (`struct NonNull<T> { pointer: *const T }`).
    fn transparent_ptr_pointee(
        &self,
        adt_def: &rustc_middle::ty::AdtDef,
        substs: rustc_middle::ty::GenericArgsRef<'tcx>,
    ) -> Option<Ty<'tcx>> {
        if !adt_def.repr().transparent() {
            return None;
        }
        let field = adt_def.non_enum_variant().fields.iter().next()?;
        let field_ty = crate::helpers::mir_utils::field_ty(self.tcx, field, substs);
        match field_ty.kind() {
            rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
            // NonNull's field is a pattern type `*const T is !null` on newer
            // toolchains; unwrap it to the underlying raw pointer.
            rustc_middle::ty::TyKind::Pat(inner, _) => match inner.kind() {
                rustc_middle::ty::TyKind::RawPtr(pointee, _) => Some(*pointee),
                _ => None,
            },
            _ => None,
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
        if !api_classify::is_as_ptr(crate::helpers::mir_utils::dep_callee_def_id(func)) {
            return false;
        }
        let dest_ty = self.body.local_decls[dest].ty;
        let prov = first_arg_val.provenance.clone().or_else(|| {
            if let Operand::Move(place) | Operand::Copy(place) = first_arg_op {
                self.local_alloc_ids
                    .get(&place.local)
                    .map(|&id| Provenance {
                        alloc_id: id,
                        offset: Int::from_u64(self.ctx, 0),
                        is_field_offset: false,
                    })
            } else {
                None
            }
        });
        if let Some(ref prov) = prov {
            self.alloc_mut(prov.alloc_id).initialized = true;
            self.set_local(
                dest,
                VmValue {
                    term: first_arg_val.term.clone(),
                    ty: dest_ty,
                    provenance: Some(prov.clone()),
                    invariants: ValueInvariants {
                        non_null: true,
                        aligned: true,
                        init: true,
                        in_bounds: first_arg_val.invariants.in_bounds,
                        align_n: first_arg_val.invariants.align_n,
                        is_field_offset: false,
                    },
                },
            );
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
                    let bytes_opt =
                        crate::helpers::mir_utils::const_operand_bytes(self.tcx, operand)
                            .or_else(|| self.trace_to_const_bytes(operand));
                    if let Some(bytes) = bytes_opt {
                        let size = z3::ast::Int::from_u64(self.ctx, bytes.len() as u64);
                        let (alloc_id, base) =
                            self.allocate(size, self.align_of_ty(pointee_ty), Some(pointee_ty));
                        self.alloc_mut(alloc_id).initialized = true;
                        for (i, &b) in bytes.iter().enumerate() {
                            self.record_byte_value(
                                alloc_id,
                                i,
                                z3::ast::Int::from_u64(self.ctx, b as u64),
                            );
                            if b == 0 {
                                self.mark_byte_nul(alloc_id, i);
                            } else {
                                self.mark_byte_non_nul(alloc_id, i);
                            }
                        }
                        val.term = base;
                        val.provenance = Some(super::state::Provenance {
                            alloc_id,
                            offset: z3::ast::Int::from_u64(self.ctx, 0),
                            is_field_offset: false,
                        });
                        val.invariants = ValueInvariants {
                            non_null: true,
                            init: true,
                            aligned: true,
                            in_bounds: false,
                            align_n: None,
                            is_field_offset: false,
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
            && matches!(
                place.projection.first().map(|p| p.kind()),
                Some(rustc_middle::mir::ProjectionElem::Deref)
            ) {
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
                            return crate::helpers::mir_utils::const_operand_bytes(self.tcx, op)
                                .or_else(|| self.trace_to_const_bytes(op));
                        }
                        #[cfg(not(rapx_rvalue_use_with_retag))]
                        Rvalue::Use(op) => {
                            return crate::helpers::mir_utils::const_operand_bytes(self.tcx, op)
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
    /// Propagate a source place's per-field values to a reference destination,
    /// shifting the field path by the source place's `Field` projection prefix.
    /// E.g. for `_3 = &(_1.0)` where `_1` is a `Handle { node: NodeRef { node:
    /// NonNull<..>, .. }, .. }`, the nested `NonNull`'s field value stored at
    /// path `[0, 1]` becomes available at `_3`'s path `[1]`, so an inlined
    /// callee that dereferences `_3` and reads its `node` field sees the
    /// provenance of the underlying allocation.
    fn propagate_field_values_to_ref(&mut self, source_place: &Place<'tcx>, dest: Local) {
        // Support both `&(local.field...)` (Field projection prefix) and
        // `&(*local)` (reborrow of a reference, pure Deref).  In the latter
        // case the reference's own per-field values already describe the
        // pointee, so they are copied unchanged.
        let only_field_deref = source_place.projection.iter().all(|p| {
            matches!(
                p.kind(),
                rustc_middle::mir::ProjectionElem::Field(..)
                    | rustc_middle::mir::ProjectionElem::Deref
            )
        });
        if !only_field_deref {
            return;
        }
        let field_prefix: Vec<usize> = source_place
            .projection
            .iter()
            .filter_map(|p| match p.kind() {
                rustc_middle::mir::ProjectionElem::Field(fi, _) => Some(fi.as_usize()),
                _ => None,
            })
            .collect();
        // A bare `&local` (no projection) exposes the pointee's whole field
        // map. Only propagate fields that carry provenance (pointer leaves);
        // plain scalar fields (e.g. array elements) must not leak into the
        // reference or they can corrupt downstream InBound reasoning.
        let empty_proj = source_place.projection.is_empty();
        let keys: Vec<Vec<usize>> = self
            .field_values
            .keys()
            .filter(|(l, _)| *l == source_place.local)
            .map(|(_, p)| p.clone())
            .collect();
        for path in keys {
            let matches_prefix = field_prefix.is_empty()
                || (path.len() > field_prefix.len()
                    && path[..field_prefix.len()] == field_prefix[..]);
            if matches_prefix {
                let rest = if field_prefix.is_empty() {
                    path.clone()
                } else {
                    path[field_prefix.len()..].to_vec()
                };
                if let Some(v) = self
                    .field_values
                    .get(&(source_place.local, path.clone()))
                    .cloned()
                {
                    if empty_proj && v.provenance.is_none() {
                        continue;
                    }
                    self.set_field_value(dest, rest, v);
                }
            }
        }
    }

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
        // Copy per-byte tracking from source alloc to ref's alloc.
        self.copy_byte_tracking(src_alloc_id, ref_alloc_id);
    }

    /// Return the per-field types for an aggregate's operands.
    fn aggregate_field_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _len) => {
                // We don't need the exact count — just the element type for size
                vec![*elem_ty]
            }
            rustc_middle::ty::TyKind::Tuple(elems) => elems.iter().collect(),
            rustc_middle::ty::TyKind::Adt(adt_def, substs) => {
                if adt_def.is_enum() {
                    return vec![];
                }
                let variant = adt_def.non_enum_variant();
                variant
                    .fields
                    .iter()
                    .map(|f| crate::helpers::mir_utils::field_ty(self.tcx, f, substs))
                    .collect()
            }
            _ => vec![],
        }
    }
}

/// Whether any atom in this (possibly compound) property is a hazard
/// (`ContractKind::Hazard`), which the caller explicitly opts into.
fn contains_hazard<'tcx>(property: &Property<'tcx>) -> bool {
    if property.contract_kind() == ContractKind::Hazard {
        return true;
    }
    match property {
        Property::And(and) => and.conjuncts.iter().any(|p| contains_hazard(p)),
        Property::Or(or) => or.disjuncts.iter().any(|p| contains_hazard(p)),
        Property::Atom(_) => false,
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
