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
    ty::{Region, Ty},
};
use z3::ast::{Ast, Bool, Int};

use crate::{
    compat::{FxHashMap, FxHashSet},
    verify::{
        contract::{ContractExpr, ContractKind, PlaceBase, Property, PropertyArg, PropertyKind},
        def_use::PlaceKey,
        slicer::RelevantItem,
    },
};

use super::state::{
    AllocId, ContentTy, ValueSource, OffsetKind, Provenance, ValueInvariants, VmState,
    VmValue,
};

use crate::verify::api_classify;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
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
                    self.exec_statement(statement);
                }
                RelevantItem::Terminator { def_id, block, switch_succ } => {
                    let body = self.tcx.optimized_mir(*def_id);
                    let terminator = body.basic_blocks[*block].terminator();
                    self.exec_terminator(terminator, *switch_succ);
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
                RelevantItem::UnknownCall => {}
            }
        }
    }

    /// Enter an inlined callee during path execution: save the caller context,
    /// switch to the callee body, and bind the caller's argument locals to the
    /// callee's parameters.
    fn handle_callee_entry(&mut self, callee: DefId, arg_locals: &[usize]) {
        let frame = self.save_frame();

        // Collect the caller argument fields from the saved map, so the callee's
        // parameters inherit them (e.g. NonZero's non-zero inner value, and an
        // iterator's `ptr`/`end_or_len`). A whole-place reborrow
        // (`_7 = &mut (*_1)`) carries its referent's fields, so resolve it too;
        // likewise a whole-place copy temporary (`_2 = copy _1`) that the
        // optimizer inserted between the caller's argument and the inlined
        // callee's parameter — follow both chains so the local that actually
        // materialized the fields is found.
        let mut arg_fields: Vec<(usize, Vec<usize>, VmValue<'z3, 'tcx>)> = Vec::new();
        for (i, arg) in arg_locals.iter().enumerate() {
            let caller_local = Local::from_usize(*arg);
            let mut source_locals: Vec<(Local, Vec<usize>)> = Vec::new();
            let mut seen: FxHashSet<(Local, Vec<usize>)> = FxHashSet::default();
            let mut stack = vec![(caller_local, Vec::new())];
            while let Some((cur, prefix)) = stack.pop() {
                if !seen.insert((cur, prefix.clone())) {
                    continue;
                }
                source_locals.push((cur, prefix.clone()));
                if let Some(r) = self.find_whole_reborrow_referent(cur) {
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
                let keys: Vec<Vec<usize>> = frame
                    .field_values
                    .keys()
                    .filter(|(l, f)| {
                        *l == src
                            && (prefix.is_empty()
                                || (f.len() >= prefix.len() && f[..prefix.len()] == prefix[..]))
                    })
                    .map(|(_, f)| f.clone())
                    .collect();
                for fields in keys {
                    if let Some(fv) = frame
                        .field_values
                        .get(&(src, fields.clone()))
                        .cloned()
                    {
                        let stripped = if prefix.is_empty() {
                            fields
                        } else {
                            fields[prefix.len()..].to_vec()
                        };
                        arg_fields.push((i + 1, stripped, fv));
                    }
                }
            }
        }

        self.current_frame.current_def_id = callee;

        for (i, arg) in arg_locals.iter().enumerate() {
            if let Some(v) = frame.local_values.get(&Local::from_usize(*arg)).cloned() {
                self.set_local(Local::from_usize(i + 1), v);
            }
        }

        for (callee_param, fields, fv) in arg_fields {
            self.set_field_value(Local::from_usize(callee_param), fields, fv);
        }

        self.caller_frames.push(frame);
    }

    /// Exit an inlined callee: capture the callee's return value, restore the
    /// caller context, and write the return value to the caller's destination.
    fn handle_callee_exit(&mut self, dest: usize) {
        let ret = self.current_frame.local_values.get(&Local::from_usize(0)).cloned();
        let ret_fields: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = self
            .current_frame
            .field_values
            .iter()
            .filter(|((l, _), _)| *l == Local::from_usize(0))
            .map(|((_, f), v)| (f.clone(), v.clone()))
            .collect();
        if let Some(frame) = self.caller_frames.pop() {
            self.restore_frame(frame);
        }
        if let Some(mut v) = ret {
            let dest_ty = self.body().local_decls[Local::from_usize(dest)].ty;
            v.ty = dest_ty;
            // Infer invariants: a non-null provenance with offset 0 means the
            // return value is valid and initialized.
            if let Some(ref prov) = v.provenance {
                if prov.offset.as_u64() == Some(0) {
                    v.invariants.non_null = true;
                    v.invariants.init = true;
                    self.alloc_mut(prov.alloc_id).initialized = true;
                }
            }
            self.set_local(Local::from_usize(dest), v);
            // The callee returned a fully-constructed value, so the caller's
            // destination stack slot is initialized.
            if let Some(dest_alloc_id) = self.current_frame.local_alloc.get(&Local::from_usize(dest)).copied()
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
        let arg_count = self.body().arg_count;
        let local_count = self.body().local_decls.len();

        // Pre-allocate ALL locals and set initial values
        for local_idx in 1..local_count {
            let local = Local::from_usize(local_idx);
            if self.current_frame.local_values.contains_key(&local) {
                continue;
            }
            let decl = &self.body().local_decls[local];
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
                        let heap_size = self.size_of_ty(heap_ty);
                        let heap_align = self.align_sym(heap_ty);
                        let heap_size_term = Int::from_u64(self.z3_ctx, heap_size.max(1));
                        // Vec/CString can hold many elements — use an external
                        // allocation so Allocated checks can pass for arbitrary
                        // capacity queries.
                        let (heap_alloc_id, heap_base) = if is_vec {
                            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                            let (id, base) =
                                self.allocate_external(max_size, heap_align.clone(), Some(heap_ty));
                            (id, base)
                        } else {
                            self.allocate(heap_size_term, heap_align, Some(heap_ty))
                        };
                        invariants.non_null = true;
                        invariants.init = true;
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
                                z3_term: heap_base.clone(),
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: heap_alloc_id,
                                    offset: Int::from_u64(self.z3_ctx, 0),
                                    offset_kind: None,
                                }),
                                invariants: ValueInvariants {
                                    non_null: true,
                                    init: true,
                                    ..Default::default()
                                },
                                source: ValueSource::None,
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
                            self.materialize_vec_len_cap(local, cap, len, heap_size);
                        }
                        self.set_local(
                            local,
                            VmValue {
                                z3_term: heap_base,
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: heap_alloc_id,
                                    offset: Int::from_u64(self.z3_ctx, 0),
                                    offset_kind: None,
                                }),
                                invariants,
                                source: ValueSource::None,
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
                                z3_term: term,
                                ty,
                                provenance: None,
                                invariants,
                                source: ValueSource::None,
                            },
                        );
                        continue;
                    }
                    let variant = adt_def.non_enum_variant();
                    let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)> =
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
                                        z3_term: field_term,
                                        ty: field_ty,
                                        provenance: None,
                                        invariants: ValueInvariants {
                                            init: true,
                                            ..Default::default()
                                        },
                                        source: ValueSource::None,
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
                                    z3_term: field_term,
                                    ty: field_ty,
                                    provenance: None,
                                    invariants: ValueInvariants {
                                        init: true,
                                        ..Default::default()
                                    },
                                    source: ValueSource::None,
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
                        if let Some(f0) = self.field_value(local, &[0]).cloned() {
                            let prov = f0.provenance.clone();
                            self.set_local(
                                local,
                                VmValue {
                                    z3_term: f0.z3_term,
                                    ty,
                                    provenance: prov,
                                    invariants: ValueInvariants {
                                        init: true,
                                        ..Default::default()
                                    },
                                    source: ValueSource::None,
                                },
                            );
                            continue;
                        }
                    }
                    let term = self.fresh_int(&format!("param_{}", local_idx));
                    self.set_local(
                        local,
                        VmValue {
                            z3_term: term,
                            ty,
                            provenance: None,
                            invariants: ValueInvariants {
                                init: true,
                                ..Default::default()
                            },
                            source: ValueSource::None,
                        },
                    );
                    continue;
                }
                // ── Reference parameter (&T, &mut T) ──
                // Create a symbolic allocation for the pointee and attach
                // provenance so that pointer-deriving operations (as_ptr,
                // add, etc.) propagate correctly.
                if let rustc_middle::ty::TyKind::Ref(..) = ty.kind() {
                    // Prefer the precise pointee type from the function
                    // signature (late-bound-liberated) so reference-field regions
                    // are `'a` rather than MIR's erased `ReErased`.
                    let precise_pointee = (local_idx <= arg_count)
                        .then(|| {
                            crate::verify::vm::region::fn_arg_ty(
                                self.tcx,
                                self.current_frame.current_def_id,
                                local_idx - 1,
                            )
                        })
                        .flatten()
                        .and_then(|precise_ty| match precise_ty.kind() {
                            rustc_middle::ty::TyKind::Ref(_, inner, _) => Some(*inner),
                            _ => None,
                        });
                    let pointee_ty = precise_pointee.unwrap_or_else(|| {
                        if let rustc_middle::ty::TyKind::Ref(_, inner_ty, _) = ty.kind() {
                            *inner_ty
                        } else {
                            ty
                        }
                    });
                    // `&MaybeUninit<T>` / `&[MaybeUninit<T>]` carry no validity
                    // invariant — the content need not be initialized — so do not
                    // claim `Init` for them (the content property reduces to
                    // `Typed`).
                    let pointee_is_maybe_uninit = api_classify::is_maybe_uninit_ty(pointee_ty);

                    invariants.non_null = true;
                    if !pointee_is_maybe_uninit {
                        invariants.init = true;
                    }
                    // A reference always points within a live allocation, so it
                    // carries the pointer-validity facts (`NonNull`, `Allocated`,
                    // `InBound`) explicitly — the content property `Init` must
                    // not be the only source of pointer validity (see
                    // std-subsumption.rs).
                    invariants.in_bounds = true;

                    if let rustc_middle::ty::TyKind::Slice(elem_ty) = pointee_ty.kind() {
                        let elem_size = self.size_of_ty(*elem_ty);
                        let len = self.fresh_int(&format!("slice_len_{}", local_idx));
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        self.constraints.assertions.push(len.ge(&zero));
                        let isize_max = Int::from_i64(self.z3_ctx, i64::MAX);
                        let elem_sz = if elem_size > 0 {
                            elem_size
                        } else {
                            crate::helpers::mir_utils::size_of_generic_param(
                                self.tcx,
                                self.current_frame.current_def_id,
                                *elem_ty,
                            )
                            .max(1)
                        };
                        let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
                        self.constraints.assertions
                            .push(Int::mul(self.z3_ctx, &[&len, &elem_sz_term]).le(&isize_max));
                        // The data allocation's byte size uses the shared
                        // symbolic `sizeof_T` so `InBound` can cancel the factor
                        // (`len·S / S == len`); `allocate_slice` computes
                        // `size = len * sizeof_T` and materializes `len` together
                        // so the two can never diverge. The alignment is the
                        // element type's alignment — symbolic (`align_T`) for a
                        // generic element type, with the layout constraint
                        // `sizeof_T % align_T == 0` established by `align_sym`.
                        let elem_align = self.align_sym(*elem_ty);
                        let elem_size_sym = self.size_sym(*elem_ty);
                        let (data_alloc_id, data_base) =
                            self.allocate_slice(len, elem_size_sym, elem_align, Some(*elem_ty));
                        if !pointee_is_maybe_uninit {
                            self.alloc_mut(data_alloc_id).initialized = true;
                        }
                        // Record placeholder per-byte symbols for the first few
                        // elements so byte-level checkers (`ValidCStr` interior-NUL,
                        // `ValidString` UTF-8) can reason over symbolic slice bytes
                        // (the length is symbolic, so only a bounded prefix is
                        // materialized — mirrors the array parameter handling).
                        let step = (elem_size.max(1)) as usize;
                        let m = 16usize;
                        for i in 0..m {
                            let off = i * step;
                            let elem_term =
                                self.fresh_int(&format!("slice_{}_idx_{}", local_idx, i));
                            self.record_byte_value(data_alloc_id, off, elem_term);
                        }
                        self.set_local(
                            local,
                            VmValue {
                                z3_term: data_base,
                                ty,
                                provenance: Some(Provenance {
                                    alloc_id: data_alloc_id,
                                    offset: Int::from_u64(self.z3_ctx, 0),
                                    offset_kind: None,
                                }),
                                invariants,
                                source: ValueSource::None,
                            },
                        );
                        continue;
                    }

                    // Non-slice reference: allocate pointee.  A generic `T`
                    // yields `sizeof_T`; a struct with a generic field is summed
                    // (`struct_size_sym`) so a field reference can be discharged.
                    let pointee_align = self.align_sym(pointee_ty);
                    let pointee_size_term = self
                        .struct_size_sym(pointee_ty)
                        .unwrap_or_else(|| self.size_sym(pointee_ty));
                    let (pointee_alloc_id, pointee_base) =
                        self.allocate(pointee_size_term, pointee_align, Some(pointee_ty));
                    if !pointee_is_maybe_uninit {
                        self.alloc_mut(pointee_alloc_id).initialized = true;
                    }
                    self.set_local(
                        local,
                        VmValue {
                            z3_term: pointee_base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id: pointee_alloc_id,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            }),
                            invariants,
                            source: ValueSource::None,
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
                            let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)> =
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
                                } else if let rustc_middle::ty::TyKind::Ref(region, pointee, _) =
                                    field_ty.kind()
                                {
                                    // Field contains a reference (&T, &mut T, &[T], etc.).
                                    // Give it provenance so that as_ptr() / as_mut_ptr()
                                    // on the field propagates the allocation info.
                                    let elem_ty = match pointee.kind() {
                                        rustc_middle::ty::TyKind::Slice(e) => *e,
                                        _ => *pointee,
                                    };
                                    self.materialize_external_field(
                                        local, idx, field_ty, elem_ty, Some(*region),
                                    );
                                } else if let rustc_middle::ty::TyKind::Slice(elem_ty) =
                                    field_ty.kind()
                                {
                                    // DST slice field (e.g. `CStr { inner: [u8] }`):
                                    // model it as an external allocation so its length
                                    // stays symbolic instead of defaulting to a single
                                    // element (which would make `inner.len()` == 1).
                                    self.materialize_external_field(
                                        local, idx, field_ty, *elem_ty, None,
                                    );
                                } else if let rustc_middle::ty::TyKind::Adt(adt, substs) =
                                    field_ty.kind()
                                {
                                    // A heap-backed smart-pointer field (`Box<[T]>`,
                                    // `Vec<T>`) inside a referenced struct: materialize
                                    // the pointee allocation so field access (e.g.
                                    // `self.buckets.iter()`) resolves to the *data*
                                    // elements, not the whole struct.
                                    if api_classify::is_std_box(adt.did())
                                        || api_classify::is_std_vec(adt.did())
                                    {
                                        if let Some(pointee) =
                                            substs.first().and_then(|s| s.as_type())
                                        {
                                            let elem_ty = match pointee.kind() {
                                                rustc_middle::ty::TyKind::Slice(e) => *e,
                                                _ => pointee,
                                            };
                                            self.materialize_external_field(
                                                local, idx, field_ty, elem_ty, None,
                                            );
                                        }
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
                                            z3_term: field_term,
                                            ty: field_ty,
                                            provenance: None,
                                            invariants: ValueInvariants {
                                                init: true,
                                                ..Default::default()
                                            },
                                            source: ValueSource::None,
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
                            z3_term: val,
                            ty,
                            provenance: None,
                            invariants,
                            source: ValueSource::None,
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
                    let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                    let pointee_align = self.align_sym(*pointee);
                    let (alloc_id, base) =
                        self.allocate_external(max_size, pointee_align, Some(*pointee));
                    self.set_local(
                        local,
                        VmValue {
                            z3_term: base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            }),
                            invariants,
                            source: ValueSource::None,
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
                        crate::helpers::mir_utils::eval_array_len(self.tcx, const_len)
                            .map(|v| v as usize);
                    let elem_size = self.size_of_ty(*elem_ty);
                    let step = (elem_size.max(1)) as usize;
                    let align = self.align_sym(*elem_ty);
                    // Symbolic-aware element size: a generic `T` gets `sizeof_T`
                    // (≥ 1) so the allocation is `N·sizeof_T` bytes, not `N`.
                    let elem_sym = self.size_sym(*elem_ty);
                    // Materialized element count (the array length `N`).
                    let n_term = match n {
                        Some(v) => Int::from_u64(self.z3_ctx, v as u64),
                        None => {
                            let const_text =
                                format!("Ty({:?}, {:?})", self.tcx.types.usize, const_len);
                            let name =
                                format!("const_{}", const_text.replace([':', '#', ' '], "_"));
                            Int::new_const(self.z3_ctx, name.as_str())
                        }
                    };
                    let (alloc_id, base) = if let Some(n) = n {
                        let total =
                            Int::mul(self.z3_ctx, &[&Int::from_u64(self.z3_ctx, n as u64), &elem_sym]);
                        self.allocate(total, align.clone(), Some(*elem_ty))
                    } else {
                        // Generic N: unbounded external allocation
                        let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                        self.allocate_external(max_size, align, Some(*elem_ty))
                    };
                    self.alloc_mut(alloc_id).set_slice_len(n_term);
                    self.alloc_mut(alloc_id).initialized = true;
                    self.current_frame.local_alloc.insert(local, alloc_id);
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
                            z3_term: base,
                            ty,
                            provenance: Some(Provenance {
                                alloc_id,
                                offset: Int::from_u64(self.z3_ctx, 0),
                                offset_kind: None,
                            }),
                            invariants: ValueInvariants {
                                init: true,
                                ..invariants
                            },
                            source: ValueSource::None,
                        },
                    );
                    continue;
                }
                // ── Struct / other parameter ──
                let term = self.fresh_int(&format!("param_{}", local_idx));
                self.set_local(
                    local,
                    VmValue {
                        z3_term: term,
                        ty,
                        provenance: None,
                        invariants,
                        source: ValueSource::None,
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
                    z3_term: term,
                    ty,
                    provenance: None,
                    invariants,
                    source: ValueSource::None,
                },
            );
        }

        // Entry-block provenance propagation: scan the first basic block
        // for simple assignments that propagate parameter values.  This
        // helps when the backward slicer omits same-block definitions
        // (e.g. `_tmp = _1 as *const T`).  Limiting to the entry block
        // ensures only unconditionally-executed assignments are covered.
        if let Some(entry_bb) = self.body().basic_blocks.iter().next() {
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
                        if let Some(src_val) = self.current_frame.local_values.get(&src_local) {
                            let has_better_prov = src_val.is_pointer()
                                && src_val.invariants.non_null
                                && self.current_frame.local_values.get(&dest_local).is_none_or(|d| {
                                    d.provenance.is_none() || !d.invariants.non_null
                                });
                            if has_better_prov {
                                self.set_local(
                                    dest_local,
                                    VmValue {
                                        z3_term: src_val.z3_term.clone(),
                                        ty: dest.ty(self.body(), self.tcx).ty,
                                        provenance: src_val.provenance.clone(),
                                        invariants: src_val.invariants.clone(),
                                        source: ValueSource::None,
                                    },
                                );
                            }
                        }
                    }
                }
            }
        }

        // Pre-warm a shared symbolic `sizeof_T` / `align_T` for every generic type
        // parameter of the caller.  Warming every declared type parameter (not
        // just those in the signature) makes the read-only `*_sym_read` fallback
        // dead.
        let mut warmed: FxHashSet<Ty<'tcx>> = FxHashSet::default();
        for param in self.tcx.generics_of(self.current_frame.current_def_id).own_params.iter() {
            if let rustc_middle::ty::GenericParamDefKind::Type { .. } = param.kind {
                warmed.insert(rustc_middle::ty::Ty::new_param(
                    self.tcx,
                    param.index,
                    param.name,
                ));
            }
        }
        for ty in warmed {
            self.size_sym(ty);
            self.align_sym(ty);
        }
    }

    /// Materialize a struct field holding a reference (`&T` / `&[T]`), a DST
    /// slice (`[T]`), or a heap-backed smart pointer (`Box`/`Vec`) as an external
    /// allocation, so field access (e.g. `self.buckets.iter()`, `as_ptr()`)
    /// resolves to the *data* rather than the whole struct. The caller
    /// pre-computes `elem_ty` (the pointee / slice element). `alive_region`
    /// carries the lifetime of a reference field (`&'a T`), marking its
    /// referent alive for `'a` (a reference guarantees its referent is alive);
    /// a raw slice / `Box` / `Vec` field carries no such guarantee and passes
    /// `None`.
    fn materialize_external_field(
        &mut self,
        local: Local,
        idx: usize,
        field_ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        alive_region: Option<Region<'tcx>>,
    ) {
        let align = self.align_sym(elem_ty);
        let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
        let (alloc_id, base) = self.allocate_external(max_size, align, Some(elem_ty));
        self.alloc_mut(alloc_id).initialized = true;
        if let Some(region) = alive_region {
            self.alloc_mut(alloc_id).liveness = Some(region);
        }
        self.set_field_value(
            local,
            vec![idx],
            VmValue {
                z3_term: base,
                ty: field_ty,
                provenance: Some(Provenance {
                    alloc_id,
                    offset: Int::from_u64(self.z3_ctx, 0),
                    offset_kind: None,
                }),
                invariants: ValueInvariants {
                    non_null: true,
                    init: true,
                    ..Default::default()
                },
                source: ValueSource::None,
            },
        );
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
        elem_alloc: &mut FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)>,
        is_raw_ptr: bool,
        nn_fresh_prefix: &str,
    ) {
        // A `NonNull<T>` guarantees its inner pointer is aligned to `T`; a raw
        // pointer carries no such guarantee.
        let align_n = if is_raw_ptr {
            None
        } else {
            Some(self.align_sym(pointee))
        };
        let invariants = if is_raw_ptr {
            // A raw pointer carries no non-null / init / align guarantee; those
            // facts must come from the struct's own `#[rapx::invariant]`s.
            ValueInvariants::default()
        } else {
            ValueInvariants {
                init: true,
                align_n,
                ..Default::default()
            }
        };
        // Only raw-pointer fields (e.g. `Iter::end_or_len = ptr + len·sizeof_T`)
        // reuse the shared per-pointee-type allocation. A `NonNull<T>` field
        // names a *distinct* heap object (e.g. each `NodeRef.node` points at its
        // own leaf), so it must get its own allocation rather than a symbolic
        // offset into a sibling's — otherwise `left_child.node` and
        // `right_child.node` would alias the same `LeafNode`, losing the per-node
        // `Init`/`Allocated` provenance.
        if is_raw_ptr && let Some(&(existing_alloc, ref base)) = elem_alloc.get(&pointee) {
            // Byte-accurate element size (`sizeof_T` for a generic `T`) so the
            // field's offset is a multiple of `align_T` (via the layout
            // constraint `sizeof_T % align_T == 0` established by `align_sym`).
            // A raw pointer field that reuses the aligned base allocation is
            // therefore itself `align_T`-aligned (e.g. `Iter::end_or_len`,
            // `ptr + len·sizeof_T`).
            let elem_align = self.align_sym(pointee);
            let elem_size = self.size_sym(pointee);
            let len_term = self.fresh_int(&format!("field_len_{}_{}", local_idx, idx));
            self.constraints.assertions
                .push(len_term.ge(&Int::from_u64(self.z3_ctx, 0)));
            let prost_offset = Int::mul(self.z3_ctx, &[&len_term, &elem_size]);
            let field_term = Int::add(self.z3_ctx, &[base, &prost_offset]);
            let mut invariants = invariants;
            if is_raw_ptr {
                invariants.align_n = Some(elem_align);
            }
            self.set_field_value(
                local,
                path,
                VmValue {
                    z3_term: field_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: existing_alloc,
                        offset: prost_offset.clone(),
                        offset_kind: Some(OffsetKind::Element(len_term.clone())),
                    }),
                    invariants,
                    source: ValueSource::None,
                },
            );
        } else {
            // A raw pointer carries no alignment or size guarantee for its
            // target, so the external allocation is created with alignment 1 and
            // a *symbolic* (unknown) size.  A `NonNull`/`Box` pointee, by
            // contrast, is genuinely aligned and keeps the concrete `i64::MAX`
            // "unbounded" size.
            let field_align = if is_raw_ptr {
                Int::from_u64(self.z3_ctx, 1)
            } else {
                self.align_sym(pointee)
            };
            let max_size = if is_raw_ptr {
                let s = self.fresh_int("raw_target_size");
                self.constraints.assertions.push(s.ge(&Int::from_u64(self.z3_ctx, 0)));
                s
            } else {
                Int::from_u64(self.z3_ctx, i64::MAX as u64)
            };
            let (field_alloc_id, field_base) =
                self.allocate_external(max_size, field_align, Some(pointee));
            elem_alloc.insert(pointee, (field_alloc_id, field_base.clone()));
            // Decompose the pointee's own fields into per-allocation tracking
            // so `(*ptr).field` derefs resolve to the field value (not the raw
            // pointer term). This is what lets `&*NonNull<LeafNode>` expose
            // `LeafNode.len`.
            self.decompose_pointee_fields(
                field_alloc_id,
                Vec::new(),
                pointee,
                pointee,
                local_idx,
                0,
            );
            // A `NonNull`/`Box` pointee is a valid value of `pointee`, so its
            // struct invariants (`ValidNum(len <= CAPACITY)` on `LeafNode`)
            // hold for the freshly-decomposed allocation.  Raw pointers carry no
            // such guarantee and are skipped.
            if !is_raw_ptr {
                self.assert_alloc_pointee_invariants(field_alloc_id, pointee);
            }
            let field_term = if is_raw_ptr {
                field_base
            } else {
                self.fresh_int(&format!("{}_{}_{}", nn_fresh_prefix, local_idx, idx))
            };
            self.set_field_value(
                local,
                path,
                VmValue {
                    z3_term: field_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: field_alloc_id,
                        offset: Int::from_u64(self.z3_ctx, 0),
                        offset_kind: None,
                    }),
                    invariants,
                    source: ValueSource::None,
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
        elem_alloc: &mut FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)>,
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
                        z3_term: field_term,
                        ty: field_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
            }
        }
    }

    /// Recursively decompose a pointee ADT's fields into per-allocation field
    /// tracking, mirroring [`decompose_adt_fields`](Self::decompose_adt_fields)
    /// but keyed by allocation instead of local. This is what lets a
    /// `&*NonNull<LeafNode>` dereference resolve `(*leaf).len` to the actual
    /// `len` field value rather than the raw pointer term.
    fn decompose_pointee_fields(
        &mut self,
        alloc_id: AllocId,
        prefix: Vec<usize>,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        local_idx: usize,
        depth: usize,
    ) {
        use rustc_middle::ty::TyKind;
        if depth > 4 {
            return;
        }
        let TyKind::Adt(adt_def, substs) = ty.kind() else {
            return;
        };
        if adt_def.is_enum() {
            return;
        }
        let variant = adt_def.non_enum_variant();
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
            let mut path = prefix.clone();
            path.push(idx);
            if let Some(pointee) = self.find_nn_pointee(field_ty) {
                let field_align = self.align_sym(pointee);
                let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                let (fa, _fb) = self.allocate_external(max_size, field_align, Some(pointee));
                self.alloc_mut(fa).initialized = true;
                let term = self.fresh_int(&format!("pointee_nn_{}_{}", local_idx, idx));
                self.memory.fields.insert(
                    (alloc_id, root_ty, path.clone()),
                    VmValue {
                        z3_term: term,
                        ty: field_ty,
                        provenance: Some(Provenance {
                            alloc_id: fa,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        invariants: ValueInvariants {
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
                self.decompose_pointee_fields(
                    fa,
                    Vec::new(),
                    pointee,
                    pointee,
                    local_idx,
                    depth + 1,
                );
            } else if let TyKind::Adt(_, _) = field_ty.kind() {
                self.decompose_pointee_fields(
                    alloc_id,
                    path,
                    field_ty,
                    root_ty,
                    local_idx,
                    depth + 1,
                );
            } else if matches!(
                field_ty.kind(),
                TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char
            ) {
                let field_term = self.fresh_int(&format!("pointee_field_{}_{}", local_idx, idx));
                self.memory.fields.insert(
                    (alloc_id, root_ty, path.clone()),
                    VmValue {
                        z3_term: field_term,
                        ty: field_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
            } else if let TyKind::Array(elem_ty, const_len) = field_ty.kind() {
                // Array field: allocate its contents so `.len()` / `as_slice()`
                // resolve to the concrete array length.
                let n = crate::helpers::mir_utils::eval_array_len(self.tcx, const_len).unwrap_or(0)
                    as u64;
                let arr_align = self.align_sym(*elem_ty);
                let arr_elem_size = self.size_sym(*elem_ty);
                // Materialize the array length (via `allocate_slice`) so `len()`
                // reads the constant `n` directly rather than `size / elem_size`,
                // which is ill-defined when the element type is a generic ZST
                // (`elem_size = 0`).
                let (fa, fb) = self.allocate_slice(
                    Int::from_u64(self.z3_ctx, n),
                    arr_elem_size,
                    arr_align,
                    Some(*elem_ty),
                );
                self.alloc_mut(fa).initialized = true;
                self.memory.fields.insert(
                    (alloc_id, root_ty, path.clone()),
                    VmValue {
                        z3_term: fb,
                        ty: field_ty,
                        provenance: Some(Provenance {
                            alloc_id: fa,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        invariants: ValueInvariants {
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
            }
        }
    }

    // ── Statement executors ──────────────────────────────────────

    pub(crate) fn exec_statement(&mut self, statement: &Statement<'tcx>) {
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
            _ => {}
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
            // On a whole-place move (`_3 = move _4`), ownership moves to `dest`:
            // invalidate `source`'s owner-field provenance so a later `Owning`
            // check does not treat the moved-out source as a second owner.
            let moved_from = match rvalue {
                #[cfg(rapx_rvalue_use_with_retag)]
                Rvalue::Use(operand, _) => match operand {
                    Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                    _ => None,
                },
                #[cfg(not(rapx_rvalue_use_with_retag))]
                Rvalue::Use(operand) => match operand {
                    Operand::Move(p) if p.projection.is_empty() => Some(p.local),
                    _ => None,
                },
                _ => None,
            };
            if let Some(src) = moved_from {
                self.invalidate_owner_field(src);
            }
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
                // Also propagate for a leading `Deref` (`_3 = copy (*_1)`): the
                // source is the pointee of a reference, whose per-field values
                // are keyed by the reference local itself, so copying the pointee
                // value into a fresh local must carry those field values along
                // (otherwise `into_leaf(self)`'s `self.node` provenance is lost).
                let has_deref_src = sp
                    .projection
                    .iter()
                    .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
                let only_field_deref = sp.projection.iter().all(|p| {
                    matches!(
                        p.kind(),
                        rustc_middle::mir::ProjectionElem::Field(..)
                            | rustc_middle::mir::ProjectionElem::Deref
                    )
                });
                if only_field || (only_field_deref && has_deref_src) {
                    let keys: Vec<Vec<usize>> = self
                        .current_frame
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
        } else {
            // Deref projection (`(*ptr).field = val`): resolve the referent
            // local and write the field there, so `&mut self` setters
            // (`set_len`, `clear`, …) actually update the referent's
            // materialized fields instead of being silently dropped.
            //
            // A pure `*ptr = val` (no trailing Field) still must NOT overwrite
            // the pointer local — writing through a pointer should not reassign
            // the pointer variable.
            let mut proj = place.projection.iter();
            if matches!(
                proj.next().map(|p| p.kind()),
                Some(rustc_middle::mir::ProjectionElem::Deref)
            ) {
                let field_indices: Vec<usize> = proj
                    .filter_map(|p| match p.kind() {
                        rustc_middle::mir::ProjectionElem::Field(idx, _) => Some(idx.as_usize()),
                        _ => None,
                    })
                    .collect();
                if !field_indices.is_empty() {
                    // `&mut self` (and other reference parameters) materialize
                    // their pointee's scalar fields keyed by the *reference*
                    // local itself, so a `(*self).field = val` write must land
                    // in `field_values[(self, field)]` directly.  (This is what
                    // makes a struct-invariant re-proof see `self.len += 1`.)
                    if self.field_value(place.local, &field_indices).is_some() {
                        let is_iter_field = field_indices == [0];
                        let mut write_value = value;
                        write_value.invariants.init = true;
                        self.set_field_value(place.local, field_indices, write_value);
                        if is_iter_field {
                            self.track_iter_ptr_update(place.local);
                        }
                        return;
                    }
                    // Otherwise resolve the dereferenced pointer (a
                    // reference/reborrow temp) back to the local it points at,
                    // matching its address term against the known local
                    // addresses.
                    let pointed = self.current_frame.local_values.get(&place.local).cloned();
                    if let Some(pointed) = pointed {
                        if let Some(referent) = self.find_local_by_address(&pointed.z3_term) {
                            let mut write_value = value;
                            write_value.invariants.init = true;
                            self.set_field_value(referent, field_indices, write_value);
                        } else if let Some(arg_idx) = place.local.as_usize().checked_sub(1) {
                            // Inline frame: the caller's address map is saved
                            // away, so resolve through the precomputed
                            // `&mut self` referent and defer the write until the
                            // caller's `field_values` is restored.
                            if let Some(referent) =
                                self.inline.arg_referents.get(arg_idx).copied().flatten()
                            {
                                self.inline.deferred_field_writes
                                    .push((referent, field_indices, value));
                            }
                        }
                    }
                }
            }
        }
        // For deref projections (`*ptr = val`): do NOT overwrite the base local.
        // Writing through a pointer should not reassign the pointer variable.
    }

    /// Record byte-level values when assigning to a place with projections.
    /// This handles patterns like `buf[i] = 0u8` (nul-store) and `arr[i] = val`.
    fn record_projected_store(&mut self, place: &Place<'tcx>, value: &VmValue<'z3, 'tcx>) {
        // Prefer the value's provenance (pointee alloc) over slots
        // (reference alloc) for ref/ptr parameters.
        let Some(alloc_id) = self
            .current_frame.local_values
            .get(&place.local)
            .and_then(|v| v.provenance_alloc_id())
            .or_else(|| self.current_frame.local_alloc.get(&place.local).copied())
        else {
            return;
        };

        let value_ty = value.ty;
        let value_size = self.size_of_ty(value_ty) as usize;

        let mut byte_offset: usize = 0;
        let mut concrete = true;

        let base_ty = self.body().local_decls[place.local].ty;
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
                self.record_byte_value(alloc_id, byte_offset, value.z3_term.clone());
                if let Some(term_val) = value.z3_term.as_u64() {
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
    fn record_indexed_store_for_vm(&mut self, place: &Place<'tcx>, value: &VmValue<'z3, 'tcx>) {
        let is_u8 = matches!(
            value.ty.kind(),
            rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
        );
        if !is_u8 {
            return;
        }
        let has_index_with_concrete = place.projection.iter().any(|p| {
            if let rustc_middle::mir::ProjectionElem::Index(local) = p {
                self.current_frame.local_values
                    .get(&local)
                    .and_then(|v| v.z3_term.simplify().as_u64())
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
                self.record_byte_value(alloc_id, byte_offset, value.z3_term.clone());
                if let Some(term_val) = value.z3_term.as_u64() {
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
    fn inject_layout_constraints(&mut self, operand: &Operand<'tcx>, val: &VmValue<'z3, 'tcx>) {
        if let Operand::Constant(constant) = operand {
            let text = format!("{:?}", constant.const_);
            if crate::helpers::mir_utils::const_int_from_debug(&text).is_none() {
                let is_align_or_size = text.starts_with("AlignOf(") || text.starts_with("SizeOf(");
                if is_align_or_size {
                    let one = Int::from_u64(self.z3_ctx, 1);
                    self.constraints.assertions.push(val.z3_term.ge(&one));
                }
            }
        }
    }

    /// HACK: `slice::align_to_offsets` computes its element split via
    /// `const { gcd(size_of::<T>(), size_of::<U>()) }`. The recursive `gcd`
    /// const fn cannot be inlined, so the VM would otherwise model the result as
    /// a fresh, unconstrained constant and lose the one fact that makes the
    /// proof go through: the gcd *divides* both sizes. That divisibility is
    /// what turns `us = sizeof_T / gcd` / `ts = sizeof_U / gcd` into exact
    /// divisions, giving `us * sizeof_U == ts * sizeof_T` (both the lcm) and
    /// hence `us_len * sizeof_U <= len * sizeof_T`. Detect the `gcd` const
    /// block and re-establish `gcd`'s key consequences as path conditions. This
    /// is a targeted workaround for a missing general property of recursive
    /// const fns, not an `align_to`-specific effect.
    fn try_emit_gcd_divisibility(&mut self, operand: &Operand<'tcx>, val: &VmValue<'z3, 'tcx>) {
        let Operand::Constant(constant) = operand else {
            return;
        };
        let rustc_middle::mir::Const::Unevaluated(uneval, _) = constant.const_ else {
            return;
        };
        // Cheap gate: only a *promoted* const block can be a `gcd` const.
        let def_name = self.tcx.def_path_str(uneval.def);
        if !def_name.contains("::{constant") {
            return;
        }
        let body = self.tcx.mir_for_ctfe(uneval.def);
        let is_gcd = body.basic_blocks.iter().any(|bb| {
            if let rustc_middle::mir::TerminatorKind::Call { func, .. } = &bb.terminator().kind {
                if let Some(did) = crate::helpers::mir_utils::dep_callee_def_id(func) {
                    return self.tcx.def_path_str(did).ends_with("::gcd");
                }
            }
            false
        });
        if !is_gcd || uneval.args.len() < 2 {
            return;
        }
        let a = self.size_sym(uneval.args.type_at(0));
        let b = self.size_sym(uneval.args.type_at(1));
        let g = &val.z3_term;
        let zero = Int::from_u64(self.z3_ctx, 0);
        // `g = gcd(a, b)`:
        // 1. g divides both a and b.
        self.constraints.assertions.push(a.rem(g)._eq(&zero));
        self.constraints.assertions.push(b.rem(g)._eq(&zero));
        // 2. the lcm identity `(a / g) * b == (b / g) * a`. Emitting it directly
        //    (rather than letting Z3 derive it from the divisibility, which its
        //    incomplete nonlinear-integer solver cannot do reliably) is what
        //    makes `us * sizeof_U == ts * sizeof_T` — and hence
        //    `us_len * sizeof_U <= len * sizeof_T` — provable.
        let a_div_g = a.div(g);
        let b_div_g = b.div(g);
        let lhs = Int::mul(self.z3_ctx, &[&a_div_g, &b]);
        let rhs = Int::mul(self.z3_ctx, &[&b_div_g, &a]);
        self.constraints.assertions.push(lhs._eq(&rhs));
    }

    /// Evaluate an Rvalue into a VmValue.
    fn eval_rvalue(
        &mut self,
        dest_place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
    ) -> VmValue<'z3, 'tcx> {
        let dest_ty = dest_place.ty(self.body(), self.tcx).ty;

        match rvalue {
            #[cfg(rapx_rvalue_use_with_retag)]
            Rvalue::Use(operand, _retag) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                self.try_emit_gcd_divisibility(operand, &val);
                val
            }
            #[cfg(not(rapx_rvalue_use_with_retag))]
            Rvalue::Use(operand) => {
                let mut val = self.value_of_operand(operand);
                self.try_materialize_const_bytes(&mut val, operand);
                self.inject_layout_constraints(operand, &val);
                self.try_emit_gcd_divisibility(operand, &val);
                val
            }
            Rvalue::Ref(_, _borrow_kind, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr
                        .provenance
                        .as_ref()
                        .map(|p| self.alloc(p.alloc_id).align.clone())
                        .filter(|a| a.simplify().as_u64() != Some(1));
                    // Inherit in_bounds. For &[T] created via Deref of a
                    // fat raw ptr (inlined from_raw_parts), set in_bounds
                    // like ReturnFreshAllocation does in builtin_models.
                    let has_deref = place
                        .projection
                        .iter()
                        .any(|p| matches!(p.kind(), rustc_middle::mir::ProjectionElem::Deref));
                    let src_ty = self.body().local_decls[place.local].ty;
                    let is_from_raw_parts_like =
                        matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(_, _));
                    let is_slice_ref =
                        if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                            matches!(inner.kind(), rustc_middle::ty::TyKind::Slice(_))
                        } else {
                            false
                        };
                    let src_in_bounds = if is_slice_ref && is_from_raw_parts_like && has_deref {
                        addr.is_pointer()
                    } else {
                        self.current_frame.local_values
                            .get(&place.local)
                            .is_some_and(|v| v.invariants.in_bounds)
                    };
                    // An empty slice (`&[]` from `align_to`'s `offset > len` /
                    // ZST branch) is built as `&*dangling`: the dangling raw
                    // pointer (`NonNull::dangling`) is aligned to the *element*
                    // type, but its provenance here may reuse `self`'s allocation
                    // (whose align is that of `T`).  Record the element type's
                    // alignment so `check_align` can discharge it.
                    let slice_elem_align = if is_slice_ref && is_from_raw_parts_like && has_deref {
                        if let rustc_middle::ty::TyKind::Ref(_, inner, _) = dest_ty.kind() {
                            if let rustc_middle::ty::TyKind::Slice(elem) = inner.kind() {
                                let a = self.align_sym(*elem);
                                if a.simplify().as_u64() != Some(1) {
                                    Some(a)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let val = VmValue {
                        z3_term: addr.z3_term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            in_bounds: src_in_bounds,
                            align_n: slice_elem_align.or(alloc_align),
                        },
                        source: ValueSource::None,
                    };
                    self.propagate_byte_values_to_ref(place, &val);
                    self.propagate_field_values_to_ref(place, dest_place.local);
                    // Expose the freshly-created reference's provenance before
                    // asserting the pointee struct's `#[rapx::invariant]`s: the
                    // invariant predicates (`ValidNum(len <= CAPACITY)` on
                    // `&LeafNode`) resolve their field places through the
                    // pointee allocation, which needs `dest_place`'s provenance
                    // to be live (`exec_assign` only stores `val` afterwards).
                    self.set_local(dest_place.local, val.clone());
                    self.assert_pointee_struct_invariants(dest_ty, dest_place.local);
                    val
                } else {
                    let term = self.fresh_int("ref_addr");
                    VmValue {
                        z3_term: term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    }
                }
            }
            Rvalue::RawPtr(_, place) => {
                if let Some(addr) = self.address_of_place(place) {
                    let alloc_align = addr
                        .provenance
                        .as_ref()
                        .map(|p| self.alloc(p.alloc_id).align.clone())
                        .filter(|a| a.simplify().as_u64() != Some(1));
                    let source_in_bounds = self
                        .current_frame.local_values
                        .get(&place.local)
                        .is_some_and(|v| v.invariants.in_bounds);
                    VmValue {
                        z3_term: addr.z3_term,
                        ty: dest_ty,
                        provenance: addr.provenance,
                        invariants: ValueInvariants {
                            non_null: true,
                            in_bounds: source_in_bounds,
                            align_n: alloc_align,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    }
                } else {
                    let term = self.fresh_int("rawptr_addr");
                    VmValue {
                        z3_term: term,
                        ty: dest_ty,
                        provenance: None,
                        invariants: ValueInvariants {
                            non_null: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    }
                }
            }
            Rvalue::BinaryOp(op, pair) => {
                let (lhs_op, rhs_op) = &**pair;
                let lhs = self.value_of_operand(lhs_op);
                let rhs = self.value_of_operand(rhs_op);
                let term = self.eval_binary_op(*op, &lhs.z3_term, &rhs.z3_term);
                let provenance = self.provenance_for_binary_op(*op, &lhs, &rhs);
                let invariants = self.invariants_for_binary_op(*op, &lhs, &rhs, &provenance);
                let lhs_pk = crate::helpers::mir_utils::operand_place(lhs_op);
                let rhs_pk = crate::helpers::mir_utils::operand_place(rhs_op);
                // Carry the direct boolean condition alongside the ite-encoded
                // result so `switchInt`/`Assert` can record a precise path
                // condition (e.g. `offset <= len - 16`) instead of
                // `ite(cond, 1, 0) != 0`, which the SMT solver often fails to
                // unfold.
                let cmp_cond = self
                    .iter_ptr_comparison(*op, &lhs, &rhs)
                    .or_else(|| match *op {
                        BinOp::Le => Some(lhs.z3_term.le(&rhs.z3_term)),
                        BinOp::Lt => Some(lhs.z3_term.lt(&rhs.z3_term)),
                        BinOp::Ge => Some(lhs.z3_term.ge(&rhs.z3_term)),
                        BinOp::Gt => Some(lhs.z3_term.gt(&rhs.z3_term)),
                        BinOp::Eq => Some(lhs.z3_term._eq(&rhs.z3_term)),
                        BinOp::Ne => Some(lhs.z3_term._eq(&rhs.z3_term).not()),
                        _ => None,
                    });
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
                        &lhs.z3_term.div(&rhs.z3_term)
                    };
                    let rem = lhs.z3_term.rem(&rhs.z3_term);
                    let mul_term = Int::mul(self.z3_ctx, &[quot, &rhs.z3_term]);
                    let sum_term = Int::add(self.z3_ctx, &[&mul_term, &rem]);
                    self.constraints.assertions.push(lhs.z3_term._eq(&sum_term));
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    self.constraints.assertions.push(rem.ge(&zero));
                    // Remainder and quotient bounds help prove length constraints
                    // involving % and / in the SMT solver.
                    if rhs.z3_term.as_u64().is_none_or(|r| r >= 1) {
                        self.constraints.assertions.push(rem.lt(&rhs.z3_term));
                    }
                    self.constraints.assertions.push(rem.le(&lhs.z3_term));
                    self.constraints.assertions.push(quot.ge(&zero));
                    // Direct inequality: (lhs/rhs)*rhs <= lhs
                    self.constraints.assertions.push(mul_term.le(&lhs.z3_term));
                    // Quotient strict bound: for rhs >= 2 and lhs >= 2,
                    // quot + 1 <= lhs (hence quot < lhs). E.g. X/2 < X for X>1.
                    if rhs.z3_term.as_u64().is_some_and(|r| r >= 2) {
                        let one = Int::from_u64(self.z3_ctx, 1);
                        let qp1 = Int::add(self.z3_ctx, &[quot, &one]);
                        // qp1 <= lhs is equivalent to quot < lhs for integers
                        self.constraints.assertions.push(qp1.le(&lhs.z3_term));
                    } else {
                        // For rhs >= 1: quot <= lhs
                        if rhs.z3_term.as_u64().is_some_and(|r| r >= 1) {
                            self.constraints.assertions.push(quot.le(&lhs.z3_term));
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
                            z3_term: term.clone(),
                            ty: fields[0],
                            provenance: provenance.clone(),
                            invariants: invariants.clone(),
                            source: ValueSource::None,
                        };
                        self.set_field_value(dest_place.local, vec![0], result_val);
                        let overflow_term = self.fresh_int("overflow_flag");
                        let overflow_val = VmValue::new(overflow_term, fields[1]);
                        self.set_field_value(dest_place.local, vec![1], overflow_val);
                    }
                }
                VmValue {
                    z3_term: term,
                    ty: dest_ty,
                    provenance,
                    invariants,
                    source: match cmp_cond {
                        Some(cond) => ValueSource::Comparison {
                            lhs: lhs_pk,
                            rhs: rhs_pk,
                            op: *op,
                            cond,
                        },
                        None => ValueSource::BinaryOp {
                            lhs: lhs_pk,
                            rhs: rhs_pk,
                            op: *op,
                        },
                    },
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
                    self.eval_unary_op(*op, &val.z3_term, is_bool)
                };
                VmValue {
                    z3_term: term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                    source: ValueSource::None,
                }
            }
            Rvalue::Cast(_kind, operand, cast_ty) => {
                let src_val = self.value_of_operand(operand);
                let src_ty = src_val.ty;
                // A raw-pointer cast to a *different* ADT pointee reinterprets the
                // allocation's fields (e.g. `NonNull<LeafNode>::as_ptr() as *mut
                // InternalNode` in `NodeRef::as_internal_ptr`).  Lazily materialize
                // the target ADT's field view (keyed by type) so a later
                // `(*cast_ptr).field` resolves to the right field instead of the
                // original view's field at the same index.
                if let rustc_middle::ty::TyKind::RawPtr(target_ty, _) = cast_ty.kind() {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = target_ty.kind() {
                        if adt_def.is_struct() {
                            if let Some(alloc_id) = src_val.provenance_alloc_id() {
                                self.decompose_pointee_fields(
                                    alloc_id,
                                    Vec::new(),
                                    *target_ty,
                                    *target_ty,
                                    0,
                                    0,
                                );
                            }
                        }
                    }
                }
                // Transmute-like casts of single-field newtypes (e.g.
                // NonZero::get's `_0 = copy _1 as T`) yield the underlying
                // field value, not the wrapper's own term.
                let term = crate::helpers::mir_utils::extract_local(operand)
                    .and_then(|l| self.field_value(l, &[0]).map(|v| v.z3_term.clone()))
                    .unwrap_or(src_val.z3_term);
                // A pointer→integer cast (`ptr as usize`) yields the (always
                // non-negative) address. Record this as a *path condition* so
                // downstream pointer arithmetic (e.g. `align_up` in a free-list
                // allocator) can discharge `NonNull` on the derived pointer —
                // `check_non_null`'s SMT query only sees path conditions, not
                // the `term >= 0` constraint `assert_value_constraints` adds.
                let src_is_ptr = matches!(src_ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)
                    | rustc_middle::ty::TyKind::Ref(..));
                let dest_is_int = matches!(
                    cast_ty.kind(),
                    rustc_middle::ty::TyKind::Uint(_) | rustc_middle::ty::TyKind::Int(_)
                );
                if src_is_ptr && dest_is_int {
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    self.constraints.assertions.push(term.ge(&zero));
                    if src_val.invariants.non_null {
                        self.constraints.assertions.push(term._eq(&zero).not());
                    }
                }
                VmValue {
                    z3_term: term,
                    ty: *cast_ty,
                    provenance: src_val.provenance,
                    invariants: ValueInvariants {
                        non_null: src_val.invariants.non_null,
                        init: src_val.invariants.init,
                        in_bounds: src_val.invariants.in_bounds,
                        align_n: if crate::helpers::mir_utils::pointee_ty(src_ty)
                            .is_some_and(|t| t.is_unit())
                        {
                            None
                        } else {
                            src_val.invariants.align_n
                        },
                    },
                    source: src_val.source.field_offset_only(),
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
                    if let Some(alloc_id) = self.current_frame.local_alloc.get(&dest_local).copied() {
                        self.alloc_mut(alloc_id).initialized = true;
                    }
                    return VmValue {
                        z3_term: field_val.z3_term,
                        ty: dest_ty,
                        provenance: field_val.provenance,
                        invariants: field_val.invariants,
                        source: ValueSource::None,
                    };
                }
                let term = self.fresh_int("aggregate");
                let dest_local = dest_place.local;
                // Prefer the pointee allocation (through a `*ptr` deref) over the
                // base local's own stack slot, so byte values land on the real
                // buffer (e.g. `((*_8).1).0 = [a, b, 0]` writes into the box).
                let dest_alloc_id = self
                    .current_frame
                    .local_values
                    .get(&dest_local)
                    .and_then(|v| v.provenance_alloc_id())
                    .or_else(|| self.current_frame.local_alloc.get(&dest_local).copied());
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
                        if dst_is_raw && (src_is_ref || field_val.invariants.non_null) {
                            field_val.invariants.in_bounds = true;
                            field_val.ty = *field_ty;
                        }
                    }
                    let field_sz = field_types
                        .get(i)
                        .copied()
                        .map(|ty| self.size_of_ty(ty) as usize)
                        .unwrap_or(1);
                    let field_term = field_val.z3_term.clone();
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
                                let nested: Vec<(Vec<usize>, VmValue<'z3, 'tcx>)> = self
                                    .current_frame
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
                                            Int::from_u64(self.z3_ctx, 0),
                                        );
                                    }
                                } else {
                                    self.mark_byte_non_nul(alloc_id, byte_offset);
                                    if !is_byte_array {
                                        self.record_byte_value(
                                            alloc_id,
                                            byte_offset,
                                            Int::from_u64(self.z3_ctx, int_val),
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
                                    Int::from_u64(self.z3_ctx, byte_val),
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
                        Some(data) => (data.z3_term.clone(), data.provenance.clone()),
                        None => (term.clone(), None),
                    }
                } else {
                    // `Box<T>` (an aggregate `Box(Unique<T>, A)`) takes its
                    // provenance from the inner `Unique<T>.pointer` (`NonNull<T>`
                    // at path `[0, 0]`), which the field-flattening above just
                    // recorded.  Without this, `Box::assume_init`'s rebuild
                    // (`Box(Unique::new_unchecked(raw), alloc)`) drops the heap
                    // provenance and a later `Box::as_ptr` field read fails
                    // `NonNull` (rustc 1.95 lowers `as_ptr` to that field read).
                    let box_prov = if let rustc_middle::ty::TyKind::Adt(adt, _) = dest_ty.kind() {
                        if api_classify::is_std_box(adt.did()) {
                            self.field_value(dest_local, &[0, 0])
                                .and_then(|v| v.provenance.clone())
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    (term.clone(), box_prov)
                };
                VmValue {
                    z3_term: result_term,
                    ty: dest_ty,
                    provenance: result_prov,
                    invariants: ValueInvariants::default(),
                    source: ValueSource::None,
                }
            }
            Rvalue::Discriminant(place) => {
                // If the ADT's variant is known symbolically (e.g. `Iterator::next`
                // returns `Some` iff the iterator was non-empty), reuse that term
                // so `switchInt(discriminant)` branches stay tied to the real
                // condition instead of a fresh unconstrained symbol.
                let place_val = self
                    .value_of_place(place)
                    .or_else(|| self.local_value(place.local).cloned());
                let term = place_val
                    .as_ref()
                    .and_then(|v| v.discriminant().cloned())
                    .unwrap_or_else(|| self.fresh_int("discriminant"));
                if place_val
                    .as_ref()
                    .map(|v| v.discriminant().is_some())
                    .unwrap_or(false)
                {
                    self.path_facts.saw_next_discriminant = true;
                }
                // For Ordering (repr i8, values: Less=-1 Equal=0 Greater=1),
                // the discriminant index equals the repr value + 1.
                // Connect the fresh discriminant term to the ADT value so
                // that SwitchInt constraints propagate to the stored value.
                if let Some(ref pv) = place_val {
                    if let rustc_middle::ty::TyKind::Adt(adt_def, _) = pv.ty.kind() {
                        if api_classify::is_std_ordering(adt_def.did()) && adt_def.is_enum() {
                            let one = Int::from_u64(self.z3_ctx, 1);
                            let discr_minus_one = Int::sub(self.z3_ctx, &[&term, &one]);
                            self.constraints.assertions.push(pv.z3_term._eq(&discr_minus_one));
                            // Also bound the discriminant to {0, 1, 2}
                            let zero = Int::from_u64(self.z3_ctx, 0);
                            let two = Int::from_u64(self.z3_ctx, 2);
                            self.constraints.assertions.push(term.ge(&zero));
                            self.constraints.assertions.push(term.le(&two));
                        }
                    }
                }
                VmValue::new(term, dest_ty)
            }
            #[cfg(not(rapx_ge_99))]
            Rvalue::ShallowInitBox(operand, _ty) => {
                let val = self.value_of_operand(operand);
                VmValue {
                    z3_term: val.z3_term,
                    ty: dest_ty,
                    provenance: val.provenance,
                    invariants: val.invariants,
                    source: ValueSource::None,
                }
            }
            Rvalue::CopyForDeref(place) => {
                if let Some(val) = self.value_of_place(place) {
                    val
                } else {
                    let term = self.fresh_int("copy_for_deref");
                    VmValue::new(term, dest_ty)
                }
            }
            Rvalue::Repeat(..) => {
                let term = self.fresh_int("repeat");
                VmValue::new(term, dest_ty)
            }
            Rvalue::ThreadLocalRef(_) => {
                let term = self.fresh_int("thread_local");
                VmValue::new(term, dest_ty)
            }
            #[cfg(not(rapx_ge_95))]
            Rvalue::NullaryOp(_op) => {
                let term = self.fresh_int("nullary");
                let op_debug = format!("{:?}", _op);
                let is_align_of = op_debug.contains("AlignOf") || op_debug.contains("min_align_of");
                let is_size_of = op_debug.contains("SizeOf");
                if is_align_of || is_size_of {
                    let one = Int::from_u64(self.z3_ctx, 1);
                    self.constraints.assertions.push(term.ge(&one));
                }
                VmValue::new(term, dest_ty)
            }
            Rvalue::WrapUnsafeBinder(_operand, _ty) => {
                let term = self.fresh_int("wrap_unsafe_binder");
                VmValue::new(term, dest_ty)
            }
            #[cfg(rapx_rvalue_has_reborrow)]
            Rvalue::Reborrow(_ty, _mutability, _place) => {
                let term = self.fresh_int("reborrow");
                VmValue {
                    z3_term: term,
                    ty: dest_ty,
                    provenance: None,
                    invariants: ValueInvariants {
                        non_null: true,
                        ..Default::default()
                    },
                    source: ValueSource::None,
                }
            }
        }
    }

    // ── Arithmetic ────────────────────────────────────────────────

    /// Encode a boolean condition as the integer `1`/`0`.
    fn bool_as_int(&self, cond: &Bool<'z3>) -> Int<'z3> {
        cond.ite(&Int::from_u64(self.z3_ctx, 1), &Int::from_u64(self.z3_ctx, 0))
    }

    /// Negate a Z3 integer (`0 - val`).
    fn negate(&self, val: &Int<'z3>) -> Int<'z3> {
        let zero = Int::from_u64(self.z3_ctx, 0);
        Int::sub(self.z3_ctx, &[&zero, val])
    }

    fn eval_binary_op(&mut self, op: BinOp, lhs: &Int<'z3>, rhs: &Int<'z3>) -> Int<'z3> {
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked => {
                Int::add(self.z3_ctx, &[lhs, rhs])
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                Int::sub(self.z3_ctx, &[lhs, rhs])
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                // `us_len = (len / ts) * us`: a non-exact division result times
                // an exact gcd quotient.  Model the product as a fresh symbol
                // and emit its byte bound `us_len * sizeof_U <= len * sizeof_T`
                // directly, so the later `from_raw_parts_mut` InBound check
                // (`us_len * sizeof_U`) stays degree-2 rather than the
                // degree-3 `div * us * sizeof_U` that Z3's NIA cannot rewrite.
                if let Some((div_lhs, div_rhs)) = self.constraints.term_caches.div_roots.get(lhs)
                {
                    if let Some(us_dividend) = self.constraints.term_caches.exact_div_roots.get(rhs)
                    {
                        if let Some(ts_dividend) = self.constraints.term_caches.exact_div_roots.get(div_rhs)
                        {
                            let us_len = self.fresh_int("us_len");
                            self.constraints
                                .assertions
                                .push(us_len._eq(&Int::mul(self.z3_ctx, &[lhs, rhs])));
                            let byte_len = Int::mul(self.z3_ctx, &[&us_len, ts_dividend]);
                            let byte_bound = Int::mul(self.z3_ctx, &[div_lhs, us_dividend]);
                            self.constraints.assertions.push(byte_len.le(&byte_bound));
                            return us_len;
                        }
                    }
                }
                Int::mul(self.z3_ctx, &[lhs, rhs])
            }
            BinOp::Div => {
                // An *exact* division (`lhs % rhs == 0` known) is represented as
                // a fresh variable rather than the `lhs / rhs` term. The caller
                // still emits the Euclidean identity `lhs == quot*rhs + rem`
                // (with `rem == 0` from the divisibility), so the fresh variable
                // satisfies `quot*rhs == lhs` linearly. This avoids the *nested*
                // division (`x / (b/gcd)`) that Z3's nonlinear solver can't
                // handle, leaving only degree-2 products that `nlsat` handles
                // far more reliably. General (any exact division), not a
                // per-function effect.
                let zero = Int::from_u64(self.z3_ctx, 0);
                let exact = self
                    .constraints
                    .assertions
                    .iter()
                    .any(|c| *c == lhs.rem(rhs)._eq(&zero));
                if exact {
                    let q = self.fresh_int("exact_div");
                    self.constraints.term_caches.exact_div_roots.insert(q.clone(), lhs.clone());
                    q
                } else {
                    // A *non-exact* division is likewise a fresh variable (the
                    // caller's Euclidean identity `lhs == q*rhs + rem` links it
                    // back), so a later `(len/ts) * us` product stays a degree-2
                    // product of two symbols instead of a `div` term that Z3's
                    // nonlinear solver cannot combine with a multiplier.
                    let q = self.fresh_int("div");
                    self.constraints.term_caches.div_roots.insert(q.clone(), (lhs.clone(), rhs.clone()));
                    q
                }
            }
            BinOp::Rem => lhs.rem(rhs),
            BinOp::Eq => self.bool_as_int(&lhs._eq(rhs)),
            BinOp::Ne => self.bool_as_int(&lhs._eq(rhs).not()),
            BinOp::Lt => self.bool_as_int(&lhs.lt(rhs)),
            BinOp::Le => self.bool_as_int(&lhs.le(rhs)),
            BinOp::Gt => self.bool_as_int(&lhs.gt(rhs)),
            BinOp::Ge => self.bool_as_int(&lhs.ge(rhs)),
            BinOp::Offset => Int::add(self.z3_ctx, &[lhs, rhs]),
            BinOp::BitAnd => {
                let result = self.fresh_int("binop");
                // BitAnd only clears bits, so it never increases a non-negative
                // value: result <= lhs.
                self.constraints.assertions.push(result.le(lhs));
                // When the mask (rhs) is a non-negative constant, the result is
                // also bounded by it: `x & c <= c` (e.g. `rhs & 31 <= 31`).
                // This lets `(rhs & (BITS - 1)) < BITS` be discharged. The
                // mask may be a folded expression (`SubWithOverflow(BITS, 1)`),
                // so `simplify()` is used to recover its constant value.
                if rhs.simplify().as_u64().is_some() {
                    self.constraints.assertions.push(result.le(rhs));
                }
                if self.constraints.term_caches.not_mask_terms.contains(rhs) {
                    // rhs is a two's-complement mask `!(align-1) == -align`,
                    // so `align = -rhs`. The result of `x & !(align-1)` is
                    // `x` rounded down to a multiple of `align` (i.e. align_up
                    // of the pre-incremented value).
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let align = Int::sub(self.z3_ctx, &[&zero, rhs]);
                    self.constraints.assertions.push(result.rem(&align)._eq(&zero));
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let addr = Int::add(self.z3_ctx, &[lhs, rhs, &one]);
                    self.constraints.assertions.push(result.ge(&addr));
                }
                result
            }
            BinOp::BitOr => {
                let result = self.fresh_int("binop");
                let zero = Int::from_u64(self.z3_ctx, 0);
                // Bitwise OR only sets bits, so the result is non-zero whenever
                // either operand is non-zero.  Emit an implication (rather than
                // `result >= lhs`, which is only valid for non-negative values)
                // so `NonZero` bit-or methods discharge their `!= 0` obligation
                // for both signed and unsigned instantiations.
                self.constraints.assertions
                    .push(lhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                self.constraints.assertions
                    .push(rhs._eq(&zero).not().implies(&result._eq(&zero).not()));
                result
            }
            _ => self.fresh_int("binop"),
        }
    }

    fn eval_unary_op(&mut self, op: UnOp, val: &Int<'z3>, is_bool: bool) -> Int<'z3> {
        match op {
            UnOp::Not => {
                if is_bool {
                    let zero = Int::from_u64(self.z3_ctx, 0);
                    let one = Int::from_u64(self.z3_ctx, 1);
                    val._eq(&zero).ite(&one, &zero)
                } else {
                    // Two's-complement bitwise NOT: !x == -x - 1.
                    let one = Int::from_u64(self.z3_ctx, 1);
                    let result = Int::sub(self.z3_ctx, &[&self.negate(val), &one]);
                    self.constraints.term_caches.not_mask_terms.insert(result.clone());
                    result
                }
            }
            UnOp::Neg => self.negate(val),
            UnOp::PtrMetadata => self.fresh_int("ptr_metadata"),
        }
    }

    /// Compute the slice length for a `&[T]` / `&mut [T]` value: the allocation
    /// size divided by the element size. Reuses the allocation's size term so
    /// it agrees with InBound/`alloc.size` checks.  Uses the symbolic element
    /// size (`size_sym_read`) so `len = (len·S) / S` cancels to `len` for a
    /// generic element type — mirroring `set_len_from_alloc`.
    pub(crate) fn slice_len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let alloc_id = val.provenance_alloc_id()?;
        let alloc = self.alloc(alloc_id);
        // The length is materialized on the data allocation (the fat pointer's
        // metadata word); `size` is `slice_len * sizeof_T`.  Fall back to the
        // `size / elem_size` derivation for allocations created before the
        // materialization was introduced (e.g. some call effects).
        if let Some(len) = alloc.slice_len() {
            return Some(len.clone());
        }
        let elem_ty = alloc.element_ty.as_ty()?;
        let elem_term = self.size_sym_read(elem_ty);
        if elem_term.simplify().as_u64() == Some(1) {
            return Some(alloc.size.clone());
        }
        Some(alloc.size.div(&elem_term))
    }

    /// Resolve `x.len()` for a pointer whose pointee ADT carries a `len` field
    /// (e.g. `NodeRef<LeafNode>`: `len()` reads `(*ptr).len`).  Returns the
    /// pointee's `len` field term, or `None` when the pointee has no such field.
    pub(crate) fn try_adt_len_field(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let alloc_id = val.provenance_alloc_id()?;
        let elem_ty = self.alloc(alloc_id).element_ty.as_ty()?;
        self.try_adt_len_field_at(alloc_id, elem_ty, elem_ty, &[])
    }

    /// Resolve a `len` field on `ty`, recursing into ADT sub-fields when there is
    /// no direct `len` (e.g. `String { vec: Vec { ptr, len, cap } }` resolves
    /// `String.len()` to `vec.len`).  `root_ty` stays fixed as the allocation's
    /// element type, which is how `decompose_pointee_fields` keys `memory.fields`.
    fn try_adt_len_field_at(
        &self,
        alloc_id: AllocId,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        prefix: &[usize],
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        // Direct `len` field.
        if let Some(len_idx) = variant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")
        {
            let mut path = prefix.to_vec();
            path.push(len_idx);
            return self
                .memory
                .fields
                .get(&(alloc_id, root_ty, path))
                .map(|v| v.z3_term.clone());
        }
        // Recurse into ADT sub-fields (e.g. `String.vec.len`).
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let field_ty = crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
            if matches!(field_ty.kind(), rustc_middle::ty::TyKind::Adt(_, _)) {
                let mut path = prefix.to_vec();
                path.push(idx);
                if let Some(len) = self.try_adt_len_field_at(alloc_id, field_ty, root_ty, &path) {
                    return Some(len);
                }
            }
        }
        None
    }

    /// Resolve `len()` for `core::ops::IndexRange` (a private `{ start, end }`
    /// struct): `len() = end - start`.  The `len` field lookup above misses it
    /// because `IndexRange` has no `len` field — its `len()` computes the
    /// difference of its two private fields.
    pub(crate) fn try_index_range_len(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = val.ty.kind() else {
            return None;
        };
        let name = self.tcx.def_path_str(adt_def.did());
        if !(name.ends_with("::IndexRange") || name == "IndexRange") {
            return None;
        }
        let alloc_id = val.provenance_alloc_id()?;
        let view_ty = crate::helpers::mir_utils::pointee_ty(val.ty).unwrap_or(val.ty);
        let start = self
            .memory.fields
            .get(&(alloc_id, view_ty, vec![0]))?
            .z3_term
            .clone();
        let end = self
            .memory.fields
            .get(&(alloc_id, view_ty, vec![1]))?
            .z3_term
            .clone();
        Some(Int::sub(self.z3_ctx, &[&end, &start]))
    }

    /// Resolve `len()` of a slice/ADT value: the pointee ADT's `len` field, then
    /// the materialized slice length, then `size / elem_size`.  Shared by the
    /// exec- and checker-side `Len` evaluators so the fallback chain is defined
    /// once.
    pub(crate) fn len_from_value(&self, val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if let Some(len) = self.try_adt_len_field(val) {
            return Some(len);
        }
        if let Some(len) = self.try_index_range_len(val) {
            return Some(len);
        }
        self.slice_len_from_value(val)
    }

    /// Resolve `x.len()` for a struct `x` (e.g. `NodeRef`) whose `len()` method
    /// reads `(*x.field).len` through a `NonNull`/raw-pointer field.  Follows
    /// that field to its pointee allocation and reads the pointee's `len` field.
    pub(crate) fn try_struct_nn_len_field(
        &self,
        local: Local,
        field_path: &[usize],
        ty: Ty<'tcx>,
    ) -> Option<Int<'z3>> {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return None;
        };
        if !adt_def.is_struct() {
            return None;
        }
        let variant = adt_def.non_enum_variant();
        let mut found: Option<(usize, Ty<'tcx>)> = None;
        for (idx, field_def) in variant.fields.iter().enumerate() {
            let fty = crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
            if let Some(pointee) = self.find_nn_pointee(fty) {
                found = Some((idx, pointee));
                break;
            }
        }
        let (nn_idx, pointee) = found?;
        let mut path = field_path.to_vec();
        path.push(nn_idx);
        let nn_val = self.field_value(local, &path)?;
        let alloc_id = nn_val.provenance_alloc_id()?;
        let rustc_middle::ty::TyKind::Adt(pointee_adt, _) = pointee.kind() else {
            return None;
        };
        let pvariant = pointee_adt.non_enum_variant();
        let len_idx = pvariant
            .fields
            .iter()
            .position(|f| f.ident(self.tcx).name.to_string() == "len")?;
        self.memory.fields
            .get(&(alloc_id, pointee, vec![len_idx]))
            .map(|v| v.z3_term.clone())
    }

    /// Resolve the type of a place (`local` + field path) by walking the ADT
    /// field definitions.
    pub(crate) fn field_type_at(&self, local: Local, field_path: &[usize]) -> Option<Ty<'tcx>> {
        let mut ty = self.body().local_decls[local].ty;
        for &idx in field_path {
            let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
                return None;
            };
            let variant = adt_def.non_enum_variant();
            let field_def = variant.fields.get(rustc_abi::FieldIdx::from_usize(idx))?;
            ty = crate::helpers::mir_utils::field_ty(self.tcx, field_def, substs);
        }
        Some(ty)
    }

    /// Compute provenance for a binary operation on pointer values.
    /// Propagates provenance with adjusted offset for pointer arithmetic
    /// (`ptr + offset`, `ptr - offset`, `Offset`).
    fn provenance_for_binary_op(
        &self,
        op: BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
    ) -> Option<Provenance<'z3>> {
        match op {
            BinOp::Add | BinOp::AddWithOverflow | BinOp::AddUnchecked | BinOp::Offset => {
                // ptr + scalar → propagate with adjusted offset
                if rhs.is_pointer() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::Sub | BinOp::SubWithOverflow | BinOp::SubUnchecked => {
                if rhs.is_pointer() {
                    // ptr - ptr → integer (difference), no provenance
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::sub(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::BitAnd => {
                if rhs.is_pointer() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    // Alignment rounding changes the intra-allocation offset
                    // unpredictably; use a fresh symbolic offset constrained
                    // by the BitAnd path conditions emitted in eval_binary_op.
                    offset: self.fresh_int("align_offset"),
                    offset_kind: None,
                })
            }
            BinOp::BitXor | BinOp::Shr | BinOp::ShrUnchecked => {
                if rhs.is_pointer() {
                    return None;
                }
                lhs.provenance.clone()
            }
            BinOp::BitOr | BinOp::Shl | BinOp::ShlUnchecked => {
                if rhs.is_pointer() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::add(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
                })
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => {
                if rhs.is_pointer() {
                    return None;
                }
                lhs.provenance.as_ref().map(|prov| Provenance {
                    alloc_id: prov.alloc_id,
                    offset: Int::mul(self.z3_ctx, &[&prov.offset, &rhs.z3_term]),
                    offset_kind: None,
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
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
        provenance: &Option<Provenance<'z3>>,
    ) -> ValueInvariants<'z3> {
        // A bitwise AND may clear the low bits entirely (`ptr & mask == 0` for a
        // small/aligned-to-zero pointer), so the result is not guaranteed
        // non-null even when the lhs pointer is.  Other pointer arithmetic
        // (`add`/`sub`/`offset`) preserves non-nullness under the VM's
        // no-wrap assumption.
        let non_null =
            !matches!(op, BinOp::BitAnd) && provenance.is_some() && lhs.invariants.non_null;

        let align_n = match op {
            BinOp::Add
            | BinOp::AddWithOverflow
            | BinOp::AddUnchecked
            | BinOp::Sub
            | BinOp::SubWithOverflow
            | BinOp::SubUnchecked
            | BinOp::Offset => {
                // If both LHS and RHS are known to be n-aligned, sum/diff is n-aligned
                match (&lhs.invariants.align_n, &rhs.invariants.align_n) {
                    (Some(a), Some(b)) if a == b => Some(a.clone()),
                    // LHS has alignment, RHS is a constant multiple of it
                    (Some(a), None) => match a.simplify().as_u64() {
                        Some(au) => {
                            let c = rhs.z3_term.as_u64().unwrap_or(1);
                            if c.is_multiple_of(au) { Some(a.clone()) } else { None }
                        }
                        // Symbolic alignment: only a zero RHS is a guaranteed
                        // multiple of `align_T`.
                        None => {
                            if rhs.z3_term.as_u64() == Some(0) {
                                Some(a.clone())
                            } else {
                                None
                            }
                        }
                    },
                    // LHS has alignment, RHS is the result of Mul by constant factor
                    (Some(a), _) if self.rhs_is_aligned_multiple(rhs, a) => Some(a.clone()),
                    _ => None,
                }
            }
            BinOp::Mul | BinOp::MulWithOverflow | BinOp::MulUnchecked => match rhs.z3_term.as_u64() {
                Some(c) => pow2_factor(c).map(|p| Int::from_u64(self.z3_ctx, p)),
                None => lhs
                    .z3_term
                    .as_u64()
                    .and_then(pow2_factor)
                    .map(|p| Int::from_u64(self.z3_ctx, p)),
            },
            _ => lhs.invariants.align_n.clone(),
        };

        ValueInvariants {
            non_null,
            align_n,
            ..Default::default()
        }
    }

    /// Check if a value is known to be a multiple of `align` (e.g. the result
    /// of a Mul by a constant factor of `align`).
    fn rhs_is_aligned_multiple(&self, val: &VmValue<'z3, 'tcx>, align: &Int<'z3>) -> bool {
        // If both the value's align_n and `align` are concrete, compare directly.
        if let Some(au) = align.simplify().as_u64() {
            if let Some(a) = val
                .invariants
                .align_n
                .as_ref()
                .and_then(|a| a.simplify().as_u64())
            {
                if a >= au && a % au == 0 {
                    return true;
                }
            }
            // If the value is a constant, check directly
            if let Some(c) = val.z3_term.as_u64() {
                if c % au == 0 {
                    return true;
                }
            }
        }
        false
    }

    // ── Storage ──────────────────────────────────────────────────

    fn exec_storage_live(&mut self, local: Local) {
        self.ensure_local_allocation(local);
        let alloc_id = self.current_frame.local_alloc[&local];
        self.alloc_mut(alloc_id).dead = false;
    }

    fn exec_storage_dead(&mut self, local: Local) {
        if let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied() {
            self.alloc_mut(alloc_id).dead = true;
        }
    }

    pub(crate) fn exec_drop(&mut self, place: &Place<'tcx>) {
        if let Some(alloc_id) = self.current_frame.local_alloc.get(&place.local).copied() {
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
    }

    // ── Terminator executors ─────────────────────────────────────

    fn exec_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        switch_succ: Option<BasicBlock>,
    ) {
        match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let caller_id = self.current_frame.current_def_id;
                self.exec_call(func, args, destination.local, caller_id);
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                self.exec_switchint(discr, targets, switch_succ);
            }
            TerminatorKind::Assert { cond, expected, .. } => {
                self.exec_assert(cond, *expected);
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
    /// Uses the successor resolved by the slicer (`switch_succ`) to determine
    /// which branch is taken, then adds a path condition asserting the
    /// discriminant equals that value.
    fn exec_switchint(
        &mut self,
        discr: &Operand<'tcx>,
        targets: &rustc_middle::mir::SwitchTargets,
        switch_succ: Option<BasicBlock>,
    ) {
        let discr_val = self.value_of_operand(discr);

        // If the discriminator is a comparison result, record the direct
        // boolean condition alongside the ite-encoded `discr == value` fact,
        // so the SMT solver can reason about `offset <= len` directly.
        let cmp_cond = discr_val.bool_cond().cloned();

        // Determine which target block is taken along the path.
        if let Some(chosen) = switch_succ {
            for (value, target) in targets.iter() {
                if target == chosen {
                    let val_term = Int::from_u64(self.z3_ctx, value as u64);
                    self.constraints.assertions.push(discr_val.z3_term._eq(&val_term));
                    if let Some(ref cond) = cmp_cond {
                        if value != 0 {
                            self.constraints.assertions.push(cond.clone());
                        } else {
                            self.constraints.assertions.push(cond.not());
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
                    let val_term = Int::from_u64(self.z3_ctx, value as u64);
                    self.constraints.assertions
                        .push(discr_val.z3_term._eq(&val_term).not());
                }
                if let Some(ref cond) = cmp_cond {
                    // For a boolean discriminator, `otherwise` means the
                    // comparison result is *not* any explicit value:
                    //   - targets include 0 → `discr != 0` → comparison true;
                    //   - targets include 1 → `discr != 1` → comparison false.
                    if targets.iter().any(|(v, _)| v == 0) {
                        self.constraints.assertions.push(cond.clone());
                    } else if targets.iter().any(|(v, _)| v == 1) {
                        self.constraints.assertions.push(cond.not());
                    }
                }
            }
        }
    }

    /// Execute an Assert terminator.
    fn exec_assert(&mut self, cond: &Operand<'tcx>, expected: bool) {
        let cond_val = self.value_of_operand(cond);
        // If the asserted operand is a comparison result, record the direct
        // boolean condition (`idx < len`) alongside the ite-encoded fact, so
        // the SMT solver can unfold it (mirrors `exec_switchint`).
        let cmp_cond = cond_val.bool_cond().cloned();
        if expected {
            let zero = Int::from_u64(self.z3_ctx, 0);
            self.constraints.assertions.push(cond_val.z3_term._eq(&zero).not());
            if let Some(c) = &cmp_cond {
                self.constraints.assertions.push(c.clone());
            }
        } else {
            let zero = Int::from_u64(self.z3_ctx, 0);
            self.constraints.assertions.push(cond_val.z3_term._eq(&zero));
            if let Some(c) = &cmp_cond {
                self.constraints.assertions.push(c.not());
            }
        }

        // Guard inference: trace the assert condition back to find non_null sources
        self.infer_guard_non_null(cond, expected);
        // Infer alignment from == 0 guards on Rem expressions
        self.infer_guard_align(cond, expected);
    }

    /// The `(lhs, rhs, op)` of the binary-op/comparison source recorded on the
    /// value bound to `pk`'s local, if any.
    fn op_source_of(
        &self,
        pk: &PlaceKey,
    ) -> Option<(Option<PlaceKey>, Option<PlaceKey>, rustc_middle::mir::BinOp)> {
        let local = pk.local()?;
        let val = self.current_frame.local_values.get(&local)?;
        val.source
            .operands()
            .map(|(l, r, o)| (l.clone(), r.clone(), o))
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

        // Check if cond is a Ne/Eq comparison of (x % n) or (x & (align-1)) against 0
        if let Some((lhs_pk, rhs_pk, _)) = self.op_source_of(&cond_pk) {
            // The lhs is (x % n) / (x & (align-1)), rhs is constant 0
            let inner_pk = match (&lhs_pk, &rhs_pk) {
                (Some(pk), None) => pk.clone(),
                (None, Some(pk)) => pk.clone(),
                _ => return,
            };
            if let Some((div_lhs, div_rhs, inner_op)) = self.op_source_of(&inner_pk) {
                match inner_op {
                    // `x % n == 0`: div_rhs is the concrete divisor constant.
                    rustc_middle::mir::BinOp::Rem => {
                        if let Some(divisor) = resolve_u64_from_place_key(&div_rhs, self) {
                            if divisor > 0 {
                                self.mark_align_n(&div_lhs, Int::from_u64(self.z3_ctx, divisor));
                            }
                        }
                    }
                    // `x & (align-1) == 0`: the mask is `align-1` (symbolic for a
                    // generic `T`), so `align = mask + 1`.
                    rustc_middle::mir::BinOp::BitAnd => {
                        if let Some(rhs_local) = div_rhs.as_ref().and_then(|pk| pk.local()) {
                            if let Some(rhs_val) = self.current_frame.local_values.get(&rhs_local) {
                                let one = Int::from_u64(self.z3_ctx, 1);
                                let align = Int::add(self.z3_ctx, &[&rhs_val.z3_term, &one]);
                                self.mark_align_n(&div_lhs, align);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    fn mark_align_n(&mut self, src_pk: &Option<PlaceKey>, align: Int<'z3>) {
        if let Some(src_pk) = src_pk {
            if let Some(local) = src_pk.local() {
                if let Some(mut val) = self.current_frame.local_values.get(&local).cloned() {
                    val.invariants.align_n = Some(align);
                    self.set_local(local, val);
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

        // Check if cond was defined by BinaryOp(Ne, (ptr, 0)) or similar:
        // mark the non-constant side as non-null.  Only `Ne` guards imply
        // non-nullness; an `Eq` guard (`assert (addr & mask) == 0`, the
        // alignment check) means the value *is* zero, not non-null.
        if let Some((lhs_pk, rhs_pk, op)) = self.op_source_of(&cond_pk) {
            if op != rustc_middle::mir::BinOp::Ne {
                return;
            }
            if rhs_pk.is_none() {
                self.mark_guard_pointer(&lhs_pk, &None);
            }
            if lhs_pk.is_none() {
                self.mark_guard_pointer(&rhs_pk, &None);
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
        if let Some((lhs_pk, rhs_pk, _)) = self.op_source_of(&pk) {
            self.mark_guard_pointer(&lhs_pk, &rhs_pk);
        }
    }

    fn mark_guard_pointer(&mut self, lhs: &Option<PlaceKey>, rhs: &Option<PlaceKey>) {
        for pk in [lhs, rhs].into_iter().flatten() {
            if let Some(local) = pk.local() {
                if let Some(mut val) = self.current_frame.local_values.get(&local).cloned() {
                    val.invariants.non_null = true;
                    self.set_local(local, val);
                }
            }
        }
    }

    /// Assert a contract fact as VM state invariants.
    fn assert_contract_fact(&mut self, property: &Property<'tcx>) {
        // A precondition with a hazard component records that the caller
        // accepts that hazard (e.g. `any(Trait(T, Copy), Alias(self, ret))` on
        // `NonNull::read`).  Inlined read/copy intrinsics whose result
        // structurally aliases the source are then treated as the accepted
        // hazard rather than a hard failure.
        if contains_hazard(property) {
            self.path_facts.alias_hazard_accepted = true;
        }
        match property {
            Property::Atom(atom) => {
                if atom.contract_kind == ContractKind::Hazard {
                    return;
                }
                // Assert the atom's own effect, then each of its transitive
                // consequences exactly once (`subsumption_closure` is
                // deduplicated).
                self.assert_atom_direct(property);
                for sub in crate::verify::contract::compound::subsumption_closure(atom) {
                    self.assert_atom_direct(&Property::Atom(sub));
                }
            }
            Property::And(and) => {
                for conj in &and.conjuncts {
                    self.assert_contract_fact(conj);
                }
            }
            Property::Or(or) => {
                // Two guard patterns are materialized by asserting the
                // *non-guard* disjuncts (the guard is vacuous for the case the
                // deref actually runs in):
                //   `any(Null(p), (atoms…))`  — nullable pointer.
                //   `Size(T, 0) || Deref`     — ZST vs non-ZST (`ValidPtr`).
                // A general `Or` without such a guard disjunct is left to the
                // checker (only one disjunct holds, so no fact is sound to
                // assert unconditionally).
                let is_guard = |d: &Box<Property<'tcx>>| {
                    matches!(d.as_ref(), Property::Atom(a) if a.kind == PropertyKind::Null || a.kind == PropertyKind::Size)
                };
                if !or.disjuncts.iter().any(&is_guard) {
                    return;
                }
                for disj in &or.disjuncts {
                    if is_guard(disj) {
                        continue;
                    }
                    self.assert_contract_fact(disj);
                }
            }
        }
    }

    /// Apply a single atom's direct effect (its `match kind` arm), without
    /// recursing into its subsumption consequences.
    fn assert_atom_direct(&mut self, property: &Property<'tcx>) {
        let Property::Atom(atom) = property else {
            return;
        };
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
                self.record_for_each_align(property);
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
                self.record_for_each_owning(property);
            }
            PropertyKind::Alive => {
                if let Some(id) = self.contract_alloc_id_field_aware(property) {
                    // The region is bound at parse time (`bind_alive_regions`):
                    // struct invariants against the struct, function `requires`
                    // against the function.
                    if let Some(PropertyArg::Region(region)) = property.args().get(1) {
                        self.alloc_mut(id).liveness = Some(*region);
                    }
                }
            }
            PropertyKind::InBound => {
                if let Some(val) = self.contract_target_value(property) {
                    self.set_in_bounds_for_value(property, val);
                }
                if let Some(fe_place) = property.for_each() {
                    self.assert_in_bound_for_each(property, fe_place);
                    self.path_facts.has_checked_bounds = true;
                } else {
                    self.assert_in_bound_single(property);
                }
                // The pointer-and-count form `InBound(p, T, n)` also guarantees
                // the allocation backs `n` elements — materialize that size so a
                // downstream `ptr.add(n)`/`ptr.sub(n)` can discharge `InBound`
                // against a concrete (or `i64::MAX`) size rather than the coarse
                // `in_bounds` flag (which only covers `count == 1`).
                if property.args().len() >= 3 {
                    self.assert_allocated_fact(property);
                }
            }
            PropertyKind::Allocated => {
                self.assert_allocated_fact(property);
                self.record_for_each_allocated(property);
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
                            // A `Typed(container.iter(), T)` *for_each* invariant
                            // declares that the container's pointer elements all
                            // point at valid `T`s. Record that target type so a
                            // single pointer loaded from the container can later
                            // discharge `Typed(ptr, T)` soundly (the fact comes
                            // from the invariant, not from the pointer type).
                            if property.for_each().is_some() {
                                self.alloc_mut(alloc_id).for_each.target_ty = Some(expected_ty);
                            }
                            // Only record the type invariant when the allocation
                            // has no element type yet.  `Init ⇒ Typed` (and other
                            // typed preconditions) may re-assert `Typed` with a
                            // *re-numbered* instantiation of the same `T` (e.g.
                            // `T/#1` vs the `T/#0` used to size the allocation),
                            // which must not clobber the original element type —
                            // doing so makes `len()` fall back to the byte size.
                            if self.alloc(alloc_id).element_ty.is_generic() {
                                self.alloc_mut(alloc_id).element_ty = ContentTy::Typed(expected_ty);
                            }
                        }
                    }
                }
            }
            PropertyKind::SplitTransmute => {
                self.path_facts.split_transmute_asserted = true;
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
                    self.current_frame.local_values.get(&local)?.provenance_alloc_id()
                });
                if let Some(id) = id {
                    self.alloc_mut(id).dead = false;
                    self.alloc_mut(id).liveness = Some(self.tcx.lifetimes.re_static);
                    self.alloc_mut(id).initialized = true;
                    self.memory.cstr_trusted.insert(id);
                    // `ValidCStr(p, n)` carries the byte length of the
                    // nul-terminated buffer.  Assert the allocation covers `n`
                    // bytes so downstream `from_raw_parts(p, n)` / InBound
                    // obligations can be discharged from the exact length
                    // (rather than a conservative `1` placeholder), and
                    // materialize the terminal NUL as a byte-level fact
                    // (`byte[n] == 0`).  A `Const` length (`from_ptr`'s `1`
                    // placeholder) is ignored — the true length is
                    // `strlen(ptr) + 1`.
                    if let Some(n) = property
                        .args()
                        .get(1)
                        .and_then(|a| match a {
                            PropertyArg::Expr(ContractExpr::Const(_)) => None,
                            a => self.resolve_contract_count(a),
                        })
                    {
                        self.constraints.assertions.push(self.alloc(id).size.ge(&n));
                        let zero = Int::from_u64(self.z3_ctx, 0);
                        self.byte_write(id, &n, &zero);
                    }
                }
            }
            PropertyKind::ValidNum => {
                if let Some(PropertyArg::Predicates(predicates)) = property.args().first() {
                    for pred in predicates {
                        if let Some(condition) = self.eval_predicate_as_bool(pred) {
                            self.constraints.assertions.push(condition);
                            // For !self.is_empty() → self.len() != 0 on
                            // Iter/IterMut: also assert len >= 1 to help
                            // Z3 with integer division reasoning.
                            if let Some(len_term) = self.try_simple_iter_len_from_pred(pred) {
                                let one = Int::from_u64(self.z3_ctx, 1);
                                self.constraints.assertions.push(len_term.ge(&one));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Get the local referenced by a contract property's target.
    fn contract_target_local(&self, property: &Property<'tcx>) -> Option<Local> {
        let cp = property.target_place()?;
        Some(cp.base.to_local())
    }

    /// Materialize a fresh external allocation for an `Allocated` contract
    /// fact, returning a value carrying the allocation's provenance.
    /// Mark the target pointer's existing allocation as live (and record its
    /// element type for downstream `Typed` checks).  Returns `true` when the
    /// pointer already carried an allocation, so a fresh external allocation
    /// should *not* be materialized (which would loosen bound checks).
    fn mark_alloc_live_keep(&mut self, val: &VmValue<'z3, 'tcx>, elem_ty: Ty<'tcx>) -> bool {
        let Some(alloc_id) = val.provenance_alloc_id() else {
            return false;
        };
        self.alloc_mut(alloc_id).dead = false;
        // An `Allocated(p, T, n)` contract on a raw-pointer parameter means the
        // caller guarantees the memory is allocated and outlives the call, so
        // it is alive for the function's execution region.
        if self.alloc(alloc_id).is_external() {
            self.alloc_mut(alloc_id).liveness = Some(self.tcx.lifetimes.re_static);
        }
        if self.alloc(alloc_id).element_ty.is_generic() {
            self.alloc_mut(alloc_id).element_ty = ContentTy::Typed(elem_ty);
        }
        true
    }

    fn materialize_external_alloc(
        &mut self,
        elem_ty: Ty<'tcx>,
        count_term: Option<Int<'z3>>,
        val_ty: Ty<'tcx>,
        huge: bool,
    ) -> VmValue<'z3, 'tcx> {
        let elem_sz_raw = self.size_of_ty(elem_ty);
        let heap_align = self.align_sym(elem_ty);
        let heap_align_n = if heap_align.simplify().as_u64() != Some(1) {
            Some(heap_align.clone())
        } else {
            None
        };
        let (heap_id, heap_base) = if huge || elem_sz_raw == 0 {
            // Struct-field targets (and generic element types): use an
            // unbounded external allocation so `Allocated`/`InBound` checks
            // auto-pass regardless of the symbolic element size.
            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
            self.allocate_external(max_size, heap_align.clone(), Some(elem_ty))
        } else {
            let elem_sz = Int::from_u64(self.z3_ctx, elem_sz_raw);
            let count = count_term.unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
            let total = Int::mul(self.z3_ctx, &[&count, &elem_sz]);
            self.allocate_external(total, heap_align, Some(elem_ty))
        };
        self.alloc_mut(heap_id).initialized = true;
        VmValue {
            z3_term: heap_base,
            ty: val_ty,
            provenance: Some(Provenance {
                alloc_id: heap_id,
                offset: Int::from_u64(self.z3_ctx, 0),
                offset_kind: None,
            }),
            invariants: ValueInvariants {
                non_null: true,
                init: true,
                in_bounds: true,
                align_n: heap_align_n,
            },
            source: ValueSource::None,
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
            .target_place()
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
            let Some(val) = self.current_frame.local_values.get(&local).cloned() else {
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
                let Some(val) = self.current_frame.local_values.get(&local).cloned() else {
                    return;
                };
                if self.mark_alloc_live_keep(&val, elem_ty) {
                    return;
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
                        // Already has a *known* (concrete) size — a preceding
                        // `Allocated`/`InBound` fact just materialized it.  Only
                        // mark it live; re-materializing would orphan an `Align`
                        // path condition recorded against the earlier term.
                        if self.alloc(alloc_id).size.as_u64().is_some() {
                            self.alloc_mut(alloc_id).dead = false;
                            return;
                        }
                        self.alloc_mut(alloc_id).dead = false;
                    }
                    let mut v = self.materialize_external_alloc(elem_ty, count_term, val.ty, true);
                    // The size materialization must not clobber a *stronger*
                    // alignment fact already on the field (e.g. `Align(ptr,
                    // usize)` set `align_n = 8`, but `Allocated(ptr, u8, n)`
                    // re-materializes with `u8`'s align of 1 → `align_n = None`).
                    if v.invariants.align_n.is_none() {
                        v.invariants.align_n = val.invariants.align_n.clone();
                    }
                    self.set_field_value(local, field_path, v);
                } else {
                    // Wrapped field / pointer-to-ADT: materialize the *field*
                    // target (not the whole local) so a downstream `Allocated`
                    // on the field sees the freshly-sized allocation.
                    let Some(val) = self.field_value(local, &field_path).cloned() else {
                        return;
                    };
                    if let Some(alloc_id) = val.provenance_alloc_id() {
                        if self.alloc(alloc_id).size.as_u64().is_some() {
                            self.alloc_mut(alloc_id).dead = false;
                            return;
                        }
                        self.alloc_mut(alloc_id).dead = false;
                    }
                    let mut v = self.materialize_external_alloc(elem_ty, count_term, val.ty, false);
                    if v.invariants.align_n.is_none() {
                        v.invariants.align_n = val.invariants.align_n.clone();
                    }
                    self.set_field_value(local, field_path, v);
                }
            }
        }
    }

    /// Resolve a contract place to `(local, field_path)`. Field projections
    /// are accumulated into `field_path`; `Downcast`/`ForEach` terminate
    /// the path (they unwrap the value in place).
    fn contract_field_path(&self, property: &Property<'tcx>) -> Option<(Local, Vec<usize>)> {
        let cp = property.target_place()?;
        let local = cp.base.to_local();
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
    fn contract_target_value(&mut self, property: &Property<'tcx>) -> Option<VmValue<'z3, 'tcx>> {
        let (local, path) = self.contract_field_path(property)?;
        if path.is_empty() {
            self.current_frame.local_values.get(&local).cloned()
        } else {
            self.field_value(local, &path).cloned()
        }
    }

    /// Write a contract target value back to its (possibly field) location.
    fn set_contract_target_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
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
        let local = cp.base.to_local();
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
            self.current_frame.local_values.get(&local)?.provenance_alloc_id()
        } else {
            self.field_value(local, &field_path)?.provenance_alloc_id()
        }
    }

    /// Resolve a contract count argument to a Z3 term by looking up
    /// the corresponding function parameter in the VM state.
    fn resolve_contract_count(&self, arg: &PropertyArg<'tcx>) -> Option<Int<'z3>> {
        match arg {
            PropertyArg::Expr(ContractExpr::Const(n)) => Some(Int::from_u64(self.z3_ctx, *n as u64)),
            // Delegate field-projected places and arithmetic (e.g. `cap * elem_size`)
            // to the general simple evaluator.
            PropertyArg::Expr(expr) => self.eval_contract_expr_simple(expr),
            _ => None,
        }
    }

    /// Evaluate a numeric predicate to a Z3 Bool for path-condition assertion.
    fn relop_to_bool(
        &self,
        op: crate::verify::contract::RelOp,
        lhs: &Int<'z3>,
        rhs: &Int<'z3>,
    ) -> Bool<'z3> {
        use crate::verify::contract::RelOp;
        match op {
            RelOp::Eq => lhs._eq(rhs),
            RelOp::Ne => lhs._eq(rhs).not(),
            RelOp::Le => lhs.le(rhs),
            RelOp::Lt => lhs.lt(rhs),
            RelOp::Ge => lhs.ge(rhs),
            RelOp::Gt => lhs.gt(rhs),
        }
    }

    fn eval_predicate_as_bool(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        use crate::verify::contract::ContractExpr;
        let lhs = self.eval_contract_expr_simple(&pred.lhs)?;
        let rhs = match &pred.rhs {
            ContractExpr::Const(v) => Int::from_u64(self.z3_ctx, *v as u64),
            _ => self.eval_contract_expr_simple(&pred.rhs)?,
        };
        Some(self.relop_to_bool(pred.op, &lhs, &rhs))
    }

    fn eval_contract_expr_simple(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::{ContractExpr, NumericBinOp};
        match expr {
            ContractExpr::SizeOf(ty) => {
                // Symbolic-aware: a generic `T` yields the shared `sizeof_T`
                // (≥ 1) instead of the concrete `1` placeholder, so bounds like
                // `size_of(T) * len <= isize::MAX` match the data allocation's
                // `len·sizeof_T` byte size.  Concrete types still return their
                // real size.
                Some(self.size_sym_read(*ty))
            }
            ContractExpr::Place(cp) => {
                let local = cp.base.to_local();
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
                    self.local_value(local).map(|v| v.z3_term.clone())
                } else {
                    self.field_value(local, &path)
                        .map(|v| v.z3_term.clone())
                        .or_else(|| {
                            // Deref+Field: the base local is a reference whose pointee
                            // fields live in the per-allocation map (e.g. the
                            // `ValidNum(len <= CAPACITY)` invariant on `&LeafNode`
                            // reads `(*leaf).len` through `memory.fields`).
                            let base_val = self.local_value(local)?;
                            let alloc_id = base_val.provenance_alloc_id()?;
                            let view_ty = crate::helpers::mir_utils::pointee_ty(base_val.ty)
                                .unwrap_or(base_val.ty);
                            self.memory.fields
                                .get(&(alloc_id, view_ty, path.clone()))
                                .map(|v| v.z3_term.clone())
                        })
                }
            }
            ContractExpr::Len(inner) => {
                // Try field-based len for Iter/IterMut first.
                if let Some(val) = self.eval_contract_expr_simple_value(inner) {
                    if let Some(term) = self.try_simple_iter_len(&val) {
                        return Some(term);
                    }
                }
                // A struct (e.g. `NodeRef`) whose `len()` reads `(*x.field).len`
                // through a `NonNull` field.
                if let ContractExpr::Place(cp) = &**inner {
                    if let Some(path) = cp.plain_field_path() {
                        let local = cp.base.to_local();
                        if let Some(ty) = self.field_type_at(local, &path) {
                            if let Some(term) = self.try_struct_nn_len_field(local, &path, ty) {
                                return Some(term);
                            }
                        }
                    }
                }
                let val = self.eval_contract_expr_simple_value(inner)?;
                self.len_from_value(&val)
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_contract_expr_simple(lhs)?;
                let r = self.eval_contract_expr_simple(rhs)?;
                Some(match op {
                    NumericBinOp::Mul => Int::mul(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Add => Int::add(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Sub => Int::sub(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Div => l.div(&r),
                    _ => return None,
                })
            }
            ContractExpr::Const(n) => Some(Int::from_u64(self.z3_ctx, *n as u64)),
            _ => None,
        }
    }

    fn eval_contract_expr_simple_value(
        &self,
        expr: &crate::verify::contract::ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
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
    fn is_iter_ref(&self, val: &VmValue<'z3, 'tcx>) -> bool {
        use rustc_middle::ty::TyKind;
        match val.ty.kind() {
            TyKind::Ref(_, pointee, _) => match pointee.kind() {
                TyKind::Adt(adt_def, _) => api_classify::is_std_iter_or_itermut(adt_def.did()),
                _ => false,
            },
            _ => false,
        }
    }

    /// When `lhs op rhs` compares an iterator's `ptr` and `end_or_len` pointers
    /// (the inlined form of `is_empty`: `ptr == end`), express the comparison
    /// element-wise as `iter_ptr_offset == base_len`. The operands may be plain
    /// temporaries (from the `as_ptr`/cast/field-read lowering), so the iterator
    /// is located via the shared buffer allocation (the `end` field's provenance
    /// alloc id). Returns `None` when this is not an iterator emptiness
    /// comparison.
    fn iter_ptr_comparison(
        &self,
        op: rustc_middle::mir::BinOp,
        lhs: &VmValue<'z3, 'tcx>,
        rhs: &VmValue<'z3, 'tcx>,
    ) -> Option<z3::ast::Bool<'z3>> {
        if !matches!(op, rustc_middle::mir::BinOp::Eq | rustc_middle::mir::BinOp::Ne) {
            return None;
        }
        let lp = lhs.provenance.as_ref()?;
        let rp = rhs.provenance.as_ref()?;
        if lp.alloc_id != rp.alloc_id {
            return None;
        }
        let (offset, base_len) = self.constraints.term_caches.iter_ptr_offset.get(&lp.alloc_id)?;
        let base_len = base_len.as_ref()?;
        let eq = offset._eq(base_len);
        Some(if matches!(op, rustc_middle::mir::BinOp::Eq) {
            eq
        } else {
            eq.not()
        })
    }

    fn try_simple_iter_len(&self, arg_val: &VmValue<'z3, 'tcx>) -> Option<Int<'z3>> {
        if !self.is_iter_ref(arg_val) {
            return None;
        }
        let local = Local::from_usize(1);
        let ptr = self.field_value(local, &[0])?;
        let end = self.field_value(local, &[1])?;
        self.iter_len_from_ptrs(ptr, end)
    }

    /// For a predicate of the form `self.len() != 0` (i.e. `!self.is_empty()`),
    /// if the self is an Iter/IterMut reference, return the field-based len term
    /// so that a `len >= 1` constraint can be added.
    fn try_simple_iter_len_from_pred(
        &self,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Int<'z3>> {
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
        let local_val = match self.current_frame.local_values.get(&local) {
            Some(v) => v,
            None => return,
        };
        if !self.is_iter_ref(local_val) {
            return;
        }
        let Some(buffer) = self.iter_buffer(local) else {
            return;
        };
        let one = Int::from_u64(self.z3_ctx, 1);
        let (new_offset, base_len) = match self.constraints.term_caches.iter_ptr_offset.get(&buffer) {
            Some((prev, base)) => (Int::add(self.z3_ctx, &[prev, &one]), base.clone()),
            None => {
                let base = self
                    .field_value(local, &[1])
                    .and_then(|end| end.provenance.as_ref())
                    .and_then(|ep| match &ep.offset_kind {
                        Some(OffsetKind::Element(e)) => Some(e.clone()),
                        _ => None,
                    });
                (one.clone(), base)
            }
        };
        // Mirror `try_iter_next`: the tracked offset must never exceed the
        // iterator's length (the inlined `post_inc_start` body itself only
        // mutates `ptr` and does not assert `offset <= len`).
        if let Some(e) = &base_len {
            self.constraints.assertions.push(new_offset.le(e));
        }
        self.constraints.term_caches.iter_ptr_offset.insert(buffer, (new_offset, base_len));
    }

    /// Set non_null invariant on the target value.
    fn set_non_null_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.invariants.non_null = true;
        self.set_contract_target_value(property, val);
    }

    fn set_in_bounds_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        val.invariants.in_bounds = true;
        self.set_contract_target_value(property, val);
    }

    fn assert_in_bound_for_each(
        &mut self,
        property: &Property<'tcx>,
        fe_place: &crate::verify::contract::ContractPlace<'tcx>,
    ) {
        let Some(fe_local) = fe_place.base.try_to_local() else {
            return;
        };
        let fe_val = match self.current_frame.local_values.get(&fe_local).cloned() {
            Some(v) => v,
            None => return,
        };
        let fe_alloc_id = match fe_val.provenance_alloc_id() {
            Some(id) => id,
            None => return,
        };
        let byte_vals: Vec<(usize, Int<'z3>)> = self.alloc_byte_values(fe_alloc_id);
        if byte_vals.is_empty() {
            return;
        }
        let slice_local = match property.args().first() {
            Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. })) => {
                match slice.as_ref() {
                    ContractExpr::Place(cp) => cp.base.try_to_local(),
                    _ => None,
                }
            }
            Some(PropertyArg::Expr(ContractExpr::Place(cp))) => cp.base.try_to_local(),
            _ => None,
        };
        let slice_val = slice_local.and_then(|loc| self.current_frame.local_values.get(&loc));
        let slice_alloc_id = slice_val.and_then(|sl_val| sl_val.provenance_alloc_id());
        let data_size = slice_alloc_id.map(|da_id| self.alloc(da_id).size.clone());
        let elem_sz = slice_alloc_id
            .and_then(|da_id| self.alloc(da_id).element_ty.as_ty())
            .map(|ty| self.size_of_ty(ty))
            .unwrap_or(1)
            .max(1);
        let Some(data_size) = data_size else { return };
        let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
        // Prefer the materialized slice length; fall back to `size / elem_size`.
        let len = slice_val
            .and_then(|sl_val| self.slice_len_from_value(sl_val))
            .unwrap_or_else(|| data_size.div(&elem_sz_term));
        let zero = Int::from_u64(self.z3_ctx, 0);
        for (_, term) in &byte_vals {
            self.constraints.assertions.push(term.ge(&zero));
            self.constraints.assertions.push(term.lt(&len));
        }
    }

    /// Record the numeric `index < len` bound for a single-index
    /// `InBound(slice, index)`, so a derived index (e.g. `index - 1` guarded by
    /// `index >= 1`) can be discharged by SMT rather than only via the coarse
    /// `in_bounds` flag. Range indices (`start..end`) are left to the checker's
    /// `extract_range_end` (`end <= len`).
    fn assert_in_bound_single(&mut self, property: &Property<'tcx>) {
        let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) =
            property.args().first()
        else {
            return;
        };
        if let ContractExpr::Place(index_place) = index.as_ref() {
            let index_local = index_place.base.to_local();
            if let rustc_middle::ty::TyKind::Adt(adt_def, _) =
                self.body().local_decls[index_local].ty.kind()
            {
                if crate::helpers::mir_utils::is_range_type(self.tcx, adt_def.did()) {
                    return;
                }
            }
        }
        let slice_local = match slice.as_ref() {
            ContractExpr::Place(cp) => cp.base.try_to_local(),
            _ => None,
        };
        let Some(slice_local) = slice_local else {
            return;
        };
        let Some(da_id) = self
            .current_frame.local_values
            .get(&slice_local)
            .and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        // Prefer the materialized slice length; fall back to `size / elem_size`
        // for allocations that never got a materialized `slice_len`.
        let alloc = self.alloc(da_id);
        let len = match alloc.slice_len() {
            Some(len) => len.clone(),
            None => {
                let elem_sz_term = alloc
                    .element_ty
                    .as_ty()
                    .map(|ty| self.size_sym_read(ty))
                    .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                alloc.size.div(&elem_sz_term)
            }
        };
        let Some(index_term) = self.eval_contract_expr_simple(index) else {
            return;
        };
        self.constraints.assertions.push(index_term.lt(&len));
    }

    /// When a `&T`/`&mut T` reference is created (e.g. via `&*NonNull<T>`), assume
    /// `T`'s `#[rapx::invariant]`s on the new reference local, rebinding the
    /// invariant's `self` place to that reference. This is what lets a struct's
    /// invariants flow through pointer dereferences into the caller's state.
    fn assert_pointee_struct_invariants(&mut self, dest_ty: Ty<'tcx>, dest_local: Local) {
        let pointee = match dest_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
            _ => return,
        };
        let adt_def = match pointee.kind() {
            rustc_middle::ty::TyKind::Adt(adt_def, _) => *adt_def,
            _ => return,
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let mut rebound = inv.clone();
            rebind_property_place(&mut rebound, dest_local);
            self.assert_contract_fact(&rebound);
        }
    }

    /// Assert a pointee ADT's `#[rapx::invariant]` struct invariants directly
    /// against its materialized per-allocation field values.  This is the
    /// pointer-field analogue of [`assert_pointee_struct_invariants`](Self::
    /// assert_pointee_struct_invariants): that helper covers `&T` references,
    /// while this one covers `NonNull<T>` / `Box<T>` pointer *fields* whose
    /// pointee is decomposed by `init_ptr_field` (e.g. `NodeRef.node:
    /// NonNull<LeafNode>` must satisfy `LeafNode`'s `len <= CAPACITY`).
    fn assert_alloc_pointee_invariants(&mut self, alloc_id: AllocId, pointee_ty: Ty<'tcx>) {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = pointee_ty.kind() else {
            return;
        };
        let invariants = crate::verify::target::get_struct_invariants_from_annotation(
            self.tcx,
            adt_def.did(),
            adt_def.did(),
        );
        for inv in &invariants {
            let Property::Atom(atom) = inv else {
                continue;
            };
            if atom.kind != PropertyKind::ValidNum {
                continue;
            }
            let Some(PropertyArg::Predicates(preds)) = atom.args.first() else {
                continue;
            };
            for pred in preds {
                if let Some(cond) = self.eval_pointee_predicate_as_bool(alloc_id, pointee_ty, pred)
                {
                    self.constraints.assertions.push(cond);
                }
            }
        }
    }

    /// Evaluate a `ValidNum` predicate against a pointee allocation (not a MIR
    /// local): field places resolve through `memory.fields` keyed by the
    /// pointee type.
    fn eval_pointee_predicate_as_bool(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        pred: &crate::verify::contract::NumericPredicate<'tcx>,
    ) -> Option<Bool<'z3>> {
        let lhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.lhs)?;
        let rhs = self.eval_pointee_expr(alloc_id, view_ty, &pred.rhs)?;
        Some(self.relop_to_bool(pred.op, &lhs, &rhs))
    }

    /// Evaluate a numeric `ContractExpr` against a pointee allocation.
    fn eval_pointee_expr(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<Int<'z3>> {
        use crate::verify::contract::NumericBinOp;
        match expr {
            ContractExpr::Const(v) => Some(Int::from_u64(self.z3_ctx, *v as u64)),
            ContractExpr::SizeOf(ty) => Some(self.size_sym_read(*ty)),
            ContractExpr::AlignOf(ty) => Some(self.align_sym_read(*ty)),
            ContractExpr::Place(cp) => {
                let path = cp.plain_field_path()?;
                self.memory.fields
                    .get(&(alloc_id, view_ty, path))
                    .map(|v| v.z3_term.clone())
            }
            ContractExpr::Binary { op, lhs, rhs } => {
                let l = self.eval_pointee_expr(alloc_id, view_ty, lhs)?;
                let r = self.eval_pointee_expr(alloc_id, view_ty, rhs)?;
                Some(match op {
                    NumericBinOp::Add => Int::add(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Sub => Int::sub(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Mul => Int::mul(self.z3_ctx, &[&l, &r]),
                    NumericBinOp::Div => l.div(&r),
                    NumericBinOp::Rem => l.rem(&r),
                    _ => return None,
                })
            }
            ContractExpr::Len(inner) => {
                let val = self.eval_pointee_expr_value(alloc_id, view_ty, inner)?;
                self.slice_len_from_value(&val)
            }
            _ => None,
        }
    }

    /// Resolve a `Place` (or `Len` inner) against a pointee allocation, returning
    /// the materialized `VmValue` so slice-length fallbacks can read provenance.
    fn eval_pointee_expr_value(
        &self,
        alloc_id: AllocId,
        view_ty: Ty<'tcx>,
        expr: &ContractExpr<'tcx>,
    ) -> Option<VmValue<'z3, 'tcx>> {
        let ContractExpr::Place(cp) = expr else {
            return None;
        };
        let path = cp.plain_field_path()?;
        self.memory.fields
            .get(&(alloc_id, view_ty, path))
            .cloned()
    }

    /// Set align invariant on the target value.
    fn set_align_for_value(&mut self, property: &Property<'tcx>, mut val: VmValue<'z3, 'tcx>) {
        if let Some(PropertyArg::Ty(ty)) = property.args().get(1) {
            let align = self.align_sym(*ty);
            if align.simplify().as_u64() != Some(1) {
                val.invariants.align_n = Some(align.clone());
                // For a *concrete* alignment, also record `term % align == 0` as a
                // path condition.  `align_n` is a value invariant that pointer
                // arithmetic (`ptr.add(n)`) drops, but the alignment fact itself
                // persists: a downstream `Align(p, T)` on `p = ptr.add(n)` can then
                // combine `term % align == 0` with the `n % align == 0` mask fact to
                // prove `p % align == 0`.  (A symbolic `align_T` is skipped — the
                // non-linear `% align_T` is not decidable, so `align_n` alone is
                // used for that case.)
                if align.simplify().as_u64().is_some() {
                    self.constraints.assertions.push(
                        val.z3_term
                            .rem(&align)
                            ._eq(&Int::from_u64(self.z3_ctx, 0)),
                    );
                }
            }
        }
        self.set_contract_target_value(property, val);
    }

    /// Set init invariant on the target value and its allocation.
    fn set_init_for_value(&mut self, property: &Property<'tcx>, val: VmValue<'z3, 'tcx>) {
        // `Init(p, MaybeUninit<T>, n)` reduces to `Typed(p, MaybeUninit<T>)`: the
        // content carries no validity invariant, so there is nothing to mark
        // initialized — the `Init ⇒ Typed` subsumption records the element type.
        let is_maybe_uninit = property
            .args()
            .get(1)
            .and_then(|a| {
                if let PropertyArg::Ty(ty) = a {
                    Some(api_classify::is_maybe_uninit_ty(*ty))
                } else {
                    None
                }
            })
            .unwrap_or(false);
        if is_maybe_uninit {
            return;
        }
        if let Some(prov) = &val.provenance {
            self.alloc_mut(prov.alloc_id).initialized = true;
        }
        if let Some((local, path)) = self.contract_field_path(property) {
            let existing = if path.is_empty() {
                self.current_frame.local_values.get(&local).cloned()
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
    fn set_owning_for_value(&mut self, val: VmValue<'z3, 'tcx>) {
        if let Some(prov) = &val.provenance {
            self.alloc_mut(prov.alloc_id).initialized = true;
        }
    }

    /// Record the `Align(container.iter(), T)` for_each fact: every element
    /// pointer is aligned to `align_of(T)`.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Align(cur, T)`.
    fn record_for_each_align(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(ty) = property.args().get(1).and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return;
        };
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).for_each.aligned_ty = Some(ty);
    }

    /// Record the `Allocated(container.iter(), T, n)` for_each fact: every
    /// element pointer backs `>= n` `T` elements (`n` may be symbolic).
    fn record_for_each_allocated(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(ty) = property.args().get(1).and_then(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        }) else {
            return;
        };
        let count = property
            .args()
            .get(2)
            .and_then(|a| self.resolve_contract_count(a))
            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).for_each.allocated = Some((ty, count));
    }

    /// Record the `Owning(container.iter())` for_each fact: every element
    /// pointer is the sole owner of its pointee.  Anchored to the container
    /// allocation so a pointer loaded from it can discharge `Owning(cur)`.
    fn record_for_each_owning(&mut self, property: &Property<'tcx>) {
        if property.for_each().is_none() {
            return;
        }
        let Some(alloc_id) = self.contract_target_value(property).and_then(|v| v.provenance_alloc_id())
        else {
            return;
        };
        self.alloc_mut(alloc_id).for_each.owning = true;
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

    /// If `operand` is a constant reference to a byte array (e.g. `b"hello\0"`),
    /// extract the raw bytes and create a tracked allocation. Updates `val`
    /// in-place with the proper provenance and invariants.
    pub(crate) fn try_materialize_const_bytes(
        &mut self,
        val: &mut VmValue<'z3, 'tcx>,
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
                let is_byte = matches!(
                    elem_ty.kind(),
                    rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                        | rustc_middle::ty::TyKind::Int(rustc_middle::ty::IntTy::I8)
                );
                if is_byte {
                    let bytes_opt =
                        crate::helpers::mir_utils::const_operand_bytes(self.tcx, operand)
                            .or_else(|| self.trace_to_const_bytes(operand));
                    if let Some(bytes) = bytes_opt {
                        let size = z3::ast::Int::from_u64(self.z3_ctx, bytes.len() as u64);
                        let align = self.align_sym(pointee_ty);
                        let (alloc_id, base) = self.allocate(size, align, Some(pointee_ty));
                        self.alloc_mut(alloc_id).initialized = true;
                        // A const/static byte materialization lives for the
                        // whole program (`'static`), so it is always alive.
                        self.alloc_mut(alloc_id).liveness =
                            Some(self.tcx.lifetimes.re_static);
                        for (i, &b) in bytes.iter().enumerate() {
                            self.record_byte_value(
                                alloc_id,
                                i,
                                z3::ast::Int::from_u64(self.z3_ctx, b as u64),
                            );
                            if b == 0 {
                                self.mark_byte_nul(alloc_id, i);
                            } else {
                                self.mark_byte_non_nul(alloc_id, i);
                            }
                        }
                        val.z3_term = base;
                        val.provenance = Some(super::state::Provenance {
                            alloc_id,
                            offset: z3::ast::Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        });
                        val.invariants = ValueInvariants {
                            non_null: true,
                            init: true,
                            in_bounds: false,
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
        let base_local = if place.projection.is_empty()
            || (place.projection.len() == 1
                && matches!(
                    place.projection.first().map(|p| p.kind()),
                    Some(rustc_middle::mir::ProjectionElem::Deref)
                ))
        {
            place.local
        } else {
            return None;
        };
        for block in self.body().basic_blocks.iter() {
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
            .current_frame
            .field_values
            .keys()
            .filter(|(l, _)| *l == source_place.local)
            .map(|(_, p)| p.clone())
            .collect();
        for path in keys {
            let matches_prefix = field_prefix.is_empty()
                || (path.len() >= field_prefix.len()
                    && path[..field_prefix.len()] == field_prefix[..]);
            if matches_prefix {
                let rest = if field_prefix.is_empty() {
                    path.clone()
                } else {
                    path[field_prefix.len()..].to_vec()
                };
                if let Some(v) = self
                    .current_frame
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
        ref_val: &VmValue<'z3, 'tcx>,
    ) {
        let Some(src_alloc_id) = self.current_frame.local_alloc.get(&source_place.local).copied() else {
            return;
        };
        let Some(ref_alloc_id) = ref_val.provenance_alloc_id() else {
            return;
        };
        if src_alloc_id == ref_alloc_id {
            return; // same allocation, bytes already there
        }
        // Copy per-byte tracking from source alloc to ref's alloc (offset 0:
        // the reference points at the source place's start).
        self.copy_byte_tracking(src_alloc_id, 0, ref_alloc_id);
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

/// Try to resolve a u64 constant from a PlaceKey's source in the VM state.
fn resolve_u64_from_place_key<'z3, 'tcx>(
    pk: &Option<PlaceKey>,
    state: &VmState<'z3, 'tcx>,
) -> Option<u64> {
    let pk = pk.as_ref()?;
    let local = pk.local()?;
    let val = state.local_value(local)?;
    val.z3_term.as_u64()
}

/// Largest power-of-two factor of a non-negative constant (the alignment
/// implied by multiplying by `c`): `c` itself if it is a power of two,
/// otherwise `2^trailing_zeros(c)`.
fn pow2_factor(c: u64) -> Option<u64> {
    if c > 0 && c.is_power_of_two() {
        Some(c)
    } else if c > 0 {
        let factor = 1u64 << c.trailing_zeros();
        if factor > 1 { Some(factor) } else { None }
    } else {
        None
    }
}

/// Rebind every `self` place in a struct invariant to the given MIR local, so
/// an invariant parsed against the struct's own `self` can be asserted on a
/// freshly-created reference (`&*NonNull<T>` → `&T`).
fn rebind_property_place<'tcx>(property: &mut Property<'tcx>, local: Local) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                match arg {
                    PropertyArg::Expr(expr) => rebind_expr_place(expr, local),
                    PropertyArg::Predicates(preds) => {
                        for pred in preds {
                            rebind_expr_place(&mut pred.lhs, local);
                            rebind_expr_place(&mut pred.rhs, local);
                        }
                    }
                    _ => {}
                }
            }
        }
        Property::And(and) => {
            for c in &mut and.conjuncts {
                rebind_property_place(c, local);
            }
        }
        Property::Or(or) => {
            for d in &mut or.disjuncts {
                rebind_property_place(d, local);
            }
        }
    }
}

fn rebind_expr_place<'tcx>(expr: &mut ContractExpr<'tcx>, local: Local) {
    match expr {
        ContractExpr::Place(cp) => {
            cp.base = PlaceBase::Local(local.as_usize());
        }
        ContractExpr::Len(inner) => rebind_expr_place(inner, local),
        ContractExpr::IndexAccess { slice, index } => {
            rebind_expr_place(slice, local);
            rebind_expr_place(index, local);
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            rebind_expr_place(lhs, local);
            rebind_expr_place(rhs, local);
        }
        ContractExpr::Unary { expr: inner, .. } => rebind_expr_place(inner, local),
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            rebind_expr_place(&mut cond.lhs, local);
            rebind_expr_place(&mut cond.rhs, local);
            rebind_expr_place(then_expr, local);
            rebind_expr_place(else_expr, local);
        }
        _ => {}
    }
}
