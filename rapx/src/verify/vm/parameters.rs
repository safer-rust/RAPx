//! Initialize symbolic function parameters and their backing allocations.

use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind};
use rustc_middle::ty::{Ty, TyKind};
use z3::ast::Int;

use crate::compat::FxHashMap;
use crate::helpers::mir_utils;
use crate::verify::api_classify;

use super::state::{AllocId, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(crate) fn materialize_constructor_result(
        &mut self,
        destination: Local,
        args: &[VmValue<'z3, 'tcx>],
        callee: rustc_hir::def_id::DefId,
        has_invariant: bool,
    ) {
        let ty = self.body().local_decls[destination].ty;
        if !has_invariant {
            self.set_local(destination, VmValue::new(self.fresh_int("ctor_unknown"), ty));
            return;
        }
        if let TyKind::Adt(adt, substs) = ty.kind()
            && api_classify::is_std_nonnull(adt.did())
            && self.tcx.item_name(callee).as_str() == "dangling"
        {
            let field_ty = mir_utils::field_ty(
                self.tcx,
                adt.non_enum_variant().fields.iter().next().unwrap(),
                substs,
            );
            let value = VmValue {
                z3_term: self.fresh_int("dangling_ptr"),
                ty,
                provenance: None,
                facts: ValueFacts {
                    non_null: true,
                    dangling: true,
                    ..Default::default()
                },
                source: ValueSource::None,
            };
            let mut field = value.clone();
            field.ty = field_ty;
            self.set_field_value(destination, vec![0], field);
            self.set_local(destination, value);
            return;
        }
        if let TyKind::Adt(adt, substs) = ty.kind()
            && mir_utils::is_raw_ptr_wrapper(self.tcx, adt.did())
            && let [pointer] = args
            && matches!(pointer.ty.kind(), TyKind::RawPtr(..))
        {
            let field_ty = mir_utils::field_ty(
                self.tcx,
                adt.non_enum_variant().fields.iter().next().unwrap(),
                substs,
            );
            let mut field = pointer.clone();
            field.ty = field_ty;
            self.set_field_value(destination, vec![0], field);
            let mut value = pointer.clone();
            value.ty = ty;
            self.set_local(destination, value);
            return;
        }
        let mut facts = ValueFacts::default();
        if self.init_box_vec_param(destination, ty, destination.as_usize(), &mut facts)
            || self.init_struct_param(destination, ty, destination.as_usize(), &mut facts)
        {
            return;
        }
        self.set_local(
            destination,
            VmValue {
                z3_term: self.fresh_int("ctor_result"),
                ty,
                provenance: None,
                facts,
                source: ValueSource::None,
            },
        );
    }

    pub(crate) fn init_parameters(&mut self) {
        let arg_count = self.body().arg_count;
        let local_count = self.body().local_decls.len();

        for local_idx in 1..local_count {
            let local = Local::from_usize(local_idx);
            if self.current_frame.local_alloc.contains_key(&local) {
                continue;
            }
            let decl = &self.body().local_decls[local];
            let ty = decl.ty;

            self.ensure_local_allocation(local);

            let mut invariants = ValueFacts::default();
            if local_idx <= arg_count {
                if self.init_box_vec_param(local, ty, local_idx, &mut invariants) {
                    continue;
                }
                if self.init_struct_param(local, ty, local_idx, &mut invariants) {
                    continue;
                }
                if self.init_reference_param(local, ty, local_idx, &mut invariants) {
                    continue;
                }
                let is_scalar = matches!(
                    ty.kind(),
                    rustc_middle::ty::TyKind::Uint(_)
                        | rustc_middle::ty::TyKind::Int(_)
                        | rustc_middle::ty::TyKind::Float(_)
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
                            facts: invariants,
                            source: ValueSource::None,
                        },
                    );
                    continue;
                }
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
                            facts: invariants,
                            source: ValueSource::None,
                        },
                    );
                    continue;
                }
                if self.init_array_param(local, ty, local_idx, &mut invariants) {
                    continue;
                }
                let term = self.fresh_int(&format!("param_{}", local_idx));
                self.set_local(
                    local,
                    VmValue {
                        z3_term: term,
                        ty,
                        provenance: None,
                        facts: invariants,
                        source: ValueSource::None,
                    },
                );
                continue;
            }
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
                    facts: invariants,
                    source: ValueSource::None,
                },
            );
        }

        self.propagate_entry_block_provenance();
        self.prewarm_generic_size_align();
    }

    /// Initialize a struct/tuple/enum parameter (a non-`Box`/`Vec` ADT):
    /// decompose it into per-field symbolic values for field-level checking.
    fn init_struct_param(
        &mut self,
        local: Local,
        ty: Ty<'tcx>,
        local_idx: usize,
        invariants: &mut ValueFacts<'z3>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return false;
        };
        if adt_def.is_enum() {
            let term = self.fresh_int(&format!("param_{}", local_idx));
            self.set_local(
                local,
                VmValue {
                    z3_term: term,
                    ty,
                    provenance: None,
                    facts: invariants.clone(),
                    source: ValueSource::None,
                },
            );
            return true;
        }
        let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)> = FxHashMap::default();
        self.decompose_adt_fields(local, vec![], ty, local_idx, &mut elem_alloc, 0);
        // A single-raw-pointer wrapper (e.g. `NonNull<T>`) *is* its pointer, so
        // carry the field's provenance onto the whole local — otherwise
        // alias/ownership reasoning can't trace a deref of `self.pointer` back to
        // "owned" (the local's provenance would be `None`).
        if mir_utils::is_raw_ptr_wrapper(self.tcx, adt_def.did())
            && let Some(f0) = self.field_value(local, &[0]).cloned() {
                let prov = f0.provenance.clone();
                self.set_local(
                    local,
                    VmValue {
                        z3_term: f0.z3_term,
                        ty,
                        provenance: prov,
                        facts: ValueFacts {
                            init: true,
                            ..Default::default()
                        },
                        source: ValueSource::None,
                    },
                );
                return true;
            }
        let term = self.fresh_int(&format!("param_{}", local_idx));
        self.set_local(
            local,
            VmValue {
                z3_term: term,
                ty,
                provenance: None,
                facts: ValueFacts {
                    init: true,
                    ..Default::default()
                },
                source: ValueSource::None,
            },
        );
        true
    }

    /// Initialize a `Box`/`Vec`/`CString` parameter: allocate its heap pointee,
    /// expose the owning pointer field, and (for `Vec`) bind symbolic
    /// `len`/`cap`.
    fn init_box_vec_param(
        &mut self,
        local: Local,
        ty: Ty<'tcx>,
        local_idx: usize,
        invariants: &mut ValueFacts<'z3>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Adt(adt_def, substs) = ty.kind() else {
            return false;
        };
        let is_vec = api_classify::is_std_vec(adt_def.did());
        let is_string = api_classify::is_std_string(adt_def.did());
        let is_cstring = api_classify::is_std_cstring(adt_def.did());
        if !(api_classify::is_std_box(adt_def.did()) || is_vec || is_string || is_cstring) {
            return false;
        }
        let heap_ty = if is_string {
            self.tcx.types.u8
        } else {
            substs.first().and_then(|s| s.as_type()).unwrap_or(ty)
        };
        let slice_elem = match heap_ty.kind() {
            TyKind::Slice(elem) if !is_vec && !is_cstring => Some(*elem),
            TyKind::Str if !is_vec && !is_cstring => Some(self.tcx.types.u8),
            _ => None,
        };
        let heap_size = self.size_of_ty(heap_ty);
        let heap_align = self.align_sym(slice_elem.unwrap_or(heap_ty));
        let heap_size_term = Int::from_u64(self.z3_ctx, heap_size.max(1));
        // Vec/CString can hold many elements — use an external allocation so
        // Allocated checks can pass for arbitrary capacity queries.
        let (heap_alloc_id, heap_base) = if let Some(elem) = slice_elem {
            let len = self.fresh_int(&format!("slice_len_{}", local_idx));
            let zero = Int::from_u64(self.z3_ctx, 0);
            self.constraints.assertions.push(len.ge(&zero));
            let elem_size = self.size_sym(elem);
            self.allocate_slice(len, elem_size, heap_align, Some(elem))
        } else if is_vec || is_string {
            let cap = self.fresh_int(&format!("vec_cap_{}", local_idx));
            let len = self.fresh_int(&format!("vec_len_{}", local_idx));
            self.materialize_vec_len_cap(cap.clone(), len.clone(), heap_size);
            let elem_size = self.size_sym(heap_ty);
            let bytes = Int::mul(self.z3_ctx, &[&cap, &elem_size]);
            let (alloc_id, base) = self.allocate_external(bytes, heap_align, Some(heap_ty));
            self.alloc_mut(alloc_id).set_slice_len(len);
            (alloc_id, base)
        } else if is_cstring {
            let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
            self.allocate_external(max_size, heap_align.clone(), Some(heap_ty))
        } else {
            self.allocate(heap_size_term, heap_align, Some(heap_ty))
        };
        invariants.non_null = true;
        invariants.init = true;
        self.content_mut(heap_alloc_id).facts.initialized = true;
        // Also expose the container's owning pointer field (Box's inner
        // `Unique<T>.pointer` → `NonNull<T>`, Vec's `buf.ptr.pointer`) so that
        // inlined bodies like `Box::into_non_null_with_allocator` — which reads
        // `(_1.0).0` and transmutes it to `NonNull<T>` — inherit the heap
        // pointer's non-null/aligned/allocated facts.
        let owner_path = self
            .container_ptr_field(ty)
            .expect("container parameter has no owning pointer field");
        self.set_field_value(
            local,
            owner_path,
            VmValue {
                z3_term: heap_base.clone(),
                ty,
                provenance: Some(Provenance {
                    alloc_id: heap_alloc_id,
                    offset: Int::from_u64(self.z3_ctx, 0),
                    offset_kind: None,
                }),
                facts: ValueFacts {
                    non_null: true,
                    init: true,
                    ..Default::default()
                },
                source: ValueSource::None,
            },
        );
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
                facts: invariants.clone(),
                source: ValueSource::None,
            },
        );
        true
    }

    /// Initialize an array parameter (`[T; N]`): give it a real allocation with
    /// provenance so downstream call effects can record the alloc_id.
    fn init_array_param(
        &mut self,
        local: Local,
        ty: Ty<'tcx>,
        local_idx: usize,
        invariants: &mut ValueFacts<'z3>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Array(elem_ty, const_len) = ty.kind() else {
            return false;
        };
        let n: Option<usize> = mir_utils::eval_array_len(self.tcx, const_len).map(|v| v as usize);
        let elem_size = self.size_of_ty(*elem_ty);
        let step = (elem_size.max(1)) as usize;
        let align = self.align_sym(*elem_ty);
        let elem_sym = self.size_sym(*elem_ty);
        let n_term = self.const_len_term(const_len);
        let (alloc_id, base) = self.allocate_slice(n_term, elem_sym, align, Some(*elem_ty));
        self.content_mut(alloc_id).facts.initialized = true;
        self.current_frame.local_alloc.insert(local, alloc_id);
        invariants.init = true;
        for i in 0..n.unwrap_or(16) {
            let off = i * step;
            let elem_term = self.fresh_int(&format!("array_{}_idx_{}", local_idx, i));
            self.record_byte_value(alloc_id, off, elem_term);
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
                facts: invariants.clone(),
                source: ValueSource::None,
            },
        );
        true
    }

    /// Initialize a reference parameter (`&T`, `&mut T`): create a symbolic
    /// allocation for the pointee, attach provenance, and (for a struct pointee)
    /// materialize its pointer/scalar fields.
    fn init_reference_param(
        &mut self,
        local: Local,
        ty: Ty<'tcx>,
        local_idx: usize,
        invariants: &mut ValueFacts<'z3>,
    ) -> bool {
        let rustc_middle::ty::TyKind::Ref(..) = ty.kind() else {
            return false;
        };
        let precise_pointee = crate::verify::vm::region::fn_arg_ty(
            self.tcx,
            self.current_frame.current_def_id,
            local_idx - 1,
        )
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
        // `&MaybeUninit<T>` / `&[MaybeUninit<T>]` carry no validity invariant —
        // the content need not be initialized — so do not claim `Init` for them
        // (the content property reduces to `Typed`).
        let pointee_is_maybe_uninit = api_classify::is_maybe_uninit_ty(pointee_ty);

        invariants.non_null = true;
        if !pointee_is_maybe_uninit {
            invariants.init = true;
        }
        // A reference always points within a live allocation, so it carries the
        // pointer-validity facts (`NonNull`, `Allocated`, `InBound`) explicitly —
        // the content property `Init` must not be the only source of pointer
        // validity (see std-subsumption.rs).
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
                mir_utils::size_of_generic_param(
                    self.tcx,
                    self.current_frame.current_def_id,
                    *elem_ty,
                )
                .max(1)
            };
            let elem_sz_term = Int::from_u64(self.z3_ctx, elem_sz);
            self.constraints
                .assertions
                .push(Int::mul(self.z3_ctx, &[&len, &elem_sz_term]).le(&isize_max));
            if let TyKind::Array(inner_ty, count) = elem_ty.kind() {
                let inner_size = self.size_sym(*inner_ty);
                let count = self.const_len_term(count);
                self.constraints.assertions.push(count.ge(&zero));
                let flat_len = Int::mul(self.z3_ctx, &[&len, &count]);
                self.constraints
                    .assertions
                    .push(inner_size.gt(&zero).implies(&flat_len.le(&isize_max)));
            }
            // The data allocation's byte size uses the shared symbolic `sizeof_T`
            // so `InBound` can cancel the factor (`len·S / S == len`);
            // `allocate_slice` computes `size = len * sizeof_T` and materializes
            // `len` together so the two can never diverge. The alignment is the
            // element type's alignment — symbolic (`align_T`) for a generic
            // element type, with the layout constraint `sizeof_T % align_T == 0`
            // established by `align_sym`.
            let elem_align = self.align_sym(*elem_ty);
            let elem_size_sym = self.size_sym(*elem_ty);
            let (data_alloc_id, data_base) =
                self.allocate_slice(len, elem_size_sym, elem_align, Some(*elem_ty));
            if !pointee_is_maybe_uninit {
                self.content_mut(data_alloc_id).facts.initialized = true;
            }
            // Record placeholder per-byte symbols for the first few elements so
            // byte-level checkers (`ValidCStr` interior-NUL, `ValidString` UTF-8)
            // can reason over symbolic slice bytes (the length is symbolic, so
            // only a bounded prefix is materialized — mirrors the array parameter
            // handling).
            let step = (elem_size.max(1)) as usize;
            let m = 16usize;
            for i in 0..m {
                let off = i * step;
                let elem_term = self.fresh_int(&format!("slice_{}_idx_{}", local_idx, i));
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
                    facts: invariants.clone(),
                    source: ValueSource::None,
                },
            );
            return true;
        }

        let (pointee_alloc_id, pointee_base) = if let rustc_middle::ty::TyKind::Array(elem_ty, const_len) = pointee_ty.kind() {
            let n = self.const_len_term(const_len);
            let elem_size = self.size_sym(*elem_ty);
            let elem_align = self.align_sym(*elem_ty);
            self.allocate_slice(n, elem_size, elem_align, Some(*elem_ty))
        } else {
            let pointee_align = self.align_sym(pointee_ty);
            let pointee_size_term = self
                .struct_size_sym(pointee_ty)
                .unwrap_or_else(|| self.size_sym(pointee_ty));
            self.allocate(pointee_size_term, pointee_align, Some(pointee_ty))
        };
        if !pointee_is_maybe_uninit {
            self.content_mut(pointee_alloc_id).facts.initialized = true;
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
                facts: invariants.clone(),
                source: ValueSource::None,
            },
        );

        // Keep a shared symbolic value for an immutable scalar referent. A
        // dereference and a later comparison trait call must observe the same
        // value; the pointer address itself is not the scalar value.
        if matches!(ty.kind(), TyKind::Ref(_, _, rustc_middle::ty::Mutability::Not))
            && matches!(pointee_ty.kind(), TyKind::Uint(_) | TyKind::Int(_) | TyKind::Bool | TyKind::Char)
        {
            let scalar = self.fresh_int(&format!("ref_arg_{local_idx}_value"));
            let mut value = VmValue::new(scalar, pointee_ty);
            value.source = ValueSource::SharedScalarReferent;
            self.store_value(
                pointee_alloc_id,
                pointee_ty,
                Vec::new(),
                value,
            );
        }

        if let rustc_middle::ty::TyKind::Adt(adt_def, substs) = pointee_ty.kind()
            && !adt_def.is_enum() {
                let variant = adt_def.non_enum_variant();
                let mut elem_alloc: FxHashMap<Ty<'tcx>, (AllocId, Int<'z3>)> =
                    FxHashMap::default();
                for (idx, field_def) in variant.fields.iter().enumerate() {
                    let field_ty: Ty<'tcx> = mir_utils::field_ty(self.tcx, field_def, substs);
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
                            "ref_field",
                        );
                    } else if let rustc_middle::ty::TyKind::Ref(region, pointee, _) =
                        field_ty.kind()
                    {
                        let elem_ty = match pointee.kind() {
                            rustc_middle::ty::TyKind::Slice(e) => *e,
                            _ => *pointee,
                        };
                        self.materialize_external_field(local, idx, field_ty, elem_ty, Some(*region));
                    } else if let rustc_middle::ty::TyKind::Slice(elem_ty) = field_ty.kind() {
                        // DST slice field (e.g. `CStr { inner: [u8] }`): model it
                        // as an external allocation so its length stays symbolic
                        // instead of defaulting to a single element (which would
                        // make `inner.len()` == 1).
                        self.materialize_external_field(local, idx, field_ty, *elem_ty, None);
                    } else if let rustc_middle::ty::TyKind::Adt(adt, substs) = field_ty.kind() {
                        // A heap-backed smart-pointer field (`Box<[T]>`, `Vec<T>`)
                        // inside a referenced struct: materialize the pointee
                        // allocation so field access (e.g. `self.buckets.iter()`)
                        // resolves to the *data* elements, not the whole struct.
                        if (api_classify::is_std_box(adt.did())
                            || api_classify::is_std_vec(adt.did()))
                            && let Some(pointee) = substs.first().and_then(|s| s.as_type())
                            {
                                let elem_ty = match pointee.kind() {
                                    rustc_middle::ty::TyKind::Slice(e) => *e,
                                    _ => pointee,
                                };
                                self.materialize_external_field(local, idx, field_ty, elem_ty, None);
                            } else if !adt.is_enum() && api_classify::is_std_vec(adt.did()) {
                                self.materialize_vec_ptr_field(local, vec![idx], field_ty);
                            }
                    } else if matches!(
                        field_ty.kind(),
                        rustc_middle::ty::TyKind::Uint(_)
                            | rustc_middle::ty::TyKind::Int(_)
                            | rustc_middle::ty::TyKind::Float(_)
                            | rustc_middle::ty::TyKind::Bool
                            | rustc_middle::ty::TyKind::Char
                    ) {
                        // Scalar field (e.g. `size: usize`) inside a referenced
                        // struct. Materialize a fresh symbolic value so that field
                        // reads return the correct term instead of the whole struct
                        // term. Non-scalar, non-pointer ADT fields (Box/Vec/etc.)
                        // are left unset so they keep their pre-existing heap
                        // modeling.
                        let field_term =
                            self.fresh_int(&format!("ref_field_{}_{}", local_idx, idx));
                        self.set_field_value(
                            local,
                            vec![idx],
                            VmValue {
                                z3_term: field_term,
                                ty: field_ty,
                                provenance: None,
                                facts: ValueFacts {
                                    init: true,
                                    ..Default::default()
                                },
                                source: ValueSource::None,
                            },
                        );
                    }
                }
            }
        true
    }

    /// Propagate parameter provenance through the entry block's simple
    /// assignments (`_tmp = _1`, `_tmp = _1 as *const T`), which the backward
    /// slicer may omit as same-block definitions.
    fn propagate_entry_block_provenance(&mut self) {
        let Some(entry_bb) = self.body().basic_blocks.iter().next() else {
            return;
        };
        for stmt in &entry_bb.statements {
            let StatementKind::Assign(assign) = &stmt.kind else {
                continue;
            };
            let (dest, rvalue) = &**assign;
            let dest_local = dest.local;
            let src = match rvalue {
                Rvalue::Use(operand, ..) => Some(operand),
                Rvalue::Cast(_, operand, _) => Some(operand),
                _ => None,
            }
            .and_then(|operand| match operand {
                Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                    Some(place.local)
                }
                _ => None,
            });
            if let Some(src_local) = src
                && let Some(src_val) = self.local_value(src_local) {
                    let has_better_prov = src_val.is_pointer()
                        && src_val.facts.non_null
                        && self.local_value(dest_local).is_none_or(|d| {
                            d.provenance.is_none() || !d.facts.non_null
                        });
                    if has_better_prov {
                        self.set_local(
                            dest_local,
                            VmValue {
                                z3_term: src_val.z3_term.clone(),
                                ty: dest.ty(self.body(), self.tcx).ty,
                                provenance: src_val.provenance.clone(),
                                facts: src_val.facts.clone(),
                                source: ValueSource::None,
                            },
                        );
                    }
                }
        }
    }

}
