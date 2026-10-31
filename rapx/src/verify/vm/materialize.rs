//! Materialize external fields and pointee values in symbolic memory.

use rustc_middle::mir::{Local, Operand, Place, Rvalue, StatementKind};
use rustc_middle::ty::{Region, Ty, TyKind};
use z3::ast::Int;

use crate::compat::{FxHashMap, FxHashSet};
use crate::helpers::mir_utils;

use super::state::{AllocId, OffsetKind, Provenance, ValueFacts, ValueSource, VmState, VmValue};

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Pre-warm a shared symbolic `sizeof_T` / `align_T` for every generic type
    /// parameter of the caller, so the read-only `*_sym_read` fallback is dead.
    pub(crate) fn prewarm_generic_size_align(&mut self) {
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
    pub(crate) fn materialize_external_field(
        &mut self,
        local: Local,
        idx: usize,
        field_ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        alive_region: Option<Region<'tcx>>,
    ) {
        self.materialize_external_field_at(local, vec![idx], field_ty, elem_ty, alive_region);
    }

    /// Materialize an external (unbounded) allocation and bind it as the value at
    /// `path`, carrying data provenance and an optional liveness region. Shared by
    /// the whole-field (`materialize_external_field`) and pointer-subfield
    /// (`materialize_vec_ptr_field`) materialization paths.
    fn materialize_external_field_at(
        &mut self,
        local: Local,
        path: Vec<usize>,
        field_ty: Ty<'tcx>,
        elem_ty: Ty<'tcx>,
        alive_region: Option<Region<'tcx>>,
    ) {
        let align = self.align_sym(elem_ty);
        let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
        let (alloc_id, base) = self.allocate_external(max_size, align, Some(elem_ty));
        self.content_mut(alloc_id).facts.initialized = true;
        if let Some(region) = alive_region {
            self.alloc_mut(alloc_id).facts.liveness = Some(region);
        }
        self.set_field_value(
            local,
            path,
            VmValue {
                z3_term: base,
                ty: field_ty,
                provenance: Some(Provenance {
                    alloc_id,
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
    }

    /// Initialize one pointer-like field (raw pointer or `NonNull<T>`) of a
    /// decomposed struct/ref parameter. The first field with a given pointee
    /// type creates a shared external allocation; later fields with the same
    /// pointee reuse it with a symbolic offset, preserving relationships like
    /// `ptr = start, end_or_len = start + len`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn init_ptr_field(
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
        let mut invariants = if is_raw_ptr {
            // A raw pointer carries no non-null / init / align guarantee; those
            // facts must come from the struct's own `#[rapx::invariant]`s.
            ValueFacts::default()
        } else {
            ValueFacts {
                init: true,
                align_n: Some(self.align_sym(pointee)),
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
            invariants.align_n = Some(elem_align);
            self.set_field_value(
                local,
                path,
                VmValue {
                    z3_term: field_term,
                    ty: field_ty,
                    provenance: Some(Provenance {
                        alloc_id: existing_alloc,
                        offset: prost_offset.clone(),
                        offset_kind: Some(OffsetKind::Element {
                            index: len_term.clone(),
                            stride: elem_size.clone(),
                        }),
                    }),
                    facts: invariants,
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
            let tail = (!is_raw_ptr).then(|| self.unsized_tail_layout(pointee)).flatten();
            let tail_len = tail.map(|_| self.fresh_int(&format!("field_len_{}_{}", local_idx, idx)));
            let max_size = if is_raw_ptr {
                let s = self.fresh_int("raw_target_size");
                self.constraints.assertions.push(s.ge(&Int::from_u64(self.z3_ctx, 0)));
                s
            } else if let (Some((elem, offset)), Some(len)) = (tail, tail_len.as_ref()) {
                self.constraints.assertions.push(len.ge(&Int::from_u64(self.z3_ctx, 0)));
                let data_size = Int::mul(self.z3_ctx, &[len, &self.size_sym(elem)]);
                Int::add(self.z3_ctx, &[&Int::from_u64(self.z3_ctx, offset), &data_size])
            } else {
                Int::from_u64(self.z3_ctx, i64::MAX as u64)
            };
            let (field_alloc_id, field_base) =
                self.allocate_external(max_size, field_align, Some(pointee));
            if let Some(len) = tail_len {
                self.alloc_mut(field_alloc_id).set_slice_len(len);
            }
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
                    facts: invariants,
                    source: ValueSource::None,
                },
            );
        }
    }

    fn unsized_tail_layout(&self, ty: Ty<'tcx>) -> Option<(Ty<'tcx>, u64)> {
        let TyKind::Adt(adt, substs) = ty.kind() else {
            return None;
        };
        if !adt.is_struct() {
            return None;
        }
        let fields = &adt.non_enum_variant().fields;
        let index = fields.len().checked_sub(1)?;
        let tail_ty = mir_utils::field_ty(self.tcx, fields.iter().last()?, substs);
        let elem = match tail_ty.kind() {
            TyKind::Slice(elem) => *elem,
            TyKind::Str => self.tcx.types.u8,
            _ => return None,
        };
        let offset = mir_utils::field_offset_in_bytes(
            self.tcx,
            self.current_frame.current_def_id,
            ty,
            index,
        );
        (offset > 0 || index == 0).then_some((elem, offset))
    }

    /// Recursively decompose a (possibly nested) struct parameter into per-field
    /// symbolic values.  Nested ADT fields (e.g. `Handle { node: NodeRef { node:
    /// NonNull<LeafNode>, .. }, .. }`) are descended into so their `NonNull` /
    /// raw-pointer leaves get external-allocation provenance — otherwise a
    /// `NonNull` buried two levels deep loses its provenance and downstream
    /// `Allocated`/`Init` checks (e.g. `descend`'s `edges.get_unchecked`) fail.
    pub(crate) fn decompose_adt_fields(
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
                mir_utils::field_ty(self.tcx, field_def, substs);
            let mut path = prefix.clone();
            path.push(idx);
            if let rustc_middle::ty::TyKind::RawPtr(inner, _) = field_ty.kind() {
                self.init_ptr_field(
                    local, path, field_ty, *inner, local_idx, idx, elem_alloc, true, "field_nn",
                );
                continue;
            }
            if let Some(pointee) = self.find_nn_pointee(field_ty) {
                self.init_ptr_field(
                    local, path, field_ty, pointee, local_idx, idx, elem_alloc, false, "field_nn",
                );
                continue;
            }
            if let rustc_middle::ty::TyKind::Adt(inner_adt, _) = field_ty.kind()
                && !inner_adt.is_enum() {
                    self.decompose_adt_fields(
                        local, path, field_ty, local_idx, elem_alloc, depth + 1,
                    );
                    continue;
                }
            let field_term = self.fresh_int(&format!("field_{}_{}", local_idx, idx));
            self.set_field_value(
                local,
                path,
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

    /// Materialize only the owning pointer field of a non-generic `Vec`-like ADT
    /// field (e.g. `struct Vec { ptr: NonNull<u8>, len, cap }`), so an inlined
    /// `Vec::as_ptr`'s `_2 = copy (*self).ptr` resolves to the data provenance.
    /// The scalar `len`/`cap` fields are deliberately left unmaterialized — their
    /// `ValidNum` invariants are established separately by the struct-invariant
    /// assertion, not by fresh unconstrained symbols (which would fail `ValidNum`).
    /// The caller has already ensured `field_ty` is a non-enum `Vec`.
    pub(crate) fn materialize_vec_ptr_field(
        &mut self,
        local: Local,
        prefix: Vec<usize>,
        field_ty: Ty<'tcx>,
    ) -> bool {
        use rustc_middle::ty::TyKind;
        let TyKind::Adt(adt_def, substs) = field_ty.kind() else {
            return false;
        };
        let variant = adt_def.non_enum_variant();
        for (i, field_def) in variant.fields.iter().enumerate() {
            let ft = mir_utils::field_ty(self.tcx, field_def, substs);
            let Some(pointee) = self.find_nn_pointee(ft) else {
                continue;
            };
            let mut path = prefix.clone();
            path.push(i);
            self.materialize_external_field_at(
                local,
                path,
                ft,
                pointee,
                Some(self.tcx.lifetimes.re_static),
            );
            return true;
        }
        false
    }

    /// Read a scalar field's value back out of the byte layer over
    /// `[offset, offset + size)` (little-endian).  Returns `None` when the byte
    /// layer does not cover the whole field (a hole, or no byte written), so
    /// the caller falls back to a fresh symbol.
    ///
    /// This is the byte→field direction of the cast cross-view materialization:
    /// when bytes are written first (`*buf = 3`) and the buffer is then
    /// reinterpreted as a `repr(C)` struct, the field value is those bytes, not
    /// an unrelated fresh symbol.
    fn field_term_from_bytes(
        &self,
        alloc_id: AllocId,
        offset: usize,
        size: usize,
    ) -> Option<Int<'z3>> {
        if size == 0 {
            return Some(Int::from_u64(self.z3_ctx, 0));
        }
        let mut term = Int::from_u64(self.z3_ctx, 0);
        for j in 0..size {
            let off = offset + j;
            if !self.is_byte_init(alloc_id, off) {
                return None;
            }
            let b = self.byte_read(alloc_id, &Int::from_u64(self.z3_ctx, off as u64));
            let weight = Int::from_u64(self.z3_ctx, 1u64 << (j * 8));
            term = Int::add(self.z3_ctx, &[&term, &Int::mul(self.z3_ctx, &[&b, &weight])]);
        }
        Some(term)
    }

    /// Recursively decompose a pointee ADT's fields into per-allocation field
    /// tracking, mirroring [`decompose_adt_fields`](Self::decompose_adt_fields)
    /// but keyed by allocation instead of local. This is what lets a
    /// `&*NonNull<LeafNode>` dereference resolve `(*leaf).len` to the actual
    /// `len` field value rather than the raw pointer term.
    ///
    /// `byte_offset` is the running byte offset of the field being decomposed,
    /// used for the byte→field cross-view materialization (see
    /// [`Self::field_term_from_bytes`]).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn decompose_pointee_fields(
        &mut self,
        alloc_id: AllocId,
        prefix: Vec<usize>,
        ty: Ty<'tcx>,
        root_ty: Ty<'tcx>,
        local_idx: usize,
        depth: usize,
        byte_offset: usize,
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
            let field_ty = mir_utils::field_ty(self.tcx, field_def, substs);
            let field_off = byte_offset + self.field_offset_in_bytes(ty, idx) as usize;
            let mut path = prefix.clone();
            path.push(idx);
            if let Some(pointee) = self.find_nn_pointee(field_ty) {
                let field_align = self.align_sym(pointee);
                let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                let (fa, _fb) = self.allocate_external(max_size, field_align, Some(pointee));
                self.content_mut(fa).facts.initialized = true;
                let term = self.fresh_int(&format!("pointee_nn_{}_{}", local_idx, idx));
                self.units[alloc_id.0].content.values.insert(
                    (root_ty, path.clone()),
                    VmValue {
                        z3_term: term,
                        ty: field_ty,
                        provenance: Some(Provenance {
                            alloc_id: fa,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
                        facts: ValueFacts {
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
                    0,
                );
            } else if let TyKind::Adt(_, _) = field_ty.kind() {
                self.decompose_pointee_fields(
                    alloc_id,
                    path,
                    field_ty,
                    root_ty,
                    local_idx,
                    depth + 1,
                    field_off,
                );
            } else if matches!(
                field_ty.kind(),
                TyKind::Uint(_) | TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char
            ) {
                // Cross-view materialization: if the backing bytes were already
                // written (e.g. `*buf = 3` before `buf as *mut Header`), read
                // the field's value back out of the byte layer instead of a
                // fresh symbol, so a byte→struct reinterpret round-trips.
                let field_size = self.size_of_ty(field_ty) as usize;
                let field_term = self
                    .field_term_from_bytes(alloc_id, field_off, field_size)
                    .unwrap_or_else(|| self.fresh_int(&format!("pointee_field_{}_{}", local_idx, idx)));
                self.units[alloc_id.0].content.values.insert(
                    (root_ty, path.clone()),
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
            } else if let TyKind::Array(elem_ty, const_len) = field_ty.kind() {
                let n = mir_utils::eval_array_len(self.tcx, const_len).unwrap_or(0);
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
                self.content_mut(fa).facts.initialized = true;
                self.units[alloc_id.0].content.values.insert(
                    (root_ty, path.clone()),
                    VmValue {
                        z3_term: fb,
                        ty: field_ty,
                        provenance: Some(Provenance {
                            alloc_id: fa,
                            offset: Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        }),
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

    /// If `operand` is a constant reference to a byte array (e.g. `b"hello\0"`),
    /// extract the raw bytes and create a tracked allocation. Updates `val`
    /// in-place with the proper provenance and invariants.
    pub(crate) fn try_materialize_const_bytes(
        &mut self,
        val: &mut VmValue<'z3, 'tcx>,
        operand: &Operand<'tcx>,
    ) {
        let operand_val = self.value_of_operand(operand);
        let op_ty = operand_val.ty;
        let (pointee_ty, _is_ref) = match op_ty.kind() {
            rustc_middle::ty::TyKind::Ref(_, inner_ty, _) => (*inner_ty, true),
            rustc_middle::ty::TyKind::RawPtr(inner_ty, _) => (*inner_ty, false),
            _ => {
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
                        mir_utils::const_operand_bytes(self.tcx, operand)
                            .or_else(|| self.trace_to_const_bytes(operand));
                    if let Some(bytes) = bytes_opt {
                        let size = z3::ast::Int::from_u64(self.z3_ctx, bytes.len() as u64);
                        let align = self.align_sym(pointee_ty);
                        let (alloc_id, base) = self.allocate(size, align, Some(pointee_ty));
                        self.content_mut(alloc_id).facts.initialized = true;
                        self.alloc_mut(alloc_id).facts.liveness =
                            Some(self.tcx.lifetimes.re_static);
                        for (i, &b) in bytes.iter().enumerate() {
                            self.record_byte_value(
                                alloc_id,
                                i,
                                z3::ast::Int::from_u64(self.z3_ctx, b as u64),
                            );
                        }
                        val.z3_term = base;
                        val.provenance = Some(super::state::Provenance {
                            alloc_id,
                            offset: z3::ast::Int::from_u64(self.z3_ctx, 0),
                            offset_kind: None,
                        });
                        val.facts = ValueFacts {
                            non_null: true,
                            init: true,
                            in_bounds: false,
                            align_n: None,
                            dangling: false,
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
                        Rvalue::Use(op, ..) => {
                            return mir_utils::const_operand_bytes(self.tcx, op)
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

    /// Propagate a source place's per-field values to a reference destination,
    /// shifting the field path by the source place's `Field` projection prefix.
    /// E.g. for `_3 = &(_1.0)` where `_1` is a `Handle { node: NodeRef { node:
    /// NonNull<..>, .. }, .. }`, the nested `NonNull`'s field value stored at
    /// path `[0, 1]` becomes available at `_3`'s path `[1]`, so an inlined
    /// callee that dereferences `_3` and reads its `node` field sees the
    /// provenance of the underlying allocation.
    pub(crate) fn propagate_field_values_to_ref(&mut self, source_place: &Place<'tcx>, dest: Local) {
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
        let keys: Vec<Vec<usize>> = self.field_paths(source_place.local);
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
                if rest.is_empty() {
                    continue;
                }
                if let Some(v) = self.field_value(source_place.local, &path).cloned() {
                    if empty_proj && v.provenance.is_none() {
                        continue;
                    }
                    self.set_field_value(dest, rest, v);
                }
            }
        }
    }

    pub(crate) fn propagate_byte_values_to_ref(
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
        self.copy_byte_tracking(src_alloc_id, 0, ref_alloc_id);
    }

    /// Return the per-field types for an aggregate's operands.
    pub(crate) fn aggregate_field_tys(&self, ty: Ty<'tcx>) -> Vec<Ty<'tcx>> {
        match ty.kind() {
            rustc_middle::ty::TyKind::Array(elem_ty, _len) => {
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
                    .map(|f| mir_utils::field_ty(self.tcx, f, substs))
                    .collect()
            }
            _ => vec![],
        }
    }

    /// Materialize the `{ptr, cap, len}` field values of a `Vec<T>` aggregate
    /// at `local`. The backing-buffer pointer is written to the owning raw
    /// pointer field (located generically via [`Self::container_ptr_field`]);
    /// the `len`/`cap` are no longer materialized as fields — they are asserted
    /// as path conditions and tracked by the backing allocation's slice length.
    ///
    /// The symbolic invariant `0 <= len <= cap` and `cap * elem_size <=
    /// isize::MAX` is asserted as a path condition so downstream `len()` /
    /// `capacity()` / `InBound` / `ValidNum` queries agree.
    pub(crate) fn materialize_vec_fields(
        &mut self,
        local: Local,
        ptr: VmValue<'z3, 'tcx>,
        cap: Int<'z3>,
        len: Int<'z3>,
    ) {
        let elem_size = self.size_of_ty(ptr.ty).max(1);
        let ty = self.body().local_decls[local].ty;
        let ptr_path = self
            .container_ptr_field(ty)
            .expect("materialize_vec_fields: container has no owning pointer field");
        self.set_field_value(local, ptr_path, ptr);
        self.materialize_vec_len_cap(cap, len, elem_size);
    }

    /// Assert the Vec length/capacity invariants `0 <= len <= cap` and
    /// `cap * elem_size <= isize::MAX` as path conditions.
    pub(crate) fn materialize_vec_len_cap(
        &mut self,
        cap: Int<'z3>,
        len: Int<'z3>,
        elem_size: u64,
    ) {
        let zero = Int::from_u64(self.z3_ctx, 0);
        self.constraints.assertions.push(len.ge(&zero));
        self.constraints.assertions.push(len.le(&cap));
        self.constraints.assertions.push(cap.ge(&zero));
        // Language invariant: a Vec's byte length fits in `isize::MAX`, so the
        // `from_raw_parts`/`from_raw_parts_mut` precondition
        // `size_of(T) * len <= isize::MAX` is provable from the materialized
        // fields (`len <= cap` and `cap * elem_size <= isize::MAX`).
        let isize_max = Int::from_u64(self.z3_ctx, isize::MAX as u64);
        let elem_term = Int::from_u64(self.z3_ctx, elem_size.max(1));
        self.constraints.assertions
            .push(Int::mul(self.z3_ctx, &[&cap, &elem_term]).le(&isize_max));
    }
}
