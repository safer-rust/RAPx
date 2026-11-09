use super::*;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(super) fn apply_memory_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        dest: Local,
        callee: Option<DefId>,
    ) {
        match effect {
            CallEffect::LoadMemory { pointer_arg } => {
                let value = args.get(*pointer_arg).and_then(|pointer| {
                    let ty = self.body().local_decls[dest].ty;
                    self.read_field_allocation(pointer, ty)
                });
                if let Some(mut value) = value {
                    value.ty = self.body().local_decls[dest].ty;
                    self.set_local(dest, value);
                } else {
                    self.set_opaque_intrinsic_result(dest);
                }
            }
            CallEffect::StoreMemory {
                pointer_arg,
                value_arg,
            } => {
                let Some((pointer, value)) = args.get(*pointer_arg).zip(args.get(*value_arg))
                else {
                    self.record_unsupported("volatile_store arguments");
                    return;
                };
                let mut value = value.clone();
                value.facts.init = true;
                if !self.write_through_pointer(pointer, Vec::new(), value) {
                    self.record_unsupported("volatile_store target");
                }
            }
            CallEffect::AtomicRmw { pointer_arg } => {
                let Some(prov) = args
                    .get(*pointer_arg)
                    .and_then(|value| value.provenance.as_ref())
                else {
                    self.record_unsupported("atomic operation target");
                    return;
                };
                self.forget_memory_values(prov.alloc_id);
                self.set_opaque_intrinsic_result(dest);
            }
            CallEffect::CopyMemory {
                source_arg,
                destination_arg,
                count_arg,
            } => {
                if let (Some(source), Some(target), Some(count)) = (
                    args.get(*source_arg),
                    args.get(*destination_arg),
                    args.get(*count_arg),
                ) {
                    self.copy_memory_values(source, target, count);
                }
            }
            CallEffect::SwapMemory {
                left_arg,
                right_arg,
            } => {
                let Some((left, right)) = args.get(*left_arg).zip(args.get(*right_arg)) else {
                    self.record_unsupported_effect("SwapMemory arguments unavailable");
                    return;
                };
                if !self.swap_memory_values(left, right) {
                    self.record_unsupported_effect("SwapMemory target unsupported");
                }
            }
            CallEffect::FillBytes {
                pointer_arg,
                byte_arg,
                count_arg,
            } => {
                let (Some(pointer), Some(byte), Some(count)) = (
                    args.get(*pointer_arg),
                    args.get(*byte_arg),
                    args.get(*count_arg),
                ) else {
                    self.record_unsupported_effect("FillBytes arguments unavailable");
                    return;
                };
                let concrete_count = count.z3_term.simplify().as_u64();
                if concrete_count == Some(0) {
                    return;
                }
                let (Some(ty), Some(byte_value)) = (
                    mir_utils::pointee_ty(pointer.ty),
                    byte.z3_term.simplify().as_u64(),
                ) else {
                    self.record_unsupported_effect(
                        "FillBytes pointee type or byte value unavailable",
                    );
                    return;
                };
                let local = self
                    .find_local_by_address(&pointer.z3_term)
                    .filter(|local| self.body().local_decls[*local].ty == ty);
                let inline_target =
                    self.inline
                        .arg_referents
                        .iter()
                        .enumerate()
                        .any(|(i, referent)| {
                            referent.is_some()
                                && self
                                    .local_value(Local::from_usize(i + 1))
                                    .is_some_and(|value| value.z3_term == pointer.z3_term)
                        });
                if concrete_count == Some(1)
                    && byte_value <= u8::MAX as u64
                    && self.fill_byte_array(pointer, byte_value)
                {
                    return;
                }
                if concrete_count != Some(1)
                    || (local.is_none() && !inline_target)
                    || !matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
                    || byte_value > u8::MAX as u64
                {
                    let allocation = pointer.provenance.as_ref().map(|provenance| {
                        format!(
                            "kind={:?}, element={:?}, size={:?}",
                            self.alloc(provenance.alloc_id).kind,
                            self.alloc(provenance.alloc_id).element_ty,
                            self.allocation_size(provenance.alloc_id),
                        )
                    });
                    self.record_unsupported_effect(&format!(
                        "FillBytes target unsupported: count={concrete_count:?}, local={}, inline_target={inline_target}, pointee={ty:?}, byte={byte_value}, provenance={:?}, allocation={allocation:?}",
                        local.is_some(),
                        pointer.provenance,
                    ));
                    return;
                }
                let value_bits = if byte_value == 0 {
                    0
                } else {
                    let size = self.size_of_ty(ty);
                    if !matches!(ty.kind(), TyKind::Uint(_)) || size == 0 || size > 8 {
                        self.record_unsupported_effect(&format!(
                            "FillBytes nonzero fill unsupported: pointee={ty:?}, size={size}"
                        ));
                        return;
                    }
                    (0..size).fold(0_u64, |bits, index| bits | (byte_value << (8 * index)))
                };
                let mut value = VmValue::new(Int::from_u64(self.z3_ctx, value_bits), ty);
                value.facts.init = true;
                self.write_through_pointer(pointer, Vec::new(), value);
                if let Some(local) = local
                    && let Some(alloc_id) = self.current_frame.local_alloc.get(&local).copied()
                {
                    self.content_mut(alloc_id).facts.initialized = true;
                }
            }
            CallEffect::WriteMemory { pointer_arg } => {
                if let Some(arg_val) = args.get(*pointer_arg)
                    && let Some(prov) = &arg_val.provenance
                {
                    // Writing a non-`u8` value through a byte buffer reinterprets
                    // it (e.g. `*mut FreeBlock` cast from a `Vec<u8>` buffer):
                    // update the allocation's element type so a later `Typed`
                    // invariant matches the written type.
                    if let rustc_middle::ty::TyKind::RawPtr(inner, _)
                    | rustc_middle::ty::TyKind::Ref(_, inner, _) = arg_val.ty.kind()
                    {
                        let cur = self.alloc(prov.alloc_id).element_ty.as_ty();
                        let is_u8 = |t: rustc_middle::ty::Ty<'_>| {
                            matches!(
                                t.kind(),
                                rustc_middle::ty::TyKind::Uint(rustc_middle::ty::UintTy::U8)
                            )
                        };
                        if let Some(c) = cur
                            && is_u8(c)
                            && !is_u8(*inner)
                        {
                            self.alloc_mut(prov.alloc_id).element_ty = ElementTy::Typed(*inner);
                        }
                    }
                    let is_vec = api_classify::is_vec_push_or_reserve(callee);
                    let is_external = self.alloc(prov.alloc_id).is_external();
                    if is_vec && !is_external {
                        let elem_ty = match arg_val.ty.kind() {
                            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => {
                                crate::verify::call_summary::effects::vec_elem_ty(*inner)
                            }
                            _ => crate::verify::call_summary::effects::vec_elem_ty(arg_val.ty),
                        };
                        let heap_align = elem_ty
                            .map(|ty| self.align_sym(ty))
                            .unwrap_or_else(|| Int::from_u64(self.z3_ctx, 1));
                        if let Some(old_data) = self.container_data_alloc(prov.alloc_id, arg_val.ty)
                        {
                            self.alloc_mut(old_data).facts.dead = true;
                        }
                        let max_size = Int::from_u64(self.z3_ctx, i64::MAX as u64);
                        let (data_alloc, data_base) =
                            self.allocate_external(max_size, heap_align, elem_ty);
                        let container_ty = match arg_val.ty.kind() {
                            TyKind::Ref(_, inner, _) | TyKind::RawPtr(inner, _) => *inner,
                            _ => arg_val.ty,
                        };
                        self.set_container_data_field(
                            prov.alloc_id,
                            arg_val.ty,
                            data_alloc,
                            data_base,
                            elem_ty.unwrap_or(container_ty),
                        );
                    }
                    let off_u64 = prov
                        .offset
                        .as_u64()
                        .or_else(|| prov.offset.simplify().as_u64());
                    let written_pointee_ty =
                        self.alloc(prov.alloc_id).element_ty.as_ty().and_then(|ty| {
                            match ty.kind() {
                                TyKind::Adt(def, args)
                                    if api_classify::is_maybe_uninit_type(def.did()) =>
                                {
                                    args.first().and_then(|arg| arg.as_type()).filter(|inner| {
                                        Some(*inner) == mir_utils::pointee_ty(arg_val.ty)
                                    })
                                }
                                _ => None,
                            }
                        });
                    if let Some(off) = off_u64 {
                        if off == 0 {
                            self.content_mut(prov.alloc_id).facts.initialized = true;
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
                            self.allocation_size(prov.alloc_id).as_u64().unwrap_or(0) as usize
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
                        let size_val = self.allocation_size(prov.alloc_id).as_u64();
                        match size_val {
                            Some(sz) if sz > 0 => {
                                for off in 0..(sz as usize).min(1024) {
                                    self.mark_byte_init(prov.alloc_id, off);
                                }
                            }
                            _ => {
                                self.content_mut(prov.alloc_id).facts.initialized = true;
                            }
                        }
                    }
                    if off_u64 == Some(0) {
                        self.content_mut(prov.alloc_id).facts.written_pointee_ty =
                            written_pointee_ty;
                    }
                }
            }
            _ => unreachable!("non-memory call effect"),
        }
    }
}
