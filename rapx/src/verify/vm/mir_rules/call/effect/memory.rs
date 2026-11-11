use super::*;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    pub(super) fn apply_memory_effect(
        &mut self,
        effect: &CallEffect,
        args: &[VmValue<'z3, 'tcx>],
        dest: Local,
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
                let ty = self.body().local_decls[dest].ty;
                let old = self.fresh_int("atomic_rmw_old");
                self.set_local(dest, VmValue::new(old, ty));
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
            _ => unreachable!("non-memory call effect"),
        }
    }
}
