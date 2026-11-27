use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::Local,
    ty::{Mutability, Ty, TyKind},
};
use z3::ast::Int;

use super::super::super::state::{AllocId, VmExecutor, VmValue};
use crate::analysis::dataflow::closure;
use crate::compat::FxHashSet;

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    /// Abstract an unresolved `Fn*` call, including scalar writes and results.
    /// Opaque argument shapes use the conservative memory effect below.
    pub(crate) fn apply_function_var_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: DefId,
    ) {
        let ty = self.body().local_decls[dest].ty;
        if !closure::can_abstract_call(self.tcx, callee, ty) {
            self.record_missing_mir(callee);
            return;
        }
        let input_receiver = caller_arg_locals
            .first()
            .copied()
            .flatten()
            .is_some_and(|local| local.as_usize() <= self.body().arg_count)
            || args
                .first()
                .and_then(VmValue::provenance_alloc_id)
                .is_some_and(|id| {
                    (1..=self.body().arg_count).any(|index| {
                        self.path_state.current_frame
                            .local_alloc
                            .get(&Local::from_usize(index))
                            == Some(&id)
                    })
                })
            || args.first().is_some_and(|arg| {
                (1..=self.body().arg_count).any(|index| {
                    self.local_value(Local::from_usize(index))
                        .is_some_and(|param| param.ty == arg.ty && param.z3_term == arg.z3_term)
                })
            });
        if !input_receiver {
            self.record_missing_mir(callee);
            return;
        }
        if ty.is_unit() || matches!(ty.kind(), TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_)) {
            if !self.apply_scalar_function_var_effect(args, caller_arg_locals, dest, ty) {
                if matches!(ty.kind(), TyKind::Bool) {
                    self.apply_opaque_function_var_effect(args, caller_arg_locals, dest, callee, ty);
                    return;
                }
                self.record_missing_mir(callee);
            }
            return;
        }
        self.apply_opaque_function_var_effect(args, caller_arg_locals, dest, callee, ty);
    }

    fn apply_opaque_function_var_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: DefId,
        ty: Ty<'tcx>,
    ) {
        // The rust-call tuple may carry references to this frame's locals.
        // Require provenance for every reference field before keeping those
        // locals private. An opaque aggregate can hide such a reference.
        for (index, arg) in args.iter().enumerate().skip(1) {
            let resolved =
                match arg.ty.kind() {
                    TyKind::Ref(..) | TyKind::RawPtr(..) => arg.provenance.is_some(),
                    TyKind::Tuple(fields) => fields.iter().enumerate().all(|(field, ty)| match ty
                        .kind()
                    {
                        TyKind::Ref(..) | TyKind::RawPtr(..) => caller_arg_locals
                            .get(index)
                            .copied()
                            .flatten()
                            .and_then(|local| self.path_state.current_frame.local_alloc.get(&local))
                            .and_then(|id| self.load_value(*id, arg.ty, &[field]))
                            .and_then(VmValue::provenance_alloc_id)
                            .is_some(),
                        TyKind::Bool
                        | TyKind::Char
                        | TyKind::Int(_)
                        | TyKind::Uint(_)
                        | TyKind::Float(_)
                        | TyKind::Never => true,
                        _ => false,
                    }),
                    _ => false,
                };
            if !resolved {
                self.record_missing_mir(callee);
                return;
            }
        }

        let private: FxHashSet<_> = self.path_state.current_frame.local_alloc.values().copied().collect();
        let borrowed: FxHashSet<_> = self.path_state
            .current_frame
            .local_alloc
            .iter()
            .filter_map(|(local, id)| {
                (matches!(self.body().local_decls[*local].ty.kind(), TyKind::Ref(..))
                    && !self.alloc(*id).dead)
                    .then(|| self.local_value(*local))
                    .flatten()
                    .and_then(VmValue::provenance_alloc_id)
                    .map(|id| self.root_alloc(id))
            })
            .collect();
        let mut affected: Vec<_> = (0..self.path_state.mem_units.len())
            .map(AllocId)
            .filter(|id| !private.contains(id))
            .collect();
        affected.extend(args.iter().filter_map(VmValue::provenance_alloc_id));
        for local in caller_arg_locals.iter().flatten() {
            if let Some(id) = self.path_state.current_frame.local_alloc.get(local) {
                affected.extend(
                    self.content(*id)
                        .values
                        .values()
                        .filter_map(VmValue::provenance_alloc_id),
                );
            }
        }
        affected = affected.into_iter().map(|id| self.root_alloc(id)).collect();
        affected.sort_by_key(|id| id.0);
        affected.dedup();
        for id in affected {
            let may_drop = !borrowed.contains(&id);
            if may_drop {
                self.alloc_mut(id).function_var_may_drop = true;
            }
            self.forget_memory_values(id);
            for alias in 0..self.path_state.mem_units.len() {
                let alias = AllocId(alias);
                if self.root_alloc(alias) == id {
                    let alloc = self.alloc_mut(alias);
                    alloc.owning = None;
                    if may_drop {
                        alloc.liveness = None;
                    }
                }
            }
        }

        let term = self.fresh_int("function_var_result");
        if matches!(ty.kind(), TyKind::Bool) {
            let zero = Int::from_u64(self.z3_ctx, 0);
            let one = Int::from_u64(self.z3_ctx, 1);
            self.path_state.constraints.assertions.push(term.ge(&zero));
            self.path_state.constraints.assertions.push(term.le(&one));
        }
        let mut result = VmValue::new(term, ty);
        result.facts.init = true;
        self.set_local(dest, result);
    }

    /// Model scalar arguments when all writable pointees have known provenance.
    /// Write through the pointer so field and whole-object updates share MIR semantics.
    fn apply_scalar_function_var_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        result_ty: Ty<'tcx>,
    ) -> bool {
        let mut targets = Vec::new();
        for (index, arg) in args.iter().enumerate().skip(1) {
            let mut fields = Vec::new();
            match arg.ty.kind() {
                TyKind::Tuple(types) if types.is_empty() => {}
                TyKind::Tuple(types) => {
                    let Some(id) = caller_arg_locals.get(index).copied().flatten()
                        .and_then(|local| self.path_state.current_frame.local_alloc.get(&local).copied())
                    else { return false };
                    for (field, ty) in types.iter().enumerate() {
                        fields.push((ty, self.load_value(id, arg.ty, &[field]).cloned()));
                    }
                }
                _ => fields.push((arg.ty, Some(arg.clone()))),
            }
            for (ty, value) in fields {
                match ty.kind() {
                    TyKind::Ref(_, inner, mutability)
                        if matches!(inner.kind(), TyKind::Bool | TyKind::Int(_) | TyKind::Uint(_)) => {
                        let Some(pointer) = value.filter(|value| value.provenance.is_some()) else { return false };
                        if *mutability == Mutability::Mut {
                            targets.push((pointer, *inner));
                        }
                    }
                    TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) => {}
                    _ => return false,
                }
            }
        }
        let private: FxHashSet<_> = self.path_state.current_frame.local_alloc.values()
            .map(|id| self.root_alloc(*id)).collect();
        if (0..self.path_state.mem_units.len()).any(|index| !private.contains(&self.root_alloc(AllocId(index)))) {
            return false;
        }
        for (pointer, ty) in targets {
            let (min, max) = if matches!(ty.kind(), TyKind::Bool) {
                (Int::from_u64(self.z3_ctx, 0), Int::from_u64(self.z3_ctx, 1))
            } else {
                let Some((min, max, _, _)) = self.integer_limits(ty) else { return false };
                (min, max)
            };
            let term = self.fresh_int("function_var_write");
            self.path_state.constraints.assertions.push(term.ge(&min));
            self.path_state.constraints.assertions.push(term.le(&max));
            let mut value = VmValue::new(term, ty);
            value.facts.init = true;
            if !self.write_through_pointer(&pointer, Vec::new(), value) { return false; }
        }
        let term = if result_ty.is_unit() {
            Int::from_u64(self.z3_ctx, 0)
        } else {
            let (min, max) = if matches!(result_ty.kind(), TyKind::Bool) {
                (Int::from_u64(self.z3_ctx, 0), Int::from_u64(self.z3_ctx, 1))
            } else {
                let Some((min, max, _, _)) = self.integer_limits(result_ty) else { return false };
                (min, max)
            };
            let term = self.fresh_int("function_var_result");
            self.path_state.constraints.assertions.push(term.ge(&min));
            self.path_state.constraints.assertions.push(term.le(&max));
            term
        };
        let mut result = VmValue::new(term, result_ty);
        result.facts.init = true;
        self.set_local(dest, result);
        true
    }
}
