use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::TyKind};
use z3::ast::Int;

use super::super::super::state::{AllocId, VmState, VmValue};
use crate::compat::FxHashSet;

impl<'z3, 'tcx> VmState<'z3, 'tcx> {
    /// Abstract a safe `Fn*` call when only a scalar boolean or `Ordering`
    /// result is required. The closure body is unavailable at a generic call
    /// site, so every allocation outside the active frame may have been
    /// reached through captures or globals. Locals explicitly passed by
    /// reference are also invalidated. Frame-private counters remain stable.
    pub(crate) fn apply_callback_effect(
        &mut self,
        args: &[VmValue<'z3, 'tcx>],
        caller_arg_locals: &[Option<Local>],
        dest: Local,
        callee: DefId,
    ) {
        let ty = self.body().local_decls[dest].ty;
        if !crate::verify::call_summary::callback::supports_result(ty) {
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
                        self.current_frame
                            .local_alloc
                            .get(&Local::from_usize(index))
                            == Some(&id)
                    })
                });
        if !input_receiver {
            self.record_missing_mir(callee);
            return;
        }
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
                            .and_then(|local| self.current_frame.local_alloc.get(&local))
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

        let private: FxHashSet<_> = self.current_frame.local_alloc.values().copied().collect();
        let borrowed: FxHashSet<_> = self
            .current_frame
            .local_alloc
            .iter()
            .filter_map(|(local, id)| {
                (matches!(self.body().local_decls[*local].ty.kind(), TyKind::Ref(..))
                    && !self.alloc(*id).facts.dead)
                    .then(|| self.local_value(*local))
                    .flatten()
                    .and_then(VmValue::provenance_alloc_id)
                    .map(|id| self.root_alloc(id))
            })
            .collect();
        let mut affected: Vec<_> = (0..self.units.len())
            .map(AllocId)
            .filter(|id| !private.contains(id))
            .collect();
        affected.extend(args.iter().filter_map(VmValue::provenance_alloc_id));
        for local in caller_arg_locals.iter().flatten() {
            if let Some(id) = self.current_frame.local_alloc.get(local) {
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
                self.alloc_mut(id).facts.callback_may_drop = true;
            }
            self.forget_memory_values(id);
            for alias in 0..self.units.len() {
                let alias = AllocId(alias);
                if self.root_alloc(alias) == id {
                    let facts = &mut self.alloc_mut(alias).facts;
                    facts.owning = None;
                    if may_drop {
                        facts.liveness = None;
                    }
                }
            }
        }

        let term = self.fresh_int("callback_result");
        if matches!(ty.kind(), TyKind::Bool) {
            let zero = Int::from_u64(self.z3_ctx, 0);
            let one = Int::from_u64(self.z3_ctx, 1);
            self.constraints.assertions.push(term.ge(&zero));
            self.constraints.assertions.push(term.le(&one));
        }
        let mut result = VmValue::new(term, ty);
        result.facts.init = true;
        self.set_local(dest, result);
    }
}
