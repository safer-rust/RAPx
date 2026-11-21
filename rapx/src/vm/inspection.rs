//! VM observations and optional tracing used by verification and other checkers.

use std::cell::{Ref, RefCell};

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::Ty};
use z3::ast::Int;

use crate::compat::FxHashSet;
use crate::vm::{VmExecutor, diagnostics::Diagnostics, state::{AllocId, MemoryEvent, VmValue}};

impl<'z3, 'tcx> VmExecutor<'z3, 'tcx> {
    pub(crate) fn diagnostics(&self) -> &Diagnostics {
        &self.path_state.diagnostics
    }

    pub(crate) fn recover_copy_memory_target(&mut self, before: &Diagnostics) {
        self.path_state.diagnostics.recover_copy_memory_target(before);
    }

    pub(crate) fn recover_missing_mir(&mut self, before: &Diagnostics) {
        self.path_state.diagnostics.recover_missing_mir(before);
    }

    pub(crate) fn current_def_id(&self) -> DefId {
        self.path_state.current_frame.current_def_id
    }

    pub(crate) fn local_alloc_id(&self, local: Local) -> Option<AllocId> {
        self.path_state.current_frame.local_alloc.get(&local).copied()
    }

    pub(crate) fn local_allocations(&self) -> impl Iterator<Item = (Local, AllocId)> + '_ {
        self.path_state.current_frame.local_alloc.iter().map(|(&local, &id)| (local, id))
    }

    pub(crate) fn cached_size(&self, ty: Ty<'tcx>) -> Option<&Int<'z3>> {
        self.path_state.constraints.term_caches.sizes.get(&ty)
    }

    pub(crate) fn incomplete_inline_terms(&self) -> impl Iterator<Item = &FxHashSet<Int<'z3>>> {
        [&self.path_state.inline.inline_truncated_terms, &self.path_state.inline.inline_branch_terms].into_iter()
    }

    pub(crate) fn opaque_intrinsic_terms(&self) -> &FxHashSet<Int<'z3>> {
        &self.path_state.inline.opaque_intrinsic_terms
    }

    pub(crate) fn has_matching_index_access_fact(&self, slice_val: &VmValue<'z3, 'tcx>, index_val: &VmValue<'z3, 'tcx>) -> bool {
        let Some(slice_len) = self.slice_len_from_value(slice_val) else { return false };
        self.path_state.index_access_facts.iter().any(|(slice, index, slice_local, _)| {
            slice.to_string() == slice_val.z3_term.to_string()
                && index.to_string() == index_val.z3_term.to_string()
                && self.local_value(*slice_local).and_then(|value| self.slice_len_from_value(value)) == Some(slice_len.clone())
        })
    }

    pub(crate) fn enable_memory_events(&mut self) {
        self.path_state.memory_events = Some(RefCell::default());
    }

    pub(crate) fn memory_events(&self) -> Option<Ref<'_, Vec<MemoryEvent>>> {
        self.path_state.memory_events.as_ref().map(RefCell::borrow)
    }
}
