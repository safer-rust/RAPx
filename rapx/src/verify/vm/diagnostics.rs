//! Path-scoped evidence for incomplete VM execution.

use crate::compat::FxHashSet;

#[derive(Default, Clone)]
pub(crate) struct Diagnostics {
    unsupported_mir: bool,
    unattributed_unsupported: bool,
    unsupported_details: FxHashSet<String>,
    unsupported_effects: FxHashSet<String>,
    missing_mir: FxHashSet<String>,
    opaque_control_flow: FxHashSet<String>,
    incomplete_inline_branch: bool,
}

impl Diagnostics {
    pub(crate) fn is_unsupported(&self) -> bool {
        self.unsupported_mir
    }

    pub(crate) fn mark_unsupported(&mut self) {
        self.unsupported_mir = true;
        self.unattributed_unsupported = true;
    }

    pub(crate) fn mark_unsupported_if(&mut self, condition: bool) {
        if condition {
            self.mark_unsupported();
        }
    }

    pub(crate) fn has_incomplete_inline_branch(&self) -> bool {
        self.incomplete_inline_branch
    }

    pub(crate) fn unsupported_details(&self) -> &FxHashSet<String> {
        &self.unsupported_details
    }

    pub(crate) fn unsupported_effects(&self) -> &FxHashSet<String> {
        &self.unsupported_effects
    }

    pub(crate) fn missing_mir(&self) -> &FxHashSet<String> {
        &self.missing_mir
    }

    pub(crate) fn opaque_control_flow(&self) -> &FxHashSet<String> {
        &self.opaque_control_flow
    }

    pub(crate) fn record_unsupported(&mut self, location: Option<&str>, operation: &str) {
        self.unsupported_mir = true;
        self.unsupported_details
            .insert(format!("{}: {operation}", location.unwrap_or("unknown location")));
    }

    pub(crate) fn record_unsupported_effect(&mut self, location: Option<&str>, effect: &str) {
        self.unsupported_mir = true;
        self.unsupported_effects
            .insert(format!("{}: {effect}", location.unwrap_or("unknown location")));
    }

    pub(crate) fn record_missing_mir(&mut self, location: Option<&str>, callee: &str) {
        self.unsupported_mir = true;
        self.missing_mir.insert(format!(
            "{callee} at {}",
            location.unwrap_or("unknown location")
        ));
    }

    pub(crate) fn record_opaque_control_flow(&mut self, location: Option<&str>, operation: &str) {
        self.unsupported_mir = true;
        self.opaque_control_flow.insert(format!(
            "{}: opaque call result controls {operation}",
            location.unwrap_or("unknown location")
        ));
    }

    pub(crate) fn only_copy_memory_target_unavailable_since(&self, before: &Self) -> bool {
        self.unsupported_mir
            && !before.unsupported_mir
            && !self.unattributed_unsupported
            && self.unsupported_effects.len() > before.unsupported_effects.len()
            && self
                .unsupported_effects
                .difference(&before.unsupported_effects)
                .all(|effect| effect.contains("CopyMemory target unavailable"))
            && self.unsupported_details == before.unsupported_details
            && self.missing_mir == before.missing_mir
            && self.opaque_control_flow == before.opaque_control_flow
    }

    pub(crate) fn recover_copy_memory_target(&mut self, before: &Self) {
        if self.only_copy_memory_target_unavailable_since(before) {
            self.unsupported_effects = before.unsupported_effects.clone();
            self.unsupported_mir = before.unsupported_mir;
        }
    }

    pub(crate) fn only_missing_mir_since(&self, before: &Self) -> bool {
        self.unsupported_mir
            && !before.unsupported_mir
            && !self.unattributed_unsupported
            && self.missing_mir.len() > before.missing_mir.len()
            && self.unsupported_details == before.unsupported_details
            && self.unsupported_effects == before.unsupported_effects
            && self.opaque_control_flow == before.opaque_control_flow
    }

    pub(crate) fn recover_missing_mir(&mut self, before: &Self) {
        if self.only_missing_mir_since(before) {
            self.missing_mir = before.missing_mir.clone();
            self.unsupported_mir = before.unsupported_mir;
        }
    }

    pub(crate) fn needs_statement_fallback(&self, was_unsupported: bool) -> bool {
        !was_unsupported
            && self.unsupported_mir
            && self.unsupported_details.is_empty()
            && self.unsupported_effects.is_empty()
    }

    pub(crate) fn needs_terminator_fallback(
        &self,
        was_unsupported: bool,
        previous_missing_mir: usize,
    ) -> bool {
        self.needs_statement_fallback(was_unsupported)
            && self.missing_mir.len() == previous_missing_mir
            && self.opaque_control_flow.is_empty()
    }

    pub(crate) fn missing_mir_count(&self) -> usize {
        self.missing_mir.len()
    }

    pub(crate) fn merge_inline_fallback(&mut self, explored: &Self) {
        self.missing_mir.extend(explored.missing_mir.iter().cloned());
        self.incomplete_inline_branch = true;
    }
}
