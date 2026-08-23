//! Debug and diagnostic display for the symbolic VM.
//!
//! Formats `VmState`, `VmValue`, and related types for human-readable output.

use std::fmt;

use super::state::{VmState, VmValue, ValueInvariants};

impl<'ctx, 'tcx> VmState<'ctx, 'tcx> {
    /// Produce a compact diagnostic summary of the VM state.
    pub fn describe(&self) -> String {
        let mut lines = Vec::new();

        // Locals
        if !self.locals.is_empty() {
            lines.push("-- VM Locals --".to_string());
            for (local, value) in self.locals.iter() {
                lines.push(format!(
                    "  _{}: {:?}",
                    local.as_usize(),
                    value.describe()
                ));
            }
        }

        // Allocations
        if !self.allocations.is_empty() {
            lines.push("-- Allocations --".to_string());
            for (idx, alloc) in self.allocations.iter().enumerate() {
                lines.push(format!(
                    "  alloc_{}: base={}, size={}, align={}",
                    idx,
                    alloc.base.to_string(),
                    alloc.size.to_string(),
                    alloc.align,
                ));
            }
        }

        // Path conditions
        if !self.path_conditions.is_empty() {
            lines.push(format!(
                "  {} path conditions asserted",
                self.path_conditions.len()
            ));
        }

        // Notes
        if !self.notes.is_empty() {
            lines.push("-- Notes --".to_string());
            for note in &self.notes {
                lines.push(format!("  * {note}"));
            }
        }

        lines.join("\n")
    }
}

impl<'ctx, 'tcx> VmValue<'ctx, 'tcx> {
    /// A compact one-line description of a symbolic value.
    fn describe(&self) -> String {
        let term_str = self.term.to_string();

        let mut flags = Vec::new();
        if self.invariants.non_null {
            flags.push("NN");
        }
        if self.invariants.aligned {
            flags.push("AL");
        }
        if self.invariants.init {
            flags.push("IN");
        }
        if self.invariants.in_bounds {
            flags.push("IB");
        }

        let provenance = self
            .provenance
            .as_ref()
            .map(|p| format!("@alloc{}", p.alloc_id.0))
            .unwrap_or_default();

        if flags.is_empty() {
            format!("{term_str} {provenance}")
        } else {
            format!("{term_str} [{}] {}", flags.join(","), provenance)
        }
    }
}

impl fmt::Display for ValueInvariants {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut flags = Vec::new();
        if self.non_null {
            flags.push("non_null");
        }
        if self.aligned {
            flags.push("aligned");
        }
        if self.init {
            flags.push("init");
        }
        if self.in_bounds {
            flags.push("in_bounds");
        }
        write!(f, "{}", flags.join("|"))
    }
}
