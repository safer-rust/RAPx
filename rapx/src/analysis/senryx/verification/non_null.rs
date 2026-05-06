//! Non-null contract checker.
//!
//! This module verifies `NonNull` obligations against the graph's operational
//! trace state for the object reached by a pointer or reference.

use crate::analysis::senryx::visitor::BodyVisitor;

impl<'tcx> BodyVisitor<'tcx> {
    /// Check that a pointer's modeled target is non-null.
    pub fn check_non_null(&self, arg: usize) -> bool {
        let point_to_id = self.chains.get_point_to_id(arg);
        let var_ty = self.chains.get_var_node(point_to_id);
        if var_ty.is_none() {
            self.show_error_info(arg);
        }
        var_ty.unwrap().ots.nonnull
    }
}
