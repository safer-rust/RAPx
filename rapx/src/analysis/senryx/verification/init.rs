//! Initialization contract checker.
//!
//! This module verifies `Init`-style obligations from graph OTS state. For
//! aggregate nodes it recursively checks modeled field nodes; for leaves it uses
//! the node's `init` flag.

use crate::analysis::senryx::visitor::BodyVisitor;

impl<'tcx> BodyVisitor<'tcx> {
    /// Check each field's init state in the graph tree, or the node itself for leaves.
    pub fn check_init(&self, arg: usize) -> bool {
        let point_to_id = self.chains.get_point_to_id(arg);
        let var = self.chains.get_var_node(point_to_id).unwrap();
        if !var.field.is_empty() {
            let mut init_flag = true;
            for field in &var.field {
                init_flag &= self.check_init(*field.1);
            }
            init_flag
        } else {
            var.ots.init
        }
    }
}
