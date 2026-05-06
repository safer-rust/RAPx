//! Type-compatibility contract checker.
//!
//! This module verifies `Typed` obligations by comparing the graph's current
//! object type with the pointer node's tracked type and then requiring
//! initialization for the reached value.

use crate::analysis::{senryx::visitor::BodyVisitor, utils::fn_info::is_strict_ty_convert};

impl<'tcx> BodyVisitor<'tcx> {
    /// Check whether the value the pointer reaches is valid for its tracked type.
    pub fn check_typed(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg).unwrap();
        let var = self.chains.get_var_node(arg);
        let var_ty = var.unwrap().ty.unwrap();
        if obj_ty != var_ty && is_strict_ty_convert(self.tcx, obj_ty, var_ty) {
            return false;
        }
        self.check_init(arg)
    }
}
