//! Boundary and size-related contract helpers.
//!
//! This module owns checks that reason about object extents, element counts,
//! and zero-sized types. `InBound` is currently conservative because the graph
//! now stores expression-shaped length contracts but does not yet discharge all
//! numeric relationships.

use crate::analysis::senryx::{
    contract::ContractExpr,
    visitor::{BodyVisitor, PlaceTy},
};
use rustc_middle::ty::Ty;

impl<'tcx> BodyVisitor<'tcx> {
    /// Return true when the modeled object reached by `arg` is zero-sized.
    ///
    /// The API name is kept for compatibility with existing call sites, but the
    /// current implementation returns `true` for ZST objects.
    pub fn check_non_zst(&self, arg: usize) -> bool {
        let obj_ty = self.chains.get_obj_ty_through_chain(arg);
        if obj_ty.is_none() {
            self.show_error_info(arg);
        }
        let ori_ty = self.visit_ty_and_get_layout(obj_ty.unwrap());
        match ori_ty {
            PlaceTy::Ty(_align, size) => size == 0,
            PlaceTy::GenericTy(_, _, tys) => {
                if tys.is_empty() {
                    return false;
                }
                for (_, size) in tys {
                    if size != 0 {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    /// Check the in-bounds contract for a pointer and element count.
    ///
    /// This is intentionally conservative until length constraints from
    /// contract facts and symbolic values are connected into one proof procedure.
    pub fn check_inbound(
        &self,
        _arg: usize,
        _length_arg: ContractExpr<'tcx>,
        _contract_ty: Ty<'tcx>,
    ) -> bool {
        false
    }
}
