//! Composite pointer-safety contract checkers.
//!
//! This module owns `Allocated`, `Deref`, `ValidPtr`, and pointer-to-reference
//! conversion checks. Several leaf predicates are still conservative
//! placeholders, but the composite APIs keep the contract structure explicit.

use crate::analysis::senryx::{contract::ContractExpr, visitor::BodyVisitor};
use rustc_middle::ty::Ty;

impl<'tcx> BodyVisitor<'tcx> {
    /// Placeholder for allocation provenance checking.
    pub fn check_allocated(&self, _arg: usize) -> bool {
        true
    }

    /// Check the composite `ValidPtr` contract.
    pub fn check_valid_ptr(
        &self,
        arg: usize,
        length_arg: ContractExpr<'tcx>,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        !self.check_non_zst(arg)
            || (self.check_non_zst(arg) && self.check_deref(arg, length_arg, contract_ty))
    }

    /// Check that a pointer can be dereferenced for the requested extent.
    pub fn check_deref(
        &self,
        arg: usize,
        length_arg: ContractExpr<'tcx>,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        self.check_allocated(arg) && self.check_inbound(arg, length_arg, contract_ty)
    }

    /// Check the composite pointer-to-reference conversion contract.
    pub fn check_ref_to_ptr(
        &self,
        arg: usize,
        length_arg: ContractExpr<'tcx>,
        contract_ty: Ty<'tcx>,
    ) -> bool {
        self.check_deref(arg, length_arg, contract_ty)
            && self.check_init(arg)
            && self.check_align(arg, contract_ty)
            && self.check_alias(arg)
    }
}
