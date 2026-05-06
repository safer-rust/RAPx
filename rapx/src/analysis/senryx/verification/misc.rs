//! Miscellaneous safety-property placeholders.
//!
//! These APIs correspond to contract tags that have not yet gained full graph
//! or symbolic proof procedures. Lightweight checks live here until they are
//! promoted into dedicated property modules.

use crate::analysis::senryx::{
    contract::{ContractExpr, NumericOp, NumericPredicate, NumericUnaryOp, RelOp},
    visitor::BodyVisitor,
};

impl<'tcx> BodyVisitor<'tcx> {
    /// Placeholder for allocator-consistency checking.
    pub fn check_allocator_consistency(&self, _func_name: String, _arg: usize) -> bool {
        true
    }

    /// Placeholder for UTF-8 string validity checking.
    pub fn check_valid_string(&self, _arg: usize) -> bool {
        true
    }

    /// Placeholder for nul-terminated C string validity checking.
    pub fn check_valid_cstr(&self, _arg: usize) -> bool {
        true
    }

    /// Check numeric predicates that are already fully constant.
    ///
    /// Non-constant predicates currently return true to preserve the previous
    /// placeholder behavior; a later `NumericProver` should discharge them with
    /// symbolic values and path constraints.
    pub fn check_valid_num(&self, predicates: &[NumericPredicate<'tcx>]) -> bool {
        predicates
            .iter()
            .all(|predicate| self.check_constant_numeric_predicate(predicate))
    }

    /// Evaluate one numeric predicate when both sides are constants.
    fn check_constant_numeric_predicate(&self, predicate: &NumericPredicate<'tcx>) -> bool {
        let (Some(lhs), Some(rhs)) = (
            Self::eval_constant_contract_expr(&predicate.lhs),
            Self::eval_constant_contract_expr(&predicate.rhs),
        ) else {
            return true;
        };

        match predicate.op {
            RelOp::Eq => lhs == rhs,
            RelOp::Ne => lhs != rhs,
            RelOp::Lt => lhs < rhs,
            RelOp::Le => lhs <= rhs,
            RelOp::Gt => lhs > rhs,
            RelOp::Ge => lhs >= rhs,
        }
    }

    /// Evaluate a contract expression when it is a literal-only expression.
    fn eval_constant_contract_expr(expr: &ContractExpr<'tcx>) -> Option<u128> {
        match expr {
            ContractExpr::Const(value) => Some(*value),
            ContractExpr::Binary { op, lhs, rhs } => {
                let lhs = Self::eval_constant_contract_expr(lhs)?;
                let rhs = Self::eval_constant_contract_expr(rhs)?;
                match op {
                    NumericOp::Add => lhs.checked_add(rhs),
                    NumericOp::Sub => lhs.checked_sub(rhs),
                    NumericOp::Mul => lhs.checked_mul(rhs),
                    NumericOp::Div => {
                        if rhs == 0 {
                            None
                        } else {
                            Some(lhs / rhs)
                        }
                    }
                    NumericOp::Rem => {
                        if rhs == 0 {
                            None
                        } else {
                            Some(lhs % rhs)
                        }
                    }
                    NumericOp::BitAnd => Some(lhs & rhs),
                    NumericOp::BitOr => Some(lhs | rhs),
                    NumericOp::BitXor => Some(lhs ^ rhs),
                }
            }
            ContractExpr::Unary { op, expr } => {
                let value = Self::eval_constant_contract_expr(expr)?;
                match op {
                    NumericUnaryOp::Not => Some(!value),
                    NumericUnaryOp::Neg => 0_u128.checked_sub(value),
                }
            }
            _ => None,
        }
    }

    /// Placeholder for aliasing constraints.
    pub fn check_alias(&self, _arg: usize) -> bool {
        true
    }
}
