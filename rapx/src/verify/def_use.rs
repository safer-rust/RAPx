//! Verify-specific extensions for def-use computation.
//!
//! Re-exports core types from `helpers/def_use` and augments
//! `PlaceKey` / `RelevantPlaces` with contract/property-aware methods.

pub use crate::helpers::def_use::*;

use rustc_middle::mir::Operand;
use rustc_middle::ty::TyCtxt;

use super::contract::{
    ContractExpr, ContractPlace, ContractProjection, NumericPredicate, PlaceBase, Property,
    PropertyArg, PropertyKind,
};
use crate::helpers::mir_utils::callee_param_index_for_local;
use crate::helpers::mir_scan::Checkpoint;

impl PlaceKey {
    /// Build a relevance place key from a parsed contract place.
    pub fn from_contract_place(place: &ContractPlace<'_>) -> Self {
        Self {
            base: match place.base {
                PlaceBase::Return => PlaceBaseKey::Return,
                PlaceBase::Arg(index) => PlaceBaseKey::Arg(index),
                PlaceBase::Local(local) => PlaceBaseKey::Local(local),
            },
            fields: place
                .projections
                .iter()
                .filter_map(|projection| match projection {
                    ContractProjection::Field { index, .. } => Some(*index),
                    ContractProjection::Downcast { .. } => Some(0),
                    ContractProjection::IterElements => None,
                })
                .collect(),
        }
    }
}

impl RelevantPlaces {
    /// Extract initial relevance roots from a required property.
    pub fn from_property(property: &Property<'_>) -> Self {
        let mut set = Self::new();
        set.collect_property(property);
        set
    }

    /// Insert a contract place as a relevance root.
    pub fn insert_contract_place(&mut self, place: &ContractPlace<'_>) {
        self.insert_place_key(PlaceKey::from_contract_place(place));
    }

    /// Collect all roots mentioned by a property.
    fn collect_property(&mut self, property: &Property<'_>) {
        if let Property::Or(or) = property {
            for group in &or.groups {
                for sub in group.iter() {
                    self.collect_property(sub);
                }
            }
            return;
        }
        let kind = property.kind();
        for (arg_index, arg) in property.args().iter().enumerate() {
            if let Some(k) = kind
                && self.collect_target_argument_root(&k, arg_index, arg)
            {
                continue;
            }
            self.collect_property_arg(arg);
        }
    }

    /// Collect a numeric std-contract target argument as a callee argument root.
    fn collect_target_argument_root(
        &mut self,
        kind: &PropertyKind,
        arg_index: usize,
        arg: &PropertyArg<'_>,
    ) -> bool {
        if !is_target_argument_index(kind, arg_index) {
            return false;
        }
        let PropertyArg::Expr(ContractExpr::Const(value)) = arg else {
            return false;
        };
        let Ok(index) = usize::try_from(*value) else {
            return false;
        };
        self.insert_place_key(PlaceKey {
            base: PlaceBaseKey::Arg(index),
            fields: Vec::new(),
        });
        true
    }

    /// Collect all roots mentioned by a property argument.
    fn collect_property_arg(&mut self, arg: &PropertyArg<'_>) {
        match arg {
            PropertyArg::Expr(expr) => self.collect_contract_expr(expr),
            PropertyArg::Predicates(predicates) => {
                for predicate in predicates {
                    self.collect_numeric_predicate(predicate);
                }
            }
            PropertyArg::Ty(_) | PropertyArg::Ident(_) => {}
        }
    }

    /// Collect all roots mentioned by a numeric predicate.
    fn collect_numeric_predicate(&mut self, predicate: &NumericPredicate<'_>) {
        self.collect_contract_expr(&predicate.lhs);
        self.collect_contract_expr(&predicate.rhs);
    }

    /// Collect all roots mentioned by a contract expression.
    fn collect_contract_expr(&mut self, expr: &ContractExpr<'_>) {
        match expr {
            ContractExpr::Place(place) => self.insert_contract_place(place),
            ContractExpr::Binary { lhs, rhs, .. } => {
                self.collect_contract_expr(lhs);
                self.collect_contract_expr(rhs);
            }
            ContractExpr::Unary { expr, .. } => self.collect_contract_expr(expr),
            ContractExpr::Len(expr) => {
                self.collect_contract_expr(expr);
                if let ContractExpr::Place(place) = expr.as_ref() {
                    self.need_len.insert(PlaceKey::from_contract_place(place));
                }
            }
            ContractExpr::IndexAccess { slice, index } => {
                self.collect_contract_expr(slice);
                self.collect_contract_expr(index);
            }
            ContractExpr::Min { a, b } | ContractExpr::Max { a, b } => {
                self.collect_contract_expr(a);
                self.collect_contract_expr(b);
            }
            ContractExpr::If {
                cond,
                then_expr,
                else_expr,
            } => {
                self.collect_numeric_predicate(cond);
                self.collect_contract_expr(then_expr);
                self.collect_contract_expr(else_expr);
            }
            ContractExpr::Const(_)
            | ContractExpr::ConstParam { .. }
            | ContractExpr::SizeOf(_)
            | ContractExpr::AlignOf(_)
            | ContractExpr::Unknown => {}
        }
    }
}

/// Return whether an argument index is a target-place position for a property.
fn is_target_argument_index(kind: &PropertyKind, arg_index: usize) -> bool {
    match kind {
        PropertyKind::NonOverlap | PropertyKind::Alias => arg_index <= 1,
        PropertyKind::ValidNum | PropertyKind::Unknown => false,
        _ => arg_index == 0,
    }
}

/// Bind callee parameter roots to concrete MIR call operands.
pub fn bind_callsite_roots(
    tcx: TyCtxt<'_>,
    relevance: &mut RelevantPlaces,
    checkpoint: &Checkpoint<'_>,
) {
    let argument_roots: Vec<(PlaceKey, usize)> = relevance
        .places
        .iter()
        .filter_map(|place| match place.base {
            PlaceBaseKey::Arg(index) => Some((place.clone(), index)),
            PlaceBaseKey::Local(local) => checkpoint
                .callee
                .and_then(|callee| callee_param_index_for_local(tcx, callee, local))
                .map(|index| (place.clone(), index)),
            _ => None,
        })
        .collect();

    let mut bound_roots = RelevantPlaces::new();
    let mut rebound_roots = Vec::new();
    for (root, index) in argument_roots {
        if let Some(operand) = checkpoint.args.get(index) {
            if let Some(place) = bind_operand_place(operand, &root.fields) {
                bound_roots.insert_place_key(place);
            } else {
                bound_roots.extend(operand_uses(operand));
            }
            rebound_roots.push(root);
        }
    }

    relevance.remove_place_keys(&rebound_roots);
    relevance.extend(bound_roots);

    // Bind need_len places: contract `Len(place)` expressions where the
    // inner place is a callee argument.  The bound callsite place is
    // registered in relevance.need_len so the backward slicer can match
    // `slice::len()` calls that operate on the same pointer/slice.
    {
        let need_len_roots: Vec<(PlaceKey, usize)> = relevance
            .need_len
            .iter()
            .filter_map(|place| match place.base {
                PlaceBaseKey::Arg(index) => Some((place.clone(), index)),
                PlaceBaseKey::Local(local) => checkpoint
                    .callee
                    .and_then(|callee| callee_param_index_for_local(tcx, callee, local))
                    .map(|index| (place.clone(), index)),
                _ => None,
            })
            .collect();
        for (root, index) in need_len_roots {
            if let Some(operand) = checkpoint.args.get(index) {
                if let Some(place) = bind_operand_place(operand, &root.fields) {
                    relevance.need_len.insert(place);
                }
            }
        }
    }
}

fn bind_operand_place(operand: &Operand<'_>, fields: &[usize]) -> Option<PlaceKey> {
    let mut place = match operand {
        Operand::Copy(place) | Operand::Move(place) => PlaceKey::from_mir_place(place),
        Operand::Constant(_) => return None,
        #[cfg(rapx_ge_99)]
        Operand::RuntimeChecks(_) => return None,
    };
    place.fields.extend(fields.iter().copied());
    Some(place)
}
