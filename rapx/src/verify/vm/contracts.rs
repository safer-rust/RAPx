use rustc_middle::mir::Local;

use crate::verify::contract::{
    ContractExpr, ContractPlace, PlaceBase, Property, PropertyArg, PropertyKind,
};

pub(crate) fn index_access_locals(property: &Property<'_>) -> Option<(Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::InBound {
        return None;
    }
    let Some(PropertyArg::Expr(ContractExpr::IndexAccess { slice, index })) = atom.args.first()
    else { return None };
    let (ContractExpr::Place(slice), ContractExpr::Place(index)) = (slice.as_ref(), index.as_ref())
    else { return None };
    (slice.projections.is_empty() && index.projections.is_empty())
        .then(|| (slice.base.to_local(), index.base.to_local()))
}

pub(crate) fn slice_offset_locals(property: &Property<'_>) -> Option<(Local, Local, Local)> {
    let Property::Atom(atom) = property else { return None };
    if atom.kind != PropertyKind::SliceOffset {
        return None;
    }
    let locals: Option<Vec<Local>> = atom.args.iter().map(|arg| {
        let PropertyArg::Expr(ContractExpr::Place(place)) = arg else { return None };
        place.projections.is_empty().then(|| place.base.to_local())
    }).collect();
    let locals = locals?;
    let [dest, base, index] = locals.as_slice() else { return None };
    Some((*dest, *base, *index))
}

pub(crate) fn bind_call_property<'tcx>(
    property: &mut Property<'tcx>,
    args: &[Option<Local>],
    destination: Local,
) -> bool {
    let mut bound = true;
    map_property_places(property, &mut |place| {
        let local = match place.base {
            PlaceBase::Return | PlaceBase::Local(0) => Some(destination),
            PlaceBase::Arg(index) => args.get(index).copied().flatten(),
            PlaceBase::Local(index) => args.get(index - 1).copied().flatten(),
        };
        if let Some(local) = local {
            place.base = PlaceBase::Local(local.as_usize());
        } else {
            bound = false;
        }
    });
    bound
}

/// Rebind every `self` place in a struct invariant to the given MIR local, so
/// an invariant parsed against the struct's own `self` can be asserted on a
/// freshly-created reference (`&*NonNull<T>` → `&T`).
pub(crate) fn rebind_property_place<'tcx>(property: &mut Property<'tcx>, local: Local) {
    map_property_places(property, &mut |place| {
        place.base = PlaceBase::Local(local.as_usize());
    });
}

fn map_property_places<'tcx>(
    property: &mut Property<'tcx>,
    map: &mut impl FnMut(&mut ContractPlace<'tcx>),
) {
    match property {
        Property::Atom(atom) => {
            for arg in &mut atom.args {
                match arg {
                    PropertyArg::Expr(expr) => map_expr_places(expr, map),
                    PropertyArg::Predicates(preds) => {
                        for pred in preds {
                            map_expr_places(&mut pred.lhs, map);
                            map_expr_places(&mut pred.rhs, map);
                        }
                    }
                    _ => {}
                }
            }
            if let Some(place) = &mut atom.for_each {
                map(place);
            }
        }
        Property::And(and) => {
            for c in &mut and.conjuncts {
                map_property_places(c, map);
            }
        }
        Property::Or(or) => {
            for d in &mut or.disjuncts {
                map_property_places(d, map);
            }
        }
    }
}

fn map_expr_places<'tcx>(
    expr: &mut ContractExpr<'tcx>,
    map: &mut impl FnMut(&mut ContractPlace<'tcx>),
) {
    match expr {
        ContractExpr::Place(cp) => map(cp),
        ContractExpr::Len(inner, _) | ContractExpr::IsEmpty(inner, _) => {
            map_expr_places(inner, map)
        }
        ContractExpr::IndexAccess { slice, index } => {
            map_expr_places(slice, map);
            map_expr_places(index, map);
        }
        ContractExpr::Binary { lhs, rhs, .. } => {
            map_expr_places(lhs, map);
            map_expr_places(rhs, map);
        }
        ContractExpr::Unary { expr: inner, .. } => map_expr_places(inner, map),
        ContractExpr::MethodCall { receiver, args, .. } => {
            map_expr_places(receiver, map);
            for arg in args {
                map_expr_places(arg, map);
            }
        }
        ContractExpr::If {
            cond,
            then_expr,
            else_expr,
        } => {
            map_expr_places(&mut cond.lhs, map);
            map_expr_places(&mut cond.rhs, map);
            map_expr_places(then_expr, map);
            map_expr_places(else_expr, map);
        }
        _ => {}
    }
}
