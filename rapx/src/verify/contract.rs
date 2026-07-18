use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp as MirBinOp;
use rustc_middle::ty::{GenericParamDefKind, Ty, TyCtxt, TyKind};
use safety_parser::syn::{
    BinOp as SynBinOp, Expr, GenericArgument, Lit, PathArguments, Type, UnOp,
};

use super::def_use::PlaceKey;
use super::helpers::{
    access_ident_recursive, match_ty_with_ident, parse_expr_into_local_and_ty,
    parse_expr_into_number,
};

#[derive(Clone, Debug, PartialEq)]
pub enum PlaceBase {
    Return,
    Arg(usize),
    Local(usize),
}

#[derive(Clone, Debug)]
pub enum ContractProjection<'tcx> {
    Field { index: usize, ty: Option<Ty<'tcx>> },
    Downcast { variant_index: usize },
}

#[derive(Clone, Debug)]
pub struct ContractPlace<'tcx> {
    pub base: PlaceBase,
    pub projections: Vec<ContractProjection<'tcx>>,
}

impl<'tcx> ContractPlace<'tcx> {
    pub fn local(base: usize, fields: Vec<(usize, Ty<'tcx>)>) -> Self {
        Self {
            base: if base == 0 {
                PlaceBase::Return
            } else {
                PlaceBase::Local(base)
            },
            projections: fields
                .into_iter()
                .map(|(index, ty)| ContractProjection::Field {
                    index,
                    ty: Some(ty),
                })
                .collect(),
        }
    }

    pub fn arg(index: usize) -> Self {
        Self {
            base: PlaceBase::Arg(index),
            projections: Vec::new(),
        }
    }

    pub fn local_base(&self) -> Option<usize> {
        match self.base {
            PlaceBase::Return => Some(0),
            PlaceBase::Local(local) => Some(local),
            PlaceBase::Arg(_) => None,
        }
    }

    pub fn field_indices(&self) -> Vec<usize> {
        self.projections
            .iter()
            .filter_map(|projection| match projection {
                ContractProjection::Field { index, .. } => Some(*index),
                ContractProjection::Downcast { .. } => None,
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum NumericOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
}

impl NumericOp {
    fn from_syn(op: &SynBinOp) -> Option<Self> {
        match op {
            SynBinOp::Add(_) => Some(Self::Add),
            SynBinOp::Sub(_) => Some(Self::Sub),
            SynBinOp::Mul(_) => Some(Self::Mul),
            SynBinOp::Div(_) => Some(Self::Div),
            SynBinOp::Rem(_) => Some(Self::Rem),
            SynBinOp::BitAnd(_) => Some(Self::BitAnd),
            SynBinOp::BitOr(_) => Some(Self::BitOr),
            SynBinOp::BitXor(_) => Some(Self::BitXor),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum NumericUnaryOp {
    Not,
    Neg,
}

impl NumericUnaryOp {
    fn from_syn(op: &UnOp) -> Option<Self> {
        match op {
            UnOp::Not(_) => Some(Self::Not),
            UnOp::Neg(_) => Some(Self::Neg),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub enum ContractExpr<'tcx> {
    Place(ContractPlace<'tcx>),
    Const(u128),
    ConstParam {
        index: u32,
        name: String,
    },
    SizeOf(Ty<'tcx>),
    AlignOf(Ty<'tcx>),
    Len(Box<ContractExpr<'tcx>>),
    IndexAccess {
        slice: Box<ContractExpr<'tcx>>,
        index: Box<ContractExpr<'tcx>>,
    },
    Binary {
        op: NumericOp,
        lhs: Box<ContractExpr<'tcx>>,
        rhs: Box<ContractExpr<'tcx>>,
    },
    Unary {
        op: NumericUnaryOp,
        expr: Box<ContractExpr<'tcx>>,
    },
    Unknown,
}

impl<'tcx> ContractExpr<'tcx> {
    pub fn new_var(base: usize) -> Self {
        Self::Place(ContractPlace::local(base, Vec::new()))
    }

    pub fn new_value(value: usize) -> Self {
        Self::Const(value as u128)
    }

    pub fn new_unknown() -> Self {
        Self::Unknown
    }

    pub fn get_var_base(&self) -> Option<usize> {
        match self {
            Self::Place(place) => place.local_base(),
            _ => None,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum RelOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl RelOp {
    pub fn from_mir(op: MirBinOp) -> Option<Self> {
        match op {
            MirBinOp::Eq => Some(Self::Eq),
            MirBinOp::Ne => Some(Self::Ne),
            MirBinOp::Lt => Some(Self::Lt),
            MirBinOp::Le => Some(Self::Le),
            MirBinOp::Gt => Some(Self::Gt),
            MirBinOp::Ge => Some(Self::Ge),
            _ => None,
        }
    }

    fn from_syn(op: &SynBinOp) -> Option<Self> {
        match op {
            SynBinOp::Eq(_) => Some(Self::Eq),
            SynBinOp::Ne(_) => Some(Self::Ne),
            SynBinOp::Lt(_) => Some(Self::Lt),
            SynBinOp::Le(_) => Some(Self::Le),
            SynBinOp::Gt(_) => Some(Self::Gt),
            SynBinOp::Ge(_) => Some(Self::Ge),
            _ => None,
        }
    }

    pub fn reversed(self) -> Self {
        match self {
            Self::Eq => Self::Eq,
            Self::Ne => Self::Ne,
            Self::Lt => Self::Gt,
            Self::Le => Self::Ge,
            Self::Gt => Self::Lt,
            Self::Ge => Self::Le,
        }
    }
}

#[derive(Clone, Debug)]
pub struct NumericPredicate<'tcx> {
    pub lhs: ContractExpr<'tcx>,
    pub op: RelOp,
    pub rhs: ContractExpr<'tcx>,
}

impl<'tcx> NumericPredicate<'tcx> {
    pub fn new(lhs: ContractExpr<'tcx>, op: RelOp, rhs: ContractExpr<'tcx>) -> Self {
        Self { lhs, op, rhs }
    }

    pub fn from_mir_locals(lhs: usize, rhs: usize, op: MirBinOp) -> Option<Self> {
        RelOp::from_mir(op)
            .map(|rel| Self::new(ContractExpr::new_var(lhs), rel, ContractExpr::new_var(rhs)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PropertyKind {
    Align,
    Size,
    NoPadding,
    NonNull,
    Allocated,
    InBound,
    NonOverlap,
    ValidNum,
    ValidString,
    ValidCStr,
    Init,
    Unwrap,
    Typed,
    /// `ownership(*p) = none` — no live owner aliases the pointee, so the
    /// callee may (re)claim ownership (psp IV.1 in primitive-sp.md).
    Owning,
    Alias,
    Alive,
    Pinned,
    NonVolatile,
    Opened,
    Trait,
    Unreachable,
    ValidPtr,
    ValidSlice,
    Deref,
    Ptr2Ref,
    Layout,
    ValidTransmute,
    TransmuteWithoutAlign,
    Nullable,
    Unknown,
}

#[derive(Clone, Debug)]
pub enum PropertyArg<'tcx> {
    Place(ContractPlace<'tcx>),
    Ty(Ty<'tcx>),
    Expr(ContractExpr<'tcx>),
    Predicates(Vec<NumericPredicate<'tcx>>),
    Ident(String),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ContractKind {
    Precond,
    Hazard,
}

#[derive(Clone, Debug)]
pub struct Property<'tcx> {
    pub kind: PropertyKind,
    pub args: Vec<PropertyArg<'tcx>>,
    pub contract_kind: ContractKind,
    /// When set, this property came from an `any(Null(guard), ...)` expansion
    /// and is vacuously true when `guard` is null.
    pub null_guard: Option<PlaceKey>,
}

impl<'tcx> Property<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Self {
        match name {
            "Align" => {
                if !Self::check_arg_length(exprs.len(), 2, "Align") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                let Some(ty) = Self::parse_type(tcx, def_id, &exprs[1], "Align") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(PropertyKind::Align, vec![target, PropertyArg::Ty(ty)])
            }
            "Size" => match exprs {
                [] => Self::new_simple(PropertyKind::Size),
                _ => Self::new_with_target(PropertyKind::Size, tcx, def_id, exprs),
            },
            "NoPadding" => Self::new_with_target(PropertyKind::NoPadding, tcx, def_id, exprs),
            "NonNull" => Self::new_with_target(PropertyKind::NonNull, tcx, def_id, exprs),
            "Allocated" => match exprs {
                [target] => Self::new_with_args(
                    PropertyKind::Allocated,
                    vec![Self::parse_target_arg(tcx, def_id, target)],
                ),
                [target_expr, ty_expr, len_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, target_expr);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "Allocated") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "Allocated");
                    Self::new_with_args(
                        PropertyKind::Allocated,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                _ => {
                    Self::check_arg_length(exprs.len(), 3, "Allocated");
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "InBound" | "InBounded" => match exprs {
                [expr] => {
                    let expr = Self::parse_contract_expr(tcx, def_id, expr, "InBound");
                    if matches!(expr, ContractExpr::IndexAccess { .. }) {
                        Self::new_with_args(PropertyKind::InBound, vec![PropertyArg::Expr(expr)])
                    } else {
                        Self::new_simple(PropertyKind::Unknown)
                    }
                }
                [_target, ty_expr, len_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "InBound") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "InBound");
                    Self::new_with_args(
                        PropertyKind::InBound,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                [target, index_expr] => {
                    // Slice-index form: `InBound(slice, index)` when the first
                    // argument is a slice. This is shorthand for the explicit
                    // `InBound(index_access(slice, index))` and lowers to the
                    // same `ContractExpr::IndexAccess`.
                    if Self::parse_target_type(tcx, def_id, target).is_some_and(ty_is_slice) {
                        let slice = Self::parse_contract_expr(tcx, def_id, target, "InBound");
                        let index = Self::parse_contract_expr(tcx, def_id, index_expr, "InBound");
                        return Self::new_with_args(
                            PropertyKind::InBound,
                            vec![PropertyArg::Expr(ContractExpr::IndexAccess {
                                slice: Box::new(slice),
                                index: Box::new(index),
                            })],
                        );
                    }

                    // Pointer-arithmetic form: `InBound(ptr, count)` with the
                    // element type inferred from the pointer.
                    let Some(ty) = Self::parse_target_type(tcx, def_id, target) else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let target = Self::parse_target_arg(tcx, def_id, target);
                    let length = Self::parse_contract_expr(tcx, def_id, index_expr, "InBound");
                    Self::new_with_args(
                        PropertyKind::InBound,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                _ => {
                    Self::check_arg_length(exprs.len(), 3, "InBound");
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "NonOverlap" => match exprs {
                [indices] => {
                    let target = Self::parse_target_arg(tcx, def_id, indices);
                    Self::new_with_args(PropertyKind::NonOverlap, vec![target])
                }
                _ => Self::new_with_targets(PropertyKind::NonOverlap, tcx, def_id, exprs),
            },
            "ValidNum" => {
                let predicates = Self::parse_valid_num(tcx, def_id, exprs);
                if predicates.is_empty() {
                    Self::new_simple(PropertyKind::Unknown)
                } else {
                    Self::new_with_args(
                        PropertyKind::ValidNum,
                        vec![PropertyArg::Predicates(predicates)],
                    )
                }
            }
            "ValidString" => Self::new_with_target(PropertyKind::ValidString, tcx, def_id, exprs),
            "ValidCStr" => Self::new_with_target(PropertyKind::ValidCStr, tcx, def_id, exprs),
            "Init" => {
                if !Self::check_arg_length(exprs.len(), 3, "Init") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                let Some(ty) = Self::parse_type(tcx, def_id, &exprs[1], "Init") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = Self::parse_contract_expr(tcx, def_id, &exprs[2], "Init");
                Self::new_with_args(
                    PropertyKind::Init,
                    vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                )
            }
            "Unwrap" => Self::new_with_target(PropertyKind::Unwrap, tcx, def_id, exprs),
            "Typed" => {
                if !Self::check_arg_length(exprs.len(), 2, "Typed") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                let Some(ty) = Self::parse_type(tcx, def_id, &exprs[1], "Typed") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(PropertyKind::Typed, vec![target, PropertyArg::Ty(ty)])
            }
            "Owning" => Self::new_with_target(PropertyKind::Owning, tcx, def_id, exprs),
            "Alias" => {
                let mut prop = Self::new_with_targets(PropertyKind::Alias, tcx, def_id, exprs);
                prop.contract_kind = ContractKind::Hazard;
                prop
            }
            "Alive" => Self::new_with_targets(PropertyKind::Alive, tcx, def_id, exprs),
            "Pinned" => Self::new_with_target(PropertyKind::Pinned, tcx, def_id, exprs),
            "NonVolatile" => Self::new_with_target(PropertyKind::NonVolatile, tcx, def_id, exprs),
            "Opened" => Self::new_with_target(PropertyKind::Opened, tcx, def_id, exprs),
            "Trait" => Self::new_with_target(PropertyKind::Trait, tcx, def_id, exprs),
            "Unreachable" => Self::new_with_target(PropertyKind::Unreachable, tcx, def_id, exprs),
            "ValidPtr" => {
                if !Self::check_arg_length(exprs.len(), 3, "ValidPtr") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                let Some(ty) = Self::parse_type(tcx, def_id, &exprs[1], "ValidPtr") else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let length = Self::parse_contract_expr(tcx, def_id, &exprs[2], "ValidPtr");
                Self::new_with_args(
                    PropertyKind::ValidPtr,
                    vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                )
            }
            "ValidSlice" => match exprs {
                [target_expr, ty_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, target_expr);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "ValidSlice") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    Self::new_with_args(PropertyKind::ValidSlice, vec![target, PropertyArg::Ty(ty)])
                }
                [target_expr] => {
                    let Some(ty) = Self::parse_target_type(tcx, def_id, target_expr) else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let target = Self::parse_target_arg(tcx, def_id, target_expr);
                    Self::new_with_args(PropertyKind::ValidSlice, vec![target, PropertyArg::Ty(ty)])
                }
                _ => {
                    Self::check_arg_length(exprs.len(), 2, "ValidSlice");
                    Self::new_simple(PropertyKind::Unknown)
                }
            },
            "Deref" => match exprs {
                [_target, ty_expr, len_expr] => {
                    let target = Self::parse_target_arg(tcx, def_id, &exprs[0]);
                    let Some(ty) = Self::parse_type(tcx, def_id, ty_expr, "Deref") else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "Deref");
                    Self::new_with_args(
                        PropertyKind::Deref,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                [target, len_expr] => {
                    let Some(ty) = Self::parse_target_type(tcx, def_id, target) else {
                        return Self::new_simple(PropertyKind::Unknown);
                    };
                    let target = Self::parse_target_arg(tcx, def_id, target);
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "Deref");
                    Self::new_with_args(
                        PropertyKind::Deref,
                        vec![target, PropertyArg::Ty(ty), PropertyArg::Expr(length)],
                    )
                }
                _ => Self::new_with_target(PropertyKind::Deref, tcx, def_id, exprs),
            },
            "Ptr2Ref" | "ValidPtr2Ref" => {
                Self::new_with_target(PropertyKind::Ptr2Ref, tcx, def_id, exprs)
            }
            "Layout" => Self::new_with_target(PropertyKind::Layout, tcx, def_id, exprs),
            "ValidTransmute" => {
                if !Self::check_arg_length(exprs.len(), 2, "ValidTransmute") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let Some(src_ty) = Self::parse_type(tcx, def_id, &exprs[0], "ValidTransmute")
                else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                let Some(dst_ty) = Self::parse_type(tcx, def_id, &exprs[1], "ValidTransmute")
                else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(
                    PropertyKind::ValidTransmute,
                    vec![PropertyArg::Ty(src_ty), PropertyArg::Ty(dst_ty)],
                )
            }
            "TransmuteWithoutAlign" => {
                if !Self::check_arg_length(exprs.len(), 2, "TransmuteWithoutAlign") {
                    return Self::new_simple(PropertyKind::Unknown);
                }
                let src_elem = unwrap_array_expr(tcx, def_id, &exprs[0]);
                let dst_elem = unwrap_array_expr(tcx, def_id, &exprs[1]);
                let (Some(src_elem), Some(dst_elem)) = (src_elem, dst_elem) else {
                    return Self::new_simple(PropertyKind::Unknown);
                };
                Self::new_with_args(
                    PropertyKind::TransmuteWithoutAlign,
                    vec![PropertyArg::Ty(src_elem), PropertyArg::Ty(dst_elem)],
                )
            }
            "NonSize" => Self::new_simple(PropertyKind::Size),
            "Null" => Self::new_with_target(PropertyKind::Nullable, tcx, def_id, exprs),
            _ => Self::new_simple(PropertyKind::Unknown),
        }
    }

    pub fn new_partial_order(lhs: usize, rhs: usize, op: MirBinOp) -> Self {
        if let Some(predicate) = NumericPredicate::from_mir_locals(lhs, rhs, op) {
            Self::new_with_args(
                PropertyKind::ValidNum,
                vec![PropertyArg::Predicates(vec![predicate])],
            )
        } else {
            Self::new_simple(PropertyKind::Unknown)
        }
    }

    pub fn new_obj_boundary(ty: Ty<'tcx>, len: ContractExpr<'tcx>) -> Self {
        Self::new_with_args(
            PropertyKind::InBound,
            vec![
                PropertyArg::Expr(ContractExpr::Unknown),
                PropertyArg::Ty(ty),
                PropertyArg::Expr(len),
            ],
        )
    }

    fn new_simple(kind: PropertyKind) -> Self {
        Self {
            kind,
            args: Vec::new(),
            contract_kind: ContractKind::Precond,
            null_guard: None,
        }
    }

    /// Parse one annotation entry into the properties it denotes.
    ///
    /// Plain entries (`Align(p, T)`, `Owning(p)`, ...) yield one property.
    /// The `any(...)` combinator may expand to several: see [`Self::parse_any`].
    pub fn parse_list(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &[Expr]) -> Vec<Self> {
        if name == "any" {
            return Self::parse_any(tcx, def_id, exprs);
        }
        vec![Self::new(tcx, def_id, name, exprs)]
    }

    /// Parse the disjunctive combinator `any(D1, D2)` written in DNF:
    /// `any` means logical OR between disjuncts, and commas inside a
    /// parenthesised disjunct mean logical AND:
    ///
    /// ```text
    /// any((Null(p)), (P1(p, ...), P2(p, ...), ...))
    /// ```
    ///
    /// A disjunct is either a single property application `P(...)` or a
    /// parenthesised conjunction `(P1(...), ..., Pn(...))`.  The shape the
    /// verifier currently supports is a null guard: exactly two disjuncts,
    /// one being `Null(p)` alone, the other a conjunction of properties over
    /// the same place `p`.  The disjunction expands to the conjunct
    /// properties, each holding whenever `p` is non-null and vacuously for a
    /// null `p` (e.g. an empty list's `head` or the last node's `next`) —
    /// the raw-pointer counterpart of `Option` invariants written through
    /// `unwrap_some()`.  Use sites are expected to be dominated by their own
    /// null checks.
    fn parse_any(tcx: TyCtxt<'tcx>, def_id: DefId, exprs: &[Expr]) -> Vec<Self> {
        if !Self::check_arg_length(exprs.len(), 2, "any") {
            return vec![Self::new_simple(PropertyKind::Unknown)];
        }

        let (Some(first), Some(second)) = (
            Self::disjunct_parts(&exprs[0]),
            Self::disjunct_parts(&exprs[1]),
        ) else {
            rap_error!("any(...) disjuncts must be property applications or (P1, P2, ...) groups");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };

        let is_null_guard =
            |disjunct: &[(String, Vec<Expr>)]| disjunct.len() == 1 && disjunct[0].0 == "Null";
        let (guard, conjuncts) = if is_null_guard(&first) && !is_null_guard(&second) {
            (first, second)
        } else if is_null_guard(&second) && !is_null_guard(&first) {
            (second, first)
        } else {
            rap_error!(
                "any(...) currently supports exactly one Null(p) disjunct next to \
                 one conjunction of properties over the same place"
            );
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };

        let guard_args = &guard[0].1;
        if guard_args.len() != 1 {
            rap_error!("Null(...) guard inside any(...) takes exactly one place");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        }
        let Some(guard_place) = Self::parse_contract_place(tcx, def_id, &guard_args[0]) else {
            rap_error!("cannot resolve the place guarded by Null(...) inside any(...)");
            return vec![Self::new_simple(PropertyKind::Unknown)];
        };
        let guard_key = crate::verify::def_use::PlaceKey::from_contract_place(&guard_place);

        let mut properties = Vec::new();
        for (inner_name, inner_args) in &conjuncts {
            let mut property = Self::new(tcx, def_id, inner_name, inner_args);
            let inner_place = property.args.first().and_then(|arg| match arg {
                PropertyArg::Place(place) => Some(place),
                PropertyArg::Expr(ContractExpr::Place(place)) => Some(place),
                _ => None,
            });
            let places_match = inner_place.is_some_and(|place| {
                crate::verify::def_use::PlaceKey::from_contract_place(place) == guard_key
            });
            if !places_match {
                rap_error!(
                    "any(Null(p), ...) requires every conjunct ({inner_name}) to \
                     constrain the guarded place"
                );
                return vec![Self::new_simple(PropertyKind::Unknown)];
            }
            property.null_guard = Some(guard_key.clone());
            properties.push(property);
        }
        properties
    }

    /// Split one disjunct into its conjunct calls: a `(P1, P2, ...)` tuple, a
    /// parenthesised single property `(P)`, or a bare property application.
    fn disjunct_parts(expr: &Expr) -> Option<Vec<(String, Vec<Expr>)>> {
        match expr {
            Expr::Tuple(tuple) => tuple.elems.iter().map(Self::call_parts).collect(),
            Expr::Paren(paren) => Self::call_parts(&paren.expr).map(|parts| vec![parts]),
            _ => Self::call_parts(expr).map(|parts| vec![parts]),
        }
    }

    /// Split a `Name(arg, ...)` call expression into its name and arguments.
    fn call_parts(expr: &Expr) -> Option<(String, Vec<Expr>)> {
        let Expr::Call(call) = expr else {
            return None;
        };
        let Expr::Path(path) = call.func.as_ref() else {
            return None;
        };
        let name = path.path.get_ident()?.to_string();
        Some((name, call.args.iter().cloned().collect()))
    }

    fn new_with_args(kind: PropertyKind, args: Vec<PropertyArg<'tcx>>) -> Self {
        Self {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
        }
    }

    fn new_with_target(
        kind: PropertyKind,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Self {
        let args = exprs
            .first()
            .map(|expr| Self::parse_target_arg(tcx, def_id, expr))
            .into_iter()
            .collect();
        Self {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
        }
    }

    fn new_with_targets(
        kind: PropertyKind,
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Self {
        let args = exprs
            .iter()
            .map(|expr| Self::parse_target_arg(tcx, def_id, expr))
            .collect();
        Self {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
        }
    }

    fn check_arg_length(expr_len: usize, required_len: usize, sp: &str) -> bool {
        if expr_len != required_len {
            rap_error!(
                "Wrong args length for {:?} Tag! expected {required_len}, got {expr_len}",
                sp
            );
            return false;
        }
        true
    }

    fn parse_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr, sp: &str) -> Option<Ty<'tcx>> {
        let ty_ident_full = access_ident_recursive(expr);
        if ty_ident_full.is_none() {
            rap_debug!("Incorrect expression for the type of {:?} Tag!", sp);
            return None;
        }
        let ty_ident = ty_ident_full.unwrap().0;
        let ty = match_ty_with_ident(tcx, def_id, ty_ident);
        if ty.is_none() {
            rap_debug!("Cannot get type in {:?} Tag!", sp);
        }
        ty
    }

    fn parse_target_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
        parse_expr_into_local_and_ty(tcx, def_id, expr).map(|(_, _, ty)| ty)
    }

    fn parse_target_arg(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> PropertyArg<'tcx> {
        // For simple identifiers that aren't local variables (e.g., lifetime param 'a
        // parsed as ident `a`), store as Ident rather than Expr which would become Unknown.
        if let Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                let s = ident.to_string();
                if s != "return"
                    && !s.starts_with("Arg_")
                    && parse_expr_into_local_and_ty(tcx, def_id, expr).is_none()
                {
                    return PropertyArg::Ident(s);
                }
            }
        }
        Self::parse_contract_place(tcx, def_id, expr)
            .map(PropertyArg::Place)
            .unwrap_or_else(|| {
                PropertyArg::Expr(Self::parse_contract_expr(tcx, def_id, expr, "target"))
            })
    }

    fn parse_contract_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
        sp: &str,
    ) -> ContractExpr<'tcx> {
        match expr {
            Expr::Paren(paren) => Self::parse_contract_expr(tcx, def_id, &paren.expr, sp),
            Expr::Group(group) => Self::parse_contract_expr(tcx, def_id, &group.expr, sp),
            Expr::Lit(expr_lit) => match &expr_lit.lit {
                Lit::Int(lit_int) => lit_int
                    .base10_parse::<u128>()
                    .map(ContractExpr::Const)
                    .unwrap_or(ContractExpr::Unknown),
                _ => ContractExpr::Unknown,
            },
            Expr::Call(expr_call) => {
                if let Some(expr) = Self::parse_index_access_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                if let Some(expr) = Self::parse_len_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                if let Some(expr) = Self::parse_layout_expr(tcx, def_id, expr_call) {
                    return expr;
                }
                ContractExpr::Unknown
            }
            // Treat `x.len` (field-access sugar) as the slice length `len(x)`.
            Expr::Field(expr_field) if matches!(&expr_field.member, safety_parser::syn::Member::Named(ident) if ident == "len") => {
                ContractExpr::Len(Box::new(Self::parse_contract_expr(
                    tcx,
                    def_id,
                    &expr_field.base,
                    sp,
                )))
            }
            // Treat `self.len()` (method-call sugar) as the slice length `len(self)`.
            Expr::MethodCall(expr_method)
                if expr_method.method == "len" && expr_method.args.is_empty() =>
            {
                ContractExpr::Len(Box::new(Self::parse_contract_expr(
                    tcx,
                    def_id,
                    &expr_method.receiver,
                    sp,
                )))
            }
            Expr::Unary(expr_unary) => {
                let Some(op) = NumericUnaryOp::from_syn(&expr_unary.op) else {
                    return ContractExpr::Unknown;
                };
                ContractExpr::Unary {
                    op,
                    expr: Box::new(Self::parse_contract_expr(tcx, def_id, &expr_unary.expr, sp)),
                }
            }
            Expr::Binary(expr_binary) => {
                let Some(op) = NumericOp::from_syn(&expr_binary.op) else {
                    return ContractExpr::Unknown;
                };
                ContractExpr::Binary {
                    op,
                    lhs: Box::new(Self::parse_contract_expr(
                        tcx,
                        def_id,
                        &expr_binary.left,
                        sp,
                    )),
                    rhs: Box::new(Self::parse_contract_expr(
                        tcx,
                        def_id,
                        &expr_binary.right,
                        sp,
                    )),
                }
            }
            _ => {
                if let Some(place) = Self::parse_contract_place(tcx, def_id, expr) {
                    ContractExpr::Place(place)
                } else if let Some(expr) = Self::parse_const_param(tcx, def_id, expr) {
                    expr
                } else if let Some(value) = Self::parse_builtin_const(tcx, expr) {
                    ContractExpr::Const(value)
                } else if let Some(value) = parse_expr_into_number(expr) {
                    ContractExpr::new_value(value)
                } else {
                    rap_debug!(
                        "Numeric expression in {:?} could not be resolved: {:?}",
                        sp,
                        expr
                    );
                    ContractExpr::Unknown
                }
            }
        }
    }

    fn parse_index_access_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let name = func_path.path.segments.last()?.ident.to_string();
        if name != "index_access" || expr_call.args.len() != 2 {
            return None;
        }

        let mut args = expr_call.args.iter();
        let slice = args.next()?;
        let index = args.next()?;
        Some(ContractExpr::IndexAccess {
            slice: Box::new(Self::parse_contract_expr(
                tcx,
                def_id,
                slice,
                "index_access",
            )),
            index: Box::new(Self::parse_contract_expr(
                tcx,
                def_id,
                index,
                "index_access",
            )),
        })
    }

    fn parse_len_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let name = func_path.path.segments.last()?.ident.to_string();
        if name != "len" || expr_call.args.len() != 1 {
            return None;
        }
        let target = expr_call.args.first()?;
        Some(ContractExpr::Len(Box::new(Self::parse_contract_expr(
            tcx, def_id, target, "len",
        ))))
    }

    fn parse_layout_expr(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr_call: &safety_parser::syn::ExprCall,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(func_path) = expr_call.func.as_ref() else {
            return None;
        };
        let last = func_path.path.segments.last()?;
        let name = last.ident.to_string();
        if name != "size_of" && name != "align_of" {
            return None;
        }

        let ty = if let Some(arg) = expr_call.args.first() {
            Self::parse_type_opt(tcx, def_id, arg)
        } else {
            Self::parse_turbofish_type(tcx, def_id, &last.arguments, "ValidNum")
        }?;

        Some(match name.as_str() {
            "size_of" => ContractExpr::SizeOf(ty),
            "align_of" => ContractExpr::AlignOf(ty),
            _ => return None,
        })
    }

    fn parse_turbofish_type(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        arguments: &PathArguments,
        sp: &str,
    ) -> Option<Ty<'tcx>> {
        let PathArguments::AngleBracketed(args) = arguments else {
            return None;
        };
        args.args.iter().find_map(|arg| match arg {
            GenericArgument::Type(ty) => Self::parse_syn_type(tcx, def_id, ty, sp),
            _ => None,
        })
    }

    fn parse_type_opt(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
        if let Expr::Path(expr_path) = expr
            && let Some(segment) = expr_path.path.segments.last()
        {
            return match_ty_with_ident(tcx, def_id, segment.ident.to_string());
        }
        let ty_ident = access_ident_recursive(expr)?.0;
        match_ty_with_ident(tcx, def_id, ty_ident)
    }

    fn parse_syn_type(tcx: TyCtxt<'tcx>, def_id: DefId, ty: &Type, sp: &str) -> Option<Ty<'tcx>> {
        let Type::Path(type_path) = ty else {
            return None;
        };
        let ident = type_path.path.segments.last()?.ident.to_string();
        match_ty_with_ident(tcx, def_id, ident).or_else(|| {
            rap_debug!("Cannot get type in {:?} Tag from {:?}", sp, type_path);
            None
        })
    }

    fn parse_builtin_const(tcx: TyCtxt<'tcx>, expr: &Expr) -> Option<u128> {
        let Expr::Path(expr_path) = expr else {
            return None;
        };
        let mut segments = expr_path.path.segments.iter();
        let first = segments.next()?.ident.to_string();
        let second = segments.next()?.ident.to_string();
        if segments.next().is_some() || second != "MAX" {
            return None;
        }

        let pointer_bits = tcx.data_layout.pointer_size().bits();
        match first.as_str() {
            "isize" => Some((1_u128 << (pointer_bits - 1)) - 1),
            "usize" => Some((1_u128 << pointer_bits) - 1),
            _ => None,
        }
    }

    fn parse_const_param(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<ContractExpr<'tcx>> {
        let Expr::Path(expr_path) = expr else {
            return None;
        };
        let ident = expr_path.path.get_ident()?.to_string();
        let mut generics = Some(tcx.generics_of(def_id));
        while let Some(current) = generics {
            if let Some(param) = current.own_params.iter().find(|param| {
                matches!(param.kind, GenericParamDefKind::Const { .. })
                    && param.name.as_str() == ident
            }) {
                return Some(ContractExpr::ConstParam {
                    index: param.index,
                    name: ident,
                });
            }
            generics = current.parent.map(|parent| tcx.generics_of(parent));
        }
        None
    }

    fn parse_contract_place(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<ContractPlace<'tcx>> {
        // Handle .unwrap_some() method call — downcast to the Some variant.
        if let Expr::MethodCall(expr_method) = expr {
            if expr_method.method == "unwrap_some" && expr_method.args.is_empty() {
                if let Some((base, fields, recv_ty)) =
                    parse_expr_into_local_and_ty(tcx, def_id, &expr_method.receiver)
                {
                    let peeled_ty = recv_ty.peel_refs();
                    if let TyKind::Adt(adt_def, _) = peeled_ty.kind() {
                        if adt_def.is_enum() {
                            let some_variant =
                                adt_def.variants().iter_enumerated().find_map(|(vidx, v)| {
                                    if v.name.to_string() == "Some" {
                                        Some(vidx.as_usize())
                                    } else {
                                        None
                                    }
                                });
                            if let Some(variant_index) = some_variant {
                                let mut projections: Vec<ContractProjection> = fields
                                    .into_iter()
                                    .map(|(index, ty)| ContractProjection::Field {
                                        index,
                                        ty: Some(ty),
                                    })
                                    .collect();
                                projections.push(ContractProjection::Downcast { variant_index });
                                let base_enum = if base == 0 {
                                    PlaceBase::Return
                                } else {
                                    PlaceBase::Local(base)
                                };
                                return Some(ContractPlace {
                                    base: base_enum,
                                    projections,
                                });
                            }
                        }
                    }
                }
            }
        }

        if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
            return Some(ContractPlace::local(base, fields));
        }
        Self::parse_named_place(expr)
    }

    fn parse_named_place(expr: &Expr) -> Option<ContractPlace<'tcx>> {
        if let Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                let s = ident.to_string();
                if let Some(num_str) = s.strip_prefix("Arg_") {
                    if let Ok(idx) = num_str.parse::<usize>() {
                        return Some(ContractPlace::arg(idx));
                    }
                }
                if s == "return" {
                    return Some(ContractPlace {
                        base: PlaceBase::Return,
                        projections: Vec::new(),
                    });
                }
            }
        }
        None
    }

    fn parse_valid_num(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &[Expr],
    ) -> Vec<NumericPredicate<'tcx>> {
        match exprs {
            [] => Vec::new(),
            [expr] => Self::parse_numeric_predicate(tcx, def_id, expr)
                .into_iter()
                .collect(),
            [value, range, ..] => {
                if let Some(predicates) = Self::parse_interval_predicates(tcx, def_id, value, range)
                {
                    predicates
                } else {
                    Self::parse_numeric_predicate(tcx, def_id, value)
                        .into_iter()
                        .collect()
                }
            }
        }
    }

    fn parse_numeric_predicate(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<NumericPredicate<'tcx>> {
        if let Expr::Binary(expr_binary) = expr {
            if let Some(op) = RelOp::from_syn(&expr_binary.op) {
                return Some(NumericPredicate::new(
                    Self::parse_contract_expr(tcx, def_id, &expr_binary.left, "ValidNum"),
                    op,
                    Self::parse_contract_expr(tcx, def_id, &expr_binary.right, "ValidNum"),
                ));
            }
        }

        Some(NumericPredicate::new(
            Self::parse_contract_expr(tcx, def_id, expr, "ValidNum"),
            RelOp::Ne,
            ContractExpr::Const(0),
        ))
    }

    fn parse_interval_predicates(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        range: &Expr,
    ) -> Option<Vec<NumericPredicate<'tcx>>> {
        match range {
            Expr::Array(array) if array.elems.len() == 2 => {
                let mut elems = array.elems.iter();
                let lower = elems.next().unwrap();
                let upper = elems.next().unwrap();
                Some(Self::build_interval_predicates(
                    tcx, def_id, value, lower, true, upper, true,
                ))
            }
            Expr::Lit(expr_lit) => {
                let Lit::Str(range_lit) = &expr_lit.lit else {
                    return None;
                };
                Self::parse_string_interval(tcx, def_id, value, &range_lit.value())
            }
            _ => None,
        }
    }

    fn parse_string_interval(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        raw_range: &str,
    ) -> Option<Vec<NumericPredicate<'tcx>>> {
        let trimmed = raw_range.trim();
        if trimmed.len() < 5 {
            return None;
        }

        let lower_inclusive = trimmed.starts_with('[');
        let upper_inclusive = trimmed.ends_with(']');
        if !(lower_inclusive || trimmed.starts_with('('))
            || !(upper_inclusive || trimmed.ends_with(')'))
        {
            return None;
        }

        let body = &trimmed[1..trimmed.len() - 1];
        let (lower_raw, upper_raw) = body.split_once(',')?;
        let lower = safety_parser::syn::parse_str::<Expr>(lower_raw.trim()).ok()?;
        let upper = safety_parser::syn::parse_str::<Expr>(upper_raw.trim()).ok()?;

        Some(Self::build_interval_predicates(
            tcx,
            def_id,
            value,
            &lower,
            lower_inclusive,
            &upper,
            upper_inclusive,
        ))
    }

    fn build_interval_predicates(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        value: &Expr,
        lower: &Expr,
        lower_inclusive: bool,
        upper: &Expr,
        upper_inclusive: bool,
    ) -> Vec<NumericPredicate<'tcx>> {
        let value_expr = Self::parse_contract_expr(tcx, def_id, value, "ValidNum");
        let lower_expr = Self::parse_contract_expr(tcx, def_id, lower, "ValidNum");
        let upper_expr = Self::parse_contract_expr(tcx, def_id, upper, "ValidNum");
        vec![
            NumericPredicate::new(
                lower_expr,
                if lower_inclusive {
                    RelOp::Le
                } else {
                    RelOp::Lt
                },
                value_expr.clone(),
            ),
            NumericPredicate::new(
                value_expr,
                if upper_inclusive {
                    RelOp::Le
                } else {
                    RelOp::Lt
                },
                upper_expr,
            ),
        ]
    }
}

/// True when `ty` denotes a slice `[T]`, possibly behind references.
fn ty_is_slice(ty: Ty<'_>) -> bool {
    matches!(ty.peel_refs().kind(), TyKind::Slice(_))
}

/// Extract the inner type from an `Expr::Array` (the `[T]` notation in
/// `TransmuteWithoutAlign([T], [U])`), then resolve it via `parse_type`.
fn unwrap_array_expr<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
    if let Expr::Array(arr) = expr
        && arr.elems.len() == 1
    {
        return Property::parse_type(tcx, def_id, &arr.elems[0], "TransmuteWithoutAlign");
    }
    Property::parse_type(tcx, def_id, expr, "TransmuteWithoutAlign")
}
