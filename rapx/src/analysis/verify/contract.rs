use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp as MirBinOp;
use rustc_middle::ty::{Ty, TyCtxt};
use safety_parser::syn::{BinOp as SynBinOp, Expr, Lit, UnOp};
use serde::{Deserialize, Serialize};

use super::helpers::{
    access_ident_recursive, match_ty_with_ident, parse_expr_into_local_and_ty,
    parse_expr_into_number,
};

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct ContractEntry {
    pub tag: String,
    pub args: Vec<String>,
}

#[derive(Clone, Debug)]
pub enum PlaceBase {
    Return,
    Arg(usize),
    Local(usize),
}

#[derive(Clone, Debug)]
pub enum ContractProjection<'tcx> {
    Field { index: usize, ty: Option<Ty<'tcx>> },
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
            .map(|projection| match projection {
                ContractProjection::Field { index, .. } => *index,
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
    SizeOf(Ty<'tcx>),
    AlignOf(Ty<'tcx>),
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

#[derive(Clone, Debug)]
pub enum PropertyContract<'tcx> {
    Align(Ty<'tcx>),
    Size(),
    NoPadding,
    NonNull,
    Allocated(Ty<'tcx>, ContractExpr<'tcx>),
    InBound(Ty<'tcx>, ContractExpr<'tcx>),
    NonOverlap,
    ValidNum(Vec<NumericPredicate<'tcx>>),
    ValidString,
    ValidCStr,
    Init(Ty<'tcx>, ContractExpr<'tcx>),
    Unwrap,
    Typed(Ty<'tcx>),
    Owning,
    Alias,
    Alive,
    Pinned,
    NonVolatile,
    Opened,
    Trait,
    Unreachable,
    ValidPtr(Ty<'tcx>, ContractExpr<'tcx>),
    Deref,
    Ptr2Ref,
    Layout,
    Unknown,
}

impl<'tcx> PropertyContract<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str, exprs: &Vec<Expr>) -> Self {
        match name {
            "Align" => {
                Self::check_arg_length(exprs.len(), 2, "Align");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Align");
                Self::Align(ty)
            }
            "Size" => Self::Size(),
            "NoPadding" => Self::NoPadding,
            "NonNull" => Self::NonNull,
            "Allocated" => {
                Self::check_arg_length(exprs.len(), 3, "Allocated");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Allocated");
                let length = Self::parse_contract_expr(tcx, def_id, &exprs[2], "Allocated");
                Self::Allocated(ty, length)
            }
            "InBound" | "InBounded" => match exprs.as_slice() {
                [_target, ty_expr, len_expr] => {
                    let ty = Self::parse_type(tcx, def_id, ty_expr, "InBound");
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "InBound");
                    Self::InBound(ty, length)
                }
                [target, len_expr] => {
                    let Some(ty) = Self::parse_target_type(tcx, def_id, target) else {
                        return Self::Unknown;
                    };
                    let length = Self::parse_contract_expr(tcx, def_id, len_expr, "InBound");
                    Self::InBound(ty, length)
                }
                _ => {
                    Self::check_arg_length(exprs.len(), 3, "InBound");
                    Self::Unknown
                }
            },
            "NonOverlap" => Self::NonOverlap,
            "ValidNum" => {
                let predicates = Self::parse_valid_num(tcx, def_id, exprs);
                if predicates.is_empty() {
                    Self::Unknown
                } else {
                    Self::ValidNum(predicates)
                }
            }
            "ValidString" => Self::ValidString,
            "ValidCStr" => Self::ValidCStr,
            "Init" => {
                Self::check_arg_length(exprs.len(), 3, "Init");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Init");
                let length = Self::parse_contract_expr(tcx, def_id, &exprs[2], "Init");
                Self::Init(ty, length)
            }
            "Unwrap" => Self::Unwrap,
            "Typed" => {
                Self::check_arg_length(exprs.len(), 2, "Typed");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "Typed");
                Self::Typed(ty)
            }
            "Owning" => Self::Owning,
            "Alias" => Self::Alias,
            "Alive" => Self::Alive,
            "Pinned" => Self::Pinned,
            "NonVolatile" => Self::NonVolatile,
            "Opened" => Self::Opened,
            "Trait" => Self::Trait,
            "Unreachable" => Self::Unreachable,
            "ValidPtr" => {
                Self::check_arg_length(exprs.len(), 3, "ValidPtr");
                let ty = Self::parse_type(tcx, def_id, &exprs[1], "ValidPtr");
                let length = Self::parse_contract_expr(tcx, def_id, &exprs[2], "ValidPtr");
                Self::ValidPtr(ty, length)
            }
            "Deref" => Self::Deref,
            "Ptr2Ref" | "ValidPtr2Ref" => Self::Ptr2Ref,
            "Layout" => Self::Layout,
            _ => Self::Unknown,
        }
    }

    pub fn new_partial_order(lhs: usize, rhs: usize, op: MirBinOp) -> Self {
        if let Some(predicate) = NumericPredicate::from_mir_locals(lhs, rhs, op) {
            Self::ValidNum(vec![predicate])
        } else {
            Self::Unknown
        }
    }

    pub fn new_obj_boundary(ty: Ty<'tcx>, len: ContractExpr<'tcx>) -> Self {
        Self::InBound(ty, len)
    }

    fn check_arg_length(expr_len: usize, required_len: usize, sp: &str) -> bool {
        if expr_len != required_len {
            panic!("Wrong args length for {:?} Tag!", sp);
        }
        true
    }

    fn parse_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr, sp: &str) -> Ty<'tcx> {
        let ty_ident_full = access_ident_recursive(expr);
        if ty_ident_full.is_none() {
            rap_error!("Incorrect expression for the type of {:?} Tag!", sp);
        }
        let ty_ident = ty_ident_full.unwrap().0;
        let ty = match_ty_with_ident(tcx, def_id, ty_ident);
        if ty.is_none() {
            rap_error!("Cannot get type in {:?} Tag!", sp);
        }
        ty.unwrap()
    }

    fn parse_target_type(tcx: TyCtxt<'tcx>, def_id: DefId, expr: &Expr) -> Option<Ty<'tcx>> {
        parse_expr_into_local_and_ty(tcx, def_id, expr).map(|(_, _, ty)| ty)
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

    fn parse_contract_place(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        expr: &Expr,
    ) -> Option<ContractPlace<'tcx>> {
        if let Some((base, fields, _ty)) = parse_expr_into_local_and_ty(tcx, def_id, expr) {
            return Some(ContractPlace::local(base, fields));
        }
        Self::parse_arg_place(expr)
    }

    fn parse_arg_place(expr: &Expr) -> Option<ContractPlace<'tcx>> {
        if let Expr::Path(expr_path) = expr {
            if let Some(ident) = expr_path.path.get_ident() {
                let s = ident.to_string();
                if let Some(num_str) = s.strip_prefix("Arg_") {
                    if let Ok(idx) = num_str.parse::<usize>() {
                        return Some(ContractPlace::arg(idx));
                    }
                }
            }
        }
        None
    }

    fn parse_valid_num(
        tcx: TyCtxt<'tcx>,
        def_id: DefId,
        exprs: &Vec<Expr>,
    ) -> Vec<NumericPredicate<'tcx>> {
        match exprs.as_slice() {
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
                if lower_inclusive { RelOp::Le } else { RelOp::Lt },
                value_expr.clone(),
            ),
            NumericPredicate::new(
                value_expr,
                if upper_inclusive { RelOp::Le } else { RelOp::Lt },
                upper_expr,
            ),
        ]
    }
}
