use rustc_hir::def_id::DefId;
use rustc_middle::mir::BinOp as MirBinOp;
use rustc_middle::ty::{Ty, TyCtxt};
use safety_parser::syn::{BinOp as SynBinOp, UnOp};

use crate::verify::def_use::PlaceKey;

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
    IterElements,
}

#[derive(Clone, Debug)]
pub struct ContractPlace<'tcx> {
    pub base: PlaceBase,
    pub projections: Vec<ContractProjection<'tcx>>,
}

pub fn resolve_field_name(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    index: &usize,
    struct_def_id: Option<rustc_span::def_id::DefId>,
) -> String {
    if let Some(struct_def_id) = struct_def_id
        && let rustc_middle::ty::TyKind::Adt(adt_def, _) =
            tcx.type_of(struct_def_id).skip_binder().kind()
    {
        let variant = adt_def.non_enum_variant();
        let field_idx = rustc_abi::FieldIdx::from_usize(*index);
        if field_idx.as_usize() < variant.fields.len() {
            return variant.fields[field_idx].name.to_string();
        }
    }
    index.to_string()
}

impl<'tcx> ContractPlace<'tcx> {
    pub fn display_user_friendly(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        let has_projections = !self.projections.is_empty();

        let base_str = match self.base {
            PlaceBase::Return => {
                if has_projections {
                    String::new()
                } else {
                    "return".to_string()
                }
            }
            PlaceBase::Arg(idx) => {
                if let Some(fn_def_id) = fn_def_id
                    && tcx.is_mir_available(fn_def_id)
                {
                    let mir_local = idx + 1;
                    let body = tcx.optimized_mir(fn_def_id);
                    if mir_local < body.local_decls.len() {
                        let local = rustc_middle::mir::Local::from_usize(mir_local);
                        let span = body.local_decls[local].source_info.span;
                        if let Ok(snippet) = tcx.sess.source_map().span_to_snippet(span)
                            && !snippet.is_empty()
                        {
                            return snippet;
                        }
                    }
                }
                format!("arg{}", idx)
            }
            PlaceBase::Local(n) => {
                if n == 0 {
                    "return".to_string()
                } else if let Some(fn_def_id) = fn_def_id
                    && tcx.is_mir_available(fn_def_id)
                {
                    let body = tcx.optimized_mir(fn_def_id);
                    if n < body.local_decls.len() {
                        let local = rustc_middle::mir::Local::from_usize(n);
                        let span = body.local_decls[local].source_info.span;
                        if let Ok(snippet) = tcx.sess.source_map().span_to_snippet(span) {
                            snippet
                        } else {
                            format!("arg{}", n)
                        }
                    } else {
                        format!("arg{}", n)
                    }
                } else {
                    format!("arg{}", n)
                }
            }
        };

        let base_str = base_str
            .strip_prefix("&mut ")
            .unwrap_or(&base_str)
            .to_string();
        let base_str = base_str.strip_prefix("&").unwrap_or(&base_str).to_string();

        if self.projections.is_empty() {
            return base_str;
        }

        let mut result = base_str;
        for projection in &self.projections {
            match projection {
                ContractProjection::Field { index, ty: _ } => {
                    let field_name = resolve_field_name(tcx, index, struct_def_id);
                    if result.is_empty() {
                        result = field_name;
                    } else {
                        result.push_str(&format!(".{}", field_name));
                    }
                }
                ContractProjection::Downcast { .. } => {
                    result.push_str(".unwrap_some()");
                }
                ContractProjection::IterElements => {
                    result.push_str(".iter()");
                }
            }
        }
        result
    }

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
    pub(crate) fn from_syn(op: &SynBinOp) -> Option<Self> {
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
    pub(crate) fn from_syn(op: &UnOp) -> Option<Self> {
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
    Min {
        a: Box<ContractExpr<'tcx>>,
        b: Box<ContractExpr<'tcx>>,
    },
    Max {
        a: Box<ContractExpr<'tcx>>,
        b: Box<ContractExpr<'tcx>>,
    },
    Unknown,
}

impl<'tcx> ContractExpr<'tcx> {
    pub fn new_value(value: usize) -> Self {
        Self::Const(value as u128)
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

    pub(crate) fn from_syn(op: &SynBinOp) -> Option<Self> {
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

    pub fn display_user_friendly(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        let op_str = match self.op {
            RelOp::Eq => "==",
            RelOp::Ne => "!=",
            RelOp::Lt => "<",
            RelOp::Le => "<=",
            RelOp::Gt => ">",
            RelOp::Ge => ">=",
        };
        format!(
            "{} {} {}",
            display_expr_user_friendly(&self.lhs, tcx, struct_def_id, fn_def_id),
            op_str,
            display_expr_user_friendly(&self.rhs, tcx, struct_def_id, fn_def_id),
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
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
    Deref,
    Ptr2Ref,
    Layout,
    ValidTransmute,
    SplitTransmute,
    Unknown,
    /// Logical OR over alternative property groups.
    /// Each inner group is a conjunction (AND); at least one group must hold.
    Or,
}

#[derive(Clone, Debug)]
pub enum PropertyArg<'tcx> {
    Place(ContractPlace<'tcx>),
    Ty(Ty<'tcx>),
    Expr(ContractExpr<'tcx>),
    Predicates(Vec<NumericPredicate<'tcx>>),
    Ident(String),
}

pub fn display_expr_user_friendly<'tcx>(
    expr: &ContractExpr<'tcx>,
    tcx: TyCtxt<'tcx>,
    struct_def_id: Option<DefId>,
    fn_def_id: Option<DefId>,
) -> String {
    match expr {
        ContractExpr::Const(n) => format!("{n}"),
        ContractExpr::ConstParam { name, .. } => name.clone(),
        ContractExpr::Place(p) => p.display_user_friendly(tcx, struct_def_id, fn_def_id),
        ContractExpr::SizeOf(ty) => format!("size_of({ty})"),
        ContractExpr::AlignOf(ty) => format!("align_of({ty})"),
        ContractExpr::Len(e) => {
            format!(
                "len({})",
                display_expr_user_friendly(e, tcx, struct_def_id, fn_def_id)
            )
        }
        ContractExpr::IndexAccess { slice, index } => {
            format!(
                "index_access({}, {})",
                display_expr_user_friendly(slice, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(index, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Binary { op, lhs, rhs } => {
            let op_str = match op {
                NumericOp::Add => "+",
                NumericOp::Sub => "-",
                NumericOp::Mul => "*",
                NumericOp::Div => "/",
                NumericOp::Rem => "%",
                NumericOp::BitAnd => "&",
                NumericOp::BitOr => "|",
                NumericOp::BitXor => "^",
            };
            format!(
                "{} {} {}",
                display_expr_user_friendly(lhs, tcx, struct_def_id, fn_def_id),
                op_str,
                display_expr_user_friendly(rhs, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Unary { op, expr } => {
            let op_str = match op {
                NumericUnaryOp::Not => "!",
                NumericUnaryOp::Neg => "-",
            };
            format!(
                "{}{}",
                op_str,
                display_expr_user_friendly(expr, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Min { a, b } => {
            format!(
                "min({}, {})",
                display_expr_user_friendly(a, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(b, tcx, struct_def_id, fn_def_id),
            )
        }
        ContractExpr::Max { a, b } => {
            format!(
                "max({}, {})",
                display_expr_user_friendly(a, tcx, struct_def_id, fn_def_id),
                display_expr_user_friendly(b, tcx, struct_def_id, fn_def_id),
            )
        }
        _ => format!("{:?}", expr),
    }
}

impl<'tcx> PropertyArg<'tcx> {
    pub fn display_for_report(
        &self,
        tcx: TyCtxt<'tcx>,
        struct_def_id: Option<DefId>,
        fn_def_id: Option<DefId>,
    ) -> String {
        match self {
            PropertyArg::Place(place) => place.display_user_friendly(tcx, struct_def_id, fn_def_id),
            PropertyArg::Ty(ty) => format!("{}", ty),
            PropertyArg::Expr(expr) => {
                display_expr_user_friendly(expr, tcx, struct_def_id, fn_def_id)
            }
            PropertyArg::Predicates(preds) => {
                let p: Vec<_> = preds
                    .iter()
                    .map(|pred| pred.display_user_friendly(tcx, struct_def_id, fn_def_id))
                    .collect();
                p.join(" && ")
            }
            PropertyArg::Ident(s) => s.clone(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContractKind {
    Precond,
    Hazard,
    Option_,
}

#[derive(Clone, Debug)]
pub struct Property<'tcx> {
    pub kind: PropertyKind,
    pub args: Vec<PropertyArg<'tcx>>,
    pub contract_kind: ContractKind,
    /// When set, this property came from an `any(Null(guard), ...)` expansion
    /// and is vacuously true when `guard` is null.
    pub null_guard: Option<PlaceKey>,
    /// For `PropertyKind::Or`: alternative property groups.
    /// Each inner `Vec` is a conjunction (all must hold); at least one group
    /// must hold in a disjunction.
    pub or_alternatives: Vec<Vec<Box<Property<'tcx>>>>,
    /// When set, this property must hold for every element of this
    /// container (e.g. `Owning(buckets.iter())`).  The target place
    /// in `args` is already stripped of the `IterElements` projection
    /// and refers to a single element slot.
    pub for_each: Option<ContractPlace<'tcx>>,
}

impl PropertyKind {
    /// True when this property is a primitive — directly SMT-checkable without
    /// prior decomposition into sub-properties.
    pub fn is_primitive(&self) -> bool {
        !matches!(self, Self::Deref | Self::Ptr2Ref | Self::Layout)
    }

    /// Primitive sub-properties a compound property decomposes into, or `None`
    /// when this is already a primitive.
    pub fn primitive_components(&self) -> Option<&'static [PropertyKind]> {
        match self {
            Self::Deref => Some(&[PropertyKind::Allocated, PropertyKind::InBound]),
            Self::Ptr2Ref => Some(&[PropertyKind::Init, PropertyKind::Align, PropertyKind::Alias]),
            Self::Layout => Some(&[PropertyKind::Allocated]),
            _ => None,
        }
    }

    /// Whether `self` implies `required` — used for struct-invariant
    /// resolution to avoid re-checking a property already guaranteed by
    /// a stronger declared invariant.
    ///
    /// - Init ⇒ Typed
    /// - InBound ⇒ Allocated
    /// - ValidPtr ⇒ Allocated, InBound
    /// - Compound SPs ⇒ each of their primitive components
    pub fn kind_implies(&self, required: &PropertyKind) -> bool {
        if self == required {
            return true;
        }
        if matches!(self, PropertyKind::Init) && matches!(required, PropertyKind::Typed) {
            return true;
        }
        if matches!(self, PropertyKind::InBound) && matches!(required, PropertyKind::Allocated) {
            return true;
        }
        if matches!(self, PropertyKind::ValidPtr)
            && matches!(required, PropertyKind::Allocated | PropertyKind::InBound)
        {
            return true;
        }
        self.primitive_components()
            .is_some_and(|primitives| primitives.contains(required))
    }
}

impl<'tcx> Property<'tcx> {
    /// The first argument, which is conventionally the target place.
    pub fn target_arg(&self) -> Option<&PropertyArg<'tcx>> {
        self.args.first()
    }

    /// The first `Ty` argument.
    pub fn ty_arg(&self) -> Option<Ty<'tcx>> {
        self.args.iter().find_map(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        })
    }

    /// The first `Expr` argument, typically a count/length expression.
    pub fn count_expr(&self) -> Option<&ContractExpr<'tcx>> {
        self.args.iter().find_map(|a| match a {
            PropertyArg::Expr(e) => Some(e),
            _ => None,
        })
    }

    /// Apply contract kind metadata from a JSON entry or attribute.
    pub fn apply_kind(&mut self, kind: Option<&str>) {
        match kind {
            Some("hazard") => self.contract_kind = ContractKind::Hazard,
            Some("option") => self.contract_kind = ContractKind::Option_,
            _ => {}
        }
    }
}

/// Reuse a property's arg structure while replacing its kind.
/// Clears `null_guard` and `or_alternatives` because primitives are plain.
pub fn with_kind<'tcx>(property: &Property<'tcx>, kind: PropertyKind) -> Property<'tcx> {
    Property {
        kind,
        args: property.args.clone(),
        contract_kind: property.contract_kind,
        null_guard: None,
        or_alternatives: Vec::new(),
        for_each: property.for_each.clone(),
    }
}
