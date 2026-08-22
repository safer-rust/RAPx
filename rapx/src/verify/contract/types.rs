use rustc_middle::ty::Ty;

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

#[derive(Clone, Copy, Debug)]
pub enum NumericUnaryOp {
    Not,
    Neg,
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
    If {
        cond: Box<NumericPredicate<'tcx>>,
        then_expr: Box<ContractExpr<'tcx>>,
        else_expr: Box<ContractExpr<'tcx>>,
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
    ValidTransmute,
    SplitTransmute,
    Unknown,
}

#[derive(Clone, Debug)]
pub enum PropertyArg<'tcx> {
    Ty(Ty<'tcx>),
    Expr(ContractExpr<'tcx>),
    Predicates(Vec<NumericPredicate<'tcx>>),
    Ident(String),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ContractKind {
    Precond,
    Hazard,
    Option_,
}

/// A safety property: either a single predicate (`Leaf`) or a disjunction of
/// alternative predicate groups (`Or`).
///
/// Conjunction (`And`) is deliberately *not* a variant: it is expressed by the
/// surrounding collection — the caller's `requires` list is already a
/// conjunction, and each `Or` group is a conjunction of its members (DNF).
///
/// Splitting `Leaf` from `Or` makes the mutually-exclusive payloads (`args`
/// vs. `groups`) explicit in the type, so a leaf can never carry alternatives
/// and an `Or` can never carry arguments.
#[derive(Clone, Debug)]
pub enum Property<'tcx> {
    Leaf(LeafProperty<'tcx>),
    Or(OrProperty<'tcx>),
}

#[derive(Clone, Debug)]
pub struct LeafProperty<'tcx> {
    pub kind: PropertyKind,
    pub args: Vec<PropertyArg<'tcx>>,
    pub contract_kind: ContractKind,
    /// When set, this property came from an `any(Null(guard), ...)` expansion
    /// and is vacuously true when `guard` is null.
    pub null_guard: Option<PlaceKey>,
    /// When set, this property must hold for every element of this
    /// container (e.g. `Owning(buckets.iter())`).  The target place
    /// in `args` is already stripped of the `IterElements` projection
    /// and refers to a single element slot.
    pub for_each: Option<ContractPlace<'tcx>>,
    /// When set, the display name of the compound `def` this property expanded
    /// from (e.g. `"Deref"`, `"ValidPtr"`), used for user-facing reports so a
    /// macro-expanded contract keeps its original name.
    pub origin_name: Option<String>,
    /// The full call-site arguments of the compound `def` (rendered as source
    /// text), used to display `name(args)` as a single entry.
    pub origin_args: Option<Vec<String>>,
    /// The human-readable meaning of the compound `def`, sourced from its `///`
    /// doc comment.
    pub origin_meaning: Option<String>,
}

#[derive(Clone, Debug)]
pub struct OrProperty<'tcx> {
    /// Alternative property groups.  Each inner `Vec` is a conjunction (all
    /// must hold); at least one group must hold in a disjunction.
    pub groups: Vec<Vec<Box<Property<'tcx>>>>,
    pub contract_kind: ContractKind,
    /// Display name of the compound `def` this property expanded from.
    pub origin_name: Option<String>,
    /// The full call-site arguments of the compound `def` (rendered source).
    pub origin_args: Option<Vec<String>>,
    /// The human-readable meaning of the compound `def`.
    pub origin_meaning: Option<String>,
}

impl<'tcx> Property<'tcx> {
    /// Build a single predicate leaf.
    pub(crate) fn new_leaf(kind: PropertyKind, args: Vec<PropertyArg<'tcx>>) -> Self {
        Self::Leaf(LeafProperty {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            null_guard: None,
            for_each: None,
            origin_name: None,
            origin_args: None,
            origin_meaning: None,
        })
    }

    /// Build a `Property::Or` disjunction from already-expanded DNF groups.
    ///
    /// Each inner `Vec` is one AND-group (all its members must hold); at least
    /// one group must hold for the disjunction to be satisfied.  This is the
    /// single place an `Or` property is constructed so that callers in the
    /// `def`, JSON (`query`), and `any(...)` (`parser`) layers share identical
    /// semantics.
    pub(crate) fn new_or(groups: Vec<Vec<Box<Property<'tcx>>>>) -> Self {
        Self::Or(OrProperty {
            groups,
            contract_kind: ContractKind::Precond,
            origin_name: None,
            origin_args: None,
            origin_meaning: None,
        })
    }

    /// The predicate kind of a leaf property (`None` for an `Or`, which has no
    /// single kind).
    pub fn kind(&self) -> Option<PropertyKind> {
        match self {
            Property::Leaf(l) => Some(l.kind),
            Property::Or(_) => None,
        }
    }

    /// The positional arguments of a leaf property (`Or` has none).
    pub fn args(&self) -> &[PropertyArg<'tcx>] {
        match self {
            Property::Leaf(l) => &l.args,
            Property::Or(_) => &[],
        }
    }

    /// The alternative groups of an `Or` property (`Leaf` has none).
    pub fn groups(&self) -> &[Vec<Box<Property<'tcx>>>] {
        match self {
            Property::Leaf(_) => &[],
            Property::Or(o) => &o.groups,
        }
    }

    pub fn contract_kind(&self) -> ContractKind {
        match self {
            Property::Leaf(l) => l.contract_kind,
            Property::Or(o) => o.contract_kind,
        }
    }

    pub fn null_guard(&self) -> Option<&PlaceKey> {
        match self {
            Property::Leaf(l) => l.null_guard.as_ref(),
            Property::Or(_) => None,
        }
    }

    pub fn for_each(&self) -> Option<&ContractPlace<'tcx>> {
        match self {
            Property::Leaf(l) => l.for_each.as_ref(),
            Property::Or(_) => None,
        }
    }

    pub fn origin_name(&self) -> Option<&str> {
        match self {
            Property::Leaf(l) => l.origin_name.as_deref(),
            Property::Or(o) => o.origin_name.as_deref(),
        }
    }

    /// The full call-site arguments of the compound `def` this property
    /// expanded from (`None` for plain primitives).
    pub fn origin_args(&self) -> Option<&[String]> {
        match self {
            Property::Leaf(l) => l.origin_args.as_deref(),
            Property::Or(o) => o.origin_args.as_deref(),
        }
    }

    /// The human-readable meaning of the compound `def`.
    pub fn origin_meaning(&self) -> Option<&str> {
        match self {
            Property::Leaf(l) => l.origin_meaning.as_deref(),
            Property::Or(o) => o.origin_meaning.as_deref(),
        }
    }

    pub fn is_or(&self) -> bool {
        matches!(self, Property::Or(_))
    }

    /// The first `Ty` argument.
    pub fn ty_arg(&self) -> Option<Ty<'tcx>> {
        self.args().iter().find_map(|a| match a {
            PropertyArg::Ty(ty) => Some(*ty),
            _ => None,
        })
    }

    /// The first `Expr` argument, typically a count/length expression.
    pub fn count_expr(&self) -> Option<&ContractExpr<'tcx>> {
        self.args().iter().find_map(|a| match a {
            PropertyArg::Expr(e) => Some(e),
            _ => None,
        })
    }

    /// Apply contract kind metadata from a JSON entry or attribute.
    pub fn apply_kind(&mut self, kind: Option<&str>) {
        let target = match self {
            Property::Leaf(l) => &mut l.contract_kind,
            Property::Or(o) => &mut o.contract_kind,
        };
        match kind {
            Some("hazard") => *target = ContractKind::Hazard,
            Some("option") => *target = ContractKind::Option_,
            _ => {}
        }
    }

    /// Tag a property (leaf or `Or`) with the display name, full call-site
    /// arguments, and meaning of the compound `def` it expanded from.
    pub(crate) fn set_origin(&mut self, name: String, args: Vec<String>, meaning: Option<String>) {
        match self {
            Property::Leaf(l) => {
                l.origin_name = Some(name);
                l.origin_args = Some(args);
                l.origin_meaning = meaning;
            }
            Property::Or(o) => {
                o.origin_name = Some(name);
                o.origin_args = Some(args);
                o.origin_meaning = meaning;
            }
        }
    }

    /// Attach a `for_each` container to a leaf property.
    pub(crate) fn set_for_each(&mut self, place: Option<ContractPlace<'tcx>>) {
        if let Property::Leaf(l) = self {
            l.for_each = place;
        }
    }

    /// Override the contract kind (e.g. `Alias` → `Hazard`).
    pub(crate) fn set_contract_kind(&mut self, k: ContractKind) {
        match self {
            Property::Leaf(l) => l.contract_kind = k,
            Property::Or(o) => o.contract_kind = k,
        }
    }
}
