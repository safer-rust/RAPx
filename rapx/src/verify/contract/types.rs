//! The contract IR: places, expressions, predicates, and the property model.
//!
//! `Property` is a DNF form (only `Atom` and `Or`; conjunction is a list), with
//! a `PropertyKind` vocabulary of safety tags. All contract front-ends
//! (attributes, JSON, compound-property macros, pest DSL) produce this IR.

use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Local, ty::{Region, Ty}};

/// The `Ident` a contract uses for the `'static` lifetime. `'static` is a Rust
/// keyword, so after the leading `'` is stripped it cannot be a plain ident
/// token; `attr::strip_lifetime_ticks` maps it to this name.
pub(crate) const STATIC_LIFETIME_IDENT: &str = "static_lifetime";

/// Whether a contract lifetime ident names the `'static` lifetime, accepting
/// both the plain `"static"` spelling and [`STATIC_LIFETIME_IDENT`] (the
/// keyword-stripped form produced by `attr::strip_lifetime_ticks`).
pub(crate) fn is_static_lifetime_ident(name: &str) -> bool {
    name == "static" || name == STATIC_LIFETIME_IDENT
}

/// The root of a contract place: a function's return value, an argument, or a
/// raw MIR local.  `Return` ⇔ `Local(0)`; `Arg(n)` ⇔ `Local(n + 1)`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PlaceBase {
    /// The function's return value.
    Return,
    /// The n-th parameter (0-indexed).
    Arg(usize),
    /// A MIR local (`0` is the return place, `1..` are the parameters).
    Local(usize),
}

impl PlaceBase {
    /// The MIR local this base denotes (`Return` ⇔ `Local(0)`, `Arg(n)` ⇔ `Local(n + 1)`).
    pub(crate) fn to_local(&self) -> Local {
        match self {
            PlaceBase::Return => Local::from_usize(0),
            PlaceBase::Arg(n) => Local::from_usize(*n + 1),
            PlaceBase::Local(n) => Local::from_usize(*n),
        }
    }

    /// Like [`to_local`](Self::to_local), but `None` for `Return`.  Callers that
    /// need a concrete `Arg`/`Local` index (e.g. resolving a container's local)
    /// use this instead of hand-copying the `Arg`/`Local` arm plus an `_ => None`.
    pub(crate) fn try_to_local(&self) -> Option<Local> {
        match self {
            PlaceBase::Return => None,
            PlaceBase::Arg(n) => Some(Local::from_usize(*n + 1)),
            PlaceBase::Local(n) => Some(Local::from_usize(*n)),
        }
    }
}

/// A step into a place, from the base down to the value a contract talks
/// about (written as `.field`, `.unwrap_some()`, or `.iter()` in the DSL).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ContractProjection<'tcx> {
    /// Select a struct/tuple field.
    Field { index: usize, ty: Option<Ty<'tcx>> },
    /// Unwrap the `Some` variant of an enum.
    Downcast { variant_index: usize },
    /// Iterate over the elements of a container.
    ForEach,
}

/// A place a contract refers to: a [`PlaceBase`] root plus a sequence of
/// [`ContractProjection`] steps into it (e.g. `self.next.value`, `head.iter()`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ContractPlace<'tcx> {
    /// The root: return value, an argument, or a MIR local.
    pub base: PlaceBase,
    /// Field / `Some`-unwrap / element steps from the base down.
    pub projections: Vec<ContractProjection<'tcx>>,
}

impl<'tcx> ContractPlace<'tcx> {
    pub(crate) fn local(base: usize, fields: Vec<(usize, Ty<'tcx>)>) -> Self {
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

    pub(crate) fn arg(index: usize) -> Self {
        Self {
            base: PlaceBase::Arg(index),
            projections: Vec::new(),
        }
    }

    pub(crate) fn local_base(&self) -> Option<usize> {
        match self.base {
            PlaceBase::Return => Some(0),
            PlaceBase::Local(local) => Some(local),
            PlaceBase::Arg(_) => None,
        }
    }

    /// The field indices when this place is a pure `Field` chain (no `Downcast`
    /// / `ForEach` steps), otherwise `None`.  Shared by the exec- and
    /// checker-side `Len` evaluators.
    pub(crate) fn plain_field_path(&self) -> Option<Vec<usize>> {
        let mut path = Vec::new();
        for proj in &self.projections {
            match proj {
                ContractProjection::Field { index, .. } => path.push(*index),
                _ => return None,
            }
        }
        Some(path)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NumericBinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Min,
    Max,
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NumericUnaryOp {
    Not,
    Neg,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ContractExpr<'tcx> {
    Place(ContractPlace<'tcx>),
    Const(u128),
    ConstParam {
        index: u32,
        name: String,
    },
    SizeOf(Ty<'tcx>),
    AlignOf(Ty<'tcx>),
    Len(Box<ContractExpr<'tcx>>, Option<DefId>),
    MethodCall {
        receiver: Box<ContractExpr<'tcx>>,
        method: DefId,
        args: Vec<ContractExpr<'tcx>>,
    },
    IsEmpty(Box<ContractExpr<'tcx>>, Option<DefId>),
    IndexAccess {
        slice: Box<ContractExpr<'tcx>>,
        index: Box<ContractExpr<'tcx>>,
    },
    Binary {
        op: NumericBinOp,
        lhs: Box<ContractExpr<'tcx>>,
        rhs: Box<ContractExpr<'tcx>>,
    },
    Unary {
        op: NumericUnaryOp,
        expr: Box<ContractExpr<'tcx>>,
    },
    If {
        cond: Box<NumericPredicate<'tcx>>,
        then_expr: Box<ContractExpr<'tcx>>,
        else_expr: Box<ContractExpr<'tcx>>,
    },
    Unknown,
}

impl<'tcx> ContractExpr<'tcx> {
    pub(crate) fn new_value(value: usize) -> Self {
        Self::Const(value as u128)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum RelOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct NumericPredicate<'tcx> {
    pub lhs: ContractExpr<'tcx>,
    pub op: RelOp,
    pub rhs: ContractExpr<'tcx>,
}

impl<'tcx> NumericPredicate<'tcx> {
    pub(crate) fn new(lhs: ContractExpr<'tcx>, op: RelOp, rhs: ContractExpr<'tcx>) -> Self {
        Self { lhs, op, rhs }
    }
}

/// The vocabulary of safety predicates a contract can assert.
///
/// Each kind's meaning and accepted argument shapes are declared in
/// `spec::SPECS` (the single source of truth); this enum only names the kinds.
/// A few kinds carry extra semantics: `Null` is the guard branch of
/// `any(Null(p), …)` (proved when `p` is null), and `Owning` asserts
/// `ownership(*p) = none` (psp IV.1 in primitive-sp.md).  The kinds `Unwrap`,
/// `Pinned`, `Opened` and `Unreachable` are declared but not yet verified (the
/// checker returns `Unknown`), and `NonVolatile` is assumed satisfied (the VM
/// does not model volatile access).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PropertyKind {
    Align,
    Size,
    NoPadding,
    NonNull,
    Allocated,
    InBound,
    SliceOffset,
    NonOverlap,
    ValidNum,
    ValidString,
    ValidCStr,
    Init,
    Unwrap,
    Typed,
    Owning,
    Alias,
    Alive,
    Pinned,
    NonVolatile,
    Opened,
    Null,
    Trait,
    Unreachable,
    ValidTransmute,
    SplitTransmute,
    ContainNoType,
    NoRawPtr,
    NoInternalMut,
    UniInternalMut,
    AtomicUpdate,
    RefSend,
    Unknown,
}

/// One argument of a predicate call — what the property is applied to.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum PropertyArg<'tcx> {
    /// A type (e.g. `T` in `Align(ptr, T)`).
    Ty(Ty<'tcx>),
    /// A value expression (e.g. `buf`, `n`).
    Expr(ContractExpr<'tcx>),
    /// An interval of comparisons, used by `ValidNum`.
    Predicates(Vec<NumericPredicate<'tcx>>),
    /// A name: lifetime, allocator, trait (e.g. `Copy`), or `sized`/`unsized`.
    Ident(String),
    /// A resolved lifetime region (e.g. `'a` in `Alive(p, 'a)`), bound against
    /// the item that declares the lifetime (a struct for its invariants).
    Region(Region<'tcx>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ContractKind {
    Precond,
    Hazard,
    Option_,
    Postcond,
}

/// Display metadata for a property expanded from a compound property
/// (`pred!`-style macro).  Purely presentational: it lets reports render a
/// macro-expanded contract as a single `name(args)` entry with its doc-derived
/// meaning, instead of the underlying primitives it expanded into.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ContractOrigin {
    pub name: String,
    pub args: Vec<String>,
    pub meaning: Option<String>,
}

/// A safety property: a boolean formula over atomic predicates.
///
/// The formula is a tree of three node kinds — `Atom` (a single predicate),
/// `And` (conjunction: all members hold), and `Or` (disjunction: at least one
/// member holds).  `Box` breaks the recursion; the top level of a contract is
/// simply a `Vec<Property>` (an implicit conjunction of requirements).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Property<'tcx> {
    Atom(AtomProperty<'tcx>),
    And(AndProperty<'tcx>),
    Or(OrProperty<'tcx>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AtomProperty<'tcx> {
    pub kind: PropertyKind,
    pub args: Vec<PropertyArg<'tcx>>,
    pub contract_kind: ContractKind,
    /// When set, this property must hold for every element of this
    /// container (e.g. `Owning(buckets.iter())`).  The target place
    /// in `args` is already stripped of the `ForEach` projection
    /// and refers to a single element slot.
    pub for_each: Option<ContractPlace<'tcx>>,
    /// Display metadata when this property was expanded from a compound property.
    pub origin: Option<ContractOrigin>,
}

/// A conjunction: every [`conjuncts`](Self::conjuncts) member must hold.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct AndProperty<'tcx> {
    pub conjuncts: Vec<Property<'tcx>>,
    pub contract_kind: ContractKind,
    /// Display metadata when this property was expanded from a compound property.
    pub origin: Option<ContractOrigin>,
}

/// A disjunction: at least one [`disjuncts`](Self::disjuncts) member must hold.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct OrProperty<'tcx> {
    pub disjuncts: Vec<Property<'tcx>>,
    pub contract_kind: ContractKind,
    /// Display metadata when this property was expanded from a compound property.
    pub origin: Option<ContractOrigin>,
}

impl<'tcx> Property<'tcx> {
    /// Build a single atomic predicate.
    pub(crate) fn new_atom(kind: PropertyKind, args: Vec<PropertyArg<'tcx>>) -> Self {
        Self::Atom(AtomProperty {
            kind,
            args,
            contract_kind: ContractKind::Precond,
            for_each: None,
            origin: None,
        })
    }

    /// Build a conjunction (`And`) of already-expanded conjuncts.
    pub(crate) fn new_and(conjuncts: Vec<Property<'tcx>>) -> Self {
        Self::And(AndProperty {
            conjuncts,
            contract_kind: ContractKind::Precond,
            origin: None,
        })
    }

    /// Build a disjunction (`Or`) of already-expanded disjuncts.
    pub(crate) fn new_or(disjuncts: Vec<Property<'tcx>>) -> Self {
        Self::Or(OrProperty {
            disjuncts,
            contract_kind: ContractKind::Precond,
            origin: None,
        })
    }

    /// Normalize a list of conjuncts into a single `Property`: a singleton is
    /// returned as-is, otherwise the list is wrapped in an `And` node.
    pub(crate) fn conjunction(conjuncts: Vec<Property<'tcx>>) -> Self {
        if conjuncts.len() == 1 {
            conjuncts.into_iter().next().unwrap()
        } else {
            Self::new_and(conjuncts)
        }
    }

    /// The predicate kind of an atom (`None` for `And`/`Or`, which have no
    /// single kind).
    pub(crate) fn kind(&self) -> Option<PropertyKind> {
        match self {
            Property::Atom(a) => Some(a.kind),
            Property::And(_) | Property::Or(_) => None,
        }
    }

    /// The positional arguments of an atom (`And`/`Or` have none).
    pub(crate) fn args(&self) -> &[PropertyArg<'tcx>] {
        match self {
            Property::Atom(a) => &a.args,
            Property::And(_) | Property::Or(_) => &[],
        }
    }

    pub(crate) fn ty_arg(&self, index: usize) -> Option<Ty<'tcx>> {
        match self.args().get(index) {
            Some(PropertyArg::Ty(ty)) => Some(*ty),
            _ => None,
        }
    }

    /// The `ContractPlace` this atom's first argument refers to, when the
    /// first argument is a place (or an index access over one, e.g. `slice[i]`).
    pub(crate) fn target_place(&self) -> Option<&ContractPlace<'tcx>> {
        match self.args().first()? {
            PropertyArg::Expr(ContractExpr::Place(cp)) => Some(cp),
            PropertyArg::Expr(ContractExpr::IndexAccess { slice, .. }) => match slice.as_ref() {
                ContractExpr::Place(cp) => Some(cp),
                _ => None,
            },
            _ => None,
        }
    }

    /// The conjuncts of an `And` property (`Atom`/`Or` have none).
    pub(crate) fn conjuncts(&self) -> &[Property<'tcx>] {
        match self {
            Property::And(a) => &a.conjuncts,
            Property::Atom(_) | Property::Or(_) => &[],
        }
    }

    /// The disjuncts of an `Or` property (`Atom`/`And` have none).
    pub(crate) fn disjuncts(&self) -> &[Property<'tcx>] {
        match self {
            Property::Or(o) => &o.disjuncts,
            Property::Atom(_) | Property::And(_) => &[],
        }
    }

    pub(crate) fn contract_kind(&self) -> ContractKind {
        match self {
            Property::Atom(a) => a.contract_kind,
            Property::And(a) => a.contract_kind,
            Property::Or(o) => o.contract_kind,
        }
    }

    /// Defer `ContractKind::Hazard` atoms to the use point, returning `None`
    /// when only hazards remain.  A hazard (e.g. `Alias`) is *marked* in a
    /// struct invariant to document the exclusive-ownership intent, but it is
    /// not a standing fact: it is enforced at the operation that consumes the
    /// pointer (whose `requires` names it), not verified at construction nor
    /// carried as an entry fact (where `assert_contract_fact` would treat
    /// `Alias` as an *accepted* structural-alias hazard via `alias_hazard_allocs`).
    pub(crate) fn strip_hazards(&self) -> Option<Property<'tcx>> {
        match self {
            Property::Atom(atom) if atom.contract_kind == ContractKind::Hazard => None,
            Property::Atom(_) => Some(self.clone()),
            Property::And(and) => {
                let conjuncts: Vec<Property<'tcx>> = and
                    .conjuncts
                    .iter()
                    .filter_map(Property::strip_hazards)
                    .collect();
                match conjuncts.len() {
                    0 => None,
                    1 => conjuncts.into_iter().next(),
                    _ => {
                        let mut stripped = and.clone();
                        stripped.conjuncts = conjuncts;
                        Some(Property::And(stripped))
                    }
                }
            }
            Property::Or(or) => {
                let disjuncts: Vec<Property<'tcx>> = or
                    .disjuncts
                    .iter()
                    .filter_map(Property::strip_hazards)
                    .collect();
                match disjuncts.len() {
                    0 => None,
                    1 => disjuncts.into_iter().next(),
                    _ => {
                        let mut stripped = or.clone();
                        stripped.disjuncts = disjuncts;
                        Some(Property::Or(stripped))
                    }
                }
            }
        }
    }

    pub(crate) fn for_each(&self) -> Option<&ContractPlace<'tcx>> {
        match self {
            Property::Atom(a) => a.for_each.as_ref(),
            Property::And(_) | Property::Or(_) => None,
        }
    }

    /// Display metadata when this property was expanded from a compound property.
    pub(crate) fn origin(&self) -> Option<&ContractOrigin> {
        match self {
            Property::Atom(a) => a.origin.as_ref(),
            Property::And(a) => a.origin.as_ref(),
            Property::Or(o) => o.origin.as_ref(),
        }
    }

    pub(crate) fn is_or(&self) -> bool {
        matches!(self, Property::Or(_))
    }

    pub(crate) fn is_and(&self) -> bool {
        matches!(self, Property::And(_))
    }

    /// Apply contract kind metadata from a JSON entry or attribute.
    pub(crate) fn apply_kind(&mut self, kind: Option<&str>) {
        let target = match self {
            Property::Atom(a) => &mut a.contract_kind,
            Property::And(a) => &mut a.contract_kind,
            Property::Or(o) => &mut o.contract_kind,
        };
        match kind {
            Some("hazard") => *target = ContractKind::Hazard,
            Some("option") => *target = ContractKind::Option_,
            Some("postcond") => *target = ContractKind::Postcond,
            _ => {}
        }
    }

    /// Tag a property (atom, `And`, or `Or`) with the display name, full
    /// call-site arguments, and meaning of the compound property it expanded from.
    pub(crate) fn set_origin(&mut self, name: String, args: Vec<String>, meaning: Option<String>) {
        let origin = ContractOrigin {
            name,
            args,
            meaning,
        };
        match self {
            Property::Atom(a) => a.origin = Some(origin),
            Property::And(a) => a.origin = Some(origin),
            Property::Or(o) => o.origin = Some(origin),
        }
    }

    /// Remove the compound-origin display metadata from this property.
    pub(crate) fn clear_origin(&mut self) {
        match self {
            Property::Atom(a) => a.origin = None,
            Property::And(a) => a.origin = None,
            Property::Or(o) => o.origin = None,
        }
    }

    /// Attach a `for_each` container to an atom.
    pub(crate) fn set_for_each(&mut self, place: Option<ContractPlace<'tcx>>) {
        if let Property::Atom(a) = self {
            a.for_each = place;
        }
    }

    /// Override the contract kind (e.g. `Alias` → `Hazard`).
    pub(crate) fn set_contract_kind(&mut self, k: ContractKind) {
        match self {
            Property::Atom(a) => a.contract_kind = k,
            Property::And(a) => a.contract_kind = k,
            Property::Or(o) => o.contract_kind = k,
        }
    }
}
