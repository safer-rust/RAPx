//! Declaration table mapping tag names to their property specs.
//!
//! This is the single source of truth for every safety tag `rapx` understands:
//! its `PropertyKind`, the argument shapes it accepts (for variable-arity tags
//! there is more than one form), its default `ContractKind`, and its rendering
//! template.
//!
//! `PropertyKind` orthogonalisation lives on `PropertyKind` in `types.rs`.
//!
//! Some tags are declared but not fully supported: `Unwrap`, `Pinned`,
//! `Opened` and `Unreachable` are parsed but the checker returns `Unknown`;
//! `NonVolatile` is assumed satisfied (the VM does not model volatile access).

use super::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArgKind {
    Target,
    Ty,
    Expr,
    Ident,
}

pub(crate) struct PropertySpec {
    /// Tag name as written in contracts (e.g. `"Allocated"`).
    pub tag: &'static str,
    /// The `PropertyKind` this tag resolves to.
    pub kind: PropertyKind,
    /// Accepted argument shapes (authoritative for positional builds only).
    pub forms: &'static [&'static [ArgKind]],
    /// Default contract kind (`Precond` / `Hazard` / `Option_`).
    pub contract_kind: ContractKind,
    /// Explanation template with `{0}`, `{1}`, `{2}` placeholders.
    pub meaning: &'static str,
}

const fn ps(
    tag: &'static str,
    kind: PropertyKind,
    forms: &'static [&'static [ArgKind]],
    contract_kind: ContractKind,
    meaning: &'static str,
) -> PropertySpec {
    PropertySpec {
        tag,
        kind,
        forms,
        contract_kind,
        meaning,
    }
}

use ArgKind::{Expr, Ident, Target, Ty};

// ── Table ────────────────────────────────────────────────────────────

static SPECS: &[PropertySpec] = &[
    // Single-form primitives.
    ps(
        "NonNull",
        PropertyKind::NonNull,
        &[&[Target]],
        ContractKind::Precond,
        "{0} as usize != 0",
    ),
    ps(
        "SliceOffset",
        PropertyKind::SliceOffset,
        &[&[Target, Target, Target]],
        ContractKind::Postcond,
        "addr({0}) = addr({1}) + start({2}) * size_of_element({1})",
    ),
    ps(
        "Null",
        PropertyKind::Null,
        &[&[Target]],
        ContractKind::Precond,
        "{0} is the null pointer",
    ),
    ps(
        "Owning",
        PropertyKind::Owning,
        &[&[Target], &[Target, Ty], &[Target, Ty, Expr]],
        ContractKind::Precond,
        "ownership(*{0}) = none: no other live owner points to the pointee",
    ),
    ps(
        "RefCountShare",
        PropertyKind::RefCountShare,
        &[&[Target]],
        ContractKind::Precond,
        "{0} carries an unclaimed Arc/Rc strong-reference share",
    ),
    // Unverified: the checker returns `Unknown` (no implementation yet).
    ps(
        "Opened",
        PropertyKind::Opened,
        &[&[Target]],
        ContractKind::Precond,
        "{0} is a valid open file descriptor",
    ),
    // Unverified: the checker returns `Unknown` (no implementation yet).
    ps(
        "Unreachable",
        PropertyKind::Unreachable,
        &[&[]],
        ContractKind::Precond,
        "this branch is unreachable",
    ),
    ps(
        "Align",
        PropertyKind::Align,
        &[&[Target, Ty]],
        ContractKind::Precond,
        "({0} as usize) % align_of::<{1}>() == 0",
    ),
    ps(
        "Typed",
        PropertyKind::Typed,
        &[&[Target], &[Target, Ty], &[Target, Ty, Expr]],
        ContractKind::Precond,
        "*{0} holds TypeInvariant({1})",
    ),
    ps(
        "Init",
        PropertyKind::Init,
        &[&[Target], &[Target, Ty], &[Target, Ty, Expr]],
        ContractKind::Precond,
        "forall i in 0..{2}: *({0} + i*sizeof({1})) |= type_invariant({1}), and the {2} value(s) are initialized",
    ),
    ps(
        "ValidString",
        PropertyKind::ValidString,
        &[&[Target, Ty, Expr], &[Target]],
        ContractKind::Precond,
        "{0} is valid UTF-8",
    ),
    // Assumed satisfied: the VM does not model volatile access.
    ps(
        "NonVolatile",
        PropertyKind::NonVolatile,
        &[&[Target], &[Target, Ty], &[Target, Ty, Expr]],
        ContractKind::Precond,
        "{0} does not reference volatile memory",
    ),
    ps(
        "ValidTransmute",
        PropertyKind::ValidTransmute,
        &[&[Ty, Ty]],
        ContractKind::Precond,
        "bytes_of({1}) within bytes_of({0})",
    ),
    ps(
        "Trait",
        PropertyKind::Trait,
        &[&[Ty, Ident]],
        ContractKind::Precond,
        "{0} satisfies the trait bound {1}",
    ),
    // Variable-arity negative type predicate: first arg is the target type,
    // the rest are negative type names the target must not (structurally)
    // contain.  Arity is validated by `build_contain_no_type`.
    ps(
        "ContainNoType",
        PropertyKind::ContainNoType,
        &[&[Ty, Ident]],
        ContractKind::Precond,
        "{0} does not structurally contain {1}",
    ),
    // `&T: Send` — the type can be shared across threads: every
    // interior-mutability / raw-pointer field of {0} is guarded by a
    // synchronization primitive (mutex/rwlock/atomic).
    ps(
        "RefSend",
        PropertyKind::RefSend,
        &[&[Ty]],
        ContractKind::Precond,
        "&{0} is Send: all shared mutations of {0} go through a synchronization primitive",
    ),
    // Interior-mutability predicates for taming raw pointers in `Send`/`Sync`.
    ps(
        "NoRawPtr",
        PropertyKind::NoRawPtr,
        &[&[Ty]],
        ContractKind::Precond,
        "{0} has no raw pointers",
    ),
    ps(
        "NoInternalMut",
        PropertyKind::NoInternalMut,
        &[&[Ty]],
        ContractKind::Precond,
        "{0} has no interior mutation through raw pointers",
    ),
    ps(
        "UniInternalMut",
        PropertyKind::UniInternalMut,
        &[&[Ty]],
        ContractKind::Precond,
        "{0} has unique interior mutation (exclusive owner, no aliasing Clone)",
    ),
    ps(
        "AtomicUpdate",
        PropertyKind::AtomicUpdate,
        &[&[Ty]],
        ContractKind::Precond,
        "{0} updates its raw pointers under synchronization or atomically",
    ),
    ps(
        "NoPadding",
        PropertyKind::NoPadding,
        &[&[Ty]],
        ContractKind::Precond,
        "{0} has no padding bytes between fields",
    ),
    ps(
        "ValidCStr",
        PropertyKind::ValidCStr,
        &[&[Target], &[Target, Expr]],
        ContractKind::Precond,
        "{0} is a null-terminated valid UTF-8 byte sequence",
    ),
    // Unverified: the checker returns `Unknown` (no implementation yet).
    ps(
        "Unwrap",
        PropertyKind::Unwrap,
        &[&[Target, Ident]],
        ContractKind::Precond,
        "unwrap({0}) = {1}",
    ),
    // Variable-arity / special-build primitives.
    ps(
        "Size",
        PropertyKind::Size,
        &[&[Ty, Ident], &[Ty, Expr]],
        ContractKind::Precond,
        "sizeof({0}) = {1}",
    ),
    ps(
        "Allocated",
        PropertyKind::Allocated,
        &[&[Target], &[Target, Ty], &[Target, Ty, Expr], &[Target, Ty, Ident], &[Target, Ty, Expr, Ident]],
        ContractKind::Precond,
        "{0} points to a live allocation of size: size_of({1}) * {2}",
    ),
    ps(
        "InBound",
        PropertyKind::InBound,
        &[&[Target], &[Target, Ty], &[Target, Expr], &[Target, Ty, Expr]],
        ContractKind::Precond,
        "same_alloc([{0}, {0} + sizeof({1})*{2}])",
    ),
    ps(
        "NonOverlap",
        PropertyKind::NonOverlap,
        &[&[Target], &[Target, Target], &[Target, Target, Ty], &[Target, Target, Ty, Expr]],
        ContractKind::Precond,
        "[{0}] are pairwise disjoint memory ranges",
    ),
    ps(
        "ValidNum",
        PropertyKind::ValidNum,
        &[&[Expr], &[Expr, Expr]],
        ContractKind::Precond,
        "{0}",
    ),
    ps(
        "Alias",
        PropertyKind::Alias,
        &[&[Target, Target]],
        ContractKind::Hazard,
        "{0} and {1} alias each other (hazard)",
    ),
    ps(
        "Alive",
        PropertyKind::Alive,
        &[&[Target, Target]],
        ContractKind::Precond,
        "*{0} outlives '{1}",
    ),
    // Unverified: the checker returns `Unknown` (no implementation yet).
    ps(
        "Pinned",
        PropertyKind::Pinned,
        &[&[Target, Ident]],
        ContractKind::Precond,
        "{0} will not be moved",
    ),
    ps(
        "SplitTransmute",
        PropertyKind::SplitTransmute,
        &[&[Ty, Ty]],
        ContractKind::Precond,
        "[{0}] as [{1}]: every size_of({1})-byte contiguous chunk of [{0}] is a valid bit-pattern of {1} (type_invariant satisfied, alignment not required)\nforall w subset bytes([{0}]), |w| == |{1}|: reinterpret_as_{1}(w) |= type_invariant({1})",
    ),
    ps(
        "TobeSpecified",
        PropertyKind::Unknown,
        &[],
        ContractKind::Precond,
        "(unresolved contract)",
    ),
];

pub(crate) fn find_spec(name: &str) -> Option<&'static PropertySpec> {
    SPECS.iter().find(|s| s.tag == name)
}

/// The first tag name that maps to `kind` (the inverse of [`find_spec`]).
pub(crate) fn tag_name_for_kind(kind: PropertyKind) -> Option<&'static str> {
    SPECS.iter().find(|s| s.kind == kind).map(|s| s.tag)
}

/// The canonical meaning template for a property kind (the first tag that maps
/// to `kind`).  Argument-dependent kinds override this at render time.
pub(crate) fn kind_meaning(kind: PropertyKind) -> &'static str {
    SPECS
        .iter()
        .find(|s| s.kind == kind)
        .map(|s| s.meaning)
        .unwrap_or("(unresolved contract)")
}
