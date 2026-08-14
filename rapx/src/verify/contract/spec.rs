//! Declaration table mapping tag names to their property specs.
//!
//! This is the single source of truth for every safety tag `rapx` understands:
//! its `PropertyKind`, the argument shapes it accepts (for variable-arity tags
//! there is more than one form), its default `ContractKind`, and the assembly
//! strategy used to build the final `Property` from raw `syn::Expr` arguments.
//!
//! `PropertyKind` orthogonalisation lives on `PropertyKind` in `types.rs`.

use super::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArgKind { Target, Ty, Expr, Ident }

/// How a tag's arguments are assembled into a `Property`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BuildKind {
    /// Positional resolution over a matched `forms` entry (common case).
    Uniform,
    /// `Size(T, sized | unsized | const)` — second arg is an ident or a const.
    Size,
    /// `Allocated(target[, T, n[, allocator]])` — 1/3/4-argument forms.
    Allocated,
    /// `InBound(index | target,index | target,T,n)` — index + for_each variants.
    InBound,
    /// `NonOverlap(indices | a,b,T,count)` — 1/4-argument forms.
    NonOverlap,
    /// `ValidNum(predicate | value, interval)`.
    ValidNum,
    /// `Pinned(ptr, lifetime)` — lifetime is optional.
    Pinned,
    /// `SplitTransmute([T], [U])` — array element types.
    SplitTransmute,
    /// One-or-more target places (`Alias`, `Alive`).
    Targets,
    /// Placeholder accepting any args; always yields `Unknown`.
    TobeSpecified,
}

pub(crate) struct PropertySpec {
    pub tag: &'static str,
    pub kind: PropertyKind,
    /// Accepted argument shapes. For `BuildKind::Targets` the single entry is
    /// a marker and the tag accepts one or more `Target` args.
    pub forms: &'static [&'static [ArgKind]],
    pub contract_kind: ContractKind,
    pub build: BuildKind,
    /// Human-readable explanation template, with `{0}`, `{1}`, `{2}`
    /// placeholders bound to the rendered positional arguments.  This keeps the
    /// display text co-located with the tag declaration instead of hardcoded in
    /// the renderer.  A few argument-dependent kinds (`InBound`, `Size`,
    /// `ValidNum`, `Alive`, `Allocated`, `NonOverlap`) override this template
    /// structurally at render time.
    pub meaning: &'static str,
}

const fn ps(
    tag: &'static str,
    kind: PropertyKind,
    forms: &'static [&'static [ArgKind]],
    contract_kind: ContractKind,
    build: BuildKind,
    meaning: &'static str,
) -> PropertySpec {
    PropertySpec { tag, kind, forms, contract_kind, build, meaning }
}

use ArgKind::{Expr, Ident, Target, Ty};

// ── Table ────────────────────────────────────────────────────────────

static SPECS: &[PropertySpec] = &[
    // Uniform single-form primitives.
    ps("NonNull",       PropertyKind::NonNull,       &[&[Target]],               ContractKind::Precond, BuildKind::Uniform, "{0} as usize != 0"),
    ps("Owning",        PropertyKind::Owning,        &[&[Target]],               ContractKind::Precond, BuildKind::Uniform, "ownership(*{0}) = none: no live owner aliases the pointee"),
    ps("Opened",        PropertyKind::Opened,        &[&[Target]],               ContractKind::Precond, BuildKind::Uniform, "{0} is a valid open file descriptor"),
    ps("Unreachable",   PropertyKind::Unreachable,   &[&[]],                     ContractKind::Precond, BuildKind::Uniform, "not Reachable()"),
    ps("Align",         PropertyKind::Align,         &[&[Target, Ty]],           ContractKind::Precond, BuildKind::Uniform, "({0} as usize) % align_of::<{1}>() == 0"),
    ps("Typed",         PropertyKind::Typed,         &[&[Target, Ty]],           ContractKind::Precond, BuildKind::Uniform, "*{0} holds TypeInvariant({1})"),
    ps("Init",          PropertyKind::Init,          &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform, "forall i in 0..{2}: *({0} + i*sizeof({1})) |= type_invariant({1}), and the {2} value(s) are initialized"),
    ps("ValidString",   PropertyKind::ValidString,   &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform, "{0} is valid UTF-8"),
    ps("NonVolatile",   PropertyKind::NonVolatile,   &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform, "{0} does not reference volatile memory"),
    ps("ValidTransmute", PropertyKind::ValidTransmute, &[&[Ty, Ty]],             ContractKind::Precond, BuildKind::Uniform, "bytes_of({1}) within bytes_of({0})"),
    ps("Trait",         PropertyKind::Trait,         &[&[Ty, Ident]],            ContractKind::Precond, BuildKind::Uniform, "{0} satisfies the trait bound {1}"),
    ps("NoPadding",     PropertyKind::NoPadding,     &[&[Ty]],                   ContractKind::Precond, BuildKind::Uniform, "{0} has no padding bytes between fields"),
    ps("ValidCStr",     PropertyKind::ValidCStr,     &[&[Target, Expr]],         ContractKind::Precond, BuildKind::Uniform, "{0} is a null-terminated valid UTF-8 byte sequence"),
    ps("Unwrap",        PropertyKind::Unwrap,        &[&[Target, Ident]],        ContractKind::Precond, BuildKind::Uniform, "unwrap({0}) = {1}"),
    // Variable-arity / special-build primitives.
    ps("Size",          PropertyKind::Size,          &[&[Ty, Ident], &[Ty, Expr]], ContractKind::Precond, BuildKind::Size, "sizeof({0}) = {1}"),
    ps("NonSize",       PropertyKind::Size,          &[&[Ty, Ident], &[Ty, Expr]], ContractKind::Precond, BuildKind::Size, "sizeof({0}) = {1}"),
    ps("Allocated",     PropertyKind::Allocated,     &[&[Target], &[Target, Ty, Expr], &[Target, Ty, Expr, Ident]], ContractKind::Precond, BuildKind::Allocated, "{0} points to a live allocation of size: size_of({1}) * {2}"),
    ps("InBound",       PropertyKind::InBound,       &[&[Expr], &[Target, Expr], &[Target, Ty, Expr]], ContractKind::Precond, BuildKind::InBound, "same_alloc([{0}, {0} + sizeof({1})*{2}])"),
    ps("InBounded",     PropertyKind::InBound,       &[&[Expr], &[Target, Expr], &[Target, Ty, Expr]], ContractKind::Precond, BuildKind::InBound, "same_alloc([{0}, {0} + sizeof({1})*{2}])"),
    ps("NonOverlap",    PropertyKind::NonOverlap,    &[&[Target], &[Target, Target, Ty, Expr]], ContractKind::Precond, BuildKind::NonOverlap, "[{0}] are pairwise disjoint memory ranges"),
    ps("ValidNum",      PropertyKind::ValidNum,      &[&[Expr], &[Expr, Expr]],   ContractKind::Precond, BuildKind::ValidNum, "{0}"),
    ps("Alias",         PropertyKind::Alias,         &[&[Target, Target]],       ContractKind::Hazard,  BuildKind::Targets, "{0} and {1} alias each other (hazard)"),
    ps("Alive",         PropertyKind::Alive,         &[&[Target, Target]],       ContractKind::Precond, BuildKind::Targets, "*{0} outlives '{1}"),
    ps("Pinned",        PropertyKind::Pinned,        &[&[Target, Ident]],        ContractKind::Precond, BuildKind::Pinned, "{0} will not be moved"),
    ps("SplitTransmute", PropertyKind::SplitTransmute, &[&[Ty, Ty]],             ContractKind::Precond, BuildKind::SplitTransmute, "[{0}] as [{1}]: every size_of({1})-byte contiguous chunk of [{0}] is a valid bit-pattern of {1} (type_invariant satisfied, alignment not required)\nforall w subset bytes([{0}]), |w| == |{1}|: reinterpret_as_{1}(w) |= type_invariant({1}) \\ align_of({1})"),
    ps("TobeSpecified", PropertyKind::Unknown,       &[],                        ContractKind::Precond, BuildKind::TobeSpecified, "(unresolved contract)"),
];

pub(crate) fn find_spec(name: &str) -> Option<&'static PropertySpec> {
    SPECS.iter().find(|s| s.tag == name)
}

/// The canonical meaning template for a property kind (the first tag that maps
/// to `kind`).  Argument-dependent kinds override this at render time.
pub(crate) fn kind_meaning(kind: PropertyKind) -> &'static str {
    SPECS.iter()
        .find(|s| s.kind == kind)
        .map(|s| s.meaning)
        .unwrap_or("(unresolved contract)")
}
