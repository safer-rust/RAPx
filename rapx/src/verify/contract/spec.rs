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
}

const fn ps(
    tag: &'static str,
    kind: PropertyKind,
    forms: &'static [&'static [ArgKind]],
    contract_kind: ContractKind,
    build: BuildKind,
) -> PropertySpec {
    PropertySpec { tag, kind, forms, contract_kind, build }
}

use ArgKind::{Expr, Ident, Target, Ty};

// ── Table ────────────────────────────────────────────────────────────

static SPECS: &[PropertySpec] = &[
    // Uniform single-form primitives.
    ps("NonNull",       PropertyKind::NonNull,       &[&[Target]],               ContractKind::Precond, BuildKind::Uniform),
    ps("Owning",        PropertyKind::Owning,        &[&[Target]],               ContractKind::Precond, BuildKind::Uniform),
    ps("Opened",        PropertyKind::Opened,        &[&[Target]],               ContractKind::Precond, BuildKind::Uniform),
    ps("Unreachable",   PropertyKind::Unreachable,   &[&[]],                     ContractKind::Precond, BuildKind::Uniform),
    ps("Align",         PropertyKind::Align,         &[&[Target, Ty]],           ContractKind::Precond, BuildKind::Uniform),
    ps("Typed",         PropertyKind::Typed,         &[&[Target, Ty]],           ContractKind::Precond, BuildKind::Uniform),
    ps("Init",          PropertyKind::Init,          &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform),
    ps("ValidString",   PropertyKind::ValidString,   &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform),
    ps("NonVolatile",   PropertyKind::NonVolatile,   &[&[Target, Ty, Expr]],     ContractKind::Precond, BuildKind::Uniform),
    ps("ValidTransmute", PropertyKind::ValidTransmute, &[&[Ty, Ty]],             ContractKind::Precond, BuildKind::Uniform),
    ps("Trait",         PropertyKind::Trait,         &[&[Ty, Ident]],            ContractKind::Precond, BuildKind::Uniform),
    ps("NoPadding",     PropertyKind::NoPadding,     &[&[Ty]],                   ContractKind::Precond, BuildKind::Uniform),
    ps("ValidCStr",     PropertyKind::ValidCStr,     &[&[Target, Expr]],         ContractKind::Precond, BuildKind::Uniform),
    ps("Unwrap",        PropertyKind::Unwrap,        &[&[Target, Ident]],        ContractKind::Precond, BuildKind::Uniform),
    // Variable-arity / special-build primitives.
    ps("Size",          PropertyKind::Size,          &[&[Ty, Ident], &[Ty, Expr]], ContractKind::Precond, BuildKind::Size),
    ps("NonSize",       PropertyKind::Size,          &[&[Ty, Ident], &[Ty, Expr]], ContractKind::Precond, BuildKind::Size),
    ps("Allocated",     PropertyKind::Allocated,     &[&[Target], &[Target, Ty, Expr], &[Target, Ty, Expr, Ident]], ContractKind::Precond, BuildKind::Allocated),
    ps("InBound",       PropertyKind::InBound,       &[&[Expr], &[Target, Expr], &[Target, Ty, Expr]], ContractKind::Precond, BuildKind::InBound),
    ps("InBounded",     PropertyKind::InBound,       &[&[Expr], &[Target, Expr], &[Target, Ty, Expr]], ContractKind::Precond, BuildKind::InBound),
    ps("NonOverlap",    PropertyKind::NonOverlap,    &[&[Target], &[Target, Target, Ty, Expr]], ContractKind::Precond, BuildKind::NonOverlap),
    ps("ValidNum",      PropertyKind::ValidNum,      &[&[Expr], &[Expr, Expr]],   ContractKind::Precond, BuildKind::ValidNum),
    ps("Alias",         PropertyKind::Alias,         &[&[Target, Target]],       ContractKind::Hazard,  BuildKind::Targets),
    ps("Alive",         PropertyKind::Alive,         &[&[Target, Target]],       ContractKind::Precond, BuildKind::Targets),
    ps("Pinned",        PropertyKind::Pinned,        &[&[Target, Ident]],        ContractKind::Precond, BuildKind::Pinned),
    ps("SplitTransmute", PropertyKind::SplitTransmute, &[&[Ty, Ty]],             ContractKind::Precond, BuildKind::SplitTransmute),
    ps("TobeSpecified", PropertyKind::Unknown,       &[],                        ContractKind::Precond, BuildKind::TobeSpecified),
];

pub(crate) fn find_spec(name: &str) -> Option<&'static PropertySpec> {
    SPECS.iter().find(|s| s.tag == name)
}
