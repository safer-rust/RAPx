//! Declaration table mapping tag names to fixed-arity PropertyKind specs.
//!
//! PropertyKind orthogonalisation lives on `PropertyKind` in `types.rs`.

use super::types::*;

#[derive(Clone, Copy)]
pub(crate) enum ArgKind { Target, Ty, Expr, Ident }

pub(crate) struct PropertySpec {
    pub tag: &'static str,
    pub kind: PropertyKind,
    pub args: &'static [ArgKind],
    pub contract_kind: ContractKind,
}

// ── Table ────────────────────────────────────────────────────────────

static SPECS: &[PropertySpec] = &[
    // [Target]
    ps("NonNull",      PropertyKind::NonNull,      &[ArgKind::Target], ContractKind::Precond),
    ps("Owning",       PropertyKind::Owning,       &[ArgKind::Target], ContractKind::Precond),
    ps("Opened",       PropertyKind::Opened,       &[ArgKind::Target], ContractKind::Precond),
    ps("Unreachable",  PropertyKind::Unreachable,  &[ArgKind::Target], ContractKind::Precond),
    // [Target, Ty]
    ps("Align",        PropertyKind::Align,        &[ArgKind::Target, ArgKind::Ty], ContractKind::Precond),
    ps("Typed",        PropertyKind::Typed,        &[ArgKind::Target, ArgKind::Ty], ContractKind::Precond),
    ps("Ptr2Ref",      PropertyKind::Ptr2Ref,      &[ArgKind::Target, ArgKind::Ty], ContractKind::Precond),
    // [Target, Ty, Expr]
    ps("Init",         PropertyKind::Init,         &[ArgKind::Target, ArgKind::Ty, ArgKind::Expr], ContractKind::Precond),
    ps("ValidPtr",     PropertyKind::ValidPtr,     &[ArgKind::Target, ArgKind::Ty, ArgKind::Expr], ContractKind::Precond),
    ps("Deref",        PropertyKind::Deref,        &[ArgKind::Target, ArgKind::Ty, ArgKind::Expr], ContractKind::Precond),
    ps("ValidString",  PropertyKind::ValidString,  &[ArgKind::Target, ArgKind::Ty, ArgKind::Expr], ContractKind::Precond),
    ps("NonVolatile",  PropertyKind::NonVolatile,  &[ArgKind::Target, ArgKind::Ty, ArgKind::Expr], ContractKind::Precond),
    // [Target, Target]
    ps("Layout",       PropertyKind::Layout,       &[ArgKind::Target, ArgKind::Target], ContractKind::Precond),
    // [Ty, Ty]
    ps("ValidTransmute", PropertyKind::ValidTransmute, &[ArgKind::Ty, ArgKind::Ty], ContractKind::Precond),
    // [Ty, Ident]
    ps("Trait",        PropertyKind::Trait,        &[ArgKind::Ty, ArgKind::Ident], ContractKind::Precond),
    // [Ty]
    ps("NoPadding",    PropertyKind::NoPadding,    &[ArgKind::Ty], ContractKind::Precond),
    // [Target, Expr]
    ps("ValidCStr",    PropertyKind::ValidCStr,    &[ArgKind::Target, ArgKind::Expr], ContractKind::Precond),
    // [Target, Ident]
    ps("Unwrap",       PropertyKind::Unwrap,       &[ArgKind::Target, ArgKind::Ident], ContractKind::Precond),
];

const fn ps(
    tag: &'static str,
    kind: PropertyKind,
    args: &'static [ArgKind],
    contract_kind: ContractKind,
) -> PropertySpec {
    PropertySpec { tag, kind, args, contract_kind }
}

pub(crate) fn find_spec(name: &str) -> Option<&'static PropertySpec> {
    SPECS.iter().find(|s| s.tag == name)
}
