//! Contract parsing, resolution, and rendering.
//!
//! Three front-ends (inline attributes, embedded JSON, and `pred!`-style
//! compound-property macros, plus the pest DSL for expressions) all funnel into
//! `Property::parse_list`, producing a single IR defined in [`types`].
//!
//! ## Layering
//!
//! Contracts go through two stages, each with its own type:
//!
//! ```text
//! #[rapx::requires(...)] text        std-*.json            pred!(...) / def_property
//!    └─ attr.rs ──▶ AttrProperty      └─ json.rs ──▶ JsonProperty   └─ compound.rs ──▶ CompoundSpec
//!                      └────────────────── builder.rs ──────────────────▶ Property   (Atom | Or)
//! ```
//!
//! Within the resolved IR, the naming follows granularity rather than stage:
//! `Property*` names the formula level (`Property`, `PropertyKind`,
//! `PropertyArg`), while `Contract*` names the expression sub-language that
//! fills `PropertyArg::Expr` (`ContractPlace`, `ContractExpr`,
//! `ContractProjection`).

pub(crate) mod json;
pub(crate) mod attr;
pub(crate) mod builder;
pub(crate) mod compound;
pub(crate) mod pest_conv;
pub(crate) mod pest_grammar;
pub(crate) mod place;
pub(crate) mod render;
pub(crate) mod resolve;
pub(crate) mod spec;
pub(crate) mod types;

pub(crate) use types::*;
