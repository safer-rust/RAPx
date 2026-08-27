//! Contract parsing, resolution, and rendering.
//!
//! Three front-ends (inline attributes, embedded JSON, and `pred!`-style `def`
//! macros, plus the pest DSL for expressions) all funnel into
//! `Property::parse_list`, producing a single IR defined in [`types`].
//!
//! ## Layering
//!
//! Contracts go through two stages, each with its own type:
//!
//! ```text
//! #[rapx::requires(...)] text                    std-*.json
//!    └─ attr.rs ──▶ AttrProperty                  └─ json.rs ──▶ JsonProperty
//!                      └───────────── builder.rs ─────────────▶ Property   (Atom | Or)
//! ```
//!
//! Within the resolved IR, the naming follows granularity rather than stage:
//! `Property*` names the formula level (`Property`, `PropertyKind`,
//! `PropertyArg`), while `Contract*` names the expression sub-language that
//! fills `PropertyArg::Expr` (`ContractPlace`, `ContractExpr`,
//! `ContractProjection`).

pub(crate) mod json;
pub(crate) mod attr;
pub mod builder;
pub mod compound;
pub mod pest_conv;
pub mod pest_grammar;
pub(crate) mod place;
pub mod query;
pub(crate) mod render;
pub(crate) mod resolve;
pub(crate) mod spec;
pub mod types;

pub use query::*;
pub use types::*;
