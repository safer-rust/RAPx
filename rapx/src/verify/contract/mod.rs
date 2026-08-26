//! Contract parsing, resolution, and rendering.
//!
//! Three front-ends (inline attributes, embedded JSON, and `pred!`-style `def`
//! macros, plus the pest DSL for expressions) all funnel into
//! `Property::parse_list`, producing a single IR defined in [`types`].

pub(crate) mod assets;
pub(crate) mod attr;
pub mod builder;
pub mod def;
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
