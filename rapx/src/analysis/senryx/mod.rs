//! Senryx unsafe-code soundness verification module.
//!
//! The module is organized around a small set of responsibilities:
//! driving the analysis (`driver`), building MIR-level state (`visitor` and
//! `dominated_graph`), parsing contracts (`contract`), dispatching unsafe
//! call-site obligations (`callsite`), and proving concrete safety properties
//! (`verification`).

/// Contract DSL and abstract-state data structures.
pub mod contract;
/// Dominated graph model used by the MIR visitor and checkers.
pub mod dominated_graph;

/// Unsafe call-site discovery and contract dispatch.
pub(crate) mod callsite;
/// Result aggregation and diagnostic formatting helpers.
mod diagnostics;
/// Top-level Senryx analysis driver.
mod driver;

/// Generic type candidate discovery for generic contract checks.
pub mod generic_check;
/// Symbolic value definitions and Z3-backed proof helpers.
pub mod symbolic_analysis;
/// Concrete safety-property verification procedures.
#[allow(unused)]
pub mod verification;
/// MIR body visitor that builds state and invokes contract checks.
#[allow(unused)]
pub mod visitor;

/// Public entry points for running the Senryx analysis.
pub use driver::{CheckLevel, SenryxCheck};
