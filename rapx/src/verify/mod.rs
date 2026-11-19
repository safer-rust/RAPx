//! The staged verification pipeline.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

pub(crate) mod api_classify;
mod auto_trait;
pub(crate) mod call_summary;
pub(crate) mod checkpoint;
pub(crate) mod contract;
pub(crate) mod display;
pub(crate) mod driver;
mod function_verifier;
pub(crate) mod loop_handling;
mod marker_trait;
pub(crate) mod path;
mod proof_cache;

pub(crate) mod property_checker;
pub(crate) mod report;
pub(crate) mod slicer;
pub(crate) mod target;
pub(crate) mod trait_ensurance;
pub(crate) mod type_invariants;
pub(crate) mod constructor_policy;

pub(crate) mod vm;
