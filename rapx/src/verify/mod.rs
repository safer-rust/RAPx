//! The staged verification pipeline.
//!
//! Contract-based, path-sensitive verification of safety properties: collect
//! targets and contracts, extract SCC-aware paths, slice them backward, execute
//! the relevant MIR symbolically, and discharge each property with Z3.

mod api_classify;
mod auto_trait;
pub(crate) mod call_summary;
mod checkpoint;
pub(crate) mod constructor_policy;
mod contract;
mod display;
pub(crate) mod driver;
mod function_verifier;
pub(crate) mod loop_handling;
mod marker_trait;
mod path;
mod proof_cache;
mod property_checker;
mod report;
pub(crate) mod slicer;
pub(crate) mod target;
mod trait_ensurance;
mod type_invariants;
pub(crate) mod vm;
