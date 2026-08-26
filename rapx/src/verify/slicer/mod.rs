//! Backward data-dependency slicer.
//!
//! Given a path tree, a checkpoint, and a property, it walks each path backward
//! to keep only the MIR items that are data-relevant to the property, producing
//! one [`ProofGoal`] per path for the symbolic VM to execute forward.

mod call_visit;
pub mod types;
mod visitor;

pub use types::{RelevantItem, ProofGoal};
pub use visitor::BackwardSlicer;
