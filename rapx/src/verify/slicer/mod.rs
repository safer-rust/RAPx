mod call_visit;
pub mod types;
mod visitor;

pub use types::{RelevantItem, ProofGoal};
pub use visitor::BackwardSlicer;
