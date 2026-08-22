mod call_visit;
pub mod types;
mod visitor;

pub use types::{RelevantItem, KeepReason, ProofGoal};
pub use visitor::BackwardSlicer;
