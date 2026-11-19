pub mod alias;
pub mod api_dependency;
pub mod callgraph;
pub mod dataflow;
pub mod heap_ownership;
pub mod path;
pub mod points_to;
pub mod range;
pub mod safety_flow;
pub mod scan;
pub mod ssa_transform;

/// This is a general trait designed for all program analysis features.
pub trait Analysis {
    fn run(&mut self);
}
