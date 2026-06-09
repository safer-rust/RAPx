pub mod alias_analysis;
pub mod api_dependency;
pub mod callgraph;
pub mod dataflow;
pub mod ownedheap_analysis;
pub mod path_analysis;
pub mod range_analysis;
pub mod ssa_transform;
pub mod scan;
pub mod upg;
pub mod utils;

/// This is a general trait designed for all program analysis features.
pub trait Analysis {
    /// Return the name of the analysis.
    fn name(&self) -> &'static str;

    /// Execute the analysis.
    fn run(&mut self);

    /// Reset the analysis and cleanup the memory.
    fn reset(&mut self);
}
