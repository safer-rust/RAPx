pub mod core;
pub mod extract;
pub mod graphs;
pub mod opt;
pub mod rcanary;
pub mod safedrop;
pub mod scan;
pub mod senryx;
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
