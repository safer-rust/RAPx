use clap::{Args, Subcommand, ValueEnum};
use std::path::PathBuf;

#[derive(Debug, Clone, Args)]
pub struct AdgArgs {
    #[arg(long)]
    /// Include private APIs in the API graph. By default, only public APIs are included.
    pub include_private: bool,
    #[arg(long)]
    /// Include unsafe APIs in API graph. By default, only safe APIs are included.
    pub include_unsafe: bool,
    /// Include Drop trait in API graph. By default, Drop is not included.
    #[arg(long)]
    pub include_drop: bool,
    /// The maximum number of iterations to search for generic APIs.
    #[arg(long, default_value_t = 10)]
    pub max_iteration: usize,
    /// The path to dump the API graph to. Output format is decided by extension suffix.
    /// default PATH = `./api_graph.dot`.
    #[arg(long, default_missing_value = "./api_graph.dot", value_name = "PATH")]
    pub dump: Option<PathBuf>,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum AliasStrategyKind {
    /// meet-over-paths (default)
    Mop,
    /// maximum-fixed-point
    Mfp,
}

// use command string to automatically generate help messages
#[derive(Debug, Clone, Subcommand)]
pub enum AnalysisKind {
    /// perform alias analysis (meet-over-paths by default)
    Alias {
        /// specify the alias analysis strategy
        #[arg(short, long, default_value = "mop")]
        strategy: AliasStrategyKind,
    },
    /// generate API dependency graphs
    Adg(AdgArgs),
    /// generate unsafety propagation graphs for each module
    Upg,
    /// generate unsafety propagation graphs for each module of the Rust standard library
    UpgStd,
    /// generate callgraphs
    Callgraph,
    /// generate dataflow graphs
    Dataflow {
        /// print debug information during dataflow analysis
        #[arg(short, long)]
        debug: bool,
    },
    /// analyze if the type holds a piece of memory on heap
    OwnedHeap,
    /// extract path constraints
    Pathcond,
    /// perform range analysis
    Range {
        /// print debug information during range analysis
        #[arg(short, long)]
        debug: bool,
    },
    /// print basic information of the crate, e.g., the number of APIs
    Scan,
    /// print the SSA form of the crate
    Ssa,
    /// print the MIR of the crate
    Mir,
    /// print the MIR of the crate in dot format
    DotMir,
}
