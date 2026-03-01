use clap::{Args, Subcommand, ValueEnum};

#[derive(Args, Debug, Clone)]
pub struct RapxArgs {
    #[command(subcommand)]
    pub command: Commands,
    #[arg(long, help = "specify the timeout seconds in running rapx")]
    pub timeout: Option<u64>,
    #[arg(long, help = "specify the tested package in the workspace")]
    pub test_crate: Option<String>,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum OptLevel {
    Report,
    Default,
    All,
}

// NOTE: docstring is automatically used to generate help messages,
// so please use it to explain the command instead of `help` attribute in `arg` macro.
#[derive(Debug, Clone, Subcommand)]
pub enum Commands {
    /// perform various analyses on the crate, e.g., alias analysis, callgraph generation
    #[command(arg_required_else_help = true)]
    Analyze {
        #[command(subcommand)]
        kind: AnalysisKind,
    },
    /// check potential vulnerabilities in the crate,
    /// e.g., use-after-free, memory leak
    Check {
        /// detect use-after-free/double-free
        #[arg(
            short = 'f',
            num_args=0..=1,
            default_missing_value = "1",
            long,
        )]
        uaf: Option<usize>,

        /// detect memory leakage
        #[arg(short = 'm', long)]
        mleak: bool,

        /// automatically detect code optimization chances
        #[arg(short = 'o', long, default_missing_value = "default")]
        opt: Option<OptLevel>,

        /// (under development) infer the safety properties required by unsafe APIs.
        #[arg(long)]
        infer: bool,

        /// (under development) verify if the safety requirements of unsafe API are satisfied.
        #[arg(long)]
        verify: bool,

        /// (under development) verify if the safety requirements of unsafe API are satisfied.
        #[arg(long)]
        verify_std: bool,
    },
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum AliasStrategyKind {
    /// meet-over-paths (default)
    Mop,
    /// maximum-fixed-point
    Mfp,
}

// use command string to automatically generate help messages
#[derive(Debug, Clone, Copy, Subcommand)]
pub enum AnalysisKind {
    /// perform alias analysis (meet-over-paths by default)
    Alias {
        /// specify the alias analysis strategy
        #[arg(short, long, default_value = "mop")]
        strategy: AliasStrategyKind,
    },
    /// generate API dependency graphs
    Adg,
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

impl RapxArgs {
    pub fn init_env(&self) {
        let Commands::Check {
            uaf: Some(level), ..
        } = self.command
        else {
            return;
        };
        unsafe {
            std::env::set_var("MOP", level.to_string());
        }
    }
}
