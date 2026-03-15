mod analyze;
pub use analyze::*;
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
    /// extract unsafe APIs and output a JSON document
    #[command(arg_required_else_help = true)]
    Extract {
        #[command(subcommand)]
        kind: ExtractKind,
    },
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum OptLevel {
    Report,
    Default,
    All,
}

// use command string to automatically generate help messages
#[derive(Debug, Clone, Copy, Subcommand)]
pub enum ExtractKind {
    /// output all `pub unsafe` APIs of the current crate as JSON
    UnsafeApis,
    /// output all `pub unsafe` APIs of the Rust standard library as JSON
    StdUnsafeApis,
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
