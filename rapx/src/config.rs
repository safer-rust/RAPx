use crate::help::{RAPX_AFTER_HELP, RAPX_VERSION};
use clap::{Parser, Subcommand, ValueEnum};

#[derive(Parser, Debug, Clone)] // requires `derive` feature
#[command(styles = CLAP_STYLING)]
#[command(version = RAPX_VERSION, about)]
#[command(about = "RAPx is a static analysis tool for Rust.")]
#[command(after_help = RAPX_AFTER_HELP)]
pub struct Config {
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
#[derive(Debug, Clone, Subcommand)]
pub enum Commands {
    /// statically analyze the crate
    #[command(arg_required_else_help = true)]
    Analyze {
        #[command(subcommand)]
        kind: AnalysisKind,
    },
    /// check potential vulnerabilities in the crate,
    /// such as use-after-free and memory leak
    Check {
        #[arg(
            short = 'f',
            num_args=0..=1,
            default_missing_value = "1",
            long,
            help = "detect use-after-free/double-free"
        )]
        uaf: Option<usize>,
        #[arg(short = 'm', long, help = "detect memory leakage")]
        mleak: bool,
        #[arg(
            short = 'o',
            long,
            default_missing_value = "default",
            help = "automatically detect code optimization chances"
        )]
        opt: Option<OptLevel>,
        #[arg(
            long,
            help = "(under development) infer the safety properties required by unsafe APIs."
        )]
        infer: bool,
        #[arg(
            long,
            help = "(under development) verify if the safety requirements of unsafe API are satisfied."
        )]
        verify: bool,
        #[arg(
            long,
            help = "(under development) verify if the safety requirements of unsafe API are satisfied."
        )]
        verify_std: bool,
    },
}

// use command string to automatically generate help messages
#[derive(Debug, Clone, Copy, Subcommand)]
pub enum AnalysisKind {
    /// perform alias analysis (meet-over-paths by default)
    Alias,
    /// perform alias analysis (maximum-fixed-point)
    AliasMfp,
    /// generate API dependency graphs
    Adg,
    /// generate unsafety propagation graphs for each module
    Upg,
    /// generate unsafety propagation graphs for each module of the Rust standard library
    UpgStd,
    /// generate callgraphs
    Callgraph,
    /// generate dataflow graphs
    Dataflow { debug: bool },
    /// analyze if the type holds a piece of memory on heap
    OwnedHeap,
    /// extract path constraints
    Pathcond,
    /// perform range analysis
    Range { debug: bool },
    /// print basic information of the crate, e.g., the number of APIs
    Scan,
    /// print the SSA form of the crate
    Ssa,
    /// print the MIR of the crate
    Mir,
    /// print the MIR of the crate in dot format
    DotMir,
}

// Keep CLI style consistent with cargo's default style
pub const CLAP_STYLING: clap::builder::styling::Styles = clap::builder::styling::Styles::styled()
    .header(clap_cargo::style::HEADER)
    .usage(clap_cargo::style::USAGE)
    .literal(clap_cargo::style::LITERAL)
    .placeholder(clap_cargo::style::PLACEHOLDER)
    .error(clap_cargo::style::ERROR)
    .valid(clap_cargo::style::VALID)
    .invalid(clap_cargo::style::INVALID);

impl Config {
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
