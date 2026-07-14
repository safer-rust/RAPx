mod analyze;
mod check;
mod verify;

pub use verify::PostfixRepeat;
pub use analyze::*;
pub use check::*;
use clap::{Args, Subcommand};
pub use verify::*;

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
    Check(CheckArgs),
    /// detect code optimization opportunities
    Opt,
    /// verify annotated functions in the crate, e.g., identify #[rapx::verify] targets
    Verify(VerifyArgs),
}

impl RapxArgs {
    pub fn init_env(&self) {
        let Commands::Check(CheckArgs {
            uaf: Some(level), ..
        }) = &self.command
        else {
            return;
        };
        unsafe {
            std::env::set_var("MOP", level.to_string());
        }
    }
}
