use super::OptLevel;
use clap::Args;

/// Arguments for the `check` command.
#[derive(Debug, Clone, Args)]
pub struct CheckArgs {
    /// detect use-after-free/double-free
    #[arg(
        short = 'f',
        num_args=0..=1,
        default_missing_value = "1",
        long,
    )]
    pub uaf: Option<usize>,

    /// detect memory leakage
    #[arg(short = 'm', long)]
    pub mleak: bool,

    /// automatically detect code optimization chances
    #[arg(short = 'o', long, default_missing_value = "default")]
    pub opt: Option<OptLevel>,

}
