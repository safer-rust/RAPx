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

    /// Run SafeDrop with AI review context
    #[arg(short = 'F', long, conflicts_with_all = ["uaf", "mleak"])]
    pub f_ai: bool,
}
