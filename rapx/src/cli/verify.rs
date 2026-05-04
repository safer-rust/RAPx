use clap::Args;

/// Arguments for the `verify` command.
#[derive(Debug, Clone, Args)]
pub struct VerifyArgs {
    /// Scan the crate for all functions annotated with #[rapx::verify] and print their DefIds.
    #[arg(long)]
    pub scan: bool,
}
