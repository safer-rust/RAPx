use clap::Args;

/// Arguments for the `verify` command.
#[derive(Debug, Clone, Args)]
pub struct VerifyArgs {
    /// Identify all functions annotated with #[rapx::verify] and print each target, its unsafe callees, and their safety contracts.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Print backward and forward visitor diagnostics for each unsafe callsite property.
    #[arg(long)]
    pub dump_visits: bool,
}
