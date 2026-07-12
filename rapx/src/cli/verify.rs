use clap::Args;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum VerifyMode {
    #[value(help = "Auto-detect: verify all functions with unsafe callees or struct invariants")]
    Scan,
    #[value(help = "Only verify functions annotated with #[rapx::verify]")]
    Targeted,
    #[value(help = "Like `scan` or `targeted` but skip struct invariant checks")]
    Invless,
}

/// Arguments for the `verify` command.
#[derive(Debug, Clone, Args)]
pub struct VerifyArgs {
    /// Identify all functions annotated with #[rapx::verify] and print each target, its unsafe callees, and their safety contracts.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Number of extra SCC postfix repetitions allowed during path enumeration.
    /// Default is 0 (postfix segments appear once each). Set to 1 to allow one extra repetition (two total occurrences), etc.
    #[arg(long, default_value_t = 0)]
    pub postfix_repeat: usize,
    /// Verification mode: `scan` auto-detects unannotated unsafe targets (default), `targeted` verifies #[rapx::verify] functions.
    #[arg(long, default_value = "scan")]
    pub mode: VerifyMode,
    /// Filter verification targets to only those within the specified crate
    /// (Rust crate name or Cargo package name, e.g. `std`, `core`, `my-crate`).
    /// Useful for standard-library workspaces and sub-workspaces.
    #[arg(long = "crate")]
    pub crate_name: Option<String>,
    /// Filter verification targets to only those within the specified module path
    /// (e.g. `my_module::inner`). When combined with `--crate`, the path is
    /// interpreted relative to that crate. Applies to all verification modes.
    #[arg(long)]
    pub module: Option<String>,
    /// Print all contract resolutions for every verification target: each
    /// unsafe callee with its resolved contracts, and the caller's own
    /// contracts (expanded form).  Useful for debugging missing or unexpected
    /// contract resolutions.
    #[arg(long)]
    pub debug_contracts: bool,
}
