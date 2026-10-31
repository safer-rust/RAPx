use clap::Args;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum VerifyMode {
    #[value(help = "Auto-detect: verify all functions with unsafe callees or struct invariants")]
    Scan,
    #[value(help = "Only verify functions annotated with #[rapx::verify]")]
    Targeted,
}

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
pub enum InlineCtor {
    True,
    False,
    #[default]
    Default,
}

/// Postfix repeat count: `auto` (default) enables automatic loop-depth
/// detection; a number N ≥ 0 sets a fixed repeat count.
#[derive(Debug, Clone)]
pub enum PostfixRepeat {
    Auto,
    Fixed(usize),
}

impl std::fmt::Display for PostfixRepeat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PostfixRepeat::Auto => write!(f, "auto"),
            PostfixRepeat::Fixed(n) => write!(f, "{n}"),
        }
    }
}

impl std::str::FromStr for PostfixRepeat {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.eq_ignore_ascii_case("auto") {
            Ok(PostfixRepeat::Auto)
        } else {
            s.parse::<usize>()
                .map(PostfixRepeat::Fixed)
                .map_err(|_| format!("expected 'auto' or a non-negative integer, got '{s}'"))
        }
    }
}

/// Arguments for the `verify` command.
#[derive(Debug, Clone, Args)]
pub struct VerifyArgs {
    /// Identify all functions annotated with #[rapx::verify] and print each target, its unsafe callees, and their safety contracts.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Number of extra SCC postfix repetitions allowed during path enumeration.
    /// `auto` (default): automatic loop-depth detection for InBound and Align.
    /// A number ≥ 0 sets a fixed repeat count.
    #[arg(long, default_value = "auto", value_parser = clap::value_parser!(PostfixRepeat))]
    pub postfix_repeat: PostfixRepeat,
    /// Verification mode: `scan` auto-detects unannotated unsafe targets (default), `targeted` verifies #[rapx::verify] functions.
    #[arg(long, default_value = "scan")]
    pub mode: VerifyMode,
    /// Skip struct invariant checks and derive safety via constructor-mutator-method chains.
    /// Works with both `scan` and `targeted` modes.
    #[arg(long = "no-invariant-target")]
    pub skip_invariant: bool,
    /// Constructor inlining: true always, false never, default only without a struct invariant.
    #[arg(long, default_value = "default")]
    pub inline_ctor: InlineCtor,
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
    /// Cap on the number of paths collected per checkpoint (defaults to the
    /// built-in `PATH_LIMIT`). Lower it to speed up verification at the cost of
    /// path coverage (paths past the cap are treated as proved).
    #[arg(long)]
    pub path_limit: Option<usize>,
    /// Cap on the number of trait impls inlined for a virtual (trait-object)
    /// call; a trait with more impls is truncated to the first `n`. Defaults to 3.
    #[arg(long)]
    pub trait_impl_limit: Option<usize>,
    /// Print all contract resolutions for every verification target: each
    /// unsafe callee with its resolved contracts, and the caller's own
    /// contracts (expanded form).  Useful for debugging missing or unexpected
    /// contract resolutions.
    #[arg(long)]
    pub debug_contracts: bool,
}
