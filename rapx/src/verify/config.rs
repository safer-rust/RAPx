//! Verification command options.

use clap::Args;
pub use crate::vm::constructor_policy::ConstructorMirMode;



#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum VerifyMode {
    #[value(help = "Auto-detect: verify all functions with unsafe callees or struct invariants")]
    Scan,
    #[value(help = "Only verify functions annotated with #[rapx::verify]")]
    Targeted,
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
            s.parse::<usize>().map(PostfixRepeat::Fixed)
                .map_err(|_| format!("expected 'auto' or a non-negative integer, got '{s}'"))
        }
    }
}

/// Configuration parsed by the `verify` command and shared throughout verification.
#[derive(Debug, Clone, Args)]
pub struct VerifyConfig {
    /// List collected verification targets and their resolved contracts without running verification.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Number of extra SCC postfix repetitions allowed during path enumeration.
    /// `auto` (default) estimates the needed repetitions for each target.
    /// A number N checks repeat counts from 0 through N.
    #[arg(long, default_value = "auto", value_parser = clap::value_parser!(PostfixRepeat))]
    pub postfix_repeat: PostfixRepeat,
    /// Verification mode: `scan` auto-detects unannotated unsafe targets (default), `targeted` verifies `#[rapx::verify]` functions.
    #[arg(long, default_value = "scan")]
    pub mode: VerifyMode,
    /// Skip standalone struct and type invariant checks and verify
    /// constructor-mutator-method sequences instead.
    #[arg(long = "no-invariant-target")]
    pub skip_invariant: bool,
    /// Constructor MIR: true prioritizes available MIR over call models;
    /// false skips MIR; default skips MIR if the direct result has an invariant,
    /// otherwise tries call models before MIR. With `--no-invariant-target`,
    /// default behaves as true.
    #[arg(long = "expand-ctor", value_name = "MODE", default_value = "default")]
    pub constructor_mir: ConstructorMirMode,
    /// Filter verification targets to only those within the specified crate
    /// (Rust crate name or Cargo package name, e.g. `std`, `core`, `my-crate`).
    /// Useful for standard-library workspaces and sub-workspaces.
    #[arg(long = "crate")]
    pub crate_filter: Option<String>,
    /// Filter verification targets to only those within the specified module path
    /// (e.g. `my_module::inner`). When combined with `--crate`, the path is
    /// interpreted relative to that crate. Applies to all verification modes.
    #[arg(long = "module")]
    pub module_filter: Option<String>,
    /// Cap on the number of paths collected per checkpoint (defaults to the
    /// built-in `PATH_LIMIT`; 0 also selects that default). Lower it to speed
    /// up verification; paths omitted by the cap are treated as proved.
    #[arg(long)]
    pub path_limit: Option<usize>,
    /// Cap on trait impls inlined for a virtual call and generic type combinations
    /// checked during monomorphization. Defaults to 1; 0 also selects that default.
    #[arg(long)]
    pub trait_impl_limit: Option<usize>,
    /// Check array const generic lengths from zero through this bound.
    /// Defaults to `ARRAY_LENGTH_LIMIT` when omitted.
    #[arg(long)]
    pub array_length_limit: Option<usize>,
    /// Print all contract resolutions for every verification target: each
    /// unsafe callee with its resolved contracts, and the caller's own
    /// contracts (expanded form), without running verification.
    #[arg(long)]
    pub debug_contracts: bool,
}

impl VerifyConfig {
    /// Effective verification path cap, including the default for zero or omission.
    pub(crate) fn path_limit(&self) -> usize {
        self.path_limit.filter(|n| *n != 0).unwrap_or(crate::limit::PATH_LIMIT)
    }

    /// Effective trait implementation cap, including the default for zero or omission.
    pub(crate) fn trait_impl_limit(&self) -> usize {
        self.trait_impl_limit.filter(|n| *n != 0).unwrap_or(crate::limit::TRAIT_IMPL_LIMIT)
    }

    pub(crate) fn array_length_limit(&self) -> usize {
        self.array_length_limit.unwrap_or(crate::limit::ARRAY_LENGTH_LIMIT)
    }

    /// Invariant-less runs expand constructor MIR under the default mode.
    pub(crate) fn constructor_mir_mode(&self) -> ConstructorMirMode {
        if self.skip_invariant && matches!(self.constructor_mir, ConstructorMirMode::Default) {
            ConstructorMirMode::True
        } else {
            self.constructor_mir
        }
    }
}
