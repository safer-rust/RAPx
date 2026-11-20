//! Verification options and constructor MIR selection.

use clap::Args;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::analysis::safety_flow::root::has_rapx_struct_invariant;
use crate::helpers::fn_info::{self, FnKind};

use super::type_invariants::has_json_type_invariants;

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum VerifyMode {
    #[value(help = "Auto-detect: verify all functions with unsafe callees or struct invariants")]
    Scan,
    #[value(help = "Only verify functions annotated with #[rapx::verify]")]
    Targeted,
}

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
pub enum ConstructorMirMode {
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

/// Configuration parsed by the `verify` command and shared throughout verification.
#[derive(Debug, Clone, Args)]
pub struct VerifyConfig {
    /// Identify all functions annotated with `#[rapx::verify]` and print each target, its unsafe callees, and their safety contracts.
    #[arg(long)]
    pub prepare_targets: bool,
    /// Number of extra SCC postfix repetitions allowed during path enumeration.
    /// `auto` (default): automatic loop-depth detection for InBound and Align.
    /// A number ≥ 0 sets a fixed repeat count.
    #[arg(long, default_value = "auto", value_parser = clap::value_parser!(PostfixRepeat))]
    pub postfix_repeat: PostfixRepeat,
    /// Verification mode: `scan` auto-detects unannotated unsafe targets (default), `targeted` verifies `#[rapx::verify]` functions.
    #[arg(long, default_value = "scan")]
    pub mode: VerifyMode,
    /// Skip struct invariant checks and derive safety via constructor-mutator-method chains.
    /// Works with both `scan` and `targeted` modes.
    #[arg(long = "no-invariant-target")]
    pub skip_invariant: bool,
    /// Constructor MIR: true prioritizes available MIR over call models;
    /// false skips MIR; default skips MIR if the direct result has an invariant,
    /// otherwise tries call models before MIR.
    #[arg(long = "expand-ctor", value_name = "MODE", default_value = "default")]
    pub constructor_mir: ConstructorMirMode,
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
    /// Cap on trait impls inlined for a virtual call and generic type combinations
    /// checked during monomorphization. Defaults to 1.
    #[arg(long)]
    pub trait_impl_limit: Option<usize>,
    /// Print all contract resolutions for every verification target: each
    /// unsafe callee with its resolved contracts, and the caller's own
    /// contracts (expanded form).  Useful for debugging missing or unexpected
    /// contract resolutions.
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

    /// Invariant-less runs expand constructor MIR under the default mode.
    pub(crate) fn constructor_mir_mode(&self) -> ConstructorMirMode {
        if self.skip_invariant && matches!(self.constructor_mir, ConstructorMirMode::Default) {
            ConstructorMirMode::True
        } else {
            self.constructor_mir
        }
    }
}

/// Resolve `default` to `false` when the constructor's direct result has an
/// invariant. Otherwise retain the CLI mode for MIR versus call summaries.
pub(crate) fn effective_constructor_mir_mode(
    tcx: TyCtxt<'_>,
    callee: DefId,
    mode: ConstructorMirMode,
) -> ConstructorMirMode {
    debug_assert_eq!(fn_info::get_type(tcx, callee), FnKind::Constructor);
    match mode {
        ConstructorMirMode::Default if constructor_result_has_invariant(tcx, callee) => {
            ConstructorMirMode::False
        }
        mode => mode,
    }
}

/// Whether a constructor returns its owning ADT directly and that result has
/// a struct or registered type invariant. Wrapped results do not qualify.
pub(crate) fn constructor_result_has_invariant(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(owner) = fn_info::get_adt_def_id_by_adt_method(tcx, callee) else {
        return false;
    };
    let output = tcx.fn_sig(callee).skip_binder().output().skip_binder();
    Some(owner) == output.ty_adt_def().map(|adt| adt.did())
        && (has_rapx_struct_invariant(tcx, owner) || has_json_type_invariants(tcx, output))
}
