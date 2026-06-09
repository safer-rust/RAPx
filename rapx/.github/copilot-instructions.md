# Copilot Instructions for RAPx

## Project Overview
- **RAPx** is a static analysis platform for Rust, focused on detecting use-after-free, memory leaks, and related bugs.
- The codebase is organized as a Rust crate with multiple analysis modules under `src/analysis/`.
- The main entry point is `src/lib.rs`, which wires together all major analyses and exposes the `RapCallback` struct for configuring analysis runs.

## Key Components
- **Analysis Modules:**
  - `alias_analysis`, `api_dependency`, `callgraph`, `dataflow`, `ownedheap_analysis`, `range_analysis`, `ssa_transform`, etc.
  - Each module implements a trait-based analyzer (e.g., `AliasAnalyzer`, `ApiDependencyAnalyzer`).
- **Integration with rustc:**
  - Uses many `rustc_*` crates as dependencies and relies on nightly features (`#![feature(rustc_private)]`).
  - Analysis is triggered via custom rustc callbacks (`RapCallback` implements `rustc_driver::Callbacks`).
- **Testing:**
  - Test cases are organized under `tests/`, often as standalone Rust projects with their own `Cargo.toml`.
  - Test binaries and MIR/SSA outputs are stored in subfolders like `tests/range/range_array/ssa_mir/`.

## Developer Workflows
- **Build:**
  - Standard: `cargo build` (requires nightly toolchain and `rustc_private` access).
  - For custom driver: `cargo run --bin rapx -- [rustc args]` or `cargo rapx ...`.
- **Test:**
  - Run all tests: `cargo test` (for unit tests in the main crate).
  - For integration tests, run test binaries in `tests/` as separate projects.
- **Debugging:**
  - Use `RUST_LOG=info` or `RUST_LOG=debug` for verbose output.
  - Many analyses print results using `rap_info!` macros.

## Project-Specific Conventions
- **Analysis Configuration:**
  - Analyses are enabled/disabled via methods on `RapCallback` (e.g., `enable_alias`, `enable_api_dependency`).
  - Some analyses accept parameters (e.g., `enable_alias("-alias1")`).
- **Default rustc Args:**
  - Always use `-Zalways-encode-mir -Zmir-opt-level=0` for maximal MIR validation.
- **External Integration:**
  - Heavy reliance on internal rustc crates; ensure nightly toolchain and proper environment.

## Examples
- To run alias analysis with field depth 1:
  ```sh
  cargo run --bin rapx -- -alias1 path/to/crate
  ```
- To generate an API dependency graph:
  ```sh
  cargo run --bin rapx -- -api path/to/crate
  ```

## References
- Main configuration: `src/lib.rs`, `Cargo.toml`
- Analysis logic: `src/analysis/`
- Test cases: `tests/`
- Documentation: https://artisan-lab.github.io/RAPx-Book/

---
_If any section is unclear or missing, please provide feedback for further refinement._
