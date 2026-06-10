# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/logo.png)
RAPx (Rust Analysis Platform with Extensions) [![license](https://img.shields.io/github/license/Artisan-Lab/RAPx)](./LICENSE-MPL)[![docs.rs](https://img.shields.io/docsrs/rapx)](https://docs.rs/rapx) is an advanced static analysis platform for Rust. It provides an extensible framework for building and integrating powerful analysis capabilities that go beyond those available in the standard rustc compiler, empowering developers to reason about safety, robustness, and performance at a deeper level.

RAPx is available on crates.io. [![crates.io](https://img.shields.io/crates/v/rapx.svg)](https://crates.io/crates/rapx)

## Features
# ![logo](https://raw.githubusercontent.com/Artisan-Lab/RAPx/main/feature.png)
RAPx is structured into two layers: a core layer offering essential program analysis algorithms (e.g., alias and dataflow analysis), and an application layer implementing specific tasks such as bug detection. This separation of concerns promotes modular development and fosters collaboration between algorithm and application developers.

The project is still under heavy development. For further details, please refer to the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/).

## Quick Start

Install `nightly-2025-12-06` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2025-12-06 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2025-12-06 install rapx --git https://github.com/Artisan-Lab/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2025-12-06 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2025-12-06
```

Check out supported options with `-help`:

```shell
$ cargo rapx --help

Usage: cargo rapx [OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]

Commands:
  analyze  perform various analyses on the crate, e.g., alias analysis, callgraph generation
  check    check potential vulnerabilities in the crate, e.g., use-after-free, memory leak
  verify   verify annotated functions in the crate, e.g., identify #[rapx::verify] targets
  help     Print this message or the help of the given subcommand(s)

Options:
      --timeout <TIMEOUT>        specify the timeout seconds in running rapx
      --test-crate <TEST_CRATE>  specify the tested package in the workspace
  -h, --help                     Print help
  -V, --version                  Print version

NOTE: multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx check -f -m`
will perform two kinds of detection in a row.

Examples:

  # Bug Detection
  1. detect use-after-free and memory leak for a riscv target:
     cargo rapx check -f -m -- --target riscv64gc-unknown-none-elf
  2. detect use-after-free and memory leak for tests:
     cargo rapx check -f -m -- --tests
  3. detect use-after-free and memory leak for all workspace members:
     cargo rapx check -f -m -- --workspace
  4. detect optimization opportunities (report mode):
     cargo rapx check -o report

  # Analysis
  5. print path-sensitive CFG paths:
     cargo rapx analyze paths
  6. generate API dependency graphs:
     cargo rapx analyze adg
  7. perform alias analysis (MFP strategy):
     cargo rapx analyze alias -s mfp

  # Contract-Based Verification
  8. identify #[rapx::verify] targets and their safety contracts:
     cargo rapx verify --prepare-targets
  9. dump full verification diagnostics (backward/forward visits + SMT):
     cargo rapx verify --dump-visits
```

### `check` command

```
Usage: cargo rapx check [OPTIONS]

Options:
  -f, --uaf [<UAF>]    detect use-after-free/double-free (optional level, default 1)
  -m, --mleak          detect memory leakage
  -o, --opt [<OPT>]    automatically detect code optimization chances
                       [possible values: report, default, all]
  -h, --help           Print help
```

### `verify` command (under development)

The `verify` command provides a contract-based verification pipeline for functions annotated with `#[rapx::verify]`. It uses path-sensitive backward/forward analysis and Z3-based SMT solving to prove safety properties.

```
Usage: cargo rapx verify [OPTIONS]

Options:
      --prepare-targets  identify #[rapx::verify] functions and list their safety contracts
      --dump-visits      dump backward and forward visitor diagnostics for each callsite
  -h, --help             Print help
```

Annotate functions with `#[rapx::verify]` and safety contracts with `#[rapx::requires(...)]`:

```rust
#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]
fn init_buffer(buf: *mut u32, len: usize) {
    unsafe {
        // rapx checks: NonNull(buf), Align(buf, u32), InBound(buf, len)
        core::ptr::write(buf.add(len - 1), 0);
    }
}

#[rapx::requires(NonNull(Arg_0))]
unsafe fn custom_ptr_op(ptr: *const i32) -> i32 {
    unsafe { *ptr }
}
```

Safety properties include: `Align`, `NonNull`, `Allocated`, `InBound`, `Init`, `ValidPtr`, `Deref`, `Ptr2Ref`, and more. See the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/) for the full list.

### Environment Variables (values are case insensitive)

| var             | default when absent | possible values     | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAP_LOG`       | info                | trace, debug, info, warn | verbosity of logging   |
| `RAP_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAP_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |
| `RAPFLAGS`      | (unset)             | CLI arguments       | arguments passed to `rapx` binary directly |

For `RAP_RECURSIVE`:
* `none`: check for current folder
* `shallow`: check for current workspace members
* `deep`: check for all workspaces from current folder

NOTE: for `shallow` or `deep`, rapx will enter each member folder to do the check.

If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`.

