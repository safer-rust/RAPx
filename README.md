# ![logo](https://raw.githubusercontent.com/safer-rust/RAPx/main/logo.png)
RAPx (Rust Analysis Platform with Extensions) [![license: MPL 2.0](https://img.shields.io/badge/license-MPL%202.0-brightgreen)](./LICENSE-MPL)[![docs.rs](https://img.shields.io/badge/docs-docs.rs-blue)](https://docs.rs/rapx) is an advanced static analysis platform for Rust. It provides an extensible framework for building and integrating powerful analysis capabilities that go beyond those available in the standard rustc compiler, empowering developers to reason about safety, robustness, and performance at a deeper level.

RAPx is available on crates.io. [![crates.io](https://img.shields.io/badge/crates.io-latest-orange)](https://crates.io/crates/rapx)

## Features
# ![logo](https://raw.githubusercontent.com/safer-rust/RAPx/main/feature.png)
RAPx is structured into two layers: a core layer offering essential program analysis algorithms (e.g., alias and dataflow analysis), and an application layer implementing specific tasks such as bug detection. This separation of concerns promotes modular development and fosters collaboration between algorithm and application developers.

The project is still under heavy development. For further details, please refer to the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/).

## Quick Start

Install `nightly-2026-04-03` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2026-04-03 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2026-04-03 install rapx --git https://github.com/safer-rust/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2026-04-03 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2026-04-03
```

Check out supported options with `-help`:

```shell
$ cargo rapx --help

Usage: cargo rapx [OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]

Commands:
  analyze  perform various analyses on the crate, e.g., alias analysis, callgraph generation
  check    check potential vulnerabilities in the crate, e.g., use-after-free, memory leak
  opt      detect code optimization opportunities
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

  1. detect use-after-free and memory leak:
     cargo rapx check -f -m
  2. detect optimization opportunities:
     cargo rapx opt
  3. perform alias analysis:
     cargo rapx analyze alias
  4. verify annotated functions:
     cargo rapx verify --prepare-targets
```

### `analyze` command

```
Usage: cargo rapx analyze <COMMAND>

Commands:
  alias       alias analysis (meet-over-paths by default)
  adg         API dependency graphs
  callgraph   callgraph generation
  dataflow    dataflow graphs
  owned-heap  analyze heap-owning types
  paths       path-sensitive CFG paths
  range       range analysis
  scan        basic crate info
  mir         print MIR
  dot-mir     print MIR as DOT
  help        Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```

### `check` command

```
Usage: cargo rapx check [OPTIONS]

Options:
  -f, --uaf [<UAF>]    detect use-after-free/double-free (optional level, default 1)
  -m, --mleak          detect memory leakage
  -h, --help           Print help
```

### `opt` command

```
Usage: cargo rapx opt
```

### `verify` command

The `verify` command provides a contract-based verification pipeline for functions annotated with `#[rapx::verify]`. It uses path-sensitive backward/forward analysis and Z3-based SMT solving to prove safety properties.

```
Usage: cargo rapx verify [OPTIONS]

Options:
      --prepare-targets            identify #[rapx::verify] functions and list their safety contracts
      --postfix-repeat <N>       number of extra SCC postfix repetitions during path enumeration (default 0)
      --mode <MODE>               verification mode: scan, targeted, invless (default scan)
  -h, --help                      Print help
```

Verification modes:
- `scan` — auto-detect: verify all functions with unsafe callees or struct invariants
- `targeted` — only verify functions annotated with `#[rapx::verify]`
- `invless` — verify without struct invariants as pre/post-conditions, deriving safety requirements automatically from the safety flow graph

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

#[rapx::requires(NonNull(_ptr))]
unsafe fn custom_ptr_op(_ptr: *const i32) -> i32 {
    unsafe { *_ptr }
}
```

Safety properties include: `Align`, `NonNull`, `Allocated`, `InBound`, `Init`, `ValidPtr`, `Deref`, `Ptr2Ref`, and more. See the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/) for the full list.

### Verification Property Support Checklist

This checklist maps RAPx's contract verification to the [Primitive Safety Properties](https://github.com/safer-rust/safety-tags/blob/main/primitive-sp.md) defined in `safer-rust/safety-tags`.

> **Legend**: ✅ = full Z3-based SMT verification (produces SOUND/UNSOUND verdicts)　— = not yet verified (parsed but no SMT lowering)

| Primitive SP                 | RAPx tag       | Supported |
|------------------------------|----------------|:---------:|
| Align(p, T)                  | `Align`        |     ✅    |
| Size(T, c)                   | `Size`         |     ✅     |
| !Padding(T)                  | `NoPadding`    |     —     |
| !Null(p)                     | `NonNull`      |     ✅    |
| Allocated(p, T, len, A)      | `Allocated`    |     ✅    |
| InBound(p, T, len)           | `InBound`      |     ✅    |
| !Overlap(dst, src, T, len)   | `NonOverlap`   |     ✅     |
| ValidNum(exp, vrange)        | `ValidNum`     |     ✅    |
| ValidString(arange)          | `ValidString`  |     —     |
| ValidCStr(p, len)            | `ValidCStr`    |     —     |
| Init(p, T, len)              | `Init`         |     ✅    |
| Unwrap(x, T)                 | `Unwrap`       |     —     |
| Typed(p, T)                  | `Typed`        |     ✅     |
| !Owned(p)                    | `Owning`       |     —     |
| Alias(p1, p2)                | `Alias`        |     ✅    |
| Alive(p, l)                  | `Alive`        |     ✅     |
| Pinned(p, l)                 | `Pinned`       |     —     |
| !Volatile(p, T, len)         | `NonVolatile`  |     —     |
| Opened(fd)                   | `Opened`       |     —     |
| Trait(T, trait)              | `Trait`        |     —     |
| !Reachable()                 | `Unreachable`  |     —     |
| ValidPtr(p, T, len)          | `ValidPtr`     |    ✅¹   |
| Deref(p, T, len)              | `Deref`        |     ✅     |
| Ptr2Ref(p, T)                 | `Ptr2Ref`      |     —     |
| Layout(p, layout)             | `Layout`       |     —     |

> ¹ **ValidPtr** is decomposed into primitive SMT obligations (`NonNull`, `Align`, `Allocated`, `InBound`, `Init`). Each primitive is checked individually; however the composite verdict remains `Unknown` until all sub-properties (including `Typed`) are fully lowered. The decomposition results are reported as diagnostic notes.

RAPx ships with a curated set of `std` library safety contracts (`std-contracts.json`) that annotate standard library functions with property tags. This enables contract-based verification for common `std`/`core` APIs without requiring user annotations.

### Environment Variables (values are case insensitive)

| var             | default when absent | possible values     | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAPX_LOG`       | info                | trace, debug, info, warn | verbosity of logging   |
| `RAPX_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAPX_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |
| `RAPXFLAGS`      | (unset)             | CLI arguments       | arguments passed to `rapx` binary directly |

For `RAPX_RECURSIVE`:
* `none`: check for current folder
* `shallow`: check for current workspace members
* `deep`: check for all workspaces from current folder

NOTE: for `shallow` or `deep`, rapx will enter each member folder to do the check.

If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`.

