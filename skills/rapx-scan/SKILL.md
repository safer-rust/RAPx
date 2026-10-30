---
name: rapx-scan
description: Run RAPx scan to inventory a Rust crate before deeper analysis — reports crate name, crate type, and four counts (total/generic/unsafe APIs, unsafe blocks). Applies to crate-level inventory only, not vulnerability detection, verification verdicts, or optimization advice.
---

# RAPx scan

## When to use

- Starting on a crate: run this first to get its public API size and unsafe footprint, then pick a
  deeper analysis.
- Comparing one crate before and after a change: same command, same crate root, compare the four
  numbers.

## How to run

From the root of the crate under analysis:

```shell
cargo rapx analyze scan 2>&1
```

Results are written to stderr only; stdout stays empty, so the stderr redirect above is required.
The output carries terminal color codes, so strip them before parsing.

Read the values by label: `# total api`, `# generic api`, `# unsafe api`, `# unsafe block`.

Logging keeps the default level. `RAPX_LOG=TRACE` is available when you want to check the arguments
passed through; do not use `RAPX_LOG=DEBUG`, it panics and aborts the whole run. No per-function log
level is currently safe to enable.

## What you get

The output has a fixed shape:

```
======== crate info ========
name: <crate name>
type: <crate type>
============================

======== API info ========
# total api    = N
# generic api  = N
# unsafe api   = N
# unsafe block = N
============================
```

The four counts:

- `total api`: number of public APIs, including ones re-exported via `pub use`; every function with a
  body counts, while trait methods that only declare a signature without a body do not.
- `generic api`: of those, how many are generic functions; included in `total api`.
- `unsafe api`: of those, how many are declared `unsafe fn`; private unsafe functions are not
  counted.
- `unsafe block`: number of `unsafe {}` blocks in the crate, counted across modules and regardless of
  visibility.

Caveats when reading them:

- `total api` is at least 2: each run adds two RAPx helper functions, so subtract 2 to get the count
  of your own APIs.
- `type:` reports only the first crate type; a crate declaring several types (e.g. `lib` plus
  `cdylib`) shows just one of them.
- `unsafe api` being 0 does not mean the crate has no unsafe code: private unsafe functions are not
  counted, but their `unsafe {}` blocks are.

Record the crate name, the type and the four numbers for later analysis, keeping the `total api`
offset in mind.
