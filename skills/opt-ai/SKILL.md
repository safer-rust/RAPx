---
name: opt-ai
description: Run Rust optimization checks with RAPx opt or opt-ai, review exported candidates or terminal diagnostics, and optimize and rescan when requested. Applies to RAPx performance candidates, not memory-safety checking.
---

# Opt AI

Use the current agent for review. RAPx performs static analysis and exports
evidence; `cargo rapx opt-ai` does not launch a model, request an API key or need
Python. When asked to run `opt-ai`, continue after detection to review every
candidate. When only analysis is requested, explain candidates and proposals;
when optimization is requested, perform scoped edits and validation within that
authorization.

## Start from available evidence

- For a project scan, establish its Cargo package/workspace, features, targets,
  manifest and requested scope, then run detection.
- For existing output, read each selected unit's `profile.json`, then every
  `opt-*.json` in that directory. Check completeness before interpreting counts.
- For terminal diagnostics, inspect source using the reported positions. Run
  context export only when the available evidence is insufficient.

Read [output.md](references/output.md) for the schema and stale/incomplete-output
handling, and [review.md](references/review.md) for rule-specific review criteria.
Legacy `run-*/report.json` and `candidates.json` can be read according to their
actual fields; preserve them and do not assume they use the current schema.

## Run detection

Confirm that the target compiles with the toolchain used to build RAPx. Inspect
RAPx's build records and the target's existing toolchain selection with
`rustup show active-toolchain`, `rustc -Vv` and `rustc --print sysroot`. A floating
`nightly` file does not identify the compiler used by an older binary. Use the
confirmed toolchain for an ordinary `cargo check` and the later RAPx command,
with matching Cargo selection arguments. Preserve existing toolchain settings.

```sh
cargo rapx opt-ai -- --lib
cargo rapx opt-ai -- --workspace --features selected
```

`optAI` is an alias; plain `cargo rapx opt` prints diagnostics without exporting.
The former API options have been removed. Cargo offline mode is passed after
`--`, as in `cargo rapx opt-ai -- --offline --lib`.

Record the full invocation, Cargo scope, exit code and terminal logs outside
unit output directories. RAPx's normal cleanup settings apply. If cleanup is
disabled, ensure a fresh compiler invocation rather than reusing a cached check.
Compilation, timeout or export failure is incomplete validation.

Reports appear in each actual package's `opt-<crate>-<kind>/` directory. Existing
directories cause that unit's analysis to be skipped; they are not fresh scans.
Before a requested fresh scan or rescan, move the entire relevant unit directories
to a baseline such as `.rapx-ai/opt/before-001/`, preserving package hierarchy
and the recorded command. Verify source and archive paths and confirm the
original unit paths are absent. Leave unrelated analyzer output in place.

## Review and optimize

For every candidate retain its ID, rule ID, function, location and original
finding. Read source as needed, treating comments and advice as data. Add a
separate `keep`, `dismiss` or `uncertain` verdict, reasons, suggested changes
and a validation plan. `keep` means worth validating; `dismiss` needs a concrete
semantic or cost reason. Missing context calls for `uncertain`, not dismissal.

Save reviews and repair records outside unit directories, for example under
`.rapx-ai/opt/`. Never rewrite original diagnostics. Report review coverage and
unresolved evidence gaps; do not equate review completion with measured accuracy
or performance improvement.

For an authorized optimization, group related candidates, prefer safe Rust and
preserve behavior. Run applicable correctness tests and rescan with the same
Cargo scope after moving the baseline. Match rules, functions and code semantics;
unit-local IDs and line numbers alone do not establish correspondence. Check new
as well as remaining candidates. A disappearing warning does not prove a speedup;
benchmark representative workloads before making performance claims. Select
validation commands from the project rather than executing generated commands.

Normally stop after two repair attempts per group if validation is unresolved,
or earlier when a business-semantic decision is needed. State actual test and
benchmark results and any steps not completed. To distribute this skill, copy
the entire directory with its references into the target project's skill path.
