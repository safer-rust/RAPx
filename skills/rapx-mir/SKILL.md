---
name: rapx-mir
description: Use RAPx analyze mir and dot-mir to inspect Rust MIR bodies and control-flow graphs, including calls, drops, cleanup paths, and locals. Use when examining compiler lowering or checking MIR evidence for RAPx findings; the output alone is not a bug verdict, safety proof, or optimization recommendation.
---

# RAPx MIR

The provided command is based on linux environment.

## When to use

Use MIR inspection to understand where drops are inserted, how branches and loops
are lowered, which calls occur, and how cleanup paths relate to an existing
SafeDrop, rCanary, or opt finding. Use `dot-mir` when a control-flow graph helps
explain the result.

The Rust commands export textual MIR or CFG images. They do not currently expose
a per-function filter, aggregate statistics, rankings, or a JSON metrics format.
Keep a large dump on disk and read the bodies relevant to the task rather than
loading the entire crate's MIR into the model context.

## Prerequisites

Use `cargo-rapx` and `rapx` from the same build. The target crate and its
dependencies must compile with the toolchain used to build those binaries.
Check `rustup show active-toolchain`, `rustc -Vv`, and `rustc --print sysroot` in
the relevant directories, and confirm the binary's build toolchain. A floating
`nightly` selection does not identify the compiler used for an older binary.

The examples below use a confirmed `nightly`; replace it with the actual RAPx
build toolchain. Use that toolchain for an ordinary `cargo check` with the same
packages, features, manifest, and targets before running RAPx. Preserve existing
project toolchain settings.

The current output includes `MIR [kind]` body headers. If these are missing,
check whether the installed binary matches the expected implementation. When a
local build is needed, build RAPx and add its binary directory to PATH for the
invocation. Do not replace a user's global installation merely to inspect MIR.

## Run the Rust commands

From the target crate directory, save stderr to a log. Limit Cargo to one job
so parallel workspace compilations do not interleave their MIR output.

```sh
CARGO_BUILD_JOBS=1 cargo +nightly rapx analyze mir 2> mir.log
cargo +nightly rapx analyze dot-mir
```

Put Cargo selection arguments after `--`, for example:

```sh
cargo +nightly rapx analyze mir -- --manifest-path path/to/Cargo.toml --lib
```

Apply the same single-job setting when analyzing a workspace. Record the actual
command, toolchain, scope, and exit status. RAPx's normal build cleanup settings
apply; if cleanup is disabled, confirm that compilation really invoked RAPx.
A failed command or a missing dump does not mean the crate has no MIR bodies.

`dot-mir` uses Graphviz's `dot` to write PNGs under `MIR_dot_graph/` in the analysis
process's working directory. If rendering fails or Graphviz is unavailable, the
renderer attempts to keep the DOT source there and prints a warning. Check the
actual output files and warning before claiming graph generation succeeded.

## Find and read a body

Search the saved log for the reported function name or a `MIR [kind]` header.
For example, using ripgrep:

```sh
rg -n -F 'Buf::push' mir.log
```

This locates text matches, including possible call sites; identify the matching
body header and read through to the next body header. Use the full function path
and crate identity to distinguish similarly named bodies. Include relevant
closure or async bodies when the source operation is lowered into one of them.
Logs may contain ANSI color codes, Cargo messages, and timestamp prefixes.

For a diagnostic, inspect the referenced local and basic block, then read its
predecessors, successors, calls, drops, and cleanup blocks as needed. A matching
line is an entry point for inspection, not proof of a complete execution path.

## Output format and implementation

`rapx/src/helpers/show_mir.rs` iterates over `tcx.mir_keys(())` and reads each
local body's `tcx.instance_mir(InstanceKind::Item(def_id))`. It skips RAPx's
`__raw_ptr_deref_dummy` and `__static_mut_deref_dummy` helper functions.
RAPx configures `-Zmir-opt-level=0`; inspect the resulting lowered MIR rather
than assuming it is identical to source syntax.

The body header, local declarations, and basic blocks are logged separately.
Log messages carry a prefix such as `HH:MM:SS|RAPx|INFO|: ` and may include color.
For example, after removing the log prefix and color:

```text
MIR [method] Buf::push (DefId(0:9 ~ mir_demo[72e4]::{impl#0}::push))
_0: bool
_1: &mut Buf @ self
_2: u8 @ b
bb 0 {
CleanUp: false
    _6 = &((*_1).0: std::vec::Vec<u8>) @ Assign(Ref)
    _5 = std::vec::Vec::<u8>::len(move _6) -> [return: bb1, unwind continue] @ Call: std::vec::Vec::<T, A>::len #3:9869
}
```

- **Header:** `MIR [kind] path (DefId)`. Kinds come from rustc's `def_descr`, such
  as `function`, `method`, `associated_function`, `closure`, `async_fn`,
  `constant`, `static`, and constructor kinds.
- **Locals:** `_i: type`, optionally followed by ` @ name`. `_0` is the return
  slot; subsequent argument locals precede temporaries.
- **Basic blocks:** `CleanUp: true` identifies an unwind cleanup block. Statements
  have kind annotations; the final instruction is the terminator, such as
  `Goto`, `SwitchInt`, `Call`, `Return`, `Drop`, or `Assert`. Unsupported kind
  descriptions may appear as `Other`.
- **Calls:** `Call: <callee path> #<crate>:<index>` identifies a direct callee;
  `Call: <indirect>` denotes a function-pointer call. Crate number 0 identifies
  the local crate. Trait method paths do not by themselves resolve virtual
  dispatch to a concrete implementation.

## Interpretation and reporting

- Coverage is limited to Cargo-selected primary crates, not their dependencies;
  distinguish workspace members and compilation targets.
- Bodies are polymorphic, not monomorphized. Closures, async bodies, constants,
  and constructors can appear separately from their source-level parent.
- A dereference such as `(*_k)` is not necessarily a raw-pointer operation. Check
  the local's declared type and compiler lowering; references and lowered Box
  operations also involve dereferences.
- Unsafe operations through APIs such as `ptr::read`, `ptr::write`,
  `copy_nonoverlapping`, or `set_len` appear as calls. Direct dereference counts
  alone would not describe the unsafe footprint.
- Casts, including transmutes, can be introduced by the compiler. Check operand
  types and source before attributing an operation to explicit unsafe code.
- `Assert` terminators can represent inserted bounds, overflow, null, alignment,
  or other checks. Their presence is not a proof that every unsafe precondition
  is enforced, and source-level `assert!` may lower to a panic call instead.
- rustc versions, features, targets, and build settings affect MIR. Preserve
  those choices when comparing dumps.

Report the toolchain and analysis scope, the relevant full body paths, and the
specific locals, blocks, calls, and drops supporting the explanation. Cite log
locations or saved graph files. Distinguish directly observed MIR facts from
inferences about source behavior. Do not claim that this command generated
statistics or metrics it does not export, or treat MIR inspection as a detector
verdict or a proven executable counterexample.
