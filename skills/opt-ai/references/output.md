# Output protocol

Each compilation unit writes to `<package>/opt-<crate>-<kind>/`. The shared check
driver identifies `lib`, `bin`, `lib-test`, `bin-test` and `integration-test`
units. Unsupported or mixed crate types fail unit identification. Separate
workspace packages keep separate directories even if their crate names match.

Read `profile.json` first and enumerate all `opt-*.json` in the same directory.
The profile is written last; a missing or invalid profile means incomplete
output. Check the top-level exit code and invocation as well. An existing output
directory causes analysis to be skipped without replacing its contents, so its
old profile cannot establish that a new command analyzed anything.

## Profile

- `schema_version`: currently 1.
- `unit`: crate name and target kind.
- `rapx_version`, `rustc_version`, `working_directory`: recorded environment.
- `status`: `completed` when at least one function was analyzed, or `skipped`
  when none was analyzed. Neither is a proof of complete optimization coverage.
- `level`: currently 1 through both CLI entries.
- `no_std`: only the bounds category runs for these units.
- `analyzed_functions`: actual number of user function graphs checked, including
  related closure graphs and excluding RAPx's two injected helper functions.
- `finding_count`: number of independent candidate files.
- `statistics`: six site counts in this order: bounds, encoding, suboptimal,
  initialization, reallocation, cloning. Grouped reports can cover multiple sites.
- `limitations`: observed events, omitted if empty. `core_crate_unavailable` and
  `no_functions_analyzed` explain skipped analysis; entries such as
  `<id>: source_location_unavailable` mark incomplete source mappings.

Zero candidates are meaningful only with a fresh completed profile, positive
function count, matching scope and successful command. Reports do not record
the Cargo invocation or full selection settings; retain these separately.

## Candidate files

Each `opt-<unit>-<index>.json` is one original report and contains:

- `id`: identity within the unit/run, matching the filename; not a stable hash.
- `rule_id`, `category`, `function`: stable rule name, six-category grouping and
  full owning function name.
- `title`, `level`: original diagnostic wording and severity.
- `file`, `line_start`, `source`: the displayed function or loop snippet.
- `annotations`: each has `file`, one-based `line`, `level`, `label` and
  `range: {start, end}`. Ranges are UTF-8 byte offsets into `source`, with an
  exclusive end. `0..0` is unmapped, not an exact event location.
- `static_advice`: original advice, which may be too broad or use inaccurate
  names; `static_status` is `optimization_candidate`.

One JSON object may annotate several positions. Source may include inactive cfg
branches, and macro locations may be incomplete. No MIR, dataflow slice, symbolic
proof or performance measurement is exported. Supplement source evidence or
record uncertainty rather than reconstructing nonexistent detector facts.

Keep later review verdicts, patches and test records outside these directories.
Before a fresh scan, move the whole relevant directories to an archive. Retain
package hierarchy in workspaces to avoid collisions, and check that the original
paths no longer exist. Match before/after candidates using rule, function and
semantics rather than the sequential ID or only finding counts.
