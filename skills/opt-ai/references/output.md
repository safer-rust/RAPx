# Output protocol

## Shared reading rules

The current SafeDrop, rCanary, and opt exports share a profile header and a
`finding` object in every candidate file. Read them in this order:

1. Verify this invocation's exit status and scope, then read its fresh
   `profile.json`. Missing or invalid profiles indicate incomplete output.
2. Read `analyzer` and choose the filename prefix below. Check that `unit`,
   versions, working directory, status, and limitations match the intended run.
3. Enumerate the analyzer's candidate files in the same directory. Their number
   must equal `finding_count`. Read each file's `finding`, verify that its ID
   matches the filename stem, and reject duplicate or mismatched IDs.
4. For SafeDrop and rCanary, require `finding.function_id` to equal the
   top-level `function.id` before using its source or MIR. The ID is a compiler
   definition index unique only within this unit/run; names can repeat. Use
   `function.location` to locate the definition. Opt embeds its source in the
   candidate and does not use this context map or these body-ID fields.
5. Read the analyzer-specific evidence described below. Count and ID agreement
   are output-consistency checks, not proof of fresh execution, correct evidence
   contents, or complete analysis coverage.

| `analyzer` | Candidate files | Additional evidence |
| --- | --- | --- |
| `safedrop` | `sd-<unit>-<index>.json` | Top-level `function`; release/use sites and witness in `finding` |
| `rcanary` | `rc-<unit>-<index>.json` | Top-level `function`; return sites, locals and solver evidence in `finding` |
| `opt` | `opt-<unit>-<index>.json` | Source, annotations and static advice inside `finding` |

The common profile fields are `analyzer`, `unit`, `rapx_version`,
`rustc_version`, `working_directory`, `status`, `analyzed_functions`,
`finding_count`, and optional `limitations`. Analyzer-specific profile fields
remain at the same JSON level. `rustc_version` is a best-effort query of
`rustc --version` on PATH; use build records to establish binary compatibility.
No schema-version field or top-level Cargo command is exported.

`completed` means analysis completed within that analyzer's model; `partial`
means known coverage loss; `skipped` means no functions were analyzed. All three
statuses use the same vocabulary, but opt currently emits only `completed` or
`skipped`. Function counts reflect each detector's traversal: opt excludes the
two injected helpers, while other analyzers retain their existing filtering.
Do not compare those counts as identical coverage measurements across detectors.
Zero findings are meaningful only with fresh completed output, positive analyzed
function count, matching scope, and successful execution. Read `limitations`
even when status is `completed`.

Older SafeDrop/rCanary reports may lack `function_id`, `function.id`, and the
context definition location. Some keyed context by the display name and can
associate a candidate with the wrong same-named body. Verify definition locations,
source, and MIR locals before relying on old context. A source-file digest does
not distinguish bodies in one file. If the required context was overwritten,
collect fresh reports after rebuilding RAPx or retain `inconclusive`; do not
select context solely by name.

Older reports may lack `analyzer` or `finding_count`; older opt profiles may
include `schema_version`, and their candidate files may be flat JSON objects.
Read these according to their actual fields and provenance, state any completion
checks that cannot be performed, and preserve the originals. Do not infer a
current-format zero-finding scan from missing fields.

Each compilation unit writes to `<package>/opt-<crate>-<kind>/`. The shared check
driver identifies `lib`, `bin`, `lib-test`, `bin-test` and `integration-test`
units. Unsupported or mixed crate types fail unit identification. Separate
workspace packages keep separate directories even if their crate names match.

Read `profile.json` first and enumerate all `opt-*.json` in the same directory.
The profile is written last; a missing or invalid profile means incomplete
output. Check the top-level exit code and invocation as well. An existing output
directory (even an empty one), or a file occupying the path, fails the command
with a nonzero exit status without replacing existing contents. Its old profile
cannot establish that a new command analyzed anything.

## Profile

- `analyzer`: `opt`.
- `unit`: crate name and target kind.
- `rapx_version`, `rustc_version`, `working_directory`: recorded environment.
- `status`: uses the common status vocabulary; currently `completed` when at
  least one function was analyzed, or `skipped` when none was analyzed. Neither
  is a proof of complete optimization coverage.
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

Each `opt-<unit>-<index>.json` contains one top-level `finding` object.
The fields below are inside `finding`; no empty or fabricated MIR context is
added. Older exports may instead have these fields at the file root.

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
