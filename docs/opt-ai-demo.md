# opt presentation: suggested two-page allocation

Use these two pages within the team's 12-page presentation to explain opt
evidence, AI review, and validation.

## Page 1: review optimization candidates with evidence

Main diagram:
`Rust source -> RAPx opt -> structured candidates -> AI review -> original evidence + advice + validation plan`.

Focus on three points:

1. Rust static analysis locates candidates and exports function source,
   precise locations, and static evidence.
2. AI assigns keep / suspected false positive / insufficient evidence,
   explains its reasoning, and proposes optimizations and validation steps.
3. Original warnings remain available. AI is not a safety proof, and offline
   and error states are explicitly reported.

Suggested narration (about 45 seconds):

> I am responsible for opt. Our goal is to turn optimization warnings into advice
> that developers can inspect. RAPx first runs its existing static analysis, then
> exports candidates with source context. The new opt-ai command asks the model
> to review each candidate and produce a report. The report retains both the
> static finding and the AI opinion, so a suspected false positive does not erase
> the original evidence. Without an API key, we can export the evidence offline
> and let an assistant review it using the companion skill.

Place `cargo rapx opt-ai` and one report screenshot at the bottom of the page.
Avoid explaining all six rule categories individually.

## Page 2: a reproducible optimization using safe Rust

Show the key code side by side:

```rust
// Before: removing the first Vec element shifts the remaining elements.
output.push_str(&parts.remove(0));
// After: consume a FIFO container from the front, preserving fragment order.
while let Some(part) = queue.pop_front() {
    output.push_str(&part);
}
```

Use a three-step diagram:
`Candidate and reasoning -> safe rewrite -> correctness tests + another opt run`.

Populate the comparison table with results from the actual demo run:

| Item | Before | After |
|---|---|---|
| Vec front-removal candidates | Script asserts 1 | Script asserts 0 |
| Agreement with the concat reference | Checked by running tests | Checked by running tests |
| Inputs | 343 short-string combinations, empty input, and growth to 1,000 fragments | Same inputs |
| Performance improvement | Not measured in this demo | Do not report a speedup factor |

Attach the `result.json` produced by `demo_opt_ai.py`; this table alone is not
evidence that the demo ran. The two implementations were written manually in
advance and selected by a feature. Do not describe them as a successful
automatically generated model patch. To demonstrate real AI review, run the
script with `--api` against the team's configured provider and show the actual
response. Do not present mock responses as real model output.

Suggested narration (about 50 seconds):

> This example joins fragments in FIFO order. Removing each first element from
> a Vec shifts the remaining elements. opt identifies that pattern. During review,
> we check whether the caller depends on contiguous storage, indexing, or other
> Vec behavior. This local FIFO use case can use VecDeque. We compare both
> implementations on the same inputs and run opt again to confirm that the
> candidate disappears. Passing tests and removing a warning provide limited
> evidence; actual speedups still require release-mode benchmarks. Our contribution
> is evidence export, review, and reporting. The candidate detection rule already
> existed before this work.

Run the demo from the repository root:

```bash
python3 tools/opt/demo_opt_ai.py --cargo-rapx "$PWD/target/debug/cargo-rapx"
```

Keep the original opt advice and the model's opinion separate. Reviewers should
correct inaccurate API names and check whether advice fits the actual use case.
A single `remove(0)` call does not establish that switching containers will be faster.
