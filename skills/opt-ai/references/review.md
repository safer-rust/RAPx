# Review criteria and detection boundaries

Both CLI commands select level 1. The following stable rule IDs describe existing
heuristics; export has not strengthened them.

| Category | Rule IDs | Scope |
|---|---|---|
| Bounds | `bounds_len`, `bounds_loop_push`, `bounds_extend` | Only `bounds_len` at level 1; loop push and extend need higher level |
| Encoding | `vec_encoding`, `array_encoding`, `string_push`, `string_lowercase` | Enabled for std units |
| Containers | `vec_remove`, `slice_contains`, `participant` | Only `vec_remove` at level 1 |
| Initialization | `local_set`, `vec_init` | Both require level 2 |
| Reallocation | `unreserved_hash`, `unreserved_vec`, `flatten_collect` | Enabled for std units; some extra Vec checks require level 2 |
| Cloning | `used_as_immutable` | Enabled for std units with heuristic filters |

For `no_std`, only bounds checks run. The tool does not currently expose a level
CLI parameter. A zero initialization count at level 1 is not evidence that all
initialization opportunities were checked.

- **Bounds:** inspect the actual indexed container, index, length relation,
  mutation, aliasing and paths. A recognized range or guard is not by itself a
  proof that an unchecked replacement is valid. Prefer safe restructuring.
- **Encoding:** the constant-origin helper looks for `u8` constants; this is not
  full UTF-8 validation. `string_lowercase` matches the call without proving
  ASCII-only input. Preserve Unicode, Result/Cow, error and panic semantics.
  AI judgment does not discharge unsafe preconditions.
- **Containers:** `vec_remove` also covers inserting at index zero. Check FIFO
  use, ordering, indexing, contiguous storage and workload size before suggesting
  VecDeque. The original advice says "VecQueue"; explain the correct API while
  preserving the diagnostic. Consider setup and conversion costs as well.
- **Initialization:** allocation reuse must preserve ownership and lifetimes;
  removing initialization requires evidence that every subsequently read element
  is initialized. Prefer safe APIs and scoped reuse.
- **Reallocation:** `unreserved_vec` primarily considers loops with one recognized
  push and searches for upstream capacity reservation. `unreserved_hash` looks
  for creation followed by insert/entry; it does not estimate workload size.
  `flatten_collect` recognizes a call pattern. Check size hints, capacity growth,
  peak memory and iterator behavior before accepting suggested replacements.
- **Cloning:** check all uses, ownership transfer, mutation, lifetimes, and Clone
  side effects. The checker follows a use as a call argument and uses signature
  and name filters; it does not prove all uses can borrow. Ordinary String
  concatenation does not necessarily copy the entire existing prefix.

Use `keep` for a plausible opportunity worth validating, `dismiss` for a concrete
reason the suggestion is unsuitable, and `uncertain` for missing evidence.
Record the exact source and assumptions that support the decision. Correctness
tests and a repeated scan validate limited aspects; performance claims need
representative release-mode benchmarks and their actual measurements.
