#![allow(dead_code)]

// The second backedge repeats the same block sequence, but its next transition
// exits the loop. A repetition budget must not discard that feasible exit.
fn two_iterations() -> usize {
    let mut i = 0usize;
    while i < 2 {
        i += 1;
    }
    i
}
