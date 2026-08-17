
// ================ LinkedList NonNull Sound ================
#[test]
fn linked_list_nonnull() {
    let output = run_with_args("verify_cases/linked_list_nonnull", CMD_VERIFY_VM);
    for &func in &[
        "LinkedList::<T>::new",
        "LinkedList::<T>::len",
        "LinkedList::<T>::is_empty",
        "LinkedList::<T>::push_back",
        "LinkedList::<T>::pop_front",
        "LinkedList::<T>::pop_back",
        "LinkedList::<T>::clear",
        "LinkedList::<T>::from_vec",
        "LinkedList::<T: Copy>::front_copy",
        "LinkedList::<T: Copy>::back_copy",
        "LinkedList::<T: Copy>::front_mut_copy",
        "LinkedList::<T: Copy>::back_mut_copy",
        "<LinkedList<T> as std::ops::Drop>::drop",
    ] {
        assert_function_result(&output, func, "SOUND");
    }
}

// ================ LinkedList RawPtr Sound ================
#[test]
fn linked_list_rawptr() {
    let output = run_with_args("verify_cases/linked_list_rawptr", CMD_VERIFY_VM);
    for &func in &[
        "LinkedList::<T>::new",
        "LinkedList::<T>::len",
        "LinkedList::<T>::is_empty",
        "LinkedList::<T>::push_back",
        "LinkedList::<T>::pop_front",
        "LinkedList::<T>::pop_back",
        "LinkedList::<T>::clear",
        "LinkedList::<T>::from_vec",
        "LinkedList::<T: Copy>::front_copy",
        "LinkedList::<T: Copy>::back_copy",
        "LinkedList::<T: Copy>::front_mut_copy",
        "LinkedList::<T: Copy>::back_mut_copy",
        "<LinkedList<T> as std::ops::Drop>::drop",
    ] {
        assert_function_result(&output, func, "SOUND");
    }
}

// ================ LinkedList NonNull Unsound ================
#[test]
fn linked_list_nonnull_unsound() {
    let output = run_with_args("verify_cases/linked_list_nonnull_unsound", CMD_VERIFY_TARGETED_VM);
    for &func in &[
        "LinkedList::<T>::pop_front",
        "LinkedList::<T>::pop_back",
        "LinkedList::<T>::front",
        "LinkedList::<T>::back",
        "LinkedList::<T>::front_mut",
        "LinkedList::<T>::back_mut",
    ] {
        assert_function_result(&output, func, "UNSOUND");
    }
}

// ================ LinkedList RawPtr Unsound ================
#[test]
fn linked_list_rawptr_unsound() {
    let output = run_with_args("verify_cases/linked_list_rawptr_unsound", CMD_VERIFY_TARGETED_VM);
    for &func in &["LinkedList::<T>::front", "LinkedList::<T>::back"] {
        assert_function_result(&output, func, "UNSOUND");
    }
    for &func in &[
        "LinkedList::<T>::pop_front",
        "LinkedList::<T>::pop_back",
        "LinkedList::<T>::front_mut",
        "LinkedList::<T>::back_mut",
    ] {
        assert_unproved_exclusive_with_result(&output, func, &["Alias", "Or"], "UNSOUND");
    }
}

// ================ Std Challenge Cases ================
#[test]
fn std_challenge_01() {
    let output = run_with_args("verify_cases/std-challenge-01", CMD_VERIFY_TARGETED_VM);
    // Challenge 1 (core transmuting methods): 44 functions are verified.
    // 43 are SOUND; the single UNSOUND one — `filter_map_next_chunk_ext` — is
    // asserted precisely below and correctly reports std's real soundness bug
    // rust-lang/rust#153803 (buffer overrun when N == 0).
    let sound = output.matches("result: SOUND").count();
    let unsound = output.matches("result: UNSOUND").count();
    assert_eq!(
        sound, 43,
        "expected 43 SOUND functions, got {sound}\n{output}"
    );
    assert_eq!(
        unsound, 1,
        "expected exactly 1 UNSOUND function (filter_map_next_chunk_ext)\n{output}"
    );

    // Regression: `filter_map_next_chunk_ext` exercises three RAPx fixes.
    //
    //   1. `is_slice_get_unchecked` must match `::<impl [T]>::get_unchecked_mut`.
    //      Otherwise `get_unchecked_mut` is classified as unsupported and gets
    //      inlined, so `MaybeUninit::write` loses the array's provenance and the
    //      `assume_init_read` checkpoint degrades to `Init | Unknown`.
    //   2. `ensure_local_allocation` must size `[MaybeUninit<T>; N]` by the
    //      symbolic element count `N` (instead of collapsing to 1 byte), so
    //      `len() = size / elem_size` stays equal to `N`.
    //   3. `check_in_bound_slice` must assert the accumulated path conditions,
    //      so the loop-carried `idx < N` guard discharges `idx + 1 <= N`.
    //
    // After these fixes the only remaining unproved obligations are the three
    // first-iteration `InBound | Failed` reports, which correctly flag std's
    // real soundness bug rust-lang/rust#153803 (buffer overrun when N == 0).
    let block = extract_block_after(&output, "function: filter_map_next_chunk_ext");
    assert_not_contain(&block, "Init | Unknown");
    assert_not_contain(&block, "Init | Failed");
    // After the three fixes the only remaining unproved obligations are the
    // three first-iteration `InBound | Failed` reports (N == 0 buffer overrun,
    // std #153803). Count actual failures by summing the `(xN)` multiplicities
    // rather than matching the folded row count.
    let in_bound_failed: usize = block
        .lines()
        .filter(|l| l.contains("InBound | Failed"))
        .map(|l| {
            l.split("(x")
                .nth(1)
                .and_then(|s| s.split(')').next())
                .and_then(|n| n.parse::<usize>().ok())
                .unwrap_or(1)
        })
        .sum();
    assert_eq!(
        in_bound_failed, 3,
        "expected exactly the 3 N == 0 first-iteration InBound failures\n{block}"
    );
}

#[test]
fn std_challenge_17() {
    let output = run_with_args("verify_cases/std-challenge-17", CMD_VERIFY_TARGETED_VM);
    assert!(
        !output.contains("UNSOUND"),
        "unexpected UNSOUND in std-challenge-17"
    );
}

#[test]
fn std_challenge_18() {
    let output = run_with_args("verify_cases/std-challenge-18", CMD_VERIFY_TARGETED_VM);
    assert!(!output.contains("UNSOUND"), "unexpected UNSOUND in std-challenge-18");
}

#[test]
fn std_challenge_02() {
    let output = run_with_args("verify_cases/std-challenge-02", CMD_VERIFY_TARGETED_VM);
    assert!(
        !output.contains("UNSOUND"),
        "unexpected UNSOUND in std-challenge-02"
    );
}

#[test]
fn std_challenge_03() {
    let output = run_with_args("verify_cases/std-challenge-03", CMD_VERIFY_TARGETED_VM);
    assert!(
        !output.contains("UNSOUND"),
        "unexpected UNSOUND in std-challenge-03"
    );
}

// ================ Std Challenge 04 (BTree node) ================
#[test]
fn std_challenge_04() {
    let output = run_with_args("verify_cases/std-challenge-04", CMD_VERIFY_TARGETED_VM);

    // Challenge 4 (`alloc::collections::btree::node`): a faithful, self-contained
    // port of `library/alloc/src/collections/btree/node.rs`. The helper slice
    // primitives / constructors / getters keep their `#[rapx::requires]`
    // contracts and are inlined at the call sites of the `#[rapx::verify]`
    // functions, which must all verify SOUND.
    assert_not_contain(&output, "result: UNSOUND");
}

// ================ Std Challenge 05 (LinkedList) ================
#[test]
fn std_challenge_05() {
    let output = run_with_args("verify_cases/std-challenge-05", CMD_VERIFY_TARGETED_VM);

    // Challenge 5 (`alloc::collections::linked_list`): a faithful, self-contained
    // port of the doubly-linked list. The challenge functions that iterate over
    // the inductive node structure (`clear`, `contains`, `split_off`, `remove`,
    // `retain`, `extract_if`) must all verify SOUND for linked lists of arbitrary
    // shape, together with the `Iter`/`IterMut`/`CursorMut`/`ExtractIf` machinery
    // they are built from.
    assert_not_contain(&output, "result: UNSOUND");
}

// ================ Std Challenge 06 (NonNull) ================
#[test]
fn std_challenge_06() {
    let output = run_with_args("verify_cases/std-challenge-06", CMD_VERIFY_TARGETED_VM);

    // Challenge 6 (`core::ptr::NonNull`): a faithful, self-contained port of
    // `library/core/src/ptr/non_null.rs`.  All 48 listed functions verify
    // SOUND for generic `T`.
    assert_not_contain(&output, "result: UNSOUND");
}

// ================ HashMap Tests ================
#[test]
fn hashmap() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_TARGETED_VM);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn hashmap_skip_invariant() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_TARGETED_SKIP_INVARIANT_VM);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

// ================ Allocator Tests ================
#[test]
fn bump_allocator() {
    let output = run_with_args("verify_cases/bump_allocator", CMD_VERIFY_VM);
    assert_function_result(&output, "BumpAllocator::new", "SOUND");
    assert_function_result(&output, "BumpAllocator::alloc", "SOUND");
    assert_function_result(&output, "BumpAllocator::reset", "SOUND");
}

#[test]
fn free_list_allocator() {
    let output = run_with_args("verify_cases/free_list_allocator", CMD_VERIFY_VM);
    assert_not_contain(&output, "result: UNSOUND");
}
