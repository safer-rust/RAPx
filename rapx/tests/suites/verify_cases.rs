
#[test]
fn linked_list_nonnull() {
    let output = run_with_args("verify_cases/linked_list_nonnull", CMD_VERIFY);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn linked_list_nonnull_skip_invariant() {
    let output = run_with_args(
        "verify_cases/linked_list_nonnull",
        CMD_VERIFY_SKIP_INVARIANT,
    );
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn linked_list_rawptr() {
    let output = run_with_args("verify_cases/linked_list_rawptr", CMD_VERIFY);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn linked_list_rawptr_skip_invariant() {
    let output = run_with_args("verify_cases/linked_list_rawptr", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn std_challenge_17() {
    let output = run_with_args("verify_cases/std-challenge-17", CMD_VERIFY_TARGETED);

    let functions = [
        "<[T] as SliceExt<T>>::get_unchecked_ext",
        "<[T] as SliceExt<T>>::get_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::split_at_unchecked_ext",
        "<[T] as SliceExt<T>>::split_at_mut_unchecked_ext",
        "<[T] as SliceExt<T>>::swap_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_ext",
        "<[T] as SliceExt<T>>::as_chunks_unchecked_mut_ext",
        "<[T] as SliceExt<T>>::align_to_ext",
        "<[T] as SliceExt<T>>::align_to_mut_ext",
        "<[T] as SliceExt<T>>::get_disjoint_unchecked_mut_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_first_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::split_last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_ext",
        "<[T] as SliceSafeExt<T>>::last_chunk_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_ext",
        "<[T] as SliceSafeExt<T>>::as_chunks_mut_ext",
        "<[T] as SliceSafeExt<T>>::as_rchunks_ext",
        "<[T] as SliceSafeExt<T>>::split_at_checked_ext",
        "<[T] as SliceSafeExt<T>>::split_at_mut_checked_ext",
        "<[T] as SliceSafeExt<T>>::reverse_ext",
        "<[T] as SliceSafeExt<T>>::rotate_left_ext",
        "<[T] as SliceSafeExt<T>>::rotate_right_ext",
        "<[T] as SliceSafeExt<T>>::copy_from_slice_ext",
        "<[T] as SliceSafeExt<T>>::copy_within_ext",
        "<[T] as SliceSafeExt<T>>::swap_with_slice_ext",
        "<[T] as SliceSafeExt<T>>::binary_search_by_ext",
        "<[T] as SliceSafeExt<T>>::partition_dedup_by_ext",
        "<[T] as SliceSafeExt<T>>::get_disjoint_mut_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_ext",
        "<[T] as SliceSimdExt<T>>::as_simd_mut_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_ext",
        "<[[T; N]] as SliceArrayExt<T, N>>::as_flattened_mut_ext",
        "get_disjoint_check_valid_ext",
        "copy_from_slice_impl",
    ];

    for fn_name in &functions {
        assert_contain(&output, fn_name);
    }

    assert_eq!(
        output.matches("result: SOUND").count(),
        38,
        "expected 38 SOUND results"
    );
}

#[test]
fn std_challenge_18() {
    let output = run_with_args("verify_cases/std-challenge-18", CMD_VERIFY_TARGETED);
    assert!(
        !output.contains("UNSOUND"),
        "unexpected UNSOUND in std-challenge-18"
    );
}

#[test]
fn hashmap() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_TARGETED);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn hashmap_skip_invariant() {
    let output = run_with_args("verify_cases/hashmap", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "result: SOUND");
    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn std_challenge_02() {
    let output = run_with_args("verify_cases/std-challenge-02", CMD_VERIFY_TARGETED);

    let functions = [
        "copy_nonoverlapping",
        "copy",
        "swap",
        "swap_nonoverlapping",
        "mem_swap",
        "zeroed",
        "copy_from_slice",
        "size_of_val",
        "align_of_val",
        "min_align_of_val",
    ];

    for fn_name in &functions {
        assert_contain(&output, fn_name);
    }

    assert_not_contain(&output, "result: UNSOUND");
}

#[test]
fn bump_allocator() {
    let output = run_with_args("verify_cases/bump_allocator", CMD_VERIFY);
    assert_function_result(&output, "BumpAllocator::new", "SOUND");
    assert_function_result(&output, "BumpAllocator::alloc", "SOUND");
    assert_function_result(&output, "BumpAllocator::reset", "SOUND");
}

#[test]
fn free_list_allocator() {
    let output = run_with_args("verify_cases/free_list_allocator", CMD_VERIFY);
    assert_function_result(&output, "FreeListAllocator::new", "SOUND");
    assert_function_result(&output, "FreeListAllocator::alloc", "SOUND");
    assert_unproved_exclusive(&output, "FreeListAllocator::alloc_unsound", &["Align"]);
    assert_function_result(&output, "FreeListAllocator::dealloc", "SOUND");
    assert_function_result(&output, "FreeListAllocator::merge", "SOUND");
}
