
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
