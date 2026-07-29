
// ================ Align Unsound Cases =============
#[test]
fn align_unsound_cases() {
    verify_unsound!("verify_units/align_unsound_1",  "unsound_enum_paths_inside_scc", "Align");
    verify_unsound!("verify_units/align_unsound_2",  "unsound_scc_selects_mixed_source", "Align");
    verify_unsound!("verify_units/align_unsound_3",  "unsound_scc_computes_misaligned_offset", "Align");
    verify_unsound!("verify_units/align_unsound_4",  "unsound_nested_scc_controller", "Align");
    verify_unsound!("verify_units/align_unsound_5",  "unsound_iteration_count_can_leave_unaligned", "Align");
    verify_unsound!("verify_units/align_unsound_6",  "unsound_pre_scc_guard_overwritten_by_scc", "Align");
    verify_unsound!("verify_units/align_unsound_7",  "unsound_scc_guard_only_on_one_branch", "Align");
    verify_unsound!("verify_units/align_unsound_8",  "unsound_helper_with_disjunctive_guard", "Align");
    verify_unsound!("verify_units/align_unsound_9",  "unsound_helper_return_path_selects_bad_ptr", "Align");
    verify_unsound!("verify_units/align_unsound_10", "unsound_multi_hop_missing_offset_guard", "Align");
    verify_unsound!("verify_units/align_unsound_11", "unsound_sub_missing_guard", "Align");
    verify_unsound!("verify_units/align_unsound_12", "unsound_byte_offset_one", "Align");
    verify_unsound!("verify_units/align_unsound_13", "unsound_usize_add_missing_offset_guard", "Align");
    verify_unsound!("verify_units/align_unsound_14", "unsound_repr_packed_field", "Align");
    verify_unsound!("verify_units/align_unsound_15", "unsound_four_phase_scc_alignment", "Align");
    verify_unsound!("verify_units/align_unsound_16", "unsound_trait_bound_cross_cast", "Align");
    verify_unsound!("verify_units/align_unsound_17", "unsound_contract_type_param_binds_generic", "Align");

    let output = run_with_args(
        "verify_units/align_repeat_threshold",
        CMD_VERIFY_REPEAT_1,
    );
    assert_unproved_exclusive(&output, "repeat2_reveals_delayed_unaligned", &["Align"]);

    let output = run_with_args(
        "verify_units/align_repeat_threshold",
        CMD_VERIFY_REPEAT_2,
    );
    assert_unproved_exclusive(&output, "repeat2_reveals_delayed_unaligned", &["Align"]);
}

#[test]
fn loop_repeat_threshold_cases() {
    let functions = [
        "repeat1_sound_repeat2_unsound_align",
        "repeat1_sound_repeat2_unsound_nonnull",
        "repeat1_sound_repeat2_unsound_allocated",
        "repeat1_sound_repeat2_unsound_validptr",
        "repeat1_sound_repeat2_unsound_deref",
        "repeat1_sound_repeat2_unsound_init",
        "repeat1_sound_repeat2_unsound_typed",
        "repeat1_sound_repeat2_unsound_inbound_counter",
        "repeat1_sound_repeat2_unsound_validnum_counter",
        "repeat1_sound_repeat2_unsound_validnum_parity_oscillation",
    ];

    let output = run_with_args(
        "verify_units/loop_repeat_threshold",
        CMD_VERIFY_REPEAT_1,
    );
    for function in functions {
        assert_function_result(&output, function, "SOUND");
    }

    let output = run_with_args(
        "verify_units/loop_repeat_threshold",
        CMD_VERIFY_REPEAT_2,
    );
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_align", &["Align"]);
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_nonnull",
        &["NonNull"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_allocated",
        &["Allocated"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validptr",
        &["ValidPtr"],
    );
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_deref", &["Deref"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_init", &["Init"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_typed", &["Typed"]);
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_inbound_counter",
        &["InBound"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validnum_counter",
        &["ValidNum"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validnum_parity_oscillation",
        &["ValidNum"],
    );
}

#[test]
fn validcstring_std_sound_cases() {
    verify_sound!("verify_units/validcstring_std_sound_01", "sound_literal_bytes_with_nul");
    verify_sound!("verify_units/validcstring_std_sound_02", "sound_variable_bytes_with_guard");
    verify_sound!("verify_units/validcstring_std_sound_03", "sound_static_from_ptr");
    verify_sound!("verify_units/validcstring_std_sound_04", "sound_branch_selects_valid_source");
    verify_sound!("verify_units/validcstring_std_sound_05", "sound_input_slice_exact_match");
    verify_sound!("verify_units/validcstring_std_sound_06", "sound_vec_with_nul_from_variables");
    verify_sound!("verify_units/validcstring_std_sound_07", "sound_loop_builds_valid_c_string");
    verify_sound!("verify_units/validcstring_std_sound_08", "sound_from_ptr_suffix_after_add");
}

#[test]
fn validcstring_std_unsound_cases() {
    verify_unsound!("verify_units/validcstring_std_unsound_01", "unsound_bytes_without_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_02", "unsound_bytes_with_interior_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_03", "unsound_static_from_ptr_without_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_05", "unsound_input_slice_only_checks_last_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_06", "unsound_vec_with_variable_interior_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_07", "unsound_loop_writes_interior_nul", "ValidCStr");
    verify_unsound!("verify_units/validcstring_std_unsound_08", "unsound_nested_scc_switches_to_invalid", "ValidCStr");

    // unsound_09 also triggers InBound via out-of-bounds pointer arithmetic
    let output = run_with_args("verify_units/validcstring_std_unsound_09", CMD_VERIFY);
    assert_unproved_exclusive(&output, "unsound_from_ptr_suffix_without_nul", &["ValidCStr", "InBound"]);

    let output = run_with_args("verify_units/validcstring_std_unsound_04", CMD_VERIFY);
    assert_unproved_exclusive(&output, "unsound_branch_mixes_valid_and_invalid", &["ValidCStr"]);
}

#[test]
fn loop_repeat_threshold_auto_cases() {
    let output = run_with_args("verify_units/loop_repeat_threshold", CMD_VERIFY);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_align", &["Align"]);
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_nonnull",
        &["NonNull"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_allocated",
        &["Allocated"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validptr",
        &["ValidPtr"],
    );
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_deref", &["Deref"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_init", &["Init"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_typed", &["Typed"]);
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_inbound_counter",
        &["InBound"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validnum_counter",
        &["ValidNum"],
    );
    assert_unproved_exclusive(
        &output,
        "repeat1_sound_repeat2_unsound_validnum_parity_oscillation",
        &["ValidNum"],
    );
}

// ================ Align Sound Cases =============
#[test]
fn align_sound_cases() {
    verify_sound!("verify_units/align_sound_1",  "sound_named_contract_binds_callsite_arg");
    verify_sound!("verify_units/align_sound_2",  "sound_enum_paths_inside_scc");
    verify_sound!("verify_units/align_sound_3",  "sound_scc_selects_aligned_source");
    verify_sound!("verify_units/align_sound_4",  "sound_scc_computes_aligned_offset");
    verify_sound!("verify_units/align_sound_5",  "sound_nested_scc_controller");
    verify_sound!("verify_units/align_sound_6",  "sound_iteration_count_switches_aligned_offsets");
    verify_sound!("verify_units/align_sound_7",  "sound_unrelated_scc_does_not_pollute_align");
    verify_sound!("verify_units/align_sound_8",  "sound_unrelated_nested_scc_with_bad_scratch");
    verify_sound!("verify_units/align_sound_9",  "sound_pre_scc_guard_with_scc_offsets");
    verify_sound!("verify_units/align_sound_10", "sound_scc_internal_noise_ignored");
    verify_sound!("verify_units/align_sound_11", "sound_helper_with_conjunctive_guard");
    verify_sound!("verify_units/align_sound_12", "sound_nested_if_before_helper");
    verify_sound!("verify_units/align_sound_13", "sound_helper_return_paths_all_aligned");
    verify_sound!("verify_units/align_sound_14", "sound_multi_hop_helper");
    verify_sound!("verify_units/align_sound_15", "sound_unrelated_condition_ignored");
    verify_sound!("verify_units/align_sound_16", "sound_add_sub_chain");
    verify_sound!("verify_units/align_sound_17", "sound_offset_zero_preserves_align");
    verify_sound!("verify_units/align_sound_18", "sound_usize_round_trip");
    verify_sound!("verify_units/align_sound_19", "sound_usize_add_guarded");
    verify_sound!("verify_units/align_sound_20", "sound_usize_mul_div_offset");
    verify_sound!("verify_units/align_sound_21", "sound_repr_c_field");
    verify_sound!("verify_units/align_sound_22", "sound_repr_align_object");
    verify_sound!("verify_units/align_sound_23", "sound_zst_trivial_alignment");
    verify_sound!("verify_units/align_sound_24", "sound_trait_bound_cross_cast");
    verify_sound!("verify_units/align_sound_25", "sound_contract_type_param_binds_concrete");
    verify_sound!("verify_units/align_sound_26", "sound_contract_type_param_binds_generic");
}

// ================ NonNull Sound Cases =============
#[test]
fn nonnull_sound_cases() {
    let output = run_with_args("verify_units/nonnull_sound_1", CMD_VERIFY);
    assert_contain(&output, "function: caller_with_contract");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_chained_propagation");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_2", CMD_VERIFY);
    assert_contain(&output, "function: sound_slice_as_ptr_branch");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_3", CMD_VERIFY);
    assert_contain(&output, "function: sound_intra_helper_from_ref");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_4", CMD_VERIFY);
    assert_contain(&output, "function: sound_scc_unrelated_state");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_5", CMD_VERIFY);
    assert_contain(&output, "function: sound_raw_arg_guarded");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_6", CMD_VERIFY);
    assert_contain(&output, "function: sound_nonnull_wrapper_from_ref");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/nonnull_sound_7", CMD_VERIFY);
    assert_contain(&output, "function: sound_ref_cast_copy_chain");
    assert_contain(&output, "result: SOUND");
}

// ================ NonNull Unsound Cases =============
#[test]
fn nonnull_unsound_cases() {
    verify_unsound!("verify_units/nonnull_unsound_1", "unsound_explicit_null_constant", "NonNull");
    verify_unsound!("verify_units/nonnull_unsound_2", "unsound_raw_pointer_argument", "NonNull");
    verify_unsound!("verify_units/nonnull_unsound_3", "unsound_branch_selects_null", "NonNull");
    verify_unsound!("verify_units/nonnull_unsound_4", "unsound_scc_overwrites_with_null", "NonNull");
    verify_unsound!("verify_units/nonnull_unsound_5", "unsound_unrelated_guard", "NonNull");
    verify_unsound!("verify_units/nonnull_unsound_6", "unsound_nonnull_wrapper_from_null", "NonNull");
}

// ================ Allocated Sound Cases =============
#[test]
fn allocated_sound_cases() {
    verify_sound!("verify_units/allocated_sound_1", "sound_stack_local_allocated");
    verify_sound!("verify_units/allocated_sound_2", "sound_slice_prefix_allocated");
    verify_sound!("verify_units/allocated_sound_3", "sound_live_vec_allocated");
    verify_sound!("verify_units/allocated_sound_4", "sound_live_box_allocated");
    verify_sound!("verify_units/allocated_sound_5", "sound_branch_selects_live_local");
    verify_sound!("verify_units/allocated_sound_6", "sound_loop_slice_element_allocated");
    verify_sound!("verify_units/allocated_sound_7", "sound_scc_selects_live_array");
    verify_sound!("verify_units/allocated_sound_8", "sound_intra_returns_slice_pointer");
}

// ================ Allocated Unsound Cases =============
#[test]
fn allocated_unsound_cases() {
    verify_unsound!("verify_units/allocated_unsound_1",  "unsound_null_not_allocated", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_2",  "unsound_stack_scope_ended", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_3",  "unsound_vec_dropped_before_use", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_4",  "unsound_empty_slice_needs_one_element", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_5",  "unsound_branch_may_select_null", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_6",  "unsound_scc_overwrites_with_null", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_7",  "unsound_vec_reallocates_old_pointer", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_8",  "unsound_slice_too_short_for_requested_len", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_9",  "unsound_intra_returns_dangling_pointer", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_10", "unsound_scc_selects_dead_temporary", "Allocated");
    verify_unsound!("verify_units/allocated_unsound_11", "unsound_adjacent_stack_objects_do_not_merge", "Allocated");
}

// ================ InBound Sound Cases =============
#[test]
fn inbound_sound_cases() {
    verify_sound!("verify_units/inbound_sound_1", "sound_ptr_add_guarded");
    verify_sound!("verify_units/inbound_sound_2", "sound_from_raw_parts_prefix_two");
    verify_sound!("verify_units/inbound_sound_3", "sound_get_unchecked_generic");
    verify_sound!("verify_units/inbound_sound_4", "sound_copy_nonoverlapping_one");
    verify_sound!("verify_units/inbound_sound_5", "sound_intra_slice_add_guarded");
    verify_sound!("verify_units/inbound_sound_6", "sound_scc_loop_index_guard");
    verify_sound!("verify_units/inbound_std_sound_1", "sound_std_get_unchecked");
    verify_sound!("verify_units/inbound_std_sound_2", "sound_std_copy_nonoverlapping");
}

#[test]
fn sliceindex_sound_cases() {
    verify_sound!("verify_units/sliceindex_sound_01", "sound_scalar_index_guard");
    verify_sound!("verify_units/sliceindex_sound_02", "sound_range_index_guard");
    verify_sound!("verify_units/sliceindex_sound_03", "sound_std_get_unchecked_sliceindex");
    verify_sound!("verify_units/sliceindex_sound_04", "sound_std_range_get_unchecked");
}

// ================ InBound Unsound Cases =============
#[test]
fn inbound_unsound_cases() {
    verify_unsound!("verify_units/inbound_unsound_1", "unsound_ptr_add_without_guard", "InBound");
    verify_unsound!("verify_units/inbound_unsound_2", "unsound_from_raw_parts_two_only_nonempty", "InBound");
    verify_unsound!("verify_units/inbound_unsound_3", "unsound_get_unchecked_wrong_guard", "InBound");
    verify_unsound!("verify_units/inbound_unsound_4", "unsound_copy_nonoverlapping_dst_unguarded", "InBound");
    verify_unsound!("verify_units/inbound_unsound_5", "unsound_branch_selects_unguarded_index", "InBound");
    verify_unsound!("verify_units/inbound_unsound_6", "unsound_scc_off_by_one", "InBound");
    verify_unsound!("verify_units/inbound_unsound_7", "unsound_len_guard_off_by_one", "InBound");
    verify_unsound!("verify_units/inbound_unsound_8", "unsound_inclusive_range_off_by_one", "InBound");
    verify_unsound!("verify_units/inbound_unsound_9", "unsound_ptr_add_off_by_one", "InBound");
    verify_unsound!("verify_units/inbound_std_unsound_1", "unsound_std_get_unchecked_wrong_guard", "InBound");

    let output = run_with_args("verify_units/inbound_std_unsound_2", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_dst_unguarded",
        &["ValidPtr", "NonOverlap", "ValidNum"],
    );
}

#[test]
fn sliceindex_unsound_cases() {
    verify_unsound!("verify_units/sliceindex_unsound_01", "unsound_scalar_index_wrong_guard", "InBound");
    verify_unsound!("verify_units/sliceindex_unsound_02", "unsound_range_index_missing_end_guard", "InBound");
    verify_unsound!("verify_units/sliceindex_unsound_03", "unsound_std_range_missing_end_guard", "InBound");
}

#[test]
fn init_std_sound_cases() {
    let output = run_with_args("verify_units/init_std_sound_1", CMD_VERIFY);
    assert_contain(&output, "function: sound_assume_init_read_after_write");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_2", CMD_VERIFY);
    assert_contain(&output, "function: sound_assume_init_after_write");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_3", CMD_VERIFY);
    assert_contain(&output, "function: sound_branch_local_init");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_4", CMD_VERIFY);
    assert_contain(&output, "function: sound_intra_helper_initializes");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/init_std_sound_5", CMD_VERIFY);
    assert_contain(&output, "function: sound_loop_initializes_slice");
    assert_contain(&output, "Init | Proved");

    let output = run_with_args("verify_units/init_std_sound_6", CMD_VERIFY);
    assert_contain(&output, "function: sound_len_bound_loop_initializes_slice");
    assert_contain(&output, "Init | Proved");
}

// ================ Init Std Unsound Cases =============
#[test]
fn init_std_unsound_cases() {
    verify_unsound!("verify_units/init_std_unsound_1", "unsound_assume_init_read_without_write", "Init");
    verify_unsound!("verify_units/init_std_unsound_2", "unsound_assume_init_without_write", "Init");
    verify_unsound!("verify_units/init_std_unsound_3", "unsound_conditional_write_then_assume", "Init");
    verify_unsound!("verify_units/init_std_unsound_4", "unsound_write_different_slot", "Init");
    verify_unsound!("verify_units/init_std_unsound_5", "unsound_intra_helper_maybe_initializes", "Init");
    verify_unsound!("verify_units/init_std_unsound_6", "unsound_from_raw_parts_uninitialized", "Init");
    verify_unsound!("verify_units/init_std_unsound_7", "unsound_from_raw_parts_wrong_element_type", "Init");
    verify_unsound!("verify_units/init_std_unsound_8", "unsound_len_bound_loop_skips_even_indices", "Init");
}

// ================ ValidNum Sound Cases =============
#[test]
fn validnum_sound_cases() {
    let output = run_with_args("verify_units/validnum_sound_1", CMD_VERIFY);
    assert_contain(&output, "function: sound_guarded_less_than");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_2", CMD_VERIFY);
    assert_contain(&output, "function: sound_guarded_nonzero");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_3", CMD_VERIFY);
    assert_contain(&output, "function: sound_constant_sum_below_cap");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_4", CMD_VERIFY);
    assert_contain(&output, "function: sound_trait_bound_size_limit");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_5", CMD_VERIFY);
    assert_contain(&output, "function: sound_scc_validnum_index_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_6", CMD_VERIFY);
    assert_contain(&output, "function: sound_guarded_variable_sum");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_7", CMD_VERIFY);
    assert_contain(&output, "function: sound_interval_guard");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_sound_8", CMD_VERIFY);
    assert_contain(&output, "function: sound_trait_bound_align_order");
    assert_contain(&output, "result: SOUND");

    let output = run_with_args("verify_units/validnum_std_sound_1", CMD_VERIFY);
    assert_contain(&output, "function: sound_std_from_raw_parts_validnum");
    assert_contain(&output, "ValidNum | Proved");

    let output = run_with_args("verify_units/validnum_std_sound_2", CMD_VERIFY);
    assert_contain(&output, "function: sound_std_copy_nonoverlapping_validnum");
    assert_contain(&output, "ValidNum | Proved");
}

#[test]
fn as_chunks_sound_cases() {
    let output = run_with_args("verify_units/as_chunks_sound_01", CMD_VERIFY);
    assert_contain(&output, "function: sound_as_chunks_unchecked_exact_div");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_exact_div_guard");
    assert_contain(&output, "result: SOUND");
}

// ================ ValidNum Unsound Cases =============
#[test]
fn validnum_unsound_cases() {
    verify_unsound!("verify_units/validnum_unsound_1", "unsound_missing_less_than_guard", "ValidNum");
    verify_unsound!("verify_units/validnum_unsound_2", "unsound_missing_nonzero_guard", "ValidNum");
    verify_unsound!("verify_units/validnum_unsound_3", "unsound_partial_sum_guard", "ValidNum");
    verify_unsound!("verify_units/validnum_unsound_4", "unsound_trait_bound_missing_size_limit", "ValidNum");
    verify_unsound!("verify_units/validnum_unsound_5", "unsound_interval_inclusive_guard", "ValidNum");

    let output = run_with_args("verify_units/validnum_std_unsound_1", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "unsound_std_from_raw_parts_validnum_overflow",
        &["ValidNum", "ValidPtr", "Init"],
    );

    let output = run_with_args("verify_units/validnum_std_unsound_2", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_validnum",
        &["ValidNum", "ValidPtr", "NonOverlap"],
    );
}

#[test]
fn as_chunks_unsound_cases() {
    let output = run_with_args("verify_units/as_chunks_unsound_01", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "unsound_as_chunks_unchecked_missing_exact_div",
        &["ValidNum"],
    );
    assert_unproved_exclusive(&output, "unsound_exact_div_missing_guard", &["ValidNum"]);
}

#[test]
fn validptr_sound_cases() {
    verify_sound!("verify_units/validptr_sound_1", "sound_zst_dangling_valid_for_any_len");
    verify_sound!("verify_units/validptr_sound_2", "sound_stack_array_full_range");
    verify_sound!("verify_units/validptr_sound_3", "sound_slice_suffix_guarded");
    verify_sound!("verify_units/validptr_sound_4", "sound_scc_each_slice_element");
    verify_sound!("verify_units/validptr_sound_5", "sound_signed_suffix_guarded");
}

#[test]
fn deref_sound_cases() {
    let output = run_with_args("verify_units/deref_sound_1", CMD_VERIFY);
    assert_contain(&output, "function: sound_deref_slice_prefix");
    assert_contain(&output, "Deref | Proved");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn validptr_unsound_cases() {
    verify_unsound!("verify_units/validptr_unsound_1", "unsound_non_zst_dangling_not_allocated", "ValidPtr");
    verify_unsound!("verify_units/validptr_unsound_2", "unsound_one_past_requires_one_element", "ValidPtr");
    verify_unsound!("verify_units/validptr_unsound_3", "unsound_stack_array_len_too_large", "ValidPtr");
    verify_unsound!("verify_units/validptr_unsound_4", "unsound_scc_branch_uses_one_past", "ValidPtr");
    verify_unsound!("verify_units/validptr_unsound_5", "unsound_signed_suffix_missing_lower_bound", "ValidPtr");
}

#[test]
fn deref_unsound_cases() {
    verify_unsound!("verify_units/deref_unsound_1", "unsound_deref_one_past", "Deref");
}

#[test]
fn typed_provenance_cases() {
    let output = run_with_args("verify_units/typed_cases", CMD_VERIFY);

    assert_contain(&output, "function: sound_reference_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_slice_element_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_repr_c_field_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_generic_reference_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_branch_all_sources_typed");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_scc_preserves_typed_source");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_maybeuninit_after_write");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_align_to_same_type");
    assert_contain(&output, "result: SOUND");

    assert_unproved_exclusive(&output, "unsound_u8_bytes_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_u16_slice_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_uninit_memory_as_u32", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_bool_bits", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_char_bits", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_invalid_enum_discriminant", &["Typed"]);
    assert_unproved_exclusive(&output, "unsound_branch_selects_untyped_source", &["Typed"]);
    assert_unproved_exclusive(
        &output,
        "unsound_scc_overwrites_with_untyped_source",
        &["Typed"],
    );
}

#[test]
fn alive_sound_cases() {
    let output = run_with_args("verify_units/alive_sound_01", CMD_VERIFY);
    assert_contain(&output, "function: SliceHost::<'a, T>::get");
    assert_contain(&output, "Alive | Proved");

    let output = run_with_args("verify_units/alive_sound_02", CMD_VERIFY);
    assert_contain(&output, "function: MutSliceHost::<'a, T>::get_mut");
    assert_contain(&output, "Alive | Proved");

    let output = run_with_args("verify_units/alive_sound_03", CMD_VERIFY);
    assert_contain(&output, "function: slice_from_host");
    assert_contain(&output, "Alive | Proved");
}

#[test]
fn alive_unsound_cases() {
    let output = run_with_args("verify_units/alive_unsound_01", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "DangerousAliaser::<'a, T>::get_mut",
        &["Alive", "NonNull", "ValidPtr"],
    );

    let output = run_with_args("verify_units/alive_unsound_02", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "slice_tied_to_unrelated_host",
        &["Alias", "Alive", "Init", "NonNull", "ValidPtr"],
    );

    let output = run_with_args("verify_units/alive_unsound_03", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "static_slice_from_local_vec",
        &["Alias", "Align", "Alive", "Init", "NonNull", "ValidPtr"],
    );
}

#[test]
fn struct_invariant() {
    let output = run_with_args("verify_units/struct_invariant_1", CMD_VERIFY);
    assert_contain(&output, "function: Wrapper::<T>::new");
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "InBound | Proved");
    assert_contain(&output, "Init | Proved");
    assert_contain(&output, "function: Wrapper::<T>::set_len");
    assert_contain(&output, "function: Wrapper::<T>::read");
    assert_contain(&output, "function: Wrapper::<T>::read_unchecked");
}

#[test]
fn skip_invariant_struct_noinvariant() {
    let output = run_with_args(
        "verify_units/struct_noinvariant_1",
        CMD_VERIFY_SKIP_INVARIANT,
    );
    assert_contain(&output, "result: UNSOUND");

    let output = run_with_args(
        "verify_units/struct_noinvariant_2",
        CMD_VERIFY_SKIP_INVARIANT,
    );
    assert_contain(&output, "result: SOUND");
}

#[test]
fn skip_invariant_sound_callee() {
    let output = run_with_args("verify_units/align_sound_1", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "function: sound_named_contract_binds_callsite_arg");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn split_transmute_unsound() {
    let output = run_with_args("verify_units/split_transmute_unsound", CMD_VERIFY);
    assert_unproved_exclusive(
        &output,
        "align_without_contract_generic",
        &["SplitTransmute"],
    );
    assert_unproved_exclusive(
        &output,
        "unsound_align_to_bool_from_bytes",
        &["SplitTransmute"],
    );
    assert_contain(&output, "function: align_without_contract_u32");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: align_without_contract_u16");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: align_without_contract_u8");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn split_transmute_nonzero() {
    let output = run_with_args("verify_units/split_transmute_nonzero", CMD_VERIFY);
    assert_contain(&output, "function: align_to_nonzero_u16");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u32");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u8");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn split_transmute_sound() {
    let output = run_with_args("verify_units/split_transmute_sound", CMD_VERIFY);
    assert_contain(&output, "function: align_to_u8_sound");
    assert_contain(&output, "result: SOUND");
}

#[test]
fn trait_unsound_prepare() {
    let output = run_with_args("verify_units/trait_unsound_1", CMD_VERIFY_PREPARE);
    assert_contain(&output, "prepare targets for unsafe trait: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "NonNull");
}

#[test]
fn trait_unsound_verify() {
    let output = run_with_args("verify_units/trait_unsound_1", CMD_VERIFY);
    assert_contain(&output, "unsafe trait impl: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "NonNull");
    assert_contain(&output, "verification: deferred");
}

#[test]
fn alias_sound_verify_cases() {
    verify_sound!("verify_units/alias_sound_01", "sound_shared_slice_no_raw_mutation");
    verify_sound!("verify_units/alias_sound_02", "sound_raw_use_after_slice_scope");
    verify_sound!("verify_units/alias_sound_03", "sound_box_from_raw_consumes_pointer");
    verify_sound!("verify_units/alias_sound_04", "RawBuf::as_slice_mut");
    verify_sound!("verify_units/alias_sound_05", "build_slice");
    verify_sound!("verify_units/alias_sound_06", "sound_cstr_from_ptr_read_only");
    verify_sound!("verify_units/alias_sound_07", "PrivateSlot::as_slice_mut");
    verify_sound!("verify_units/alias_sound_08", "ReadOnlySlot::<'a>::as_slice");
    verify_sound!("verify_units/alias_sound_09", "sound_box_from_raw_then_into_raw");
    verify_sound!("verify_units/alias_sound_10", "sound_cstring_from_raw_no_reuse");
    verify_sound!("verify_units/alias_sound_11", "sound_copy_nonoverlapping_disjoint");
    verify_sound!("verify_units/alias_sound_12", "sound_vec_reserve_before_raw_slice");
    verify_sound!("verify_units/alias_sound_13", "as_bytes_mut_sound");
    verify_sound!("verify_units/alias_sound_14", "as_bytes_sound");
}

#[test]
fn alias_unsound_verify_cases() {
    verify_hazard!("verify_units/alias_unsound_01", "unsound_shared_slice_then_raw_write", "Alias");
    verify_hazard!("verify_units/alias_unsound_02", "unsound_mut_slice_then_raw_read", "Alias");
    verify_hazard!("verify_units/alias_unsound_03", "unsound_vec_push_while_raw_slice_live", "Alias");
    verify_hazard!("verify_units/alias_unsound_04", "unsound_box_from_raw_then_raw_write", "Alias");
    verify_hazard!("verify_units/alias_unsound_09", "unsound_cstring_from_raw_then_raw_write", "Alias");
    verify_hazard!("verify_units/alias_unsound_10", "unsound_cstr_from_ptr_then_raw_mutation", "Alias");
    verify_hazard!("verify_units/alias_unsound_15", "unsound_vec_from_raw_parts_then_raw_write", "Alias");
    verify_hazard!("verify_units/alias_unsound_16", "unsound_vec_reserve_while_raw_slice_live", "Alias");
    verify_hazard!("verify_units/alias_unsound_18", "as_bytes_mut_unsound", "Alias");
    verify_hazard!("verify_units/alias_unsound_19", "as_bytes_mut_ptr_missing_alias", "Alias");
    verify_hazard!("verify_units/alias_unsound_20", "as_bytes_mut_ptr_len_missing_alias", "Alias");

    // Multi-property unsound cases
    let output = run_with_args("verify_units/alias_unsound_05", CMD_VERIFY);
    assert_unproved_exclusive(&output, "unsound_box_from_raw_drop_then_raw_read", &["Alias", "Allocated", "ValidPtr", "Typed"]);

    let output = run_with_args("verify_units/alias_unsound_06", CMD_VERIFY);
    assert_unproved_exclusive(&output, "RawSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_07", CMD_VERIFY);
    assert_unproved_exclusive(&output, "make_mut_slice", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_08", CMD_VERIFY);
    assert_unproved_exclusive(&output, "unsound_copy_nonoverlapping_overlap", &["NonOverlap"]);

    let output = run_with_args("verify_units/alias_unsound_11", CMD_VERIFY);
    assert_unproved_exclusive(&output, "PublicRawSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_12", CMD_VERIFY);
    assert_unproved_exclusive(&output, "GetterSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_13", CMD_VERIFY);
    assert_unproved_exclusive(&output, "WriterSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_14", CMD_VERIFY);
    assert_unproved_exclusive(&output, "SplitSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);

    let output = run_with_args("verify_units/alias_unsound_17", CMD_VERIFY);
    assert_unproved_exclusive(&output, "TraitSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn filter_by_module() {
    let output = run_with_args(
        "verify_units/module_filter",
        &["verify", "--mode", "targeted", "--module", "a"],
    );
    assert_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter",
        &["verify", "--mode", "scan", "--module", "b"],
    );
    assert_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: c::h");
}

#[test]
fn filter_by_crate() {
    let output = run_with_args(
        "verify_units/module_filter_crate",
        &["verify", "--mode", "targeted", "--crate", "verify_module_filter"],
    );
    assert_contain(&output, "function: a::f");
    assert_contain(&output, "function: b::g");
    assert_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter_crate",
        &["verify", "--mode", "targeted", "--crate", "verify_module_filter", "--module", "a"],
    );
    assert_contain(&output, "function: a::f");
    assert_not_contain(&output, "function: b::g");
    assert_not_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter_crate",
        &["verify", "--mode", "targeted", "--crate", "nonexistent_crate"],
    );
    assert_contain(&output, "--crate \"nonexistent_crate\" matched no targets");
}
