
// ================ Align Unsound Cases =============
unsound_tests! {
    align_unsound_01: "verify_units/align_unsound_1"  => "unsound_enum_paths_inside_scc" => "Align",
    align_unsound_02: "verify_units/align_unsound_2"  => "unsound_scc_selects_mixed_source" => "Align",
    align_unsound_03: "verify_units/align_unsound_3"  => "unsound_scc_computes_misaligned_offset" => "Align",
    align_unsound_04: "verify_units/align_unsound_4"  => "unsound_nested_scc_controller" => "Align",
    align_unsound_05: "verify_units/align_unsound_5"  => "unsound_iteration_count_can_leave_unaligned" => "Align",
    align_unsound_06: "verify_units/align_unsound_6"  => "unsound_pre_scc_guard_overwritten_by_scc" => "Align",
    align_unsound_07: "verify_units/align_unsound_7"  => "unsound_scc_guard_only_on_one_branch" => "Align",
    align_unsound_08: "verify_units/align_unsound_8"  => "unsound_helper_with_disjunctive_guard" => "Align",
    align_unsound_09: "verify_units/align_unsound_9"  => "unsound_helper_return_path_selects_bad_ptr" => "Align",
    align_unsound_10: "verify_units/align_unsound_10" => "unsound_multi_hop_missing_offset_guard" => "Align",
    align_unsound_11: "verify_units/align_unsound_11" => "unsound_sub_missing_guard" => "Align",
    align_unsound_12: "verify_units/align_unsound_12" => "unsound_byte_offset_one" => "Align",
    align_unsound_13: "verify_units/align_unsound_13" => "unsound_usize_add_missing_offset_guard" => "Align",
    align_unsound_14: "verify_units/align_unsound_14" => "unsound_repr_packed_field" => "Align",
    align_unsound_15: "verify_units/align_unsound_15" => "unsound_four_phase_scc_alignment" => "Align",
    align_unsound_16: "verify_units/align_unsound_16" => "unsound_trait_bound_cross_cast" => "Align",
    align_unsound_17: "verify_units/align_unsound_17" => "unsound_contract_type_param_binds_generic" => "Align",
}

// ================ ValidCStr Sound Cases =============
sound_tests! {
    validcstring_std_sound_01: "verify_units/validcstring_std_sound_01" => "sound_literal_bytes_with_nul",
    validcstring_std_sound_02: "verify_units/validcstring_std_sound_02" => "sound_variable_bytes_with_guard",
    validcstring_std_sound_03: "verify_units/validcstring_std_sound_03" => "sound_static_from_ptr",
    validcstring_std_sound_04: "verify_units/validcstring_std_sound_04" => "sound_branch_selects_valid_source",
    validcstring_std_sound_05: "verify_units/validcstring_std_sound_05" => "sound_input_slice_exact_match",
    validcstring_std_sound_06: "verify_units/validcstring_std_sound_06" => "sound_vec_with_nul_from_variables",
    validcstring_std_sound_07: "verify_units/validcstring_std_sound_07" => "sound_loop_builds_valid_c_string",
    validcstring_std_sound_08: "verify_units/validcstring_std_sound_08" => "sound_from_ptr_suffix_after_add",
}

// ================ ValidCStr Unsound Cases =============
unsound_tests! {
    validcstring_std_unsound_01: "verify_units/validcstring_std_unsound_01" => "unsound_bytes_without_nul" => "ValidCStr",
    validcstring_std_unsound_02: "verify_units/validcstring_std_unsound_02" => "unsound_bytes_with_interior_nul" => "ValidCStr",
    validcstring_std_unsound_03: "verify_units/validcstring_std_unsound_03" => "unsound_static_from_ptr_without_nul" => "ValidCStr",
    validcstring_std_unsound_04: "verify_units/validcstring_std_unsound_04" => "unsound_branch_mixes_valid_and_invalid" => "ValidCStr",
    validcstring_std_unsound_05: "verify_units/validcstring_std_unsound_05" => "unsound_input_slice_only_checks_last_nul" => "ValidCStr",
    validcstring_std_unsound_06: "verify_units/validcstring_std_unsound_06" => "unsound_vec_with_variable_interior_nul" => "ValidCStr",
    validcstring_std_unsound_07: "verify_units/validcstring_std_unsound_07" => "unsound_loop_writes_interior_nul" => "ValidCStr",
    validcstring_std_unsound_08: "verify_units/validcstring_std_unsound_08" => "unsound_nested_scc_switches_to_invalid" => "ValidCStr",
}

// ================ ValidString Sound Cases =============
sound_tests! {
    validstring_std_sound_01: "verify_units/validstring_std_sound_01" => "sound_valid_utf8_literal",
    string_as_ptr_sound_01: "verify_units/string_as_ptr_sound_01" => "sound_string_as_ptr",
}

// ================ ValidString Unsound Cases =============
unsound_tests! {
    validstring_std_unsound_01: "verify_units/validstring_std_unsound_01" => "unsound_invalid_utf8_literal" => "ValidString",
}

// ================ Align Sound Cases =============
sound_tests! {
    align_sound_01: "verify_units/align_sound_1"  => "sound_named_contract_binds_callsite_arg",
    align_sound_02: "verify_units/align_sound_2"  => "sound_enum_paths_inside_scc",
    align_sound_03: "verify_units/align_sound_3"  => "sound_scc_selects_aligned_source",
    align_sound_04: "verify_units/align_sound_4"  => "sound_scc_computes_aligned_offset",
    align_sound_05: "verify_units/align_sound_5"  => "sound_nested_scc_controller",
    align_sound_06: "verify_units/align_sound_6"  => "sound_iteration_count_switches_aligned_offsets",
    align_sound_07: "verify_units/align_sound_7"  => "sound_unrelated_scc_does_not_pollute_align",
    align_sound_08: "verify_units/align_sound_8"  => "sound_unrelated_nested_scc_with_bad_scratch",
    align_sound_09: "verify_units/align_sound_9"  => "sound_pre_scc_guard_with_scc_offsets",
    align_sound_10: "verify_units/align_sound_10" => "sound_scc_internal_noise_ignored",
    align_sound_11: "verify_units/align_sound_11" => "sound_helper_with_conjunctive_guard",
    align_sound_12: "verify_units/align_sound_12" => "sound_nested_if_before_helper",
    align_sound_13: "verify_units/align_sound_13" => "sound_helper_return_paths_all_aligned",
    align_sound_14: "verify_units/align_sound_14" => "sound_multi_hop_helper",
    align_sound_15: "verify_units/align_sound_15" => "sound_unrelated_condition_ignored",
    align_sound_16: "verify_units/align_sound_16" => "sound_add_sub_chain",
    align_sound_17: "verify_units/align_sound_17" => "sound_offset_zero_preserves_align",
    align_sound_18: "verify_units/align_sound_18" => "sound_usize_round_trip",
    align_sound_19: "verify_units/align_sound_19" => "sound_usize_add_guarded",
    align_sound_20: "verify_units/align_sound_20" => "sound_usize_mul_div_offset",
    align_sound_21: "verify_units/align_sound_21" => "sound_repr_c_field",
    align_sound_22: "verify_units/align_sound_22" => "sound_repr_align_object",
    align_sound_23: "verify_units/align_sound_23" => "sound_zst_trivial_alignment",
    align_sound_24: "verify_units/align_sound_24" => "sound_trait_bound_cross_cast",
    align_sound_25: "verify_units/align_sound_25" => "sound_contract_type_param_binds_concrete",
    align_sound_26: "verify_units/align_sound_26" => "sound_contract_type_param_binds_generic",
}

// ================ NonNull Sound Cases =============
sound_tests! {
    nonnull_sound_02: "verify_units/nonnull_sound_2" => "sound_slice_as_ptr_branch",
    nonnull_sound_03: "verify_units/nonnull_sound_3" => "sound_intra_helper_from_ref",
    nonnull_sound_04: "verify_units/nonnull_sound_4" => "sound_scc_unrelated_state",
    nonnull_sound_05: "verify_units/nonnull_sound_5" => "sound_raw_arg_guarded",
    nonnull_sound_06: "verify_units/nonnull_sound_6" => "sound_nonnull_wrapper_from_ref",
    nonnull_sound_07: "verify_units/nonnull_sound_7" => "sound_ref_cast_copy_chain",
}

// ================ NonNull Unsound Cases =============
unsound_tests! {
    nonnull_unsound_01: "verify_units/nonnull_unsound_1" => "unsound_explicit_null_constant" => "NonNull",
    nonnull_unsound_02: "verify_units/nonnull_unsound_2" => "unsound_raw_pointer_argument" => "NonNull",
    nonnull_unsound_03: "verify_units/nonnull_unsound_3" => "unsound_branch_selects_null" => "NonNull",
    nonnull_unsound_04: "verify_units/nonnull_unsound_4" => "unsound_scc_overwrites_with_null" => "NonNull",
    nonnull_unsound_05: "verify_units/nonnull_unsound_5" => "unsound_unrelated_guard" => "NonNull",
    nonnull_unsound_06: "verify_units/nonnull_unsound_6" => "unsound_nonnull_wrapper_from_null" => "NonNull",
}

// ================ Allocated Sound Cases =============
sound_tests! {
    allocated_sound_01: "verify_units/allocated_sound_1" => "sound_stack_local_allocated",
    allocated_sound_02: "verify_units/allocated_sound_2" => "sound_slice_prefix_allocated",
    allocated_sound_03: "verify_units/allocated_sound_3" => "sound_live_vec_allocated",
    allocated_sound_04: "verify_units/allocated_sound_4" => "sound_live_box_allocated",
    allocated_sound_05: "verify_units/allocated_sound_5" => "sound_branch_selects_live_local",
    allocated_sound_06: "verify_units/allocated_sound_6" => "sound_loop_slice_element_allocated",
    allocated_sound_07: "verify_units/allocated_sound_7" => "sound_scc_selects_live_array",
    allocated_sound_08: "verify_units/allocated_sound_8" => "sound_intra_returns_slice_pointer",
}

// ================ Allocated Unsound Cases =============
unsound_tests! {
    allocated_unsound_01: "verify_units/allocated_unsound_1"  => "unsound_null_not_allocated" => "Allocated",
    allocated_unsound_02: "verify_units/allocated_unsound_2"  => "unsound_stack_scope_ended" => "Allocated",
    allocated_unsound_03: "verify_units/allocated_unsound_3"  => "unsound_vec_dropped_before_use" => "Allocated",
    allocated_unsound_04: "verify_units/allocated_unsound_4"  => "unsound_empty_slice_needs_one_element" => "Allocated",
    allocated_unsound_05: "verify_units/allocated_unsound_5"  => "unsound_branch_may_select_null" => "Allocated",
    allocated_unsound_06: "verify_units/allocated_unsound_6"  => "unsound_scc_overwrites_with_null" => "Allocated",
    allocated_unsound_07: "verify_units/allocated_unsound_7"  => "unsound_vec_reallocates_old_pointer" => "Allocated",
    allocated_unsound_08: "verify_units/allocated_unsound_8"  => "unsound_slice_too_short_for_requested_len" => "Allocated",
    allocated_unsound_09: "verify_units/allocated_unsound_9"  => "unsound_intra_returns_dangling_pointer" => "Allocated",
    allocated_unsound_10: "verify_units/allocated_unsound_10" => "unsound_scc_selects_dead_temporary" => "Allocated",
    allocated_unsound_11: "verify_units/allocated_unsound_11" => "unsound_adjacent_stack_objects_do_not_merge" => "Allocated",
}

// ================ InBound Sound Cases =============
sound_tests! {
    inbound_sound_01: "verify_units/inbound_sound_1" => "sound_ptr_add_guarded",
    inbound_sound_02: "verify_units/inbound_sound_2" => "sound_from_raw_parts_prefix_two",
    inbound_sound_03: "verify_units/inbound_sound_3" => "sound_get_unchecked_generic",
    inbound_sound_04: "verify_units/inbound_sound_4" => "sound_copy_nonoverlapping_one",
    inbound_sound_05: "verify_units/inbound_sound_5" => "sound_intra_slice_add_guarded",
    inbound_sound_06: "verify_units/inbound_sound_6" => "sound_scc_loop_index_guard",
    inbound_std_sound_01: "verify_units/inbound_std_sound_1" => "sound_std_get_unchecked",
    inbound_std_sound_02: "verify_units/inbound_std_sound_2" => "sound_std_copy_nonoverlapping",
    inbound_sound_07: "verify_units/inbound_sound_7"  => "sound_scalar_index_guard",
    inbound_sound_08: "verify_units/inbound_sound_8"  => "sound_range_index_guard",
    inbound_sound_09: "verify_units/inbound_sound_9"  => "sound_std_get_unchecked_sliceindex",
    inbound_sound_10: "verify_units/inbound_sound_10" => "sound_std_range_get_unchecked",
    inbound_sound_11: "verify_units/inbound_sound_11" => "sound_vec_from_raw_parts_inbound",
}

// ================ InBound Unsound Cases =============
unsound_tests! {
    inbound_unsound_01: "verify_units/inbound_unsound_1" => "unsound_ptr_add_without_guard" => "InBound",
    inbound_unsound_02: "verify_units/inbound_unsound_2" => "unsound_from_raw_parts_two_only_nonempty" => "InBound",
    inbound_unsound_03: "verify_units/inbound_unsound_3" => "unsound_get_unchecked_wrong_guard" => "InBound",
    inbound_unsound_04: "verify_units/inbound_unsound_4" => "unsound_copy_nonoverlapping_dst_unguarded" => "InBound",
    inbound_unsound_05: "verify_units/inbound_unsound_5" => "unsound_branch_selects_unguarded_index" => "InBound",
    inbound_unsound_06: "verify_units/inbound_unsound_6" => "unsound_scc_off_by_one" => "InBound",
    inbound_unsound_07: "verify_units/inbound_unsound_7" => "unsound_len_guard_off_by_one" => "InBound",
    inbound_unsound_08: "verify_units/inbound_unsound_8" => "unsound_inclusive_range_off_by_one" => "InBound",
    inbound_unsound_09: "verify_units/inbound_unsound_9" => "unsound_ptr_add_off_by_one" => "InBound",
    inbound_std_unsound_01: "verify_units/inbound_std_unsound_1" => "unsound_std_get_unchecked_wrong_guard" => "InBound",
    inbound_unsound_10: "verify_units/inbound_unsound_10" => "unsound_scalar_index_wrong_guard" => "InBound",
    inbound_unsound_11: "verify_units/inbound_unsound_11" => "unsound_range_index_missing_end_guard" => "InBound",
    inbound_unsound_12: "verify_units/inbound_unsound_12" => "unsound_std_range_missing_end_guard" => "InBound",
}

// ================ Init Std Sound Cases =============
sound_tests! {
    init_std_sound_01: "verify_units/init_std_sound_1" => "sound_assume_init_read_after_write",
    init_std_sound_02: "verify_units/init_std_sound_2" => "sound_assume_init_after_write",
    init_std_sound_03: "verify_units/init_std_sound_3" => "sound_branch_local_init",
    init_std_sound_04: "verify_units/init_std_sound_4" => "sound_intra_helper_initializes",
    init_std_sound_05: "verify_units/init_std_sound_5" => "sound_loop_initializes_slice",
    init_std_sound_06: "verify_units/init_std_sound_6" => "sound_len_bound_loop_initializes_slice",
}

// ================ Init Std Unsound Cases =============
unsound_tests! {
    init_std_unsound_01: "verify_units/init_std_unsound_1" => "unsound_assume_init_read_without_write" => "Init",
    init_std_unsound_02: "verify_units/init_std_unsound_2" => "unsound_assume_init_without_write" => "Init",
    init_std_unsound_03: "verify_units/init_std_unsound_3" => "unsound_conditional_write_then_assume" => "Init",
    init_std_unsound_04: "verify_units/init_std_unsound_4" => "unsound_write_different_slot" => "Init",
    init_std_unsound_05: "verify_units/init_std_unsound_5" => "unsound_intra_helper_maybe_initializes" => "Init",
    init_std_unsound_06: "verify_units/init_std_unsound_6" => "unsound_from_raw_parts_uninitialized" => "Init",
    init_std_unsound_08: "verify_units/init_std_unsound_8" => "unsound_len_bound_loop_skips_even_indices" => "Init",
}

// ================ ValidNum Sound Cases =============
sound_tests! {
    validnum_sound_01: "verify_units/validnum_sound_1" => "sound_guarded_less_than",
    validnum_sound_02: "verify_units/validnum_sound_2" => "sound_guarded_nonzero",
    validnum_sound_03: "verify_units/validnum_sound_3" => "sound_constant_sum_below_cap",
    validnum_sound_04: "verify_units/validnum_sound_4" => "sound_trait_bound_size_limit",
    validnum_sound_05: "verify_units/validnum_sound_5" => "sound_scc_validnum_index_guard",
    validnum_sound_06: "verify_units/validnum_sound_6" => "sound_guarded_variable_sum",
    validnum_sound_07: "verify_units/validnum_sound_7" => "sound_interval_guard",
    validnum_sound_08: "verify_units/validnum_sound_8" => "sound_trait_bound_align_order",
    validnum_std_sound_01: "verify_units/validnum_std_sound_1" => "sound_std_from_raw_parts_validnum",
    validnum_std_sound_02: "verify_units/validnum_std_sound_2" => "sound_std_copy_nonoverlapping_validnum",
    nonzero_type_invariant: "verify_units/nonzero_type_invariant" => "sound_nonzero_type_invariant",
    validnum_ifelse_sound_01: "verify_units/validnum_ifelse_sound_1" => "sound_zst_ifelse",
}

// ================ ValidNum Unsound Cases =============
unsound_tests! {
    validnum_unsound_01: "verify_units/validnum_unsound_1" => "unsound_missing_less_than_guard" => "ValidNum",
    validnum_unsound_02: "verify_units/validnum_unsound_2" => "unsound_missing_nonzero_guard" => "ValidNum",
    validnum_unsound_03: "verify_units/validnum_unsound_3" => "unsound_partial_sum_guard" => "ValidNum",
    validnum_unsound_04: "verify_units/validnum_unsound_4" => "unsound_trait_bound_missing_size_limit" => "ValidNum",
    validnum_unsound_05: "verify_units/validnum_unsound_5" => "unsound_interval_inclusive_guard" => "ValidNum",
    validnum_ifelse_unsound_01: "verify_units/validnum_ifelse_unsound_1" => "unsound_sized_ifelse" => "ValidNum",
}

// ================ ValidPtr Sound Cases =============
sound_tests! {
    validptr_sound_01: "verify_units/validptr_sound_1" => "sound_zst_dangling_valid_for_any_len",
    validptr_sound_02: "verify_units/validptr_sound_2" => "sound_stack_array_full_range",
    validptr_sound_03: "verify_units/validptr_sound_3" => "sound_slice_suffix_guarded",
    validptr_sound_04: "verify_units/validptr_sound_4" => "sound_scc_each_slice_element",
    validptr_sound_05: "verify_units/validptr_sound_5" => "sound_signed_suffix_guarded",
}

// ================ ValidPtr Unsound Cases =============
unsound_tests! {
    validptr_unsound_01: "verify_units/validptr_unsound_1" => "unsound_non_zst_dangling_not_allocated" => "ValidPtr",
    validptr_unsound_02: "verify_units/validptr_unsound_2" => "unsound_one_past_requires_one_element" => "ValidPtr",
    validptr_unsound_03: "verify_units/validptr_unsound_3" => "unsound_stack_array_len_too_large" => "ValidPtr",
    validptr_unsound_04: "verify_units/validptr_unsound_4" => "unsound_scc_branch_uses_one_past" => "ValidPtr",
    validptr_unsound_05: "verify_units/validptr_unsound_5" => "unsound_signed_suffix_missing_lower_bound" => "ValidPtr",
}

// ================ Deref Unsound Cases =============
unsound_tests! {
    deref_unsound_01: "verify_units/deref_unsound_1" => "unsound_deref_one_past" => "Deref",
}

// ================ Alias Sound Verify Cases =============
sound_tests! {
    alias_sound_01: "verify_units/alias_sound_01" => "sound_shared_slice_no_raw_mutation",
    alias_sound_02: "verify_units/alias_sound_02" => "sound_raw_use_after_slice_scope",
    alias_sound_03: "verify_units/alias_sound_03" => "sound_box_from_raw_consumes_pointer",
    alias_sound_04: "verify_units/alias_sound_04" => "sound_struct_slice_only",
    alias_sound_05: "verify_units/alias_sound_05" => "sound_helper_shared_slice",
    alias_sound_06: "verify_units/alias_sound_06" => "sound_cstr_from_ptr_read_only",
    alias_sound_07: "verify_units/alias_sound_07" => "PrivateSlot::as_slice_mut",
    alias_sound_08: "verify_units/alias_sound_08" => "ReadOnlySlot::<'a>::as_slice",
    alias_sound_09: "verify_units/alias_sound_09" => "sound_box_from_raw_then_into_raw",
    alias_sound_10: "verify_units/alias_sound_10" => "sound_cstring_from_raw_no_reuse",
    alias_sound_11: "verify_units/alias_sound_11" => "sound_copy_nonoverlapping_disjoint",
    alias_sound_12: "verify_units/alias_sound_12" => "sound_vec_reserve_before_raw_slice",
    alias_sound_13: "verify_units/alias_sound_13" => "as_bytes_mut_sound",
    alias_sound_14: "verify_units/alias_sound_14" => "as_bytes_sound",
}

// ================ Alias Unsound Verify Cases =============
unsound_hazard_tests! {
    alias_unsound_03: "verify_units/alias_unsound_03" => "unsound_vec_push_while_raw_slice_live" => "Alias",
    alias_unsound_04: "verify_units/alias_unsound_04" => "unsound_box_from_raw_then_raw_write" => "Alias",
    alias_unsound_09: "verify_units/alias_unsound_09" => "unsound_cstring_from_raw_then_raw_write" => "Alias",
    alias_unsound_10: "verify_units/alias_unsound_10" => "unsound_cstr_from_ptr_then_raw_mutation" => "Alias",
    alias_unsound_15: "verify_units/alias_unsound_15" => "unsound_vec_from_raw_parts_then_raw_write" => "Alias",
    alias_unsound_16: "verify_units/alias_unsound_16" => "unsound_vec_reserve_while_raw_slice_live" => "Alias",
    alias_unsound_18: "verify_units/alias_unsound_18" => "as_bytes_mut_unsound" => "Alias",
    alias_unsound_19: "verify_units/alias_unsound_19" => "as_bytes_mut_ptr_missing_alias" => "Alias",
}

// ================ NonOverlap Sound Cases =============
sound_tests! {
    nonoverlap_sound_01: "verify_units/nonoverlap_sound_01" => "sound_copy_nonoverlapping_adjacent",
    nonoverlap_sound_02: "verify_units/nonoverlap_sound_02" => "sound_copy_nonoverlapping_disjoint",
}

// ================ User-Defined DSL Contract (pred!) Case =============
sound_tests! {
    dsl_custom_def: "verify_units/dsl_custom_def" => "sound_read",
}


// ================ Align Repeat Threshold Cases =============
#[test]
fn align_repeat_threshold_repeat1() {
    let output = run_with_args("verify_units/align_repeat_threshold", CMD_VERIFY_REPEAT_1);
    assert_unproved_exclusive(&output, "repeat2_reveals_delayed_unaligned", &["Align"]);
}

#[test]
fn align_repeat_threshold_repeat2() {
    let output = run_with_args("verify_units/align_repeat_threshold", CMD_VERIFY_REPEAT_2);
    assert_unproved_exclusive(&output, "repeat2_reveals_delayed_unaligned", &["Align"]);
}

// ================ Loop Repeat Threshold Cases =============
#[test]
fn loop_repeat_threshold_repeat1_all() {
    let output = run_with_args("verify_units/loop_repeat_threshold", CMD_VERIFY_REPEAT_1);
    for func in [
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
    ] {
        assert_function_result(&output, func, "SOUND");
    }
}

#[test]
fn loop_repeat_threshold_repeat2_all() {
    let output = run_with_args("verify_units/loop_repeat_threshold", CMD_VERIFY_REPEAT_2);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_align", &["Align"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_nonnull", &["NonNull"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_allocated", &["Allocated"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validptr", &["ValidPtr"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_deref", &["Deref"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_init", &["Init"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_typed", &["Typed"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_inbound_counter", &["InBound"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validnum_counter", &["ValidNum"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validnum_parity_oscillation", &["ValidNum"]);
}

#[test]
fn loop_repeat_threshold_auto_cases() {
    let output = run_with_args("verify_units/loop_repeat_threshold", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_align", &["Align"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_nonnull", &["NonNull"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_allocated", &["Allocated"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validptr", &["ValidPtr"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_deref", &["Deref"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_init", &["Init"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_typed", &["Typed"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_inbound_counter", &["InBound"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validnum_counter", &["ValidNum"]);
    assert_unproved_exclusive(&output, "repeat1_sound_repeat2_unsound_validnum_parity_oscillation", &["ValidNum"]);
}

// ================ ValidCStr Manual Cases =============
#[test]
fn validcstring_std_unsound_09() {
    let output = run_with_args("verify_units/validcstring_std_unsound_09", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "unsound_from_ptr_suffix_without_nul", &["ValidCStr", "InBound"]);
}

// ================ NonNull Manual Cases =============
#[test]
fn nonnull_sound_01() {
    let output = run_with_args("verify_units/nonnull_sound_1", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: caller_with_contract");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_chained_propagation");
    assert_contain(&output, "result: SOUND");
}

// ================ InBound Manual Cases =============
#[test]
fn inbound_std_unsound_02() {
    let output = run_with_args("verify_units/inbound_std_unsound_2", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_dst_unguarded",
        &["ValidPtr", "NonOverlap", "ValidNum"],
    );
}

// ================ AsChunks Sound Cases =============
#[test]
fn as_chunks_sound_cases() {
    let output = run_with_args("verify_units/as_chunks_sound_01", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: sound_as_chunks_unchecked_exact_div");
    assert_contain(&output, "result: SOUND");
    assert_contain(&output, "function: sound_exact_div_guard");
    assert_contain(&output, "result: SOUND");
}

// ================ ValidNum Manual Unsound Cases =============
#[test]
fn validnum_std_unsound_01() {
    let output = run_with_args("verify_units/validnum_std_unsound_1", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "unsound_std_from_raw_parts_validnum_overflow",
        &["ValidNum", "ValidPtr", "Init"],
    );
}

#[test]
fn validnum_std_unsound_02() {
    let output = run_with_args("verify_units/validnum_std_unsound_2", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "unsound_std_copy_nonoverlapping_validnum",
        &["ValidNum", "ValidPtr", "NonOverlap"],
    );
}

// ================ AsChunks Unsound Cases =============
#[test]
fn as_chunks_unsound_cases() {
    let output = run_with_args("verify_units/as_chunks_unsound_01", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "unsound_as_chunks_unchecked_missing_exact_div",
        &["ValidNum"],
    );
    assert_unproved_exclusive(&output, "unsound_exact_div_missing_guard", &["ValidNum"]);
}

// ================ Deref Sound Cases =============
#[test]
fn deref_sound_cases() {
    let output = run_with_args("verify_units/deref_sound_1", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: sound_deref_slice_prefix");
    assert_contain(&output, "Deref | Proved");
    assert_contain(&output, "result: SOUND");
}

// ================ Typed Provenance Cases =============
#[test]
fn typed_provenance_cases() {
    let output = run_with_args("verify_units/typed_cases", CMD_VERIFY_TARGETED);
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

// ================ Alive Sound Cases =============
#[test]
fn alive_sound_01() {
    let output = run_with_args("verify_units/alive_sound_01", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: SliceHost::<'a, T>::get");
    assert_contain(&output, "Alive | Proved");
}

#[test]
fn alive_sound_02() {
    let output = run_with_args("verify_units/alive_sound_02", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: MutSliceHost::<'a, T>::get_mut");
    assert_contain(&output, "Alive | Proved");
}

#[test]
fn alive_sound_03() {
    let output = run_with_args("verify_units/alive_sound_03", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: slice_from_host");
    assert_contain(&output, "Alive | Proved");
}

// ================ Alive Unsound Cases =============
#[test]
fn alive_unsound_01() {
    let output = run_with_args("verify_units/alive_unsound_01", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "DangerousAliaser::<'a, T>::get_mut",
        &["Alive", "NonNull", "ValidPtr"],
    );
}

#[test]
fn alive_unsound_02() {
    let output = run_with_args("verify_units/alive_unsound_02", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "slice_tied_to_unrelated_host",
        &["ValidNum", "Alive", "ValidPtr", "Init", "NonNull", "Alias"],
    );
}

#[test]
fn alive_unsound_03() {
    let output = run_with_args("verify_units/alive_unsound_03", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(
        &output,
        "static_slice_from_local_vec",
        &["Alive", "Init", "Alias", "Align", "NonNull", "ValidPtr"],
    );
}

// ================ Struct Invariant =============
#[test]
fn struct_invariant() {
    let output = run_with_args("verify_units/struct_invariant_1", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: Wrapper::<T>::new");
    assert_contain(&output, "Align | Proved");
    assert_contain(&output, "InBound | Proved");
    assert_contain(&output, "Init | Proved");
    assert_contain(&output, "function: Wrapper::<T>::set_len");
    assert_contain(&output, "function: Wrapper::<T>::read");
    assert_contain(&output, "function: Wrapper::<T>::read_unchecked");
}

// ================ Skip Invariant Cases =============
#[test]
fn skip_invariant_struct_noinvariant_1() {
    let output = run_with_args("verify_units/struct_noinvariant_1", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn skip_invariant_struct_noinvariant_2() {
    let output = run_with_args("verify_units/struct_noinvariant_2", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "result: SOUND");
}

#[test]
fn skip_invariant_sound_callee() {
    let output = run_with_args("verify_units/align_sound_1", CMD_VERIFY_SKIP_INVARIANT);
    assert_contain(&output, "function: sound_named_contract_binds_callsite_arg");
    assert_contain(&output, "result: SOUND");
}

// ================ Split Transmute Cases =============
#[test]
fn split_transmute_unsound() {
    let output = run_with_args("verify_units/split_transmute_unsound", CMD_VERIFY_TARGETED);
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
    let output = run_with_args("verify_units/split_transmute_nonzero", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: align_to_nonzero_u16");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u32");
    assert_contain(&output, "result: UNSOUND");
    assert_contain(&output, "function: align_to_nonzero_u8");
    assert_contain(&output, "result: UNSOUND");
}

#[test]
fn split_transmute_sound() {
    let output = run_with_args("verify_units/split_transmute_sound", CMD_VERIFY_TARGETED);
    assert_contain(&output, "function: align_to_u8_sound");
    assert_contain(&output, "result: SOUND");
}

// ================ Trait Unsound Cases =============
#[test]
fn trait_unsound_prepare() {
    let output = run_with_args("verify_units/trait_unsound_1", &["verify", "--prepare-targets"]);
    assert_contain(&output, "prepare targets for unsafe trait: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "NonNull");
}

#[test]
fn trait_unsound_verify() {
    let output = run_with_args("verify_units/trait_unsound_1", CMD_VERIFY_TARGETED);
    assert_contain(&output, "unsafe trait impl: Buffer");
    assert_contain(&output, "impl for: VecBuf");
    assert_contain(&output, "ensures");
    assert_contain(&output, "NonNull");
    assert_contain(&output, "verification: deferred");
}

// ================ Alias Multi-Property Unsound Cases =============
#[test]
fn alias_unsound_01() {
    let output = run_with_args("verify_units/alias_unsound_01", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive_with_result(&output, "unsound_shared_slice_then_raw_write", &["Alias", "ValidNum"], "UNSOUND");
}

#[test]
fn alias_unsound_02() {
    let output = run_with_args("verify_units/alias_unsound_02", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive_with_result(&output, "unsound_mut_slice_then_raw_read", &["Alias", "ValidNum"], "UNSOUND");
}

#[test]
fn alias_unsound_20() {
    let output = run_with_args("verify_units/alias_unsound_20", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive_with_result(&output, "as_bytes_mut_ptr_len_missing_alias", &["Alias", "ValidNum"], "UNSOUND");
}

// Custom test: from_raw_parts wrong element type causes multiple failures
#[test]
fn init_std_unsound_07() {
    let output = run_with_args("verify_units/init_std_unsound_7", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive_with_result(&output, "unsound_from_raw_parts_wrong_element_type", &["Init", "Align", "ValidPtr"], "UNSOUND");
}

#[test]
fn alias_unsound_05() {
    let output = run_with_args("verify_units/alias_unsound_05", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "unsound_box_from_raw_drop_then_raw_read", &["Alias", "Allocated", "ValidPtr", "Typed"]);
}

#[test]
fn alias_unsound_06() {
    let output = run_with_args("verify_units/alias_unsound_06", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "RawSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn alias_unsound_07() {
    let output = run_with_args("verify_units/alias_unsound_07", &["verify"]);
    assert_unproved_exclusive(&output, "make_mut_slice", &["Alias", "Alive", "Init", "NonNull", "ValidPtr", "ValidNum"]);
}

// ================ NonOverlap Unsound Cases =============
#[test]
fn nonoverlap_unsound_01() {
    let output = run_with_args("verify_units/nonoverlap_unsound_01", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "unsound_copy_nonoverlapping_overlap", &["NonOverlap"]);
}

// ================ Alias Long Multi-Property Unsound Cases =============
#[test]
fn alias_unsound_11() {
    let output = run_with_args("verify_units/alias_unsound_11", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "PublicRawSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn alias_unsound_12() {
    let output = run_with_args("verify_units/alias_unsound_12", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "GetterSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn alias_unsound_13() {
    let output = run_with_args("verify_units/alias_unsound_13", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "WriterSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn alias_unsound_14() {
    let output = run_with_args("verify_units/alias_unsound_14", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "SplitSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

#[test]
fn alias_unsound_17() {
    let output = run_with_args("verify_units/alias_unsound_17", CMD_VERIFY_TARGETED);
    assert_unproved_exclusive(&output, "TraitSlot::as_slice_mut", &["Alias", "Alive", "Init", "NonNull", "ValidPtr"]);
}

// ================ Module/Crate Filter Tests =============
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
        &["verify", "--mode", "targeted", "--crate", "module_filter_crate"],
    );
    assert_contain(&output, "function: a::f");
    assert_contain(&output, "function: b::g");
    assert_contain(&output, "function: c::h");

    let output = run_with_args(
        "verify_units/module_filter_crate",
        &["verify", "--mode", "targeted", "--crate", "module_filter_crate", "--module", "a"],
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

// ================ NoPadding (intrinsics::raw_eq) Cases =============
sound_tests! {
    raw_eq_sound_01: "verify_units/raw_eq_sound_01" => "sound_raw_eq_no_padding",
}

unsound_tests! {
    raw_eq_unsound_01: "verify_units/raw_eq_unsound_01" => "unsound_raw_eq_padded" => "NoPadding",
}
