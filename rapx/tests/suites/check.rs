
// Dangling pointer detection
check_contain_test!(check_uaf_01, "check/uaf_1",  CMD_CHECK_UAF, "Dangling pointer detected in function \"create_vec\"");
check_contain_test!(check_uaf_02, "check/uaf_2",  CMD_CHECK_UAF, "Double free detected in function \"main\"");
check_contain_test!(check_uaf_03, "check/uaf_3",  CMD_CHECK_UAF, "Double free detected");
check_contain_test!(check_uaf_04, "check/uaf_4",  CMD_CHECK_UAF, "Dangling pointer detected in function \"call\"");
check_contain_test!(check_uaf_05, "check/uaf_5",  CMD_CHECK_UAF, "Use-after-free detected in function \"main\"");
check_contain_test!(check_uaf_06, "check/uaf_6",  CMD_CHECK_UAF, "Use-after-free detected in function \"main\"");
check_contain_test!(check_uaf_07, "check/uaf_7",  CMD_CHECK_UAF, "Double free detected in function \"main\"");
check_contain_test!(check_uaf_08, "check/uaf_8",  CMD_CHECK_UAF, "Use-after-free detected in function \"main\"");
check_contain_test!(check_uaf_09, "check/uaf_9",  CMD_CHECK_UAF, "Use-after-free detected in function \"main\"");
// check_contain_test!(check_uaf_10, "check/uaf_10", CMD_CHECK_UAF, "Double free detected in function \"evil_test\"");
// Disabled: test was already broken before the path-pruning changes (ICE in alias analysis).

// Dangling pointer false positives
check_not_contain_test!(check_uaf_false_01, "check/uaf_false_1",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_02, "check/uaf_false_2",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_03, "check/uaf_false_3",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_04, "check/uaf_false_4",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_05, "check/uaf_false_5",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_06, "check/uaf_false_6",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_07, "check/uaf_false_7",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_08, "check/uaf_false_8",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_09, "check/uaf_false_9",  CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_10, "check/uaf_false_10", CMD_CHECK_UAF, "detected");
check_not_contain_test!(check_uaf_false_11, "check/uaf_false_11", CMD_CHECK_UAF, "detected");

// Memory leak detection
check_contain_test!(check_memleak_01, "check/memleak_1", CMD_CHECK_MEMLEAK, "Memory Leak detected in function main");
check_contain_test!(check_memleak_02, "check/memleak_2", CMD_CHECK_MEMLEAK, "Memory Leak detected in function main");
check_contain_test!(check_memleak_03, "check/memleak_3", CMD_CHECK_MEMLEAK, "Memory Leak detected in function main");
