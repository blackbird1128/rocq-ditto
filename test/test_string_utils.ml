open Alcotest
open Ditto.String_utils

let test_split_prefix_simple () =
  check
    (option (pair string string))
    "Splitting a simple prefix should return that prefix and the rest of the \
     string"
    (Some ("hello", "world"))
    (split_prefix "hello" "helloworld")

let test_splitting_prefix_is_string () =
  check
    (option (pair string string))
    "Spltting by prefix when the prefix is the whole string should return that \
     string and an empty string"
    (Some ("helloworld", ""))
    (split_prefix "helloworld" "helloworld")

let test_splitting_unexisting_prefix () =
  check
    (option (pair string string))
    "Splitting by prefix when the prefix isn't in the string should returns \
     None"
    None
    (split_prefix "zebra" "hello world")

let test_splitting_empty_prefix () =
  check
    (option (pair string string))
    "Splitting by prefix when the prefix is an empty string should return an \
     empty string and the string"
    (Some ("", "hello world"))
    (split_prefix "" "hello world")

let test_splitting_prefix_longer_than_container () =
  check
    (option (pair string string))
    "Splitting by prefix when the prefix is longer than the string should \
     return None"
    None
    (split_prefix "hello" "hell")

let test_remove_prefix_simple () =
  check string
    "Removing a simple prefix from a string should return that string without \
     the prefix"
    "world"
    (remove_prefix "helloworld" "hello")

let test_remove_prefix_prefix_is_whole_string () =
  check string
    "Removing a prefix when the prefix is the entire string should return an \
     empty string"
    ""
    (remove_prefix "helloworld" "helloworld")

let test_remove_prefix_not_existing_prefix () =
  check string "Removing a non-existing prefix should leave the string intact"
    "hello world"
    (remove_prefix "hello world" "zebra")

let test_remove_prefix_empty_prefix () =
  check string "Removing an empty prefix should leave the string intact"
    "hello world"
    (remove_prefix "hello world" "")

let test_remove_prefix_longer_than_container () =
  check string
    "Remove a prefix longer than the string should leave the string intact"
    "helloworld"
    (remove_prefix "helloworld" "helloworldworldworld")

let test_remove_suffix_simple () =
  check string
    "Removing a simple suffix from a string should return that string without \
     the suffix"
    "hello"
    (remove_suffix "helloworld" "world")

let test_remove_suffix_suffix_is_whole_string () =
  check string
    "Removing a suffix when the suffix is the entire string should return an \
     empty string"
    ""
    (remove_suffix "helloworld" "helloworld")

let test_remove_suffix_not_existing_suffix () =
  check string "Removing a non-existing suffix should leave the string intact"
    "hello world"
    (remove_suffix "hello world" "zebra")

let test_remove_suffix_empty_suffix () =
  check string "Removing an empty suffix should leave the string intact"
    "hello world"
    (remove_suffix "hello world" "")

let test_remove_suffix_longer_than_container () =
  check string
    "Remove a suffix longer than the string should leave the string intact"
    "helloworld"
    (remove_suffix "helloworld" "worldworldhelloworld")

let test_simple_contains () =
  check bool "\"hello world\" should contains \"world\"" true
    (contains ~substring:"world" "hello world")

let test_simple_not_contains () =
  check bool "\"hello world\" should not contains \"zebra\"" false
    (contains ~substring:"zebra" "hello world")

let test_not_contains_substring_longer_than_container () =
  check bool "\"hello world\" should not contains \"hello world from tests\""
    false
    (contains ~substring:"hello world from tests" "hello world")

let test_zero_size_container_substring () =
  check bool "An empty string should no contains a substring" false
    (contains ~substring:"hello" "")

let test_zero_size_substring_contained_anywhere () =
  check bool "An empty substring should be found in any string" true
    (contains ~substring:"" "hello")

let () =
  run "String utils"
    [
      ( "String utils tests",
        [
          test_case "test splitting a simple prefix from a string" `Quick
            test_split_prefix_simple;
          test_case "test splitting a prefix when it is the entire string"
            `Quick test_splitting_prefix_is_string;
          test_case "test splitting by an unexisting prefix" `Quick
            test_splitting_unexisting_prefix;
          test_case "test splitting by an empty prefix" `Quick
            test_splitting_empty_prefix;
          test_case "test splitting by a prefix longer than the string" `Quick
            test_splitting_prefix_longer_than_container;
          test_case "test removing a simple prefix" `Quick
            test_remove_prefix_simple;
          test_case
            "test removing a prefix when it is the entire string" `Quick
            test_remove_prefix_prefix_is_whole_string;
          test_case "test removing a non-existing prefix" `Quick
            test_remove_prefix_not_existing_prefix;
          test_case "test removing an empty prefix" `Quick
            test_remove_prefix_empty_prefix;
          test_case
            "test removing a prefix longer than the string" `Quick
            test_remove_prefix_longer_than_container;
          test_case "test removing a simple suffix" `Quick
            test_remove_suffix_simple;
          test_case
            "test removing a suffix when it is the entire string" `Quick
            test_remove_suffix_suffix_is_whole_string;
          test_case "test removing a non-existing suffix" `Quick
            test_remove_suffix_not_existing_suffix;
          test_case "test removing an empty suffix" `Quick
            test_remove_suffix_empty_suffix;
          test_case
            "test removing a suffix longer than the string" `Quick
            test_remove_suffix_longer_than_container;
          test_case "test a simple string containing a simple substring" `Quick
            test_simple_contains;
          test_case
            "test a simple string doesn't contains an unrelated substring"
            `Quick test_simple_not_contains;
          test_case "test that a string doesn't contains a longer substring"
            `Quick test_not_contains_substring_longer_than_container;
          test_case "test that an empty string doesn't contain a substring"
            `Quick test_zero_size_container_substring;
          test_case "test that an empty substring is contained in any string"
            `Quick test_zero_size_substring_contained_anywhere;
        ] );
    ]
