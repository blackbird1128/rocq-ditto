open Alcotest
open Ditto.String_utils
open Ditto_test_support.Test_support
open Ditto

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

let test_split_words_simple () =
  check (list string) "Each word should be split correctly at the space"
    [ "hello"; "world" ]
    (split_words "hello world")

let test_split_words_empty () =
  check (list string) "An empty string should return no words" []
    (split_words "")

let test_split_words_multiple_spaces () =
  check (list string) "Each word should be split correctly, normalizing spaces"
    [ "hello"; "world" ]
    (split_words "hello   world")

let test_split_words_tab () =
  check (list string) "Each word should be split correctly at the tab"
    [ "hello"; "world" ]
    (split_words "hello\tworld")

let test_split_words_trimming () =
  check (list string) "Each word should be trimmed correctly at both ends"
    [ "hello"; "world" ]
    (split_words "  hello  world  ")

let test_split_at_simple () =
  check
    (result (pair string string) error_testable)
    "The words should be split at ','"
    (Ok ("hello", "world"))
    (split_at ',' "hello,world")

let test_split_at_empty () =
  check
    (result (pair string string) error_testable)
    "split_at on an empty string should return an error"
    (Error.string_to_or_error "Couldn't find the split point ',' in \"\"")
    (split_at ',' "")

let test_split_at_first () =
  check
    (result (pair string string) error_testable)
    "split_at should split at the first occurrence"
    (Ok ("hello", "world,there"))
    (split_at ',' "hello,world,there")

let test_split_at_no_separator () =
  check
    (result (pair string string) error_testable)
    "split_at should fail when the separator is absent"
    (Error.format_to_or_error "Couldn't find the split point %C in %S" ','
       "helloworld")
    (split_at ',' "helloworld")

let test_split_at_first_char () =
  check
    (result (pair string string) error_testable)
    "split_at should return an empty string and the rest of the string when \
     the separator is the first char"
    (Ok ("", "hey there"))
    (split_at ',' ",hey there")

let test_split_at_last_char () =
  check
    (result (pair string string) error_testable)
    "split_at should return the first part of the string and an empty string \
     when the separator is the last char"
    (Ok ("hey there", ""))
    (split_at ',' "hey there,")

let test_cut_simple () =
  check
    (result (pair string string) error_testable)
    "the string should be cut at -<8-"
    (Ok ("cut", "here"))
    (cut "->8-" "cut->8-here")

let test_cut_empty_string () =
  check
    (result (pair string string) error_testable)
    "an empty string should not be cut"
    (Error.format_to_or_error "Couldn't find the cut point \"->8-\" in \"\"")
    (cut "->8-" "")

let test_cut_no_cut_point () =
  check
    (result (pair string string) error_testable)
    "cut should fail when the cut string isn't in the container"
    (Error.format_to_or_error "Couldn't find the cut point %S in %S" "--"
       "helloworld")
    (cut "--" "helloworld")

let test_cut_first_occurence () =
  check
    (result (pair string string) error_testable)
    "cut should cut at the first occurrence"
    (Ok ("cut", "here--not--here"))
    (cut "--" "cut--here--not--here")

let test_cut_prefix () =
  check
    (result (pair string string) error_testable)
    "cut on a prefix should return an empty string and the rest of the string"
    (Ok ("", "world"))
    (cut "prefix" "prefixworld")

let test_cut_suffix () =
  check
    (result (pair string string) error_testable)
    "cut on a suffix should return the first part of the string and an empty \
     string"
    (Ok ("world", ""))
    (cut "suffix" "worldsuffix")

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
          test_case "test removing a prefix when it is the entire string" `Quick
            test_remove_prefix_prefix_is_whole_string;
          test_case "test removing a non-existing prefix" `Quick
            test_remove_prefix_not_existing_prefix;
          test_case "test removing an empty prefix" `Quick
            test_remove_prefix_empty_prefix;
          test_case "test removing a prefix longer than the string" `Quick
            test_remove_prefix_longer_than_container;
          test_case "test removing a simple suffix" `Quick
            test_remove_suffix_simple;
          test_case "test removing a suffix when it is the entire string" `Quick
            test_remove_suffix_suffix_is_whole_string;
          test_case "test removing a non-existing suffix" `Quick
            test_remove_suffix_not_existing_suffix;
          test_case "test removing an empty suffix" `Quick
            test_remove_suffix_empty_suffix;
          test_case "test removing a suffix longer than the string" `Quick
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
          test_case "test splitting a simple string of two words" `Quick
            test_split_words_simple;
          test_case "test splitting words in an empty string" `Quick
            test_split_words_empty;
          test_case "test splitting words separated by multiple spaces" `Quick
            test_split_words_multiple_spaces;
          test_case "test splitting words separated by a tab" `Quick
            test_split_words_tab;
          test_case "test splitting words correctly trim" `Quick
            test_split_words_trimming;
          test_case "test splitting at char simple string" `Quick
            test_split_at_simple;
          test_case "test splitting at char empty string" `Quick
            test_split_at_empty;
          test_case "test splitting at char with separator absent" `Quick
            test_split_at_no_separator;
          test_case "test splitting at char, multiple separators" `Quick
            test_split_at_first;
          test_case "test splitting at char on the first char" `Quick
            test_split_at_first_char;
          test_case "test splitting at char on the last char" `Quick
            test_split_at_last_char;
          test_case "test cutting at string simple string" `Quick
            test_cut_simple;
          test_case "test cutting a string with no cut point" `Quick
            test_cut_no_cut_point;
          test_case "test cutting at string empty string" `Quick
            test_cut_empty_string;
          test_case "test cutting the first occurrence" `Quick
            test_cut_first_occurence;
          test_case "test cutting at the prefix of a string" `Quick
            test_cut_prefix;
          test_case "test cutting at the suffix of a string" `Quick
            test_cut_suffix;
        ] );
    ]
