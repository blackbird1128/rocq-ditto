open Bechamel
open Toolkit
open Ditto

(* This is our /protected/ function which take an argument and return a simple
   function: [unit -> 'a]. The function must be wrapped into a [Staged.t].

   NOTE: [words] is __outside__ our [(unit -> 'a) Staged.t]*)

(* let make_list words = *)
(*   Staged.stage @@ fun () -> *)
(*   let rec go n acc = if n = 0 then acc else go (n - 1) (n :: acc) in *)
(*   ignore (go ((words / 3) + 1) []) *)

(* From our function [make_list], we make an indexed (by [args]) test. It's a list
   of tests which are applied with [args] such as:

    {[
      let test =
        [ make_list 0
        ; make_list 10
        ; make_list 100
        ; make_list 400
        ; make_list 1000 ]
    ]} *)

let head_opt_list (words : int) =
  Staged.stage @@ fun () ->
  let words_list = List.init words (fun _ -> 0) in
  List_utils.head_opt words_list |> Sys.opaque_identity

let last_and_len_fun_split (words : int) =
  Staged.stage @@ fun () ->
  let words_list = List.init words (fun _ -> 0) in
  ( List_utils.last words_list |> Sys.opaque_identity,
    List.length words_list |> Sys.opaque_identity )

let last_and_len_fun_list (words : int) =
  Staged.stage @@ fun () ->
  let words_list = List.init words (fun _ -> 0) in
  List_utils.last_and_len words_list |> Sys.opaque_identity

let array_list (words : int) =
  Staged.stage @@ fun () ->
  Array.init words Fun.id |> Array.to_list |> Sys.opaque_identity

let head_opt_list_tests =
  Test.make_indexed ~name:"head opt" ~args:[ 10; 100; 1000 ] head_opt_list

let last_and_len_tests =
  Test.make_indexed ~name:"last and len fun" ~args:[ 10; 100; 1000 ]
    last_and_len_fun_list

let last_and_len_split_tests =
  Test.make_indexed ~name:"last and len split" ~args:[ 10; 100; 1000 ]
    last_and_len_fun_split

let array_tests =
  Test.make_indexed ~name:"array" ~args:[ 10; 100; 1_000 ] array_list

let tests =
  Test.make_grouped ~name:"list"
    [
      head_opt_list_tests;
      array_tests;
      last_and_len_tests;
      last_and_len_split_tests;
    ]

(* let test = *)
(*   Test.make_indexed ~name:"list" ~fmt:"%s %d" ~args:[ 0; 10; 100; 400; 1000 ] *)
(*     make_list *)

(* From our test, we can start to benchmark it!

   A benchmark is a /run/ of your test multiple times. From results given by
   [Benchmark.all], an analyse is needed to infer measures of one call of your
   test.

   [Bechamel] asks 3 things:
   - what you want to record (see [instances])
   - how you want to analyse (see [ols])
   - how you want to benchmark your test (see [cfg])

   The core of [Bechamel] (see [Bechamel.Toolkit]) has some possible measures
   such as the [monotonic-clock] to see time performances.

   The analyse can be OLS (Ordinary Least Square) or RANSAC. In this example, we
   use only one.

   Finally, to launch the benchmark, we need some others details such as:
   - should we stabilise the GC?
   - how many /run/ you want
   - the maximum of time allowed by the benchmark
   - etc.

   [raw_results] is what the benchmark produced. [results] is what the analyse
   can infer. The first one is used to show graphs or to let the user (with
   [Measurement_raw]) to infer something else than what [ols] did. The second is
   mostly what you want: a synthesis of /samples/. *)

let benchmark () =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:Measure.[| run |]
  in

  let cfg =
    Benchmark.cfg ~limit:2_000 ~quota:(Time.second 1.0) ~stabilize:true ()
  in
  let raw_results =
    Benchmark.all cfg
      [ Instance.monotonic_clock; Instance.major_allocated ]
      tests
  in
  Analyze.all ols Instance.monotonic_clock raw_results

let print_result (name, result) =
  match Analyze.OLS.estimates result with
  | Some [ nanoseconds ] ->
      let r_square =
        match Analyze.OLS.r_square result with
        | Some value -> Printf.sprintf "%.4f" value
        | None -> "n/a"
      in
      Printf.printf "%-24s %12.2f ns   r² %s\n" name nanoseconds r_square
  | _ -> Format.printf "%-24s %a@." name Analyze.OLS.pp result

let () =
  Printf.printf "benchmark                     time per run        fit\n";
  Printf.printf "------------------------------------------------------\n";
  benchmark () |> Hashtbl.to_seq |> List.of_seq
  |> List.sort (fun (left, _) (right, _) -> String.compare left right)
  |> List.iter print_result
