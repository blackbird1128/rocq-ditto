open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr

let normalize_strings (strings : string list) : string list =
  List.map (fun str -> String.trim str) strings

let testable_nary_tree pp_a equal_a =
  Alcotest.testable (pp_nary_tree pp_a) (equal_nary_tree equal_a)

let document_to_range_representation_pairs (doc : Coq_document.t) :
    (string * Lang.Range.t) list =
  List.map (fun node -> (node.repr, node.range)) doc.elements

let parse_json_target (json : Yojson.Safe.t) : (string * Lang.Range.t) list =
  let open Yojson.Safe.Util in
  json |> to_list
  |> List.map (fun elem ->
         let range = range_of_yojson (member "range" elem) in
         let repr = to_string (member "repr" elem) in
         (repr, range))

let get_target (uri_str : string) =
  let uri_str_without_ext = Filename.remove_extension uri_str in
  let target = uri_str_without_ext ^ "_target.v.target.json" in
  let target_doc = Yojson.Safe.from_file target in
  parse_json_target target_doc

let pp_int fmt x = Format.fprintf fmt "%d" x
let int_tree = testable_nary_tree pp_int ( = )
let proof_status_testable = Alcotest.testable Proof.pp_proof_status ( = )
let range_testable = Alcotest.testable Lang.Range.pp ( = )
let uuidm_testable = Alcotest.testable Uuidm.pp ( = )
let error_testable = Alcotest.testable Error.pp ( = )

let make_dummy_node start_line start_char start_offset end_line end_char
    end_offset : syntaxNode =
  {
    ast = None;
    repr = "dummy";
    id = Unique_id.uuid ();
    proof_id = None;
    diagnostics = [];
    range =
      {
        start =
          { line = start_line; character = start_char; offset = start_offset };
        end_ = { line = end_line; character = end_char; offset = end_offset };
      };
  }

let make_dummy_node_from_repr start_line start_char start_offset repr :
    syntaxNode =
  let start_point : Lang.Point.t =
    { line = start_line; character = start_char; offset = start_offset }
  in
  let range = Range_utils.range_from_starting_point_and_repr start_point repr in
  {
    ast = None;
    repr;
    id = Unique_id.uuid ();
    proof_id = None;
    diagnostics = [];
    range;
  }

let check_list_sorted ~cmp ~pp lst =
  let rec find_failure idx = function
    | [] | [ _ ] -> None
    | x :: y :: rest ->
        if cmp x y <= 0 then find_failure (idx + 1) (y :: rest)
        else Some (idx, x, y)
  in
  match find_failure 0 lst with
  | None -> ()
  | Some (idx, x, y) ->
      let pp_list = Fmt.Dump.list pp in
      let list_str = Format.asprintf "@[<v>Full list:@ %a@]" pp_list lst in
      Alcotest.failf "List is not sorted at index %d: %a > %a\n%s" idx pp x pp y
        list_str

let create_fixed_test (test_text : string) (f : Doc.t -> unit -> unit)
    (doc : Doc.t) =
  Alcotest.test_case test_text `Quick (f doc)

let test_parsing_ex1 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> elem.repr) doc.elements in
  Alcotest.(check int)
    "More than one element was parsed." 1 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match" [ "Compute 1 + 1." ] nodes_repr

let test_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let nodes_repr = List.map (fun elem -> elem.repr) doc.elements in
  Alcotest.(check int)
    "The wrong number of elements was parsed" 7 (List.length nodes_repr);
  Alcotest.(check (list string))
    "parsed element don't match"
    [
      "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B.";
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    nodes_repr

let test_proof_parsing_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.(check proof_status_testable)
    "The proof should be proved." Proof.Proved proof.status

let test_parsing_admit (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be admitted."
    Proof.Admitted proof.status

let test_parsing_defined (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_function (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved."
    Proof.Proved proof.status

let test_parsing_abort1 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be aborted."
    Proof.Aborted proof.status

let test_parsing_abort2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 2 (List.length proofs);
  let first_proof = List.hd proofs in
  let second_proof = List.nth proofs 1 in
  Alcotest.check proof_status_testable "The first proof should be aborted"
    Proof.Aborted first_proof.status;
  Alcotest.check proof_status_testable "The second proof is proved" Proof.Proved
    second_proof.status

let test_proof_parsing_name_and_steps_ex2 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proof = List.hd (Result.get_ok (Coq_document.get_proofs doc)) in
  Alcotest.(check string)
    "The proof name should be modus ponens" "modus_ponens"
    (Option.default "got none" (Proof.get_proof_name proof));
  Alcotest.(check int)
    "The proof should have 6 steps (including Proof. and Qed.)" 6
    (List.length proof.proof_steps);
  Alcotest.(check string)
    "The proof expression is wrong."
    "Theorem modus_ponens:\n  forall A B: Prop, A /\\ (A -> B) -> B."
    proof.proposition.repr;
  let proof_steps_normalized =
    normalize_strings (List.map (fun s -> s.repr) proof.proof_steps)
  in
  Alcotest.(check (list string))
    "The proof should have the following steps."
    [
      "Proof.";
      "intros.";
      "destruct H as [H1 H2].";
      "apply H2.";
      "assumption.";
      "Qed.";
    ]
    proof_steps_normalized

let test_proof_parsing_multiple_proofs_ex3 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed" 2 (List.length proofs);
  let proof_names = List.filter_map (fun p -> Proof.get_proof_name p) proofs in
  Alcotest.(check (list string))
    "One or more proof does't have the correct name"
    [ "and_split"; "and_split_bis" ]
    proof_names;
  ()

let test_parsing_comment_ex4 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  Alcotest.(check int)
    "The wrong number of nodes was parsed" 1 (List.length doc.elements);
  let node = List.hd doc.elements in
  Alcotest.(check string)
    "Comment was badly parsed" "(* single comment *)" node.repr;
  Alcotest.(check bool)
    "Comment node should not have an AST" true (Option.is_empty node.ast)

let test_parsing_multiples_comments_ex5 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 5
    (List.length comment_nodes);
  Alcotest.(check int)
    "The wrong number of total nodes was parsed" 12 (List.length doc.elements)

let test_parsing_embedded_comments_ex6 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> node.repr) comment_nodes in
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(* in the same line comment *)"; "(* classical comment *)" ]
    comment_nodes_repr

let test_parsing_weird_comments_ex7 (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let comment_nodes =
    List.filter (fun node -> Option.is_empty node.ast) doc.elements
  in
  let comment_nodes_repr = List.map (fun node -> node.repr) comment_nodes in
  print_endline
    ("comment nodes length : " ^ string_of_int (List.length comment_nodes));
  Alcotest.(check int)
    "The wrong number of comment nodes was parsed" 2
    (List.length comment_nodes);
  Alcotest.(check (list string))
    "Comments badly parsed"
    [ "(*in the same line comment*)"; "(**weird comment*)" ]
    comment_nodes_repr

let test_parsing_instance (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in

  let proofs = Result.get_ok (Coq_document.get_proofs doc) in
  Alcotest.(check int)
    "The wrong number of proofs was parsed." 1 (List.length proofs);
  let first_proof = List.hd proofs in
  Alcotest.check proof_status_testable "The proof should be proved" Proof.Proved
    first_proof.status

let test_searching_node (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let first_node_id = (List.hd doc.elements).id in
  let node_compute = Coq_document.element_with_id_opt first_node_id doc in
  let node_compute_id = Option.map (fun node -> node.id) node_compute in
  Alcotest.(check (option uuidm_testable))
    "Item with the wrong id was retrieved" (Some first_node_id) node_compute_id;
  Alcotest.(check (option string))
    "The wrong repr was retrieved" (Some "Compute 1.")
    (Option.map (fun node -> node.repr) node_compute);
  let absurd_node = Coq_document.element_with_id_opt (Unique_id.uuid ()) doc in
  Alcotest.(check (option uuidm_testable))
    "No element should be retrieved" None
    (Option.map (fun x -> x.id) absurd_node)

let test_reformat_comment_node (doc : Doc.t) () : unit =
  let starting_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in

  let comment_node =
    comment_syntax_node_of_string "(* a comment *)" starting_point
    |> Result.get_ok
  in

  let reformatted_node = Syntax_node.reformat_node comment_node in
  let reformat_id = Result.map (fun x -> x.id) reformatted_node in

  Alcotest.(check (result uuidm_testable string))
    "Should return an error"
    (Error "The node need to have an AST to be reformatted") reformat_id

let test_reformat_keep_id (doc : Doc.t) () : unit =
  let starting_point : Lang.Point.t = { line = 0; character = 0; offset = 0 } in

  let content_node =
    syntax_node_of_string "Compute 1 + 1." starting_point |> Result.get_ok
  in

  let reformatted_node = Syntax_node.reformat_node content_node in
  let reformat_id = Result.map (fun x -> x.id) reformatted_node in

  Alcotest.(check (result uuidm_testable string))
    "Should return the same id" (Ok content_node.id) reformat_id

let test_id_assign_document (doc : Doc.t) () : unit =
  let doc = Coq_document.parse_document doc in
  let nodes_ids = List.map (fun x -> x.id) doc.elements in
  check_list_sorted ~cmp:Uuidm.compare ~pp:Uuidm.pp nodes_ids

let test_sorting_nodes (doc : Doc.t) () : unit =
  let node1 = make_dummy_node 0 0 1 0 12 13 in
  (* your example *)
  let node2 = make_dummy_node 0 14 15 1 2 18 in
  (* overlaps with node1 *)
  let node3 = make_dummy_node 2 0 19 2 10 29 in
  (* does not overlap *)

  let sorted = List.sort Syntax_node.compare_nodes [ node2; node3; node1 ] in
  let ids = List.map (fun n -> n.id) sorted in

  (* node1 and node2 overlap; smallest common = 18 *)
  (* node1 starts at 16 < 18 => node1 before node2 *)
  (* node3 is later and doesn't overlap *)
  let expected = [ node1.id; node2.id; node3.id ] in

  Alcotest.(check (list uuidm_testable))
    "The nodes should be ordered correctly" expected ids

let test_colliding_nodes_no_common_lines (doc : Doc.t) () : unit =
  let target_node = make_dummy_node 0 0 1 0 12 13 in
  let other_node = make_dummy_node 1 0 15 1 10 25 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_no_collision (doc : Doc.t) () : unit =
  let target_node = make_dummy_node_from_repr 0 0 1 "hello" in
  let other_node = make_dummy_node_from_repr 0 20 20 "world" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_common_line_collision (doc : Doc.t) () : unit =
  let target_node = make_dummy_node_from_repr 0 0 1 "hello" in
  let other_node = make_dummy_node_from_repr 0 3 4 "world" in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_colliding_nodes_one_common_line_no_collision (doc : Doc.t) () : unit =
  let target_node = make_dummy_node 0 0 1 1 10 15 in
  let other_node = make_dummy_node 1 12 17 1 20 25 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should not be colliding" [] colliding_nodes_ids

let test_colliding_nodes_multiple_common_lines_collision (doc : Doc.t) () : unit
    =
  let target_node = make_dummy_node 0 0 1 2 20 42 in
  let other_node = make_dummy_node 1 12 17 2 25 456 in

  let colliding_nodes_ids =
    Syntax_node.colliding_nodes target_node [ other_node ]
    |> List.map (fun node -> node.id)
  in

  Alcotest.(check (list uuidm_testable))
    "the two nodes should be colliding" [ other_node.id ] colliding_nodes_ids

let test_removing_only_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in

  let parsed_target = get_target uri_str in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc =
    Result.get_ok (Coq_document.remove_node_with_id first_node_id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in

  let second_node = List.nth doc.elements 1 in
  let parsed_target = get_target uri_str in

  let new_doc =
    Result.get_ok (Coq_document.remove_node_with_id second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in

  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_removing_node_same_line_as_other (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let second_node = List.nth doc.elements 1 in
  let new_doc =
    Result.get_ok (Coq_document.remove_node_with_id second_node.id doc)
  in
  let new_doc_res = document_to_range_representation_pairs new_doc in
  Alcotest.(check (list (pair string range_testable)))
    "The two lists should be the same" parsed_target new_doc_res

let test_adding_node_on_empty_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 11 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in
  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_before_busy_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 11 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_multiple_line_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n        +\n        1."
         start_point)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_between (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 11; offset = 12 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 2." start_point)
  in

  let new_doc =
    Coq_document.insert_node ~shift_method:ShiftHorizontally node doc
  in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_collision_next_line (doc : Doc.t) () : unit =
  (* TODO bugged for now, fix later *)
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1\n+\n1." start_point)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_adding_node_colliding_many (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 6; character = 2; offset = 75 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 1 +\n  2 + 3 + 4\n  + 5 + 6."
         start_point)
  in

  let new_doc = Coq_document.insert_node node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_single_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 42." start_point)
  in

  let second_node_id = (List.nth doc.elements 1).id in

  let new_doc = Coq_document.replace_node second_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_first_node_on_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 0; offset = 12 } in

  let node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Compute 123." start_point)
  in

  let second_node_id = (List.nth doc.elements 1).id in

  let new_doc = Coq_document.replace_node second_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_in_middle_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 11; offset = 23 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 123456." start_point)
  in

  let third_node_id = (List.nth doc.elements 2).id in

  let new_doc = Coq_document.replace_node third_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_node_end_of_line (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 2; character = 22; offset = 34 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string "Compute 12345." start_point)
  in

  let fourth_node_id = (List.nth doc.elements 3).id in

  let new_doc = Coq_document.replace_node fourth_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_smaller_node_with_bigger_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 1 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Theorem th : forall n : nat,\nn + 0 = n." start_point)
  in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc = Coq_document.replace_node first_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_bigger_node_with_smaller_node (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 1; character = 0; offset = 1 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Theorem th : forall n : nat, n + 0 = n." start_point)
  in

  let first_node_id = (List.hd doc.elements).id in

  let new_doc = Coq_document.replace_node first_node_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_block_by_other_block (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let start_point : Lang.Point.t = { line = 16; character = 0; offset = 461 } in

  let node =
    Result.get_ok
      (Syntax_node.syntax_node_of_string
         "Lemma l4_19_stdlib :\n\
         \  forall A B C C' : Point,\n\
         \  Bet A C B -> Cong A C A C' -> Cong B C B C' ->\n\
         \  C = C'."
         start_point)
  in

  let first_proof = Coq_document.get_proofs doc |> Result.get_ok |> List.hd in
  let thm_id = first_proof.proposition.id in

  let new_doc = Coq_document.replace_node thm_id node doc in
  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in

  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replacing_simple_auto_by_steps (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_transformation
      Transformations.replace_auto_with_steps doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replace_multiple_branch_auto_by_steps (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_transformation
      Transformations.replace_auto_with_steps doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replace_auto_using_zarith_by_steps (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_transformation
      Transformations.replace_auto_with_steps doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let test_replace_auto_with_backtracking (doc : Doc.t) () : unit =
  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let doc = Coq_document.parse_document doc in
  let parsed_target = get_target uri_str in

  let new_doc =
    Transformations.apply_proof_transformation
      Transformations.replace_auto_with_steps doc
  in

  let new_doc_res = Result.map document_to_range_representation_pairs new_doc in
  Alcotest.(check (result (list (pair string range_testable)) error_testable))
    "The two list should be the same " (Ok parsed_target) new_doc_res

let setup_test_table table (doc : Doc.t) =
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if simply ordered nodes are sorted correctly"
       test_sorting_nodes doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on different lines are not colliding"
       test_colliding_nodes_no_common_lines doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on the same line are not colliding"
       test_colliding_nodes_common_line_no_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "check if two nodes on the same line are colliding"
       test_colliding_nodes_common_line_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test
       "check if two nodes with one common line are not colliding"
       test_colliding_nodes_one_common_line_no_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test
       "check if two nodes with multiple common lines are colliding"
       test_colliding_nodes_multiple_common_lines_collision doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if reformat fail on comment"
       test_reformat_comment_node doc);
  Hashtbl.add table "test_dummy.v"
    (create_fixed_test "Check if reformat keep the same id"
       test_reformat_keep_id doc);
  Hashtbl.add table "ex_parsing1.v"
    (create_fixed_test "test parsing ex 1" test_parsing_ex1 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing ex 2" test_parsing_ex2 doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test parsing basic proof properties ex 2"
       test_parsing_ex2 doc);
  Hashtbl.add table "ex_admit.v"
    (create_fixed_test "test parsing admitted proof" test_parsing_admit doc);
  Hashtbl.add table "ex_defined1.v"
    (create_fixed_test "test parsing defined proof" test_parsing_defined doc);
  Hashtbl.add table "ex_function1.v"
    (create_fixed_test "test parsing function proof" test_parsing_function doc);
  Hashtbl.add table "ex_abort1.v"
    (create_fixed_test "test parsing aborted proof 1" test_parsing_abort1 doc);
  Hashtbl.add table "ex_abort2.v"
    (create_fixed_test "test parsing aborted proof 2" test_parsing_abort2 doc);
  Hashtbl.add table "ex_instance1.v"
    (create_fixed_test "test parsing an instance proof" test_parsing_instance
       doc);
  Hashtbl.add table "ex_parsing2.v"
    (create_fixed_test "test names and steps retrival ex 2"
       test_proof_parsing_name_and_steps_ex2 doc);
  Hashtbl.add table "ex_parsing3.v"
    (create_fixed_test "test parsing of two proofs ex3"
       test_proof_parsing_multiple_proofs_ex3 doc);
  Hashtbl.add table "ex_parsing4.v"
    (create_fixed_test "test parsing single comment" test_parsing_comment_ex4
       doc);
  Hashtbl.add table "ex_parsing5.v"
    (create_fixed_test "test parsing multiple complex comments"
       test_parsing_multiples_comments_ex5 doc);
  Hashtbl.add table "ex_parsing6.v"
    (create_fixed_test "test parsing embedded comments"
       test_parsing_embedded_comments_ex6 doc);
  Hashtbl.add table "ex_parsing7.v"
    (create_fixed_test "test parsing weird comments"
       test_parsing_weird_comments_ex7 doc);
  Hashtbl.add table "ex_id_assign1.v"
    (create_fixed_test "test the initial ordering of nodes in the document"
       test_id_assign_document doc);
  Hashtbl.add table "ex_id_assign2.v"
    (create_fixed_test "test the initial ordering of nodes in a simple proof"
       test_id_assign_document doc);
  Hashtbl.add table "ex_id_assign3.v"
    (create_fixed_test "test the initial ordering of nodes with comments"
       test_id_assign_document doc);

  Hashtbl.add table "ex_removing1.v"
    (create_fixed_test "test removing only node on a line"
       test_removing_only_node_on_line doc);
  Hashtbl.add table "ex_removing2.v"
    (create_fixed_test "test removing a node spanning multiple lines"
       test_removing_multiple_line_node doc);
  Hashtbl.add table "ex_removing3.v"
    (create_fixed_test "test removing a node on the same line as another one"
       test_removing_node_same_line_as_other doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test searching node" test_searching_node doc);
  Hashtbl.add table "ex_adding1.v"
    (create_fixed_test "test adding new nodes on an empty line"
       test_adding_node_on_empty_line doc);
  Hashtbl.add table "ex_adding2.v"
    (create_fixed_test "test adding new node on a filled line"
       test_adding_node_before_busy_line doc);
  Hashtbl.add table "ex_adding3.v"
    (create_fixed_test "test adding a new node spanning multiple lines"
       test_adding_multiple_line_node doc);
  Hashtbl.add table "ex_adding4.v"
    (create_fixed_test "test adding a node between two nodes on the same line"
       test_adding_node_between doc);
  (* Hashtbl.add table "ex_adding5.v" *)
  (*   (create_fixed_test "test adding a node that will collide on another line" *)
  (*      test_adding_collision_next_line doc); *)
  (* Hashtbl.add table "ex_adding6.v" *)
  (*   (create_fixed_test "test adding a node that will collide with many nodes" *)
  (*      test_adding_node_colliding_many doc); *)
  (* TODO Fix offset counting *)
  Hashtbl.add table "ex_replacing1.v"
    (create_fixed_test "test replacing the single node on one line"
       test_replacing_single_node_on_line doc);
  Hashtbl.add table "ex_replacing2.v"
    (create_fixed_test "test replacing the first node on one line"
       test_replacing_first_node_on_line doc);
  Hashtbl.add table "ex_replacing3.v"
    (create_fixed_test "test replacing a node in the middle of a line"
       test_replacing_node_in_middle_of_line doc);
  Hashtbl.add table "ex_replacing4.v"
    (create_fixed_test "test replacing a node with some spaces after"
       test_replacing_node_end_of_line doc);
  Hashtbl.add table "ex_replacing5.v"
    (create_fixed_test "test replacing a node with a bigger node"
       test_replacing_smaller_node_with_bigger_node doc);
  Hashtbl.add table "ex_replacing6.v"
    (create_fixed_test "test replacing a node with a smaller node"
       test_replacing_bigger_node_with_smaller_node doc);
  Hashtbl.add table "ex_replacing7.v"
    (create_fixed_test
       "test replacing a theorem block with another theorem block"
       test_replacing_block_by_other_block doc);

  Hashtbl.add table "ex_auto1.v"
    (create_fixed_test "test replacing simple auto with all the taken steps"
       test_replacing_simple_auto_by_steps doc);
  Hashtbl.add table "ex_auto2.v"
    (create_fixed_test "test replacing branching auto with all the taken steps"
       test_replace_multiple_branch_auto_by_steps doc);
  (* Hashtbl.add table "ex_auto3.v" *)
  (*   (create_fixed_test "test replacing auto with zarith" *)
  (*      test_replace_auto_using_zarith_by_steps doc); *)
  (* Hashtbl.add table "ex_auto4.v" *)
  (*   (create_fixed_test "test replacing auto with backtracking by steps" *)
  (*      test_replace_auto_with_backtracking doc); *)
  (* TODO commit files *)
  ()

let test_runner ~io ~token:_ ~(doc : Doc.t) =
  let test_hash_table = Hashtbl.create 50 in

  let uri_str = Lang.LUri.File.to_string_uri doc.uri in
  let uri_name_str = Filename.basename uri_str in

  setup_test_table test_hash_table doc;
  let global_tests = Hashtbl.find_all test_hash_table "global" in
  let file_tests = Hashtbl.find_all test_hash_table uri_name_str in
  let tests = [ ("parsing tests", global_tests @ file_tests) ] in
  print_endline
    ("Running " ^ string_of_int (List.length global_tests) ^ " global tests");
  print_endline
    ("Running "
    ^ string_of_int (List.length file_tests)
    ^ " file test for: " ^ uri_name_str);
  flush_all ();
  Alcotest.run ~and_exit:true
    ~argv:[| "ignored"; "--color=always" |]
    "document parsing and modification tests" tests;
  ()

let main () = Theory.Register.Completed.add test_runner
let () = main ()
