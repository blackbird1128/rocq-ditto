open Proof
open Fleche
open Syntax_node
open Sexplib

type proofState = NoProof | ProofOpened

type t = {
  id_counter : Unique_id.counter;
  filename : string;
  elements : syntaxNode list;
  document_repr : string;
  initial_state : Coq.State.t;
}

type removeMethod = LeaveBlank | ShiftNode
type shiftMethod = ShiftVertically | ShiftHorizontally

let pp_coq_document (fmt : Format.formatter) (doc : t) : unit =
  Format.fprintf fmt "filename: %s@ " doc.filename;
  Format.fprintf fmt "elements:@ ";
  List.iter
    (fun node ->
      Format.fprintf fmt "%a %s@ " Lang.Range.pp node.range node.repr)
      (* see to add id maybe ? *)
    doc.elements;
  Format.fprintf fmt "document repr: %s" doc.document_repr

let get_proofs (doc : t) : (proof list, string) result =
  let rec aux (nodes : syntaxNode list) (cur_proof_acc : syntaxNode list)
      (proofs_acc : (proof, string) result list) (cur_state : proofState) :
      (proof, string) result list =
    match nodes with
    | [] -> proofs_acc
    | x :: tail -> (
        if Syntax_node.node_can_open_proof x then
          aux tail [ x ] proofs_acc ProofOpened
        else if Syntax_node.node_can_close_proof x then
          let proof = proof_from_nodes (List.rev (x :: cur_proof_acc)) in
          aux tail [] (proof :: proofs_acc) NoProof
        else
          match cur_state with
          | NoProof -> aux tail [] proofs_acc NoProof
          | ProofOpened -> aux tail (x :: cur_proof_acc) proofs_acc ProofOpened)
  in
  let res = aux doc.elements [] [] NoProof in
  let err_opt =
    List.find_opt (fun proof_res -> Result.is_error proof_res) res
  in
  match err_opt with
  | Some error -> Error (Result.get_error error)
  | None -> Ok (List.rev (List.map Result.get_ok res))

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let get_line_col_positions text pos : Lang.Point.t =
  let rec aux line col index =
    if index = pos then (line, col, index)
    else if index >= String.length text then (line, col, index)
    else if text.[index] = '\n' then aux (line + 1) 0 (index + 1)
    else aux line (col + 1) (index + 1)
  in
  let line, character, offset = aux 0 0 0 in
  (* Start from line 0, column 0, character 0 *)
  { line; character; offset }

let matches_with_line_col content pattern : (string * Lang.Range.t) list =
  let re =
    Re.Perl.compile_pat
      ~opts:[ Re.Perl.(`Multiline); Re.Perl.(`Dotall); Re.Perl.(`Ungreedy) ]
      pattern
  in

  let matches =
    Re.all re content
    |> List.map (fun g ->
           let start_pos = Re.Group.start g 0 in
           let end_pos = Re.Group.stop g 0 in
           let start_point = get_line_col_positions content start_pos in
           let end_point = get_line_col_positions content end_pos in
           let range : Lang.Range.t =
             { start = start_point; end_ = end_point }
           in
           (Re.Group.get g 0, range))
  in
  matches

let are_flat_ranges_colliding (a : int * int) (b : int * int) : bool =
  let a_start, a_end = a in
  let b_start, b_end = b in

  (a_start >= b_start && a_start <= b_end)
  || (a_end >= b_start && a_end <= b_end)

let common_range (a : int * int) (b : int * int) : (int * int) option =
  if are_flat_ranges_colliding a b then
    let a_start, a_end = a in
    let b_start, b_end = b in
    Some (max a_start b_start, min a_end b_end)
  else None

(*return the nodes colliding with target node*)
let colliding_nodes (target : syntaxNode) (doc : t) : syntaxNode list =
  let target_line_range = (target.range.start.line, target.range.end_.line) in
  let target_offset_range =
    (target.range.start.offset, target.range.end_.offset)
  in
  List.filter
    (fun node ->
      let node_line_range = (node.range.start.line, node.range.end_.line) in
      if are_flat_ranges_colliding target_line_range node_line_range then
        let node_offset_range =
          (node.range.start.offset, node.range.end_.offset)
        in
        are_flat_ranges_colliding target_offset_range node_offset_range
      else false)
    doc.elements

let compare_nodes (a : syntaxNode) (b : syntaxNode) : int =
  match
    common_range
      (a.range.start.line, a.range.end_.line)
      (b.range.start.line, b.range.end_.line)
  with
  | Some common_line_range ->
      let smallest_common = fst common_line_range in
      if a.range.start.line < smallest_common then -1
      else if b.range.start.line < smallest_common then 1
      else compare a.range.start.character b.range.start.character
  | None -> compare a.range.start.line b.range.start.line

let second_node_included_in (a : syntaxNode) (b : syntaxNode) : bool =
  if a.range.start.offset < b.range.start.offset then
    if
      b.range.start.offset < a.range.end_.offset
      && b.range.end_.offset < a.range.end_.offset
    then true
    else false
  else false

let merge_nodes (nodes : syntaxNode list) : syntaxNode list =
  let rec merge_aux (acc : syntaxNode list) (nodes : syntaxNode list) =
    match nodes with
    | [] -> List.rev acc
    | curr_node :: rest -> (
        match acc with
        | acc_node :: acc_tail when second_node_included_in acc_node curr_node
          ->
            merge_aux acc rest
        | _ -> merge_aux (curr_node :: acc) rest)
  in
  merge_aux [] nodes

let parse_document (doc : Doc.t) : t =
  let nodes = doc.nodes in
  let document_repr = doc.contents.raw in
  let filename = Lang.LUri.File.to_string_uri doc.uri in

  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in
  let ast_nodes =
    List.map
      (fun (node : Doc.Node.t) ->
        {
          ast = node.ast;
          range = node.range;
          repr = node_representation node document_repr;
          id = Unique_id.uuid ();
          proof_id = None;
          diagnostics = node.diags;
        })
      nodes_with_ast
  in
  let comments = matches_with_line_col document_repr "\\(\\*.*\\*\\)$" in
  let comments_nodes =
    List.map
      (fun comment ->
        {
          ast = None;
          range = snd comment;
          repr = fst comment;
          id = Unique_id.uuid ();
          proof_id = None;
          diagnostics = [];
        })
      comments
  in

  let all_nodes =
    merge_nodes (List.sort compare_nodes (ast_nodes @ comments_nodes))
  in
  let doc_counter = Unique_id.create () in

  {
    id_counter = doc_counter;
    elements = all_nodes;
    document_repr;
    filename;
    initial_state = doc.root;
  }

let rec dump_to_string (doc : t) : string =
  let rec aux (repr_nodes : syntaxNode list) (doc_repr : string)
      (previous_node : syntaxNode) =
    match repr_nodes with
    | [] -> doc_repr
    | node :: tail ->
        let line_diff = node.range.start.line - previous_node.range.end_.line in
        let repr =
          if previous_node.range = node.range then
            (* treating the first node as a special case to deal with eventual empty lines before *)
            doc_repr
            ^ String.make node.range.start.line '\n'
            ^ String.make node.range.start.character ' '
            ^ node.repr
          else if node.range.start.line = previous_node.range.end_.line then
            let char_diff =
              node.range.start.character - previous_node.range.end_.character
            in
            if char_diff <= 0 then (
              print_endline
                "Error: node start - previous en char negative or zero ";
              print_endline
                ("previous node range: "
                ^ Lang.Range.to_string previous_node.range);
              print_endline
                ("current node range: " ^ Lang.Range.to_string node.range);
              "ERR")
            else doc_repr ^ String.make char_diff ' ' ^ node.repr
          else if line_diff <= 0 then (
            print_endline "line diff negative";
            print_endline
              ("previous node range: "
              ^ Lang.Range.to_string previous_node.range);
            print_endline
              ("current node range: " ^ Lang.Range.to_string node.range);
            "ERR")
          else
            doc_repr ^ String.make line_diff '\n'
            ^ String.make node.range.start.character ' '
            ^ node.repr
        in
        aux tail repr node
  in

  let sorted_elements = List.sort compare_nodes doc.elements in
  List.iter
    (fun x -> print_endline (Lang.Range.to_string x.range))
    sorted_elements;
  aux sorted_elements "" (List.hd sorted_elements)

let element_before_id_opt (target_id : Uuidm.t) (doc : t) : syntaxNode option =
  match List.find_index (fun elem -> elem.id = target_id) doc.elements with
  | Some elem_id ->
      if elem_id - 1 < 0 then None
      else
        List.find_mapi
          (fun i elem -> if i = elem_id - 1 then Some elem else None)
          doc.elements
  | None -> None

let element_with_id_opt (element_id : Uuidm.t) (doc : t) : syntaxNode option =
  List.find_opt (fun elem -> elem.id = element_id) doc.elements

let proof_with_id_opt (proof_id : Uuidm.t) (doc : t) : proof option =
  let proofs_res = get_proofs doc in
  match proofs_res with
  | Ok proofs ->
      List.find_opt (fun elem -> elem.proposition.id = proof_id) proofs
  | Error err ->
      print_endline "No proof found !";
      None

let split_at_id (target_id : Uuidm.t) (doc : t) :
    syntaxNode list * syntaxNode list =
  let rec aux (elements : syntaxNode list) (acc : syntaxNode list) =
    match elements with
    | [] -> (acc, [])
    | x :: tail ->
        if x.id = target_id then (List.rev acc, tail) else aux tail (x :: acc)
  in
  aux doc.elements []

let elements_starting_at_line (line_number : int) (nodes : syntaxNode list) :
    syntaxNode list =
  List.filter (fun elem -> elem.range.start.line = line_number) nodes

let remove_node_with_id (target_id : Uuidm.t) ?(remove_method = ShiftNode)
    (doc : t) : (t, string) result =
  match element_with_id_opt target_id doc with
  | None ->
      Error
        ("The element with id: " ^ Uuidm.to_string target_id
       ^ " wasn't found in the document")
  | Some elem -> (
      let before, after = split_at_id target_id doc in
      let offset_shift = elem.range.start.offset - elem.range.end_.offset in
      (* the offset shift is negative as we are moving back nodes *)
      let block_height = elem.range.end_.line - elem.range.start.line + 1 in
      (* each block is at least a line high *)

      match remove_method with
      | LeaveBlank -> Ok { doc with elements = before @ after }
      | ShiftNode ->
          if
            List.length
              (elements_starting_at_line elem.range.start.line doc.elements)
            > 1
          then
            Ok
              {
                doc with
                elements =
                  List.concat
                    [
                      before;
                      List.map
                        (fun node ->
                          if node.range.start.line = elem.range.start.line then
                            shift_node 0 offset_shift 0 node
                          else shift_node 0 0 offset_shift node)
                        after;
                    ];
              }
          else
            Ok
              {
                doc with
                elements =
                  List.concat
                    [
                      before;
                      List.map
                        (shift_node (-block_height) 0 (offset_shift - 1))
                        after;
                    ];
              })

let insert_node (new_node : syntaxNode) ?(shift_method = ShiftVertically)
    (doc : t) : (t, string) result =
  let element_before_new_node_start, element_after_new_node_start =
    List.partition (fun node -> compare_nodes node new_node < 0) doc.elements
  in

  let element_after_range_opt =
    Option.map (fun x -> x.range) (List.nth_opt element_after_new_node_start 0)
  in

  let node_offset_size =
    new_node.range.end_.offset - new_node.range.start.offset
  in
  let offset_space =
    match element_after_range_opt with
    | Some element_after_range ->
        element_after_range.start.offset - new_node.range.start.offset - 1
    | None -> 0
  in

  let new_lines_push =
    String.fold_left
      (fun acc c -> if c = '\n' then acc + 1 else acc)
      0 new_node.repr
  in
  let total_shift = node_offset_size - offset_space + new_lines_push in

  match shift_method with
  | ShiftHorizontally ->
      if new_node.range.start.line != new_node.range.end_.line then
        Error
          ("Error when trying to shift " ^ new_node.repr ^ " at : "
          ^ Lang.Range.to_string new_node.range
          ^ ". Shifting horizontally is only possible with 1 line height node")
      else
        let multi_lines_nodes_after_same_line =
          elements_starting_at_line new_node.range.start.line
            element_after_new_node_start
          |> List.find_opt (fun node ->
                 node.range.start.character > new_node.range.start.character
                 && node.range.end_.line - node.range.start.line >= 1)
          |> Option.has_some
        in
        if multi_lines_nodes_after_same_line then
          Error
            ("Can't shift multi-lines nodes on the same line ("
            ^ string_of_int new_node.range.start.line
            ^ ") as the node inserted")
        else
          Ok
            {
              doc with
              elements =
                element_before_new_node_start
                @ new_node
                  :: List.map
                       (fun node ->
                         if node.range.start.line = new_node.range.start.line
                         then shift_node 0 total_shift 0 node
                         else shift_node 0 0 total_shift node)
                       element_after_new_node_start;
            }
  | ShiftVertically ->
      let line_shift =
        if List.length (colliding_nodes new_node doc) = 0 then 0
        else new_node.range.end_.line - new_node.range.start.line + 1
      in

      (*there can be less offset but still space *)
      Ok
        {
          doc with
          elements =
            element_before_new_node_start
            @ new_node
              :: List.map
                   (fun node -> shift_node line_shift 0 total_shift node)
                   element_after_new_node_start;
        }

(* How would one insert a node ? *)

(* depend on the shift method *)
(*
    - get the nodes before and after 
    
    - if we shift horizontally:
    first check that we are inserting a one line wide node

    - if we shift vertically

    shift all nodes after by the offset amount
    and the number of lines of height ? 
    
   *)

let replace_node (target_id : Uuidm.t) (replacement : syntaxNode) (doc : t) :
    (t, string) result =
  match validate_syntax_node replacement with
  | Error err -> Error err
  | Ok replacement -> (
      match element_with_id_opt target_id doc with
      | Some target -> (
          let replacement_shifted =
            {
              replacement with
              range =
                Range_transformation.range_from_starting_point_and_repr
                  target.range.start replacement.repr;
            }
          in

          let target_height =
            target.range.end_.line - target.range.start.line + 1
          in

          let replacement_height =
            replacement_shifted.range.end_.line
            - replacement_shifted.range.start.line + 1
          in

          let removed_node_doc =
            Result.get_ok
              (remove_node_with_id ~remove_method:ShiftNode target.id doc)
            (* we already checked for the node existence *)
          in
          if replacement_height = 1 then
            insert_node replacement_shifted ~shift_method:ShiftHorizontally
              removed_node_doc
          else
            match
              insert_node replacement_shifted ~shift_method:ShiftVertically
                removed_node_doc
            with
            | Ok new_doc ->
                if target_height - replacement_height < 0 then
                  let diff = replacement_height - target_height in

                  let nodes_before, nodes_after =
                    List.partition
                      (fun node -> compare_nodes node replacement_shifted < 0)
                      new_doc.elements
                  in
                  Ok new_doc
                else Ok new_doc
            | Error err -> Error err)
      | None ->
          Error
            ("The target node with id : " ^ Uuidm.to_string target_id
           ^ " doesn't exists"))

let apply_transformation_step (step : transformation_step) (doc : t) :
    (t, string) result =
  match step with
  | Remove id -> remove_node_with_id id doc
  | Replace (id, new_node) -> replace_node id new_node doc
  | Add new_node -> insert_node new_node doc
  | Attach (attached_node, attach_position, anchor_id) -> (
      match element_with_id_opt anchor_id doc with
      | Some target ->
          print_endline ("target repr : " ^ target.repr);
          print_endline ("target range: " ^ Lang.Range.to_string target.range);
          let line_target = target.range.end_.line in
          let attached_node_start_point =
            match attach_position with
            | LineBefore -> shift_point (-1) 0 0 target.range.start
            | LineAfter -> shift_point 1 0 0 target.range.end_
          in

          let new_node_range =
            Range_transformation.range_from_starting_point_and_repr
              attached_node_start_point attached_node.repr
          in
          print_endline ("N node range: " ^ Lang.Range.to_string new_node_range);
          let new_node_range : Lang.Range.t =
            {
              start =
                shift_point 0
                  (-new_node_range.start.character)
                  0 new_node_range.start;
              end_ =
                shift_point 0 0
                  (-new_node_range.start.character)
                  new_node_range.end_;
            }
          in
          print_endline "there and back again";
          print_endline ("attached node repr: " ^ attached_node.repr);
          print_endline
            ("new node range: " ^ Lang.Range.to_string new_node_range);

          let new_node =
            match attached_node.ast with
            | Some _ ->
                let node =
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string attached_node.repr
                       new_node_range.start)
                in
                { node with id = attached_node.id }
            | None ->
                let node =
                  Result.get_ok
                    (Syntax_node.comment_syntax_node_of_string
                       attached_node.repr new_node_range.start)
                in
                { node with id = attached_node.id }
          in

          print_endline "new node created";

          insert_node new_node doc
      | None ->
          Error
            ("Can't find the node with id: " ^ Uuidm.to_string anchor_id
           ^ " to attach to"))

let transformation_step_to_string (step : transformation_step) : string =
  match step with
  | Remove id -> "Removing " ^ Uuidm.to_string id
  | Replace (id, new_node) ->
      "Replacing " ^ Uuidm.to_string id ^ " with " ^ new_node.repr
  | Add node -> "Adding " ^ node.repr
  | Attach (attached_node, attach_position, anchor_id) ->
      "Attaching node " ^ attached_node.repr ^ " to node with id: "
      ^ Uuidm.to_string anchor_id

let apply_transformations_steps (steps : transformation_step list) (doc : t) :
    (t, string) result =
  List.fold_left
    (fun doc_acc_err step ->
      match doc_acc_err with
      | Ok doc -> apply_transformation_step step doc
      | Error err -> Error err)
    (Ok doc) steps
