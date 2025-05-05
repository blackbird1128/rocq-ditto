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
  if List.exists Result.is_error res then
    Error "One ore more proofs was badly parsed"
  else Ok (List.rev (List.map Result.get_ok res))

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
  if
    (a_start >= b_start && a_start <= b_end)
    || (a_end >= b_start && a_end <= b_end)
  then true
  else false

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
          id = -1;
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
          id = -1;
          proof_id = None;
          diagnostics = [];
        })
      comments
  in

  let all_nodes =
    merge_nodes (List.sort compare_nodes (ast_nodes @ comments_nodes))
  in
  let doc_counter = Unique_id.create () in
  let numbered_all_nodes =
    List.map
      (fun node -> { node with id = Unique_id.next doc_counter })
      all_nodes
  in

  {
    id_counter = doc_counter;
    elements = numbered_all_nodes;
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
        let repr =
          if previous_node.range = node.range then
            (* treating the first node as a special case to deal with eventual empty lines before *)
            doc_repr
            ^ String.make node.range.start.line '\n'
            ^ String.make node.range.start.character ' '
            ^ node.repr
          else if node.range.start.line = previous_node.range.end_.line then
            doc_repr
            ^ String.make
                (node.range.start.line - previous_node.range.end_.line)
                '\n'
            ^ String.make
                (node.range.start.character - previous_node.range.end_.character)
                ' '
            ^ node.repr
          else
            doc_repr
            ^ String.make
                (node.range.start.line - previous_node.range.end_.line)
                '\n'
            ^ String.make node.range.start.character ' '
            ^ node.repr
        in
        aux tail repr node
  in

  let sorted_elements = List.sort compare_nodes doc.elements in
  aux sorted_elements "" (List.hd sorted_elements)

let element_before_id_opt (target_id : int) (doc : t) : syntaxNode option =
  match List.find_index (fun elem -> elem.id = target_id) doc.elements with
  | Some elem_id ->
      if elem_id - 1 < 0 then None
      else
        List.find_mapi
          (fun i elem -> if i = elem_id - 1 then Some elem else None)
          doc.elements
  | None -> None

let element_with_id_opt (element_id : int) (doc : t) : syntaxNode option =
  List.find_opt (fun elem -> elem.id = element_id) doc.elements

let proof_with_id_opt (proof_id : int) (doc : t) : proof option =
  let proofs_res = get_proofs doc in
  match proofs_res with
  | Ok proofs ->
      List.find_opt (fun elem -> elem.proposition.id = proof_id) proofs
  | Error err -> None

let split_at_id (target_id : int) (doc : t) : syntaxNode list * syntaxNode list
    =
  let rec aux (elements : syntaxNode list) (acc : syntaxNode list) =
    match elements with
    | [] -> (acc, [])
    | x :: tail ->
        if x.id = target_id then (List.rev acc, tail) else aux tail (x :: acc)
  in
  aux doc.elements []

let elements_starting_at_line (line_number : int) (doc : t) : syntaxNode list =
  List.filter (fun elem -> elem.range.start.line = line_number) doc.elements

let shift_nodes (n_line : int) (n_char : int) (n_offset : int)
    (nodes : syntaxNode list) : syntaxNode list =
  List.map (Syntax_node.shift_node n_line n_char n_offset) nodes

let remove_node_with_id (target_id : int) ?(remove_method = ShiftNode) (doc : t)
    : (t, string) result =
  match element_with_id_opt target_id doc with
  | None ->
      Error
        ("The element with id: " ^ string_of_int target_id
       ^ "wasn't found in the document")
  | Some elem -> (
      let before, after = split_at_id target_id doc in
      let offset_shift = elem.range.end_.offset - elem.range.start.offset in
      match remove_method with
      | LeaveBlank -> Ok { doc with elements = before @ after }
      | ShiftNode ->
          if
            List.length (elements_starting_at_line elem.range.start.line doc)
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
                            shift_node 0 (-offset_shift) 0 node
                          else shift_node 0 0 (-offset_shift) node)
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
                      shift_nodes (-offset_shift + 1) 0 (-offset_shift - 1)
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

  let node_with_id = { new_node with id = Unique_id.next doc.id_counter } in
  if
    shift_method = ShiftHorizontally
    && new_node.range.start.line != new_node.range.end_.line
  then
    Error
      ("Error when trying to shift " ^ new_node.repr ^ " at : "
      ^ Lang.Range.to_string new_node.range
      ^ ". Shifting horizontally is only possible with 1 line wide node")
  else
    match element_after_range_opt with
    | Some element_after_range -> (
        let node_offset_size =
          node_with_id.range.end_.offset - node_with_id.range.start.offset
        in
        let offset_space =
          element_after_range.start.offset - node_with_id.range.start.offset - 1
        in

        let total_shift = node_offset_size - offset_space in

        match shift_method with
        | ShiftHorizontally ->
            Ok
              {
                doc with
                elements =
                  element_before_new_node_start
                  @ node_with_id
                    :: List.map
                         (fun node ->
                           if
                             node.range.start.line
                             = node_with_id.range.start.line
                           then shift_node 0 total_shift 0 node
                           else shift_node 0 0 total_shift node)
                         element_after_new_node_start;
              }
        | ShiftVertically ->
            let line_shift =
              if List.length (colliding_nodes node_with_id doc) = 0 then 0
              else
                node_with_id.range.end_.line - node_with_id.range.start.line + 1
            in

            (*there can be less offset but still space *)
            Ok
              {
                doc with
                elements =
                  element_before_new_node_start
                  @ node_with_id
                    :: List.map
                         (fun node -> shift_node line_shift 0 total_shift node)
                         element_after_new_node_start;
              })
    | None ->
        Ok
          {
            doc with
            elements = element_before_new_node_start @ [ node_with_id ];
          }

let replace_node (target_id : int) (replacement : syntaxNode) (doc : t) :
    (t, string) result =
  match element_with_id_opt target_id doc with
  | Some node ->
      let removed_node_doc =
        Result.get_ok
          (remove_node_with_id ~remove_method:LeaveBlank node.id doc)
        (* we already checked for the node existence *)
      in
      insert_node replacement ~shift_method:ShiftHorizontally removed_node_doc
  | None ->
      Error
        ("The target node with id : " ^ string_of_int target_id
       ^ " doesn't exists")

let apply_transformation_step (step : transformation_step) (doc : t) :
    (t, string) result =
  match step with
  | Remove id -> remove_node_with_id id doc
  | Replace (id, new_node) -> replace_node id new_node doc
  | Add new_node -> insert_node new_node doc

let transformation_step_to_string (step : transformation_step) : string =
  match step with
  | Remove id -> "Removing " ^ string_of_int id
  | Replace (id, new_node) ->
      "Replacing " ^ string_of_int id ^ " with " ^ new_node.repr
  | Add node -> "Adding " ^ node.repr

let apply_transformations_steps (steps : transformation_step list) (doc : t) :
    (t, string) result =
  List.fold_left
    (fun doc_acc_err step ->
      match doc_acc_err with
      | Ok doc -> apply_transformation_step step doc
      | Error err -> Error err)
    (Ok doc) steps
