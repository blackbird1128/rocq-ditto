open Proof
open Fleche
open Syntax_node

type proofState = NoProof | ProofOpened

type t = {
  id_counter : Unique_id.counter;
  filename : string;
  elements : syntaxNode list;
  document_repr : string;
}

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

module IntMap = Map.Make (Int)

let get_proofs (doc : t) : proof list =
  let map_acc = IntMap.empty in
  let map_proofs =
    List.fold_left
      (fun map_acc elem ->
        match elem.proof_id with
        | Some id -> (
            match IntMap.find_opt id map_acc with
            | Some proof ->
                IntMap.add id
                  { proof with proof_steps = elem :: proof.proof_steps }
                  map_acc
            | None ->
                (IntMap.add id
                   { proposition = elem; proof_steps = []; status = Proved })
                  map_acc)
        | None -> map_acc)
      map_acc doc.elements
  in
  let proofs_rev = snd (List.split (IntMap.to_list map_proofs)) in
  List.filter_map
    (fun proof ->
      let last_step = List.hd proof.proof_steps in
      let proof_status = Proof.proof_status_from_last_node last_step in
      match proof_status with
      | Ok status ->
          Some { proof with proof_steps = List.rev proof.proof_steps; status }
      | Error err -> None)
    proofs_rev

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let doc_to_yojson (doc : t) : Yojson.Safe.t =
  `Assoc
    [
      ("filename", `String doc.filename);
      ("elements", `List (List.map Syntax_node.to_yojson doc.elements));
      ("document_repr", `String doc.document_repr);
    ]

let doc_of_yojson (json : Yojson.Safe.t) : t =
  let open Yojson.Safe.Util in
  {
    id_counter = Unique_id.create ();
    filename = json |> member "filename" |> to_string;
    document_repr = json |> member "document_repr" |> to_string;
    elements =
      json |> member "elements" |> to_list |> List.map Syntax_node.of_yojson;
  }

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

let compare_nodes (a : syntaxNode) (b : syntaxNode) : int =
  let comp = compare a.range.start.offset b.range.start.offset in
  if comp = 0 then compare a.range.end_.offset b.range.end_.offset else comp

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

let parse_document (nodes : Doc.Node.t list) (document_repr : string)
    (filename : string) : t =
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
        })
      comments
  in
  let rec aux (spans : syntaxNode list) (proof_state : proofState)
      (proof_id : int option) document =
    match spans with
    | [] -> (
        match proof_state with
        | ProofOpened ->
            raise (Invalid_argument "proof started but ended at document end")
        | NoProof -> List.rev document)
    | span :: rest -> (
        if node_can_open_proof span then
          let cur_id = Option.default 0 proof_id in
          let span_with_id = { span with proof_id = Some cur_id } in
          aux rest ProofOpened proof_id (span_with_id :: document)
        else if node_can_close_proof span then
          let cur_id = Option.default 0 proof_id in
          let span_with_id = { span with proof_id = Some cur_id } in

          match proof_state with
          | ProofOpened ->
              aux rest NoProof (Some (cur_id + 1)) (span_with_id :: document)
          | NoProof -> raise (Invalid_argument "proof ended but never started")
        else
          match proof_state with
          | ProofOpened ->
              let cur_id = Option.default 0 proof_id in
              let span_with_id = { span with proof_id = Some cur_id } in
              aux rest proof_state proof_id (span_with_id :: document)
          | NoProof -> aux rest proof_state proof_id (span :: document))
    (* Skip spans not part of any proof *)
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
  let res = aux numbered_all_nodes NoProof None [] in
  { id_counter = doc_counter; elements = res; document_repr; filename }

let rec dump_to_string (doc : t) : string =
  let rec aux (repr_nodes : syntaxNode list) (doc_repr : string)
      (previous_node : syntaxNode) =
    match repr_nodes with
    | [] -> doc_repr
    | node :: tail ->
        let previous_node_range = previous_node.range in
        let node_repr = node.repr in
        let node_range = node.range in
        let repr =
          if previous_node_range = node_range then
            (* treating the first node as a special case to deal with eventual empty lines before *)
            doc_repr
            ^ String.make node_range.start.line '\n'
            ^ String.make node_range.start.character ' '
            ^ node_repr
          else if node_range.start.line = previous_node_range.end_.line then
            doc_repr
            ^ String.make
                (node_range.start.line - previous_node_range.end_.line)
                '\n'
            ^ String.make
                (node_range.start.character - previous_node_range.end_.character)
                ' '
            ^ node_repr
          else
            doc_repr
            ^ String.make
                (node_range.start.line - previous_node_range.end_.line)
                '\n'
            ^ String.make node_range.start.character ' '
            ^ node_repr
        in
        aux tail repr node
  in

  aux doc.elements "" (List.hd doc.elements)

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
  let proofs = get_proofs doc in
  List.find_opt (fun elem -> elem.proposition.id = proof_id) proofs

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

let remove_node_with_id (target_id : int) (doc : t) : t =
  match element_with_id_opt target_id doc with
  | Some elem ->
      let before, after = split_at_id target_id doc in
      if List.length (elements_starting_at_line elem.range.start.line doc) > 1
      then
        {
          doc with
          elements =
            List.concat
              [
                before;
                List.map
                  (fun node ->
                    if node.range.start.line = elem.range.start.line then
                      shift_node 0
                        (elem.range.start.offset - elem.range.end_.offset)
                        (*newline ?*)
                        0
                        node
                    else
                      shift_node 0 0
                        (elem.range.start.offset - elem.range.end_.offset)
                        node)
                  after;
              ];
        }
      else
        {
          doc with
          elements =
            List.concat
              [
                before;
                shift_nodes
                  (-(elem.range.end_.line - elem.range.start.line + 1))
                  0
                  (elem.range.start.offset - elem.range.end_.offset - 1)
                  after;
              ];
        }
      (* Shift n char off the line if more than one element   *)
  | None -> doc

(*return the nodes colliding with target node*)
let colliding_nodes (target : syntaxNode) (doc : t) : syntaxNode list =
  let target_range_start = target.range.start.offset in
  let target_range_end = target.range.end_.offset in
  List.filter
    (fun node ->
      let node_range_start = node.range.start.offset in
      let node_range_end = node.range.end_.offset in
      if
        node_range_start >= target_range_start
        && node_range_start <= target_range_end
      then true
      else if
        node_range_end >= target_range_start
        && node_range_end <= target_range_end
      then true
      else false)
    doc.elements

let insert_node (new_node : syntaxNode) ?(shift_method = ShiftVertically)
    (doc : t) : (t, string) result =
  if
    shift_method = ShiftHorizontally
    && new_node.range.start.line != new_node.range.end_.line
  then Error "Shifting horizontally is only possible with 1 line wide node"
  else
    let node_with_id = { new_node with id = Unique_id.next doc.id_counter } in
    match colliding_nodes new_node doc with
    | [] ->
        let nodes_sorted = List.sort compare_nodes (new_node :: doc.elements) in
        Ok { doc with elements = nodes_sorted }
    | collision ->
        let element_before_new_node_start =
          List.filter
            (fun node -> node.range.start < new_node.range.start)
            doc.elements
        in
        let element_after_new_node_start =
          List.filter
            (fun node -> node.range.start >= new_node.range.start)
            doc.elements
        in
        if shift_method = ShiftVertically then
          let shifted =
            shift_nodes
              (new_node.range.end_.line - new_node.range.start.line + 1)
              0
              (new_node.range.end_.offset - new_node.range.start.offset + 1)
              element_after_new_node_start
          in
          Ok
            {
              doc with
              elements =
                element_before_new_node_start @ (node_with_id :: shifted);
            }
        else
          let shifted =
            List.map
              (fun node ->
                shift_node
                  (new_node.range.end_.line - new_node.range.start.line)
                  0
                  (new_node.range.end_.offset - new_node.range.start.offset)
                  node)
              element_after_new_node_start
          in
          Ok
            {
              doc with
              elements =
                element_before_new_node_start @ (node_with_id :: shifted);
            }

let remove_proof (target : proof) (doc : t) : t =
  let proof_nodes = target.proposition :: target.proof_steps in
  List.fold_left
    (fun doc_acc node -> remove_node_with_id node.id doc_acc)
    doc proof_nodes

let insert_proof (target : proof) (doc : t) : (t, string) result =
  let proof_nodes = target.proposition :: target.proof_steps in
  let rec aux (nodes : syntaxNode list) (doc_acc : t) : (t, string) result =
    match nodes with
    | [] -> Ok doc_acc
    | node :: tail -> (
        match insert_node node doc_acc with
        | Ok new_doc -> aux tail new_doc
        | Error msg -> Error msg)
  in
  aux proof_nodes doc

let replace_proof (target : proof) (doc : t) : (t, string) result =
  match proof_with_id_opt target.proposition.id doc with
  | Some elem -> (
      let proof_id = target.proposition.id in
      let doc_removed = remove_proof elem doc in
      match element_before_id_opt proof_id doc with
      | Some element_before -> insert_proof target doc_removed
      | None -> insert_proof target doc_removed)
  | None ->
      Error
        ("proof with id "
        ^ string_of_int target.proposition.id
        ^ "isn't in the document")
