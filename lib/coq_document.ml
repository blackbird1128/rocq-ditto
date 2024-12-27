open Proof
open Fleche
open Annotated_ast_node

type proofState = NoProof | ProofOpened

type t = {
  filename : string;
  elements : annotatedASTNode list;
  document_repr : string;
}

type insertPosition = Before of int | After of int | Start | End

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
                (IntMap.add id { proposition = elem; proof_steps = [] }) map_acc
            )
        | None -> map_acc)
      map_acc doc.elements
  in
  let proofs_rev = snd (List.split (IntMap.to_list map_proofs)) in
  List.map
    (fun proof -> { proof with proof_steps = List.rev proof.proof_steps })
    proofs_rev

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let doc_to_yojson (doc : t) : Yojson.Safe.t =
  `Assoc
    [
      ("filename", `String doc.filename);
      ("elements", `List (List.map Annotated_ast_node.to_yojson doc.elements));
      ("document_repr", `String doc.document_repr);
    ]

let parse_document (nodes : Doc.Node.t list) (document_repr : string)
    (filename : string) : t =
  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in
  let rec aux (spans : Doc.Node.t list) (proof_state : proofState)
      (proof_id : int option) document =
    match spans with
    | [] -> (
        match proof_state with
        | ProofOpened ->
            raise (Invalid_argument "proof started but ended at document end")
        | NoProof -> List.rev document)
    | span :: rest -> (
        let annotated_span =
          {
            ast = Option.get span.ast;
            range = span.range;
            repr = node_representation span document_repr;
            id = Unique_id.next ();
            proof_id = None;
          }
        in
        if is_doc_node_ast_proof_start annotated_span then
          let cur_id = Option.default 0 proof_id in
          let span_with_id = { annotated_span with proof_id = Some cur_id } in
          aux rest ProofOpened proof_id (span_with_id :: document)
        else if is_doc_node_ast_proof_end annotated_span then
          let cur_id = Option.default 0 proof_id in
          let span_with_id = { annotated_span with proof_id = Some cur_id } in

          match proof_state with
          | ProofOpened ->
              aux rest NoProof (Some (cur_id + 1)) (span_with_id :: document)
          | NoProof -> raise (Invalid_argument "proof ended but never started")
        else
          match proof_state with
          | ProofOpened ->
              let cur_id = Option.default 0 proof_id in
              let span_with_id =
                { annotated_span with proof_id = Some cur_id }
              in
              aux rest proof_state proof_id (span_with_id :: document)
          | NoProof -> aux rest proof_state proof_id (annotated_span :: document)
        )
    (* Skip spans not part of any proof *)
  in

  { elements = aux nodes_with_ast NoProof None []; document_repr; filename }

let rec dump_to_string (doc : t) : string =
  let rec aux (annotated_nodes : annotatedASTNode list) (doc_repr : string)
      (previous_line : int) =
    match annotated_nodes with
    | [] -> doc_repr
    | node :: tail ->
        let repr =
          doc_repr
          ^ String.make (node.range.start.line - previous_line) '\n'
          ^ String.make node.range.start.character ' '
          ^ node.repr
        in
        aux tail repr node.range.end_.line
  in
  aux doc.elements "" 0

let element_with_id_opt (element_id : int) (doc : t) : annotatedASTNode option =
  List.find_opt (fun elem -> elem.id = element_id) doc.elements

let split_at_id (target_id : int) (doc : t) :
    annotatedASTNode list * annotatedASTNode list =
  let rec aux (elements : annotatedASTNode list) (acc : annotatedASTNode list) =
    match elements with
    | [] -> (acc, [])
    | x :: tail ->
        if x.id = target_id then (List.rev acc, tail) else aux tail (x :: acc)
  in
  aux doc.elements []

let elements_starting_at_line (line_number : int) (doc : t) =
  List.filter (fun elem -> elem.range.start.line = line_number) doc.elements

let shift_nodes (n_line : int) (n_char : int) (nodes : annotatedASTNode list) :
    annotatedASTNode list =
  List.map (Annotated_ast_node.shift_node n_line n_char) nodes

let remove_node_with_id (target_id : int) (doc : t) : t =
  match element_with_id_opt target_id doc with
  | Some elem ->
      let before, after = split_at_id target_id doc in
      let line_shift =
        if List.length (elements_starting_at_line elem.range.start.line doc) > 1
        then 0
        else -1
      in
      {
        doc with
        elements = List.concat [ before; shift_nodes line_shift 0 after ];
      }
      (* Shift n char off the line if more than one element   *)
  | None -> doc

let insert_node (new_node : annotatedASTNode) (doc : t)
    (insert_pos : insertPosition) : (t, string) result =
  match insert_pos with
  | Before id -> (
      let target_node = element_with_id_opt id doc in
      match target_node with
      | Some target ->
          let before, after = split_at_id id doc in
          Ok
            {
              doc with
              elements =
                List.concat
                  [
                    before;
                    [ new_node ];
                    shift_nodes 1 (String.length new_node.repr) (target :: after);
                  ];
            }
      | None -> Error ("node with id " ^ string_of_int id ^ "doesn't exist"))
  | After id -> (
      let target_node = element_with_id_opt id doc in
      match target_node with
      | Some target ->
          let before, after = split_at_id id doc in
          Ok
            {
              doc with
              elements =
                List.concat
                  [
                    before;
                    [ target ];
                    [ new_node ];
                    shift_nodes 1 (String.length new_node.repr) after;
                  ];
            }
      | None -> Error ("node with id " ^ string_of_int id ^ "doesn't exist"))
  | Start ->
      Ok
        {
          doc with
          elements =
            shift_nodes 1
              (String.length new_node.repr)
              (new_node :: doc.elements);
        }
  | End -> Ok { doc with elements = doc.elements @ [ new_node ] }

(* let remove_coq_element (element_id: int) (doc: t) : (t, string) result = *)
(*   let element = element_with_id element_id doc in *)
(*   match element with *)
(*     Some elem -> *)
(*      if List.length (elements_starting_at_line elem.range.start.line doc) > 1 then *)
(*        List.t *)
(*      else *)
(*    | None -> Error "element not found" *)

(* let replace_coq_element (updated_element : coq_element) (doc : t) = *)
(*   { *)
(*     doc with *)
(*     elements = *)
(*       List.map *)
(*         (fun elem -> *)
(*           match (updated_element, elem) with *)
(*           | CoqNode updated_node, CoqNode old_node -> *)
(*               if updated_node.id = old_node.id then updated_element else elem *)
(*           | CoqStatement updated_proof, CoqStatement old_proof -> *)
(*               if updated_proof.proposition.id = old_proof.proposition.id then *)
(*                 updated_element *)
(*               else elem *)
(*           | _, e -> e) *)
(*         doc.elements; *)
(*   } *)
