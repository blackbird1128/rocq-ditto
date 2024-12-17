open Proof
open Fleche
open Annotated_ast_node

type t = {
  filename : string;
  elements : annotatedASTNode list;
  document_repr : string;
}

let coq_element_to_string (x : coq_element) : string =
  match x with
  | CoqNode e ->
      Ppvernac.pr_vernac (Coq.Ast.to_coq e.ast.v) |> Pp.string_of_ppcmds
  | CoqStatement e -> Proof.proof_to_coq_script_string e

let get_theorem_names (doc : t) : string list =
  List.map
    (fun x ->
      match x with
      | CoqStatement e -> Option.default "" (Proof.get_proof_name e)
      | _ -> "")
    doc.elements
  |> List.filter (fun s -> String.length s > 0)

let get_proofs (doc : t) : proof list =
  List.filter_map
    (fun x -> match x with CoqStatement e -> Some e | _ -> None)
    doc.elements

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let parse_document (nodes : Doc.Node.t list) (document_repr : string)
    (filename : string) : t =
  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in
  let rec aux (spans : Doc.Node.t list) current_proof document =
    match spans with
    | [] -> (
        match current_proof with
        | Some _ ->
            raise (Invalid_argument "proof started but ended at document end")
        | None -> List.rev document)
    | span :: rest -> (
        let annotated_span =
          {
            ast = Option.get span.ast;
            range = span.range;
            repr = node_representation span document_repr;
            id = Unique_id.next ();
          }
        in
        if is_doc_node_ast_proof_start annotated_span then
          aux rest
            (Some { proposition = annotated_span; proof_steps = [] })
            document
        else if is_doc_node_ast_proof_end annotated_span then
          match current_proof with
          | Some current_proof ->
              let completed_proof =
                {
                  current_proof with
                  proof_steps =
                    List.rev (annotated_span :: current_proof.proof_steps);
                }
              in
              aux rest None (CoqStatement completed_proof :: document)
          | None -> raise (Invalid_argument "proof ended but never started")
        else
          match current_proof with
          | Some proof ->
              aux rest
                (Some
                   {
                     proof with
                     proof_steps = annotated_span :: proof.proof_steps;
                   })
                document
          | None -> aux rest None (CoqNode annotated_span :: document))
    (* Skip spans not part of any proof *)
  in
  { elements = aux nodes_with_ast None []; document_repr; filename }

let rec dump_to_string (doc : t) : string =
  let annotated_nodes =
    List.concat_map
      (fun elem ->
        match elem with
        | CoqNode e -> [ e ]
        | CoqStatement p -> Proof.proof_nodes p)
      doc.elements
  in

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
  aux annotated_nodes "" 0

let get_annotated_nodes (doc : t) : annotatedASTNode list =
  List.concat_map
    (fun elem ->
      match elem with
      | CoqNode e -> [ e ]
      | CoqStatement p -> Proof.proof_nodes p)
    doc.elements

let element_with_id (element_id : int) (doc : t) : annotatedASTNode option =
  let nodes = get_annotated_nodes doc in
  List.find_opt (fun elem -> elem.id = element_id) nodes

let elements_starting_at_line (line_number : int) (doc : t) =
  List.filter
    (fun elem ->
      match elem with
      | CoqNode e -> e.range.start.line = line_number
      | CoqStatement p -> p.proposition.range.start.line = line_number)
    doc.elements

let split_doc_before_after_id (element_id : int) (doc : t) :
    coq_element list * coq_element list =
  let rec aux (elements : coq_element list) (acc : coq_element list) :
      coq_element list * coq_element list =
    match elements with
    | [] -> acc
    | elem :: tail ->
        if elem.id = element_id then (acc, tail) else aux tail (elem :: acc)
  in
  aux doc.elements []

(* let remove_coq_element (element_id: int) (doc: t) : (t, string) result = *)
(*   let element = element_with_id element_id doc in *)
(*   match element with *)
(*     Some elem -> *)
(*      if List.length (elements_starting_at_line elem.range.start.line doc) > 1 then *)
(*        List.t *)
(*      else *)
(*    | None -> Error "element not found" *)

let replace_coq_element (updated_element : coq_element) (doc : t) =
  {
    doc with
    elements =
      List.map
        (fun elem ->
          match (updated_element, elem) with
          | CoqNode updated_node, CoqNode old_node ->
              if updated_node.id = old_node.id then updated_element else elem
          | CoqStatement updated_proof, CoqStatement old_proof ->
              if updated_proof.proposition.id = old_proof.proposition.id then
                updated_element
              else elem
          | _, e -> e)
        doc.elements;
  }
