open Proof
open Fleche
open Annotated_ast_node

type coq_element = CoqNode of annotatedASTNode | CoqStatement of proof

let coq_element_to_string (x : coq_element) : string =
  match x with
  | CoqNode e ->
      Ppvernac.pr_vernac (Coq.Ast.to_coq e.ast.v) |> Pp.string_of_ppcmds
  | CoqStatement e -> Proof.proof_to_coq_script_string e

let get_theorem_names (elements : coq_element list) : string list =
  List.map
    (fun x ->
      match x with
      | CoqStatement e -> Option.default "" (Proof.get_proof_name e)
      | _ -> "")
    elements
  |> List.filter (fun s -> String.length s > 0)

let get_proofs (elements : coq_element list) : proof list =
  List.filter_map
    (fun x -> match x with CoqStatement e -> Some e | _ -> None)
    elements

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let parse_document (nodes : Doc.Node.t list) (document_repr : string) :
    coq_element list =
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
  aux nodes_with_ast None []

let rec dump_to_string (doc : coq_element list) : string =
  let annotated_nodes =
    List.concat_map
      (fun elem ->
        match elem with
        | CoqNode e -> [ e ]
        | CoqStatement p -> Proof.proof_nodes p)
      doc
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

let replace_node (new_node : annotatedASTNode) (nodes : annotatedASTNode list) =
  List.map (fun node -> if node.id = new_node.id then new_node else node) nodes

module IntMap = Map.Make (Int)

let replace_proof (proof : proof) (nodes : annotatedASTNode list) :
    annotatedASTNode list =
  let proof_nodes = Proof.proof_nodes proof in
  let build_replacement_map replacements =
    List.fold_left
      (fun map elem -> IntMap.add elem.id elem map)
      IntMap.empty replacements
  in
  let replacement_map = build_replacement_map proof_nodes in
  List.map
    (fun elem ->
      match IntMap.find_opt elem.id replacement_map with
      | Some new_elem -> new_elem (* Replace if found *)
      | None -> elem (* Keep original if not found *))
    nodes

let replace_coq_element (element : coq_element) (nodes : annotatedASTNode list)
    =
  match element with
  | CoqNode e -> replace_node e nodes
  | CoqStatement p -> replace_proof p nodes
