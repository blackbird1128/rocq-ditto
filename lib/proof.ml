open Fleche
open Syntax_node
open Vernacexpr
open Proof_tree

type proof_status = Admitted | Proved | Aborted

let pp_proof_status (fmt : Format.formatter) (status : proof_status) : unit =
  match status with
  | Admitted -> Format.fprintf fmt "Admitted"
  | Proved -> Format.fprintf fmt "Proved"
  | Aborted -> Format.fprintf fmt "Aborted"

type transformation_step =
  | Remove of int
  | Replace of int * syntaxNode
  | Add of syntaxNode

let pp_transformation_step (fmt : Format.formatter) (step : transformation_step)
    : unit =
  match step with
  | Remove id -> Format.fprintf fmt "Removing node with id : %d." id
  | Replace (id, new_node) ->
      if new_node.range.start.line != new_node.range.end_.line then
        Format.fprintf fmt "Replacing node with id: %d by node: %s at %s" id
          new_node.repr
          (Lang.Range.to_string new_node.range)
  | Add new_node ->
      Format.fprintf fmt "Adding new node: %s at %s" new_node.repr
        (Lang.Range.to_string new_node.range)

type proof = {
  proposition : syntaxNode;
  proof_steps : syntaxNode list;
  status : proof_status;
}
(* proposition can also be a type, better name ? *)

(* A node can have multiple names (ie mutual recursive defs) *)
let get_names (node : syntaxNode) : string list =
  match node.ast with
  | Some ast -> (
      match ast.ast_info with
      | Some infos ->
          List.concat_map
            (fun (info : Lang.Ast.Info.t) ->
              match info.name.v with None -> [] | Some s -> [ s ])
            infos
      | None -> [])
  | None -> []

let proof_status_from_last_node (node : syntaxNode) :
    (proof_status, string) result =
  match node.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ -> Error "not a valid closing node"
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacEndProof proof_end -> (
              match proof_end with
              | Admitted -> Ok Admitted
              | Proved _ -> Ok Proved)
          | Vernacexpr.VernacAbort -> Ok Aborted
          | Vernacexpr.VernacAbortAll -> Ok Aborted
          | _ -> Error "not a valid closing node"))
  | None -> Error "not a valid closing node (no ast)"

let get_proof_name (p : proof) : string option =
  List.nth_opt (get_names p.proposition) 0

let get_tree_name (Node (x, children)) : string option =
  List.nth_opt (get_names x) 0

let doc_node_to_string (d : Doc.Node.Ast.t) : string =
  let pp_expr = Ppvernac.pr_vernac_expr (Coq.Ast.to_coq d.v).CAst.v.expr in
  Pp.string_of_ppcmds pp_expr

let print_proof (proof : proof) : unit =
  print_endline proof.proposition.repr;
  List.iter (fun p -> print_endline ("  " ^ p.repr)) proof.proof_steps

let rec print_tree (tree : syntaxNode nary_tree) (indent : string) : unit =
  match tree with
  | Node (value, children) ->
      Printf.printf "%sNode(%s)\n" indent value.repr;
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let last_offset (p : proof) : int =
  List.fold_left
    (fun acc elem ->
      if elem.range.end_.offset > acc then elem.range.end_.offset else acc)
    0
    (p.proposition :: p.proof_steps)

let proof_nodes (p : proof) : syntaxNode list = p.proposition :: p.proof_steps

let proof_from_nodes (nodes : syntaxNode list) : (proof, string) result =
  if List.length nodes < 3 then
    Error "Not enough elements to create a proof from the nodes ."
  else
    let last_node_status =
      List.hd (List.rev nodes) |> proof_status_from_last_node
    in
    match last_node_status with
    | Ok status ->
        Ok { proposition = List.hd nodes; proof_steps = List.tl nodes; status }
    | Error err -> Error err
