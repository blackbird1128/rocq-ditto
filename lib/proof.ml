open Fleche
open Syntax_node
open Vernacexpr
open Nary_tree

type proof_status = Admitted | Proved | Aborted

let pp_proof_status (fmt : Format.formatter) (status : proof_status) : unit =
  match status with
  | Admitted -> Format.fprintf fmt "Admitted"
  | Proved -> Format.fprintf fmt "Proved"
  | Aborted -> Format.fprintf fmt "Aborted"

type attach_position = LineAfter | LineBefore

type transformation_step =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * syntaxNode
  | Add of syntaxNode
  | Attach of syntaxNode * attach_position * Uuidm.t

let pp_transformation_step (fmt : Format.formatter) (step : transformation_step)
    : unit =
  match step with
  | Remove id ->
      Format.fprintf fmt "Removing node with id : %s." (Uuidm.to_string id)
  | Replace (id, new_node) ->
      if new_node.range.start.line != new_node.range.end_.line then
        Format.fprintf fmt "Replacing node with id: %s by node: %s at %s"
          (Uuidm.to_string id) new_node.repr
          (Code_range.to_string new_node.range)
  | Add new_node ->
      Format.fprintf fmt "Adding new node: %s at %s" new_node.repr
        (Code_range.to_string new_node.range)
  | Attach (attached_node, attach_position, anchor_id) ->
      Format.fprintf fmt "Attaching node %s to node with id: %s "
        attached_node.repr
        (Uuidm.to_string anchor_id)

let transformation_step_to_string (step : transformation_step) : string =
  Format.asprintf "%a" pp_transformation_step step

let print_transformation_step (step : transformation_step) : unit =
  match step with
  | Remove id ->
      print_endline ("Removing node with id : " ^ Uuidm.to_string id ^ ".")
  | Replace (id, new_node) ->
      if new_node.range.start.line != new_node.range.end_.line then
        print_endline
          ("Replacing node with id: " ^ Uuidm.to_string id ^ " by node: "
         ^ new_node.repr ^ " at "
          ^ Code_range.to_string new_node.range)
  | Add new_node ->
      print_endline
        ("Adding new node: " ^ new_node.repr ^ " at "
        ^ Code_range.to_string new_node.range)
  | Attach (attached_node, attach_position, anchor_id) ->
      print_endline
        ("Attaching node " ^ attached_node.repr ^ " to node with id: "
       ^ Uuidm.to_string anchor_id)
(* TODO add precisions *)

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

let get_theorem_kind (x : proof) : Decls.theorem_kind option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | VernacStartTheoremProof (kind, _) -> Some kind
          | _ -> None))
  | None -> None

let get_constr_expr (x : proof) : Constrexpr.constr_expr option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof
              (kind, [ ((ident, univ), (binders, expr)) ]) ->
              Some expr
          | _ -> None))
  | None -> None

type theorem_components = {
  kind : Decls.theorem_kind;
  name : Names.lident;
  universe : Constrexpr.universe_decl_expr option;
  binders : Constrexpr.local_binder_expr list;
  expr : Constrexpr.constr_expr;
}

let get_theorem_components (x : proof) : theorem_components option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof
              (kind, [ ((name, universe), (binders, expr)) ]) ->
              Some { kind; name; universe; binders; expr }
          | _ -> None))
  | None -> None

let syntax_node_from_theorem_components (c : theorem_components)
    (start_point : Code_point.t) : syntaxNode =
  let expr_syn =
    Vernacexpr.VernacStartTheoremProof
      (c.kind, [ ((c.name, c.universe), (c.binders, c.expr)) ])
  in
  let synpure_expr = VernacSynPure expr_syn in
  let control = Syntax_node.mk_vernac_control synpure_expr in
  let coq_ast = Coq.Ast.of_coq control in
  Syntax_node.syntax_node_of_coq_ast coq_ast start_point

let proof_status_from_last_node (node : syntaxNode) :
    (proof_status, Error.t) result =
  match node.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).CAst.v.expr with
      | VernacSynterp _ ->
          Error.string_to_or_error_err "not a valid closing node"
      | VernacSynPure expr -> (
          match expr with
          | Vernacexpr.VernacEndProof proof_end -> (
              match proof_end with
              | Admitted -> Ok Admitted
              | Proved _ -> Ok Proved)
          | Vernacexpr.VernacAbort -> Ok Aborted
          | Vernacexpr.VernacAbortAll -> Ok Aborted
          | _ -> Error.string_to_or_error_err "not a valid closing node"))
  | None -> Error.string_to_or_error_err "not a valid closing node (no ast)"

let get_proof_name (p : proof) : string option =
  List.nth_opt (get_names p.proposition) 0

let get_proof_status (p : proof) : proof_status option =
  if List.length p.proof_steps < 1 then None
  else
    Result.to_option
      (proof_status_from_last_node
         (List.nth p.proof_steps (List.length p.proof_steps - 1)))

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

let proof_nodes (p : proof) : syntaxNode list = p.proposition :: p.proof_steps

let proof_from_nodes (nodes : syntaxNode list) : (proof, Error.t) result =
  if List.length nodes < 2 then
    Error.string_to_or_error_err
      ("Not enough elements to create a proof from the nodes.\nnodes: "
      ^ String.concat "" (List.map (fun node -> node.repr) nodes))
  else
    let last_node_status =
      List.hd (List.rev nodes) |> proof_status_from_last_node
    in
    match last_node_status with
    | Ok status ->
        Ok { proposition = List.hd nodes; proof_steps = List.tl nodes; status }
    | Error err -> Error err
