open Fleche
open Syntax_node
open Vernacexpr

type proof_status = Admitted | Proved | Aborted
[@@deriving show { with_path = false }]

type attach_position = LineAfter | LineBefore | SameLine
[@@deriving show { with_path = false }]

type transformation_step =
  | Remove of Uuidm.t
  | Replace of Uuidm.t * Syntax_node.t
  | Add of Syntax_node.t
  | Attach of Syntax_node.t * attach_position * Uuidm.t

let pp_transformation_step (fmt : Format.formatter) (step : transformation_step)
    : unit =
  match step with
  | Remove id -> Format.fprintf fmt "Remove(%s)." (Uuidm.to_string id)
  | Replace (id, new_node) ->
      Format.fprintf fmt "Replace(%s, %s)" (Uuidm.to_string id) (repr new_node)
  | Add new_node ->
      Format.fprintf fmt "Add(%s) at %s" (repr new_node)
        (Code_range.to_string new_node.range)
  | Attach (attached_node, attach_position, anchor_id) ->
      Format.fprintf fmt "Attach(%s, %s, %s)" (repr attached_node)
        (show_attach_position attach_position)
        (Uuidm.to_string anchor_id)

let transformation_step_to_string (step : transformation_step) : string =
  Format.asprintf "%a" pp_transformation_step step

(* TODO add precisions *)

type t = { proposition : Syntax_node.t; proof_steps : Syntax_node.t list }
(* proposition can also be a type, better name ? *)

let get_theorem_kind (x : t) : Decls.theorem_kind option =
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

let get_constr_expr (x : t) : Constrexpr.constr_expr option =
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
          | Vernacexpr.VernacStartTheoremProof (_, [ ((_, _), (_, expr)) ]) ->
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

let get_theorem_components (x : t) : theorem_components option =
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

let syntax_node_of_theorem_components (c : theorem_components)
    (start_point : Code_point.t) : Syntax_node.t =
  let expr_syn =
    Vernacexpr.VernacStartTheoremProof
      (c.kind, [ ((c.name, c.universe), (c.binders, c.expr)) ])
  in
  let synpure_expr = VernacSynPure expr_syn in
  let control = Syntax_node.mk_vernac_control synpure_expr in
  let coq_ast = Coq.Ast.of_coq control in
  Syntax_node.syntax_node_of_coq_ast coq_ast start_point

let syntax_node_of_theorem_components_in_state ~(token : Coq.Limits.Token.t)
    ~(st : Coq.State.t) (c : theorem_components) (start_point : Code_point.t) :
    (Syntax_node.t, Error.t) result =
  let expr_syn =
    Vernacexpr.VernacStartTheoremProof
      (c.kind, [ ((c.name, c.universe), (c.binders, c.expr)) ])
  in
  let synpure_expr = VernacSynPure expr_syn in
  let control = Syntax_node.mk_vernac_control synpure_expr in
  let coq_ast = Coq.Ast.of_coq control in
  Syntax_node.syntax_node_of_coq_ast_in_state ~token ~st coq_ast start_point

let proof_status_of_vernacexpr (expr : Vernacexpr.synpure_vernac_expr) :
    (proof_status, Error.t) result =
  match expr with
  | Vernacexpr.VernacEndProof Admitted -> Ok Admitted
  | Vernacexpr.VernacEndProof (Proved _) -> Ok Proved
  | Vernacexpr.VernacAbort | Vernacexpr.VernacAbortAll -> Ok Aborted
  | _ -> Error.string_to_or_error "not a valid closing node"

let proof_status_from_last_node (node : Syntax_node.t) :
    (proof_status, Error.t) result =
  match node.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ ->
          Error.format_to_or_error "(%s) is not a valid closing node"
            (Syntax_node.repr node)
      | VernacSynPure expr -> proof_status_of_vernacexpr expr)
  | None ->
      Error.format_to_or_error "(%s) is not a valid closing node (no ast)"
        (Syntax_node.repr node)

let get_proof_name (p : t) : string option =
  match p.proposition.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof (_, [ ((name, _), _) ]) ->
              Some (Names.Id.to_string name.v)
          | _ -> None))
  | None -> None

let status (p : t) : proof_status =
  match List_utils.last p.proof_steps with
  | Some last -> (
      match proof_status_from_last_node last with
      | Ok status -> status
      | Error _ -> assert false (* impossible by proof_from_nodes invariant *))
  | None -> assert false (* a proof always has a last closing proof steps *)

let get_proof_conclusion (p : t) : Constrexpr.constr_expr option =
  let rec get_conclusion (expr : Constrexpr.constr_expr) =
    match expr.v with
    | Constrexpr.CProdN (_, body) -> get_conclusion body
    | Constrexpr.CLetIn (_, _, _, body) -> get_conclusion body
    | Constrexpr.CNotation (_, (_, notation_key), (args, _, _, _)) ->
        if notation_key = "_ -> _" then (
          match args with
          | [ _; right ] -> get_conclusion right
          | _ ->
              Logs.debug (fun m ->
                  m
                    "fun: get_proof_conclusion\n\
                     You should never see this message\n\
                     Please fill an issue");
              assert false)
        else Some expr
    | _ -> Some expr
  in

  match get_theorem_components p with
  | Some components -> get_conclusion components.expr
  | None -> None

let map_proof_proposition (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : t) : transformation_step option =
  let ( let+ ) = Option.bind in
  let x_start = x.proposition.range.start in
  let+ components = get_theorem_components x in

  let new_expr = Constrexpr_map.constr_expr_map f components.expr in
  if not (Constrexpr_ops.constr_expr_eq components.expr new_expr) then
    let new_components = { components with expr = new_expr } in

    let new_node = syntax_node_of_theorem_components new_components x_start in

    Some (Replace (x.proposition.id, new_node))
  else None

let map_proof_proposition_in_state
    (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) (x : t) :
    (transformation_step option, Error.t) result =
  let ( let* ) = Result.bind in
  let x_start = x.proposition.range.start in
  let components_opt = get_theorem_components x in
  match components_opt with
  | Some components ->
      let new_expr = Constrexpr_map.constr_expr_map f components.expr in
      if not (Constrexpr_ops.constr_expr_eq components.expr new_expr) then
        let new_components = { components with expr = new_expr } in

        let* new_node =
          syntax_node_of_theorem_components_in_state ~token ~st new_components
            x_start
        in

        Ok (Some (Replace (x.proposition.id, new_node)))
      else Ok None
  | None -> Ok None

let proof_nodes (p : t) : Syntax_node.t list = p.proposition :: p.proof_steps

let proof_from_nodes (nodes : Syntax_node.t list) : (t, Error.t) result =
  match nodes with
  | [] | [ _ ] ->
      Error.string_to_or_error
        ("Not enough elements to create a proof from the nodes.\nnodes: "
        ^ String.concat " " (List.map (fun node -> repr node) nodes))
  | proposition :: tail as nodes ->
      if not (Syntax_node.can_open_proof proposition) then
        Error.format_to_or_error
          "The provided first node (%s) can't open a proof"
          (Syntax_node.repr proposition)
      else
        (* there is a last node as there is more than one node in the list, that last node might end the proof or  *)
        let last_node = List_utils.last tail |> Option.get in
        if not (Syntax_node.can_close_proof last_node) then
          Error.format_to_or_error
            "The provided last node (%s) can't close a proof"
            (Syntax_node.repr last_node)
        else Ok { proposition = List.hd nodes; proof_steps = List.tl nodes }
