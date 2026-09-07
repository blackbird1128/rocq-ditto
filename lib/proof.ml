type proof_status = Admitted | Proved | Aborted
[@@deriving show { with_path = false }]

type closing = { node : Syntax_node.t; status : proof_status }

let equal_closing (a : closing) (b : closing) =
  Syntax_node.equal a.node b.node && a.status = b.status

type t = {
  opening : Syntax_node.t;
  proof_steps : Syntax_node.t list;
  closing : closing;
}

type theorem_components = {
  kind : Decls.theorem_kind;
  name : Names.lident;
  universe : Constrexpr.universe_decl_expr option;
  binders : Constrexpr.local_binder_expr list;
  expr : Constrexpr.constr_expr;
}

let equal (a : t) (b : t) =
  Syntax_node.equal a.opening b.opening
  && List.equal Syntax_node.equal a.proof_steps b.proof_steps
  && equal_closing a.closing b.closing

let get_theorem_components (p : t) : theorem_components option =
  match Syntax_node.synpure_expr p.opening with
  | Some
      (Vernacexpr.VernacStartTheoremProof
         (kind, [ ((name, universe), (binders, expr)) ])) ->
      Some { kind; name; universe; binders; expr }
  | _ -> None

let get_theorem_kind (p : t) : Decls.theorem_kind option =
  Option.map (fun c -> c.kind) (get_theorem_components p)

let get_constr_expr (p : t) : Constrexpr.constr_expr option =
  Option.map (fun c -> c.expr) (get_theorem_components p)

let get_proof_name (p : t) : Names.Id.t option =
  Option.map (fun c -> c.name.v) (get_theorem_components p)

let coq_ast_of_theorem_components (c : theorem_components) : Coq.Ast.t =
  let expr_syn =
    Vernacexpr.VernacStartTheoremProof
      (c.kind, [ ((c.name, c.universe), (c.binders, c.expr)) ])
  in
  let synpure_expr = Vernacexpr.VernacSynPure expr_syn in
  let control = Syntax_node.mk_vernac_control synpure_expr in
  Coq.Ast.of_coq control

let syntax_node_of_theorem_components (c : theorem_components)
    (start_point : Code_point.t) : Syntax_node.t =
  let coq_ast = coq_ast_of_theorem_components c in
  Syntax_node.of_coq_ast coq_ast start_point

let syntax_node_of_theorem_components_in_state ~(token : Coq.Limits.Token.t)
    ~(st : Coq.State.t) (c : theorem_components) (start_point : Code_point.t) :
    (Syntax_node.t, Error.t) result =
  let coq_ast = coq_ast_of_theorem_components c in
  Syntax_node.of_coq_ast_in_state ~token ~st coq_ast start_point

let closing_from_last_node (node : Syntax_node.t) : (closing, Error.t) result =
  match Syntax_node.synpure_expr node with
  | Some expr -> (
      match expr with
      | Vernacexpr.VernacEndProof Admitted -> Ok { node; status = Admitted }
      | Vernacexpr.VernacEndProof (Proved _) -> Ok { node; status = Proved }
      | Vernacexpr.VernacAbort | Vernacexpr.VernacAbortAll ->
          Ok { node; status = Aborted }
      | _ ->
          Error.format_to_or_error "(%s) is not a valid closing node"
            (Syntax_node.repr node))
  | None -> (
      match node.kind with
      | Vernac _ ->
          Error.format_to_or_error "(%s) is not a valid closing node"
            (Syntax_node.repr node)
      | Comment ->
          Error.format_to_or_error
            "(%s) is not a valid closing node (is a comment)"
            (Syntax_node.repr node))

let status (p : t) : proof_status = p.closing.status

let get_proof_conclusion (p : t) : Constrexpr.constr_expr option =
  match get_theorem_components p with
  | Some components -> Constrexpr_utils.get_conclusion components.expr
  | None -> None

let map_proof_proposition (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : t) : Transforming_step.t option =
  let ( let* ) = Option.bind in
  let x_start = x.opening.range.start in
  let* components = get_theorem_components x in

  let new_expr = Constrexpr_map.constr_expr_map f components.expr in
  if not (Constrexpr_ops.constr_expr_eq components.expr new_expr) then
    let new_components = { components with expr = new_expr } in

    let new_node = syntax_node_of_theorem_components new_components x_start in

    Some (Transforming_step.Replace (x.opening.id, new_node))
  else None

let map_proof_proposition_in_state
    (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) (x : t) :
    (Transforming_step.t option, Error.t) result =
  let ( let* ) = Result.bind in
  let x_start = x.opening.range.start in
  match get_theorem_components x with
  | Some components ->
      let new_expr = Constrexpr_map.constr_expr_map f components.expr in
      if not (Constrexpr_ops.constr_expr_eq components.expr new_expr) then
        let new_components = { components with expr = new_expr } in

        let* new_node =
          syntax_node_of_theorem_components_in_state ~token ~st new_components
            x_start
        in

        Ok (Some (Transforming_step.Replace (x.opening.id, new_node)))
      else Ok None
  | None -> Ok None

let all_nodes (p : t) : Syntax_node.t list =
  p.opening :: (p.proof_steps @ [ p.closing.node ])

let proof_nodes (p : t) : Syntax_node.t list = p.opening :: p.proof_steps

let of_nodes (nodes : Syntax_node.t list) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  match List_utils.split_head_last nodes with
  | None ->
      Error.string_to_or_error
        ("Not enough elements to create a proof from the nodes.\nnodes: ["
        ^ String.concat " " (List.map (fun node -> Syntax_node.repr node) nodes)
        ^ "]")
  | Some (opening, body, last) ->
      if not (Syntax_node.can_open_proof opening) then
        Error.format_to_or_error
          "The provided first node (%s) can't open a proof"
          (Syntax_node.repr opening)
      else
        let* closing = closing_from_last_node last in
        Ok { opening; proof_steps = body; closing }
