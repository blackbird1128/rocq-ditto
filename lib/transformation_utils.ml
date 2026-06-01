open Syntax_node
open Proof
open Vernacexpr

let ( let+ ) = Option.bind

let map_raw_tactic_expr_in_node
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (node : Syntax_node.t) : Proof.transformation_step option =
  let ( let+ ) = Option.bind in
  let open Proof in
  let+ raw_tac_expr = get_node_raw_tactic_expr node in
  let raw_expr_mapped = Tacexpr_map.tacexpr_map f raw_tac_expr in
  if raw_tac_expr = raw_expr_mapped then None
  else
    let selector = get_node_goal_selector_opt node in
    let+ new_node =
      Syntax_node.raw_tactic_expr_to_syntax_node raw_expr_mapped ?selector
        node.range.start
      |> Result.to_option
    in
    Some (Replace (node.id, new_node))

let map_definition_body (f : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (x : Syntax_node.t) : transformation_step option =
  match x.ast with
  | Some ast -> (
      match (Coq.Ast.to_coq ast.v).v.expr with
      | VernacSynPure
          (Vernacexpr.VernacDefinition
             ((discharge, definition_object_kind), name_decl, expr)) -> (
          match expr with
          | ProveBody _ -> None
          | DefineBody (binders, raw_red_expr_opt, expr1, opt_expr) ->
              let new_expr = Constrexpr_map.constr_expr_map f expr1 in
              if not (Constrexpr_ops.constr_expr_eq expr1 new_expr) then
                let new_define_body =
                  DefineBody (binders, raw_red_expr_opt, new_expr, opt_expr)
                in
                let new_vernacexpr =
                  VernacSynPure
                    (VernacDefinition
                       ( (discharge, definition_object_kind),
                         name_decl,
                         new_define_body ))
                in
                let new_vernac_control =
                  Syntax_node.mk_vernac_control new_vernacexpr
                in
                let new_node =
                  Syntax_node.syntax_node_of_coq_ast
                    (Coq.Ast.of_coq new_vernac_control)
                    x.range.start
                in
                Some (Replace (x.id, new_node))
              else None)
      | _ -> None)
  | None -> None

let map_tacdef_bodies_in_node
    (f :
      Ltac_plugin.Tacexpr.raw_tactic_expr -> Ltac_plugin.Tacexpr.raw_tactic_expr)
    (g : Constrexpr.constr_expr -> Constrexpr.constr_expr)
    (node : Syntax_node.t) : transformation_step option =
  let+ tacdef_bodies = Syntax_node.get_node_tacdef_bodies node in
  let tacdef_bodies_mapped =
    List.map
      (fun (body : Ltac_plugin.Tacexpr.tacdef_body) ->
        match body with
        | Ltac_plugin.Tacexpr.TacticDefinition (name, tacexpr) ->
            Ltac_plugin.Tacexpr.TacticDefinition
              (name, Tacexpr_map.tacexpr_map_with_constr f g tacexpr)
        | Ltac_plugin.Tacexpr.TacticRedefinition (name, tacexpr) ->
            Ltac_plugin.Tacexpr.TacticRedefinition
              (name, Tacexpr_map.tacexpr_map_with_constr f g tacexpr))
      tacdef_bodies
  in

  if not (List.equal ( = ) tacdef_bodies tacdef_bodies_mapped) then
    let+ new_node =
      Syntax_node.tacdef_body_list_to_syntax_node tacdef_bodies_mapped
        node.range.start
      |> Result.to_option
    in

    Some (Replace (node.id, new_node))
  else None

let map_syntax_node (f : Syntax_node.t -> Syntax_node.t) (x : Syntax_node.t) :
    transformation_step option =
  let fx = f x in
  if not (x = fx) then Some (Replace (x.id, fx)) else None

let map_vernacexpr_in_node
    (f : Vernacexpr.vernac_expr -> Vernacexpr.vernac_expr) (x : Syntax_node.t) :
    transformation_step option =
  match x.ast with
  | Some ast ->
      let mapped_vernacexpr = f (Coq.Ast.to_coq ast.v).v.expr in
      let new_node =
        Syntax_node.syntax_node_of_vernacexpr mapped_vernacexpr x.range.start
      in
      if not (x = new_node) then Some (Replace (x.id, new_node)) else None
  | None -> None
