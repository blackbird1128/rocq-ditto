open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Annotated_ast_node
open Vernacexpr

let depth_to_bullet_type (depth : int) =
  let bullet_number = 1 + (depth / 3) in
  match depth mod 3 with
  | 0 -> VernacBullet (Proof_bullet.Dash bullet_number)
  | 1 -> VernacBullet (Proof_bullet.Plus bullet_number)
  | 2 -> VernacBullet (Proof_bullet.Star bullet_number)
  | _ -> VernacBullet (Proof_bullet.Dash bullet_number)

let create_annotated_ast_bullet (depth : int) (range : Lang.Range.t) :
    annotatedASTNode =
  let example_without_dirpath : Loc.source =
    InFile { dirpath = None; file = "main.ml" }
  in
  let control_r =
    {
      control = [];
      (* No control flags *)
      attrs = [];
      (* Default attributes *)
      expr =
        VernacSynPure (depth_to_bullet_type depth)
        (* The pure expression we created *);
    }
  in
  let loc = Loc.create example_without_dirpath 0 0 0 0 in
  let vernac_control = CAst.make ~loc control_r in
  let ast_node = Coq.Ast.of_coq vernac_control in
  ast_node_of_coq_ast ast_node range

let add_bullets (proof_tree : annotatedASTNode nary_tree) : Ditto.Proof.proof =
  let rec aux (depth : int) (node : annotatedASTNode nary_tree) =
    match node with
    | Node (x, []) -> [ x ]
    | Node (x, [ child ]) -> x :: aux depth child
    | Node (x, childrens) ->
        x
        :: List.concat
             (List.map
                (fun child ->
                  (match child with
                  | Node (y, _) -> create_annotated_ast_bullet depth y.range)
                  :: aux (depth + 1) child)
                childrens)
    (* each bullet need a different id *)
  in
  let res = aux 0 proof_tree in
  { proposition = List.hd res; proof_steps = List.tl res }

let replace_by_lia (doc : Doc.t) (proof_tree : annotatedASTNode nary_tree) :
    (Ditto.Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let proof = Proof.tree_to_proof proof_tree in
  let init_state = Proof.get_init_state doc proof in
  let rec aux (st : Petanque.Agent.State.t) (previous_goals : int)
      (node : annotatedASTNode nary_tree) : annotatedASTNode list =
    match node with
    | Node (x, childrens) -> (
        let lia_node =
          Result.get_ok (Annotated_ast_node.ast_node_of_string "lia." x.range)
        in
        let state_x = Petanque.Agent.run ~token ~st ~tac:x.repr () in
        let proof_state_x = Proof.get_proof_state state_x in
        let new_goals = count_goals token proof_state_x in
        let state_lia = Petanque.Agent.run ~token ~st ~tac:lia_node.repr () in
        match state_lia with
        | Ok state_uw ->
            let goals_with_lia = count_goals token state_uw.st in
            if goals_with_lia < previous_goals then
              if goals_with_lia = 0 then
                [ lia_node; qed_ast_node (shift_range 1 0 lia_node.range) ]
              else [ lia_node ]
            else
              x
              :: List.concat (List.map (aux proof_state_x new_goals) childrens)
        | Error err ->
            x :: List.concat (List.map (aux proof_state_x new_goals) childrens))
  in
  match init_state with
  | Some (Ok state) ->
      let head_tree = top_n 1 proof_tree in
      let tail_tree = List.hd (bottom_n 2 proof_tree) in
      let list = aux state.st 1 tail_tree in
      let list_head_tail = flatten head_tree @ list in
      Ok (Proof.proof_from_nodes list_head_tail)
  | _ -> Error "can't create an initial state for the proof "

let fold_replace_by_lia (doc : Doc.t) (proof_tree : annotatedASTNode nary_tree)
    : (Ditto.Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Proof.depth_first_fold_with_state doc token
      (fun state acc node ->
        let previous_goals, steps_acc = acc in
        if Annotated_ast_node.is_doc_node_proof_intro_or_end node then
          (state, (previous_goals, node :: steps_acc))
        else
          let state_node =
            Proof.get_proof_state
              (Petanque.Agent.run ~token ~st:state ~tac:node.repr ())
          in
          let lia_node =
            Result.get_ok
              (Annotated_ast_node.ast_node_of_string "lia." node.range)
          in

          let new_goals = count_goals token state in
          let state_lia =
            Petanque.Agent.run ~token ~st:state ~tac:lia_node.repr ()
          in
          match state_lia with
          | Ok state_uw ->
              let goals_with_lia = count_goals token state_uw.st in
              if goals_with_lia < previous_goals then
                if goals_with_lia = 0 then
                  ( state_uw.st,
                    ( goals_with_lia,
                      [
                        lia_node; qed_ast_node (shift_range 1 0 lia_node.range);
                      ]
                      @ steps_acc ) )
                else (state_uw.st, (goals_with_lia, lia_node :: steps_acc))
              else (state_node, (new_goals, node :: steps_acc))
          | Error err -> (state_node, (new_goals, node :: steps_acc)))
      (1, []) proof_tree
  in
  match res with
  | Ok (goals, steps) -> Ok (Proof.proof_from_nodes (List.rev steps))
  | Error err -> Error err

let pp_goal (goal : string Coq.Goals.Reified_goal.t) : unit =
  print_endline ("Goal : " ^ goal.ty);
  print_endline "---------------------";
  print_endline "Hypothesis: ";
  List.iter
    (fun (hyp : string Coq.Goals.Reified_goal.hyp) ->
      List.iter (fun name -> print_endline name) hyp.names)
    goal.hyps;
  print_endline "----------------------";
  ()

let pp_goal_stack
    (stack :
      (string Coq.Goals.Reified_goal.t list
      * string Coq.Goals.Reified_goal.t list)
      list) =
  print_endline ("size stack : " ^ string_of_int (List.length stack));
  List.iter
    (fun elem ->
      List.iter
        (fun (goal : string Coq.Goals.Reified_goal.t) -> pp_goal goal)
        (snd elem))
    stack;
  ()

let fold_inspect (doc : Doc.t) (proof_tree : annotatedASTNode nary_tree) =
  let token = Coq.Limits.Token.create () in

  let _ =
    Proof.depth_first_fold_with_state doc token
      (fun state acc node ->
        if Annotated_ast_node.is_doc_node_proof_intro_or_end node then
          (state, node :: acc)
        else
          let state_node =
            Proof.get_proof_state
              (Petanque.Agent.run ~token ~st:state ~tac:node.repr ())
          in
          print_endline ("Treating node : " ^ node.repr);
          let goals_err_opt = Petanque.Agent.goals ~token ~st:state_node in
          match goals_err_opt with
          | Ok (Some goals) ->
              List.iter pp_goal goals.goals;
              print_endline "\n";
              (state_node, node :: acc)
          | _ ->
              print_endline "error getting goals";
              (state_node, node :: acc))
      [] proof_tree
  in
  ()

let fold_replace_assumption_with_apply (doc : Doc.t)
    (proof_tree : annotatedASTNode nary_tree) :
    (Ditto.Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Proof.depth_first_fold_with_state doc token
      (fun state acc node ->
        if Annotated_ast_node.is_doc_node_proof_intro_or_end node then
          (state, node :: acc)
        else
          let state_node =
            Proof.get_proof_state
              (Petanque.Agent.run ~token ~st:state ~tac:node.repr ())
          in
          if String.starts_with ~prefix:"assumption" node.repr then
            let goal_count_after_assumption =
              Proof.count_goals token state_node
            in

            let curr_goal_err = Proof.get_current_goal token state in
            match curr_goal_err with
            | Ok curr_goal ->
                let hypothesis_apply_repr =
                  List.map
                    (fun name -> "apply " ^ name ^ ".")
                    (Proof.get_hypothesis_names curr_goal)
                in

                let apply_states =
                  List.filter_map
                    (fun repr ->
                      let r =
                        Petanque.Agent.run ~token ~st:state ~tac:repr ()
                      in
                      match r with
                      | Ok state_uw -> Some (repr, state_uw.st)
                      | Error _ -> None)
                    hypothesis_apply_repr
                in

                let replacement =
                  List.find
                    (fun tuple_n_r ->
                      Proof.count_goals token (snd tuple_n_r)
                      = goal_count_after_assumption)
                    apply_states
                in
                let new_node =
                  Result.get_ok
                    (Annotated_ast_node.ast_node_of_string (fst replacement)
                       node.range)
                in

                (state_node, new_node :: acc)
            | Error _ -> (state_node, node :: acc)
          else (state_node, node :: acc))
      [] proof_tree
  in
  match res with
  | Ok steps -> Ok (Proof.proof_from_nodes (List.rev steps))
  | Error err -> Error err
