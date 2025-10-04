open Fleche
open Nary_tree
open Proof
open Syntax_node
open Vernacexpr
open Runner
open Sexplib.Conv
open Re

let depth_to_bullet_type (depth : int) =
  let bullet_number = 1 + (depth / 3) in
  match depth mod 3 with
  | 0 -> VernacBullet (Proof_bullet.Dash bullet_number)
  | 1 -> VernacBullet (Proof_bullet.Plus bullet_number)
  | 2 -> VernacBullet (Proof_bullet.Star bullet_number)
  | _ -> VernacBullet (Proof_bullet.Dash bullet_number)

let create_annotated_ast_bullet (depth : int) (starting_point : Code_point.t) :
    syntaxNode =
  let control_r =
    {
      control = [];
      attrs = [];
      expr =
        VernacSynPure (depth_to_bullet_type depth)
        (* The pure expression we created *);
    }
  in
  let vernac_control = CAst.make control_r in
  let ast_node = Coq.Ast.of_coq vernac_control in
  syntax_node_of_coq_ast ast_node starting_point

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

let fold_inspect (doc : Coq_document.t) (proof_tree : syntaxNode nary_tree) :
    unit =
  let token = Coq.Limits.Token.create () in

  let _ =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let state_node = Result.get_ok (Runner.run_node token state node) in
        let goals_err_opt = Runner.goals ~token ~st:state_node in
        match goals_err_opt with
        | Ok (Some goals) ->
            List.iter pp_goal goals.goals;
            print_endline "\n";
            Ok (state_node, node :: acc)
        | _ ->
            print_endline "error getting goals";
            Ok (state_node, node :: acc))
      [] proof_tree
  in
  ()

(* let add_bullets (doc : Coq_document.t) (proof_tree : syntaxNode nary_tree) : *)
(*     (transformation_step list, Error.t) result = *)
(*   let token = Coq.Limits.Token.create () in *)
(*   let rec aux state acc depth tree = *)
(*     match tree with *)
(*     | Node (x, children) -> *)
(*        let new_state = Result.get_ok (Runner.run_node token state x) in *)
(*        let new_acc = if  List.length children > 0 then *)

(*         List.fold_left *)
(*           (fun (state_acc, res_acc) child -> aux state_acc res_acc 0 child) *)
(*           (new_state, acc) children *)
(*   in *)
(*   match get_init_state doc (root proof_tree) token with *)
(*   | Ok state -> *)
(*       let a = aux state [] 0 proof_tree in *)
(*       Ok [] *)
(*   | Error _ -> Error.string_to_or_error_err "Unable to retrieve initial state" *)

let simple_proof_repair (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let token = Coq.Limits.Token.create () in
  let admit_creator =
   fun node -> Syntax_node.syntax_node_of_string "admit." node.range.start
  in
  let module SyntaxNodeSet = Set.Make (struct
    type t = syntaxNode

    let compare = Syntax_node.compare_nodes
  end) in
  let ignore_set = SyntaxNodeSet.empty in

  match get_init_state doc (root proof_tree) token with
  | Ok state ->
      let* _, steps_acc, ignore_acc, _ =
        Nary_tree.depth_first_fold_with_children_as_trees
          (fun acc node children ->
            print_endline ("treating " ^ node.repr);
            match acc with
            | Ok (state_acc, steps_acc, ignore_acc, prev_goal_count) -> (
                if SyntaxNodeSet.mem node ignore_acc then
                  Ok (state_acc, steps_acc, ignore_acc, prev_goal_count)
                else
                  let state_res = Runner.run_node token state_acc node in
                  match state_res with
                  | Ok new_state ->
                      let num_goals = Runner.count_goals token new_state in
                      if
                        List.length children = 0
                        && (not
                              (Syntax_node.is_syntax_node_proof_intro_or_end
                                 node))
                        && prev_goal_count <= num_goals
                      then
                        let* admit_node = admit_creator node in
                        let* admit_state =
                          Runner.run_node token new_state admit_node
                        in
                        Ok (admit_state, steps_acc, ignore_acc, prev_goal_count)
                      else Ok (new_state, steps_acc, ignore_acc, num_goals)
                  | Error err ->
                      let childs =
                        List.concat (List.map Nary_tree.flatten children)
                        |> List.filter (fun x ->
                               not (is_syntax_node_proof_intro_or_end x))
                      in

                      let ignore_acc =
                        SyntaxNodeSet.union ignore_acc
                          (SyntaxNodeSet.of_list childs)
                      in
                      let* admit_node = admit_creator node in
                      let* admit_state =
                        Runner.run_node token state_acc admit_node
                        |> Result.map_error Error.tag_with_debug_infos
                      in
                      let num_goals = Runner.count_goals token admit_state in

                      Ok
                        ( admit_state,
                          Replace (node.id, admit_node) :: steps_acc,
                          ignore_acc,
                          num_goals ))
            | Error err -> Error err)
          (Ok (state, [], ignore_set, 1))
          proof_tree
      in

      let removed_steps =
        SyntaxNodeSet.to_list ignore_acc |> List.map (fun x -> Remove x.id)
      in
      Ok (steps_acc @ removed_steps)
  | _ -> Error.string_to_or_error_err "Unable to retrieve initial state"

type op_type = Cut | Keep

let admit_branch_at_error (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let admit_creator =
   fun node ->
    Result.get_ok (Syntax_node.syntax_node_of_string "admit" node.range.start)
  in
  let rec aux state_acc tree steps_acc =
    match tree with
    | Node (x, children) -> (
        if is_syntax_node_proof_intro_or_end x then
          let state = Result.get_ok (Runner.run_node token state_acc x) in
          List.fold_left
            (fun (state, acc) child ->
              let new_state, new_acc = aux state child acc in
              (new_state, new_acc))
            (state, steps_acc) children
        else
          let state = Runner.run_node token state_acc x in

          (* Fold over the children using the updated state and accumulator *)
          match state with
          | Ok state ->
              List.fold_left
                (fun (state, acc) child ->
                  let new_state, new_acc = aux state child acc in
                  (new_state, new_acc))
                (state, steps_acc) children
          | Error err ->
              let admit_node = admit_creator x in
              let cut_node_state =
                Runner.run_node token state_acc admit_node |> Result.get_ok
              in

              let cut_node_goals_count =
                Runner.count_goals token cut_node_state
              in
              let children_nodes =
                List.concat (List.map Nary_tree.flatten children)
              in

              let next_state =
                List.fold_left
                  (fun state_acc node ->
                    if node_can_close_proof node then state_acc
                    else Result.get_ok (Runner.run_node token state_acc node))
                  cut_node_state children_nodes
              in

              let next_state_goals = Runner.count_goals token next_state in

              if cut_node_goals_count = next_state_goals then
                let children_nodes =
                  List.concat (List.map Nary_tree.flatten children)
                in

                let remove_steps =
                  List.filter_map
                    (fun node ->
                      if node_can_open_proof node || node_can_close_proof node
                      then None
                      else Some (Remove node.id))
                    (x :: children_nodes)
                in
                (cut_node_state, steps_acc @ (Add admit_node :: remove_steps))
              else
                List.fold_left
                  (fun (state, acc) child ->
                    let new_state, new_acc = aux state child acc in
                    (new_state, new_acc))
                  (cut_node_state, steps_acc)
                  children)
  in
  let cur_proof = Runner.tree_to_proof proof_tree in
  match get_init_state doc cur_proof.proposition token with
  | Ok state ->
      let _, steps = aux state proof_tree [] in
      Ok steps
  | _ -> Error.string_to_or_error_err "Unable to retrieve initial state"

let cut_replace_branch (cut_tactic : string) (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let node_creator =
   fun node ->
    Result.get_ok
      (Syntax_node.syntax_node_of_string cut_tactic node.range.start)
  in

  let rec aux state_acc tree steps_acc =
    match tree with
    | Node (x, children) -> (
        let state = Result.get_ok (Runner.run_node token state_acc x) in
        if is_syntax_node_proof_intro_or_end x then
          List.fold_left
            (fun (state, acc) child ->
              let new_state, new_acc = aux state child acc in
              (new_state, new_acc))
            (state, steps_acc) children
        else
          let cut_node = node_creator x in
          let cut_node_state_res = Runner.run_node token state_acc cut_node in
          (* Fold over the children using the updated state and accumulator *)
          match cut_node_state_res with
          | Ok cut_node_state ->
              let cut_node_goals_count =
                Runner.count_goals token cut_node_state
              in
              let children_nodes =
                List.concat (List.map Nary_tree.flatten children)
              in

              let next_state =
                List.fold_left
                  (fun state_acc node ->
                    if node_can_close_proof node then state_acc
                    else Result.get_ok (Runner.run_node token state_acc node))
                  state children_nodes
              in

              let next_state_goals = Runner.count_goals token next_state in

              if cut_node_goals_count = next_state_goals then
                let children_nodes =
                  List.concat (List.map Nary_tree.flatten children)
                in

                let remove_steps =
                  List.filter_map
                    (fun node ->
                      if node_can_open_proof node || node_can_close_proof node
                      then None
                      else Some (Remove node.id))
                    (x :: children_nodes)
                in
                (cut_node_state, steps_acc @ (Add cut_node :: remove_steps))
              else
                List.fold_left
                  (fun (state, acc) child ->
                    let new_state, new_acc = aux state child acc in
                    (new_state, new_acc))
                  (state, steps_acc) children
          | Error err ->
              List.fold_left
                (fun (state, acc) child ->
                  let new_state, new_acc = aux state child acc in
                  (new_state, new_acc))
                (state, steps_acc) children)
  in
  let cur_proof = Runner.tree_to_proof proof_tree in
  match get_init_state doc cur_proof.proposition token with
  | Ok state ->
      let _, steps = aux state proof_tree [] in
      Ok steps
  | _ -> Error.string_to_or_error_err "Unable to retrieve initial state"

let fold_replace_assumption_with_apply (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let state_node = Runner.run_node token state node |> Result.get_ok in
        if
          String.starts_with ~prefix:"assumption" node.repr
          && not (String.contains node.repr ';')
        then
          let goal_count_after_assumption =
            Runner.count_goals token state_node
          in

          let curr_goal_err = Runner.get_current_goal token state in
          match curr_goal_err with
          | Ok curr_goal ->
              let hypothesis_apply_repr =
                List.map
                  (fun name -> "apply " ^ name ^ ".")
                  (Runner.get_hypothesis_names curr_goal)
              in
              let apply_nodes =
                List.map
                  (fun repr ->
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string repr node.range.start))
                  hypothesis_apply_repr
              in

              let apply_states =
                List.filter_map
                  (fun node ->
                    let r = Runner.run_node token state node in
                    match r with
                    | Ok state_uw -> Some (node, state_uw)
                    | Error _ -> None)
                  apply_nodes
              in

              let replacement =
                List.find
                  (fun tuple_n_r ->
                    Runner.count_goals token (snd tuple_n_r)
                    = goal_count_after_assumption)
                  apply_states
              in
              let new_node = fst replacement in

              Ok (state_node, Replace (node.id, new_node) :: acc)
          | Error err -> Ok (state_node, acc)
        else Ok (state_node, acc))
      [] proof_tree
  in
  res

let remove_empty_lines (proof : proof) : proof =
  let nodes = proof_nodes proof in
  let first_node_opt = List.nth_opt nodes 0 in
  match first_node_opt with
  | Some first_node ->
      let res =
        List.fold_left
          (fun acc node ->
            let prev_node, acc_nodes, shift = acc in
            if prev_node = node then (node, node :: acc_nodes, shift)
            else
              let shift_value =
                prev_node.range.end_.line - node.range.start.line + 1 + shift
              in
              let shifted = shift_node shift_value 0 node in
              (node, shifted :: acc_nodes, shift_value))
          (first_node, [], 0) nodes
      in
      let _, res_func, _ = res in
      Result.get_ok (proof_from_nodes (List.rev res_func))
  | None -> proof

let id_transform (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  Ok []

let admit_proof (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  let proof_close_node =
    List.find Syntax_node.is_syntax_node_proof_end proof.proof_steps
  in
  let* admitted_node =
    syntax_node_of_string "Admitted." proof_close_node.range.start
  in
  Ok [ Replace (proof_close_node.id, admitted_node) ]

let remove_random_step (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let num_steps = List.length proof.proof_steps in
  if num_steps <= 2 then Ok []
  else
    let rand_num = Random.int_in_range ~min:1 ~max:(num_steps - 2) in
    let rand_node = List.nth proof.proof_steps rand_num in
    let incorrect_node =
      Syntax_node.syntax_node_of_string "fail." rand_node.range.start
      |> Result.get_ok
    in
    Ok [ Replace (rand_node.id, incorrect_node) ]

let admit_and_comment_proof_steps (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let remove_all_steps =
    List.map (fun step -> Remove step.id) proof.proof_steps
  in
  let first_proof_node = List.hd proof.proof_steps in

  let comment_content =
    List.fold_left
      (fun str_acc step -> str_acc ^ step.repr ^ "\n")
      "(* "
      (List_utils.take
         (max 0 (List.length proof.proof_steps - 1))
         proof.proof_steps)
    ^ " *)"
  in

  let comment_node =
    Result.get_ok
      (Syntax_node.comment_syntax_node_of_string comment_content
         first_proof_node.range.start)
  in

  let admitted_start =
    shift_point 1 (-comment_node.range.end_.character) comment_node.range.end_
  in

  let admitted_node =
    Result.get_ok (Syntax_node.syntax_node_of_string "Admitted." admitted_start)
  in
  Ok
    (remove_all_steps
    @ [
        Attach (comment_node, LineAfter, proof.proposition.id);
        Attach (admitted_node, LineAfter, comment_node.id);
      ])

let remove_unecessary_steps (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token_reduce = Coq.Limits.Token.create () in

  let rec aux state acc nodes =
    match nodes with
    | [] -> acc
    | x :: tail -> (
        if
          ((not (is_syntax_node_proof_intro_or_end x))
          && not (is_syntax_node_bullet x))
          && Runner.can_reduce_to_zero_goals state tail
        then aux state (Remove x.id :: acc) tail
        else
          let token = Coq.Limits.Token.create () in
          match Runner.run_node token state x with
          | Ok state_node -> aux state_node acc tail
          | Error err ->
              print_endline (Error.to_string_hum err);
              raise Exit;
              [])
  in
  match get_init_state doc proof.proposition token_reduce with
  | Ok state ->
      let steps = aux state [] (proof_nodes proof) in
      Ok steps
  | _ -> Error.string_to_or_error_err "Unable to retrieve initial state"

let compress_intro (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let rec aux state (acc_intro, acc_steps) nodes =
    match nodes with
    | [] -> acc_steps
    | x :: tail ->
        let state_node = Result.get_ok (Runner.run_node token state x) in
        if
          String.starts_with ~prefix:"intro." x.repr
          && not (String.contains x.repr ';')
        then aux state_node (x :: acc_intro, acc_steps) tail
        else if List.length acc_intro > 0 then
          let steps =
            List.mapi
              (fun i node ->
                if i = 0 then
                  let intros_node =
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string "intros."
                         node.range.start)
                  in
                  Replace (node.id, intros_node)
                else Remove node.id)
              acc_intro
          in
          aux state_node ([], acc_steps @ steps) tail
        else aux state_node ([], acc_steps) tail
  in

  match get_init_state doc proof.proposition token with
  | Ok state ->
      let steps = aux state ([], []) (proof_nodes proof) in
      Ok steps
  | _ -> Error.string_to_or_error_err "Unable to retrieve initial state"

let fold_add_time_taken (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  match
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        let t1 = Unix.gettimeofday () in
        let new_state_run = Runner.run_node token state node in
        let t2 = Unix.gettimeofday () in
        let time_to_run = t2 -. t1 in
        let new_state = Result.get_ok new_state_run in
        if time_to_run > 0.0 then
          let comment_content =
            "Time spent on this step: " ^ string_of_float time_to_run
          in

          let nodes_on_same_line =
            List.filter
              (fun x -> x != node && x.range.start.line = node.range.start.line)
              (proof_nodes proof)
          in
          let furthest_char_node =
            List.fold_left
              (fun max_char_node elem ->
                if
                  elem.range.start.character
                  > max_char_node.range.start.character
                then elem
                else max_char_node)
              node nodes_on_same_line
          in

          let comment_start_point =
            shift_point 0 5 furthest_char_node.range.end_
          in
          match
            Syntax_node.comment_syntax_node_of_string comment_content
              comment_start_point
          with
          | Ok comment_node -> Ok (new_state, Add comment_node :: acc)
          | Error err -> Error err
        else Ok (new_state, acc))
      [] proof
  with
  | Ok acc -> Ok acc
  | Error err -> Error err

(* TODO move this somewhere sensible *)

let print_parents (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    unit =
  Hashtbl.iter
    (fun (k_idx, k_tactic) (v_idx, v_tactic) ->
      Printf.printf
        "Parent: (idx: %d, tactic: %s) -> Child: (idx: %d, tactic: %s)\n" k_idx
        k_tactic.repr v_idx v_tactic.repr)
    parents

let replace_auto_with_steps (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let ( let* ) = Result.bind in
  let re =
    Re.Perl.compile_pat "auto(.*?)\\."
      ~opts:[ Re.Perl.(`Multiline); Re.Perl.(`Dotall); Re.Perl.(`Ungreedy) ]
  in

  let re_in_remove = Str.regexp " (in.*)\\." in

  let extract text =
    match Re.exec_opt re text with
    | Some group -> Re.Group.get group 1
    | None -> "No match"
  in

  let count_leading_spaces s =
    let re = Str.regexp "^ *" in
    if Str.string_match re s 0 then String.length (Str.matched_string s) else 0
  in

  let rec pop_until_split stack =
    match stack with
    | [] -> []
    | (_, _, _, num_children, _, _) :: tail ->
        if num_children <= 1 then pop_until_split tail else stack
  in

  let rec pop_until_prev_depth stack target_depth =
    match stack with
    | [] -> []
    | (_, _, depth, _, _, reduced_goals) :: tail ->
        if depth >= target_depth && not reduced_goals then
          pop_until_prev_depth tail target_depth
        else stack
  in

  let res =
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        if Option.is_empty node.ast then Ok (state, acc)
        else
          let* new_state = Runner.run_node token state node in

          if
            String.starts_with ~prefix:"auto" node.repr
            && not (String.contains node.repr ';')
          then (
            let node_args = extract node.repr in

            let info_auto = "info_auto" ^ node_args ^ "." in
            let* info_auto_node =
              Syntax_node.syntax_node_of_string info_auto node.range.start
            in

            let* _, diagnostics =
              Runner.run_node_with_diagnostics token state info_auto_node
              |> Result.map_error fst
            in

            let tactic_diagnostic_repr =
              Pp.string_of_ppcmds (List.nth diagnostics 1).message
            in

            let auto_tactics =
              String.split_on_char '\n' tactic_diagnostic_repr
            in
            let intros =
              List_utils.take_while (fun tac -> tac = "intro.") auto_tactics
            in
            let intros_nodes =
              List.map
                (fun repr ->
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string repr node.range.start))
                intros
            in

            let after_intros =
              List_utils.drop_while (fun tac -> tac = "intro.") auto_tactics
            in
            let rest_cleaned =
              List.map
                (fun repr -> Str.global_replace re_in_remove "." repr)
                after_intros
            in

            let depth_tuples =
              List.map (fun tac -> (count_leading_spaces tac, tac)) rest_cleaned
            in

            let depth_tuples_nodes_rev =
              List.rev_map
                (fun (depth, tac) ->
                  ( depth,
                    Result.get_ok
                      (Syntax_node.syntax_node_of_string tac node.range.start)
                  ))
                depth_tuples
            in

            let depth_tuple_nodes_rev_indexed =
              List.mapi
                (fun i (depth, node) -> (depth, node, i))
                depth_tuples_nodes_rev
            in

            let* default_node =
              Syntax_node.syntax_node_of_string "idtac." node.range.start
            in

            let default_node_tuple =
              (-1, default_node, List.length depth_tuples_nodes_rev)
            in

            let parents = Hashtbl.create (List.length depth_tuples_nodes_rev) in

            List.iteri
              (fun i (current_depth, current_node) ->
                let next_nodes =
                  List_utils.drop i depth_tuple_nodes_rev_indexed
                in

                let prev_node_tuple =
                  Option.default default_node_tuple
                    (List.find_opt
                       (fun (depth, _, _) -> depth < current_depth)
                       next_nodes)
                in
                let prev_node_depth, prev_node, prev_node_index =
                  prev_node_tuple
                in

                if current_depth > prev_node_depth then
                  Hashtbl.add parents
                    (prev_node_index, prev_node)
                    (i, current_node))
              depth_tuples_nodes_rev;

            let tree =
              Runner.proof_tree_from_parents
                (List.length depth_tuples_nodes_rev, default_node)
                parents
            in

            let tree_with_depths =
              Nary_tree.mapi
                (fun i node ->
                  let matching_tuple =
                    List.nth ((-1, "idtac") :: depth_tuples) i
                  in
                  (node, fst matching_tuple + 1))
                tree
            in
            let* before_state =
              List.fold_left
                (fun state_acc node ->
                  let* state_acc = state_acc in
                  match Runner.run_node token state_acc node with
                  | Ok new_state -> Ok new_state
                  | Error err -> Error err)
                (Ok state) intros_nodes
            in

            let auto_steps =
              Nary_tree.depth_first_fold_with_children
                (fun steps_stack (node, depth) children ->
                  let _, _, prev_depth, _, _, _ = List.hd steps_stack in
                  let steps_stack =
                    if prev_depth >= depth then
                      pop_until_prev_depth steps_stack depth
                    else steps_stack
                  in
                  let ( prev_node,
                        prev_state,
                        prev_depth,
                        prev_num_children,
                        prev_goal_count,
                        prev_reduced_goals ) =
                    List.hd steps_stack
                  in

                  let number_children = List.length children in
                  let cur_state =
                    Result.get_ok (Runner.run_node token prev_state node)
                  in

                  let goal_count = Runner.count_goals token cur_state in
                  if number_children = 0 then
                    if goal_count < prev_goal_count then
                      (node, cur_state, depth, number_children, goal_count, true)
                      :: steps_stack
                    else pop_until_split steps_stack
                  else
                    (node, cur_state, depth, number_children, goal_count, false)
                    :: steps_stack)
                [ (default_node, before_state, -1, 0, 0, false) ]
                tree_with_depths
            in

            let tactics =
              intros
              @ List.rev_map
                  (fun (node, _, _, _, _, _) -> String.trim node.repr)
                  auto_steps
            in
            let filtered_tactics =
              List.filter (fun repr -> repr != "idtac.") tactics
            in

            let tactic_nodes =
              List.mapi
                (fun i repr ->
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string repr
                       (shift_point i 0 node.range.start)))
                filtered_tactics
            in
            let shifted_nodes =
              snd
                (List.fold_left_map
                   (fun acc node ->
                     let char_shift =
                       if acc != 0 then node.range.start.character else 0
                     in
                     (acc + char_shift + String.length node.repr + 1, node))
                   0 tactic_nodes)
            in

            let add_steps = List.map (fun node -> Add node) shifted_nodes in

            Ok (new_state, add_steps @ (Remove node.id :: acc)))
          else Ok (new_state, acc))
      [] proof
  in
  res

let chop_dot (x : string) : (string, Error.t) result =
  let len = String.length x in
  if len = 0 then
    Error (Error.tag (Error.of_string "chop_dot: empty string") ~tag:"chop_dot")
  else if x.[len - 1] <> '.' then
    Error
      (Error.tag_arg
         (Error.of_string "chop_dot: expected string ending with '.'")
         "string" x [%sexp_of: string])
  else Ok (String.sub x 0 (len - 1))

let secure_node (x : syntaxNode) : (syntaxNode, Error.t) result =
  let re =
    Re.(
      seq
        [
          str "by";
          rep1 (char ' ');
          group (compl [ set ".;" ] |> rep1);
          (* group 1: content *)
          group (set ".;");
          (* group 2: final punctuation *)
        ])
    |> Re.compile
  in
  let new_repr =
    Re.replace ~all:true re
      ~f:(fun g ->
        let content = Re.Group.get g 1 |> String.trim in
        let ending = Re.Group.get g 2 in
        if
          String.length content > 0
          && content.[0] = '('
          && content.[String.length content - 1] = ')'
        then "by " ^ content ^ ending
        else "by (" ^ content ^ ")" ^ ending)
      x.repr
  in

  Syntax_node.syntax_node_of_string new_repr x.range.start

let turn_into_oneliner (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in

  let proof = Runner.tree_to_proof proof_tree in

  let proof_status : Proof.proof_status option = Proof.get_proof_status proof in

  match proof_status with
  | Some Proof.Aborted | Some Proof.Admitted -> Ok []
  | Some Proof.Proved -> (
      let cleaned_tree =
        Nary_tree.filter
          (fun node ->
            (not (is_syntax_node_command_allowed_in_proof node))
            && ((not (node_can_open_proof node))
               && not (node_can_close_proof node))
            && Option.has_some node.ast)
          proof_tree
      in

      match cleaned_tree with
      | None -> Ok []
      | Some cleaned_tree ->
          let rec get_oneliner (tree : syntaxNode nary_tree) :
              (string, Error.t) result =
            match tree with
            | Node (x, childrens) ->
                let* safe_x = secure_node x in
                let* x_without_dot = chop_dot safe_x.repr in

                let last_children_opt =
                  if List.length childrens > 0 then
                    List.nth_opt childrens (List.length childrens - 1)
                  else None
                in

                let childrens_length_without_proof_end =
                  match last_children_opt with
                  | Some (Node (last_children, _)) ->
                      if is_syntax_node_proof_end last_children then
                        List.length childrens - 1
                      else List.length childrens
                  | None -> 0
                in

                (* Helper: map childrens with error propagation *)
                let map_children f lst =
                  let rec aux acc = function
                    | [] -> Ok (List.rev acc)
                    | x :: xs ->
                        let* v = f x in
                        aux (v :: acc) xs
                  in
                  aux [] lst
                in

                if is_syntax_node_proof_intro_or_end safe_x then
                  let* mapped = map_children get_oneliner childrens in
                  Ok (String.concat " " mapped)
                else if childrens_length_without_proof_end > 1 then
                  let* mapped = map_children get_oneliner childrens in
                  Ok (x_without_dot ^ ";\n[" ^ String.concat "\n| " mapped ^ "]")
                else if childrens_length_without_proof_end = 1 then
                  let* mapped = map_children get_oneliner childrens in
                  Ok (x_without_dot ^ ";\n" ^ String.concat " " mapped)
                else Ok x_without_dot
          in

          let* one_liner_repr = get_oneliner cleaned_tree in
          let one_liner_repr = one_liner_repr ^ "." in
          print_endline ("oneliner repr " ^ one_liner_repr);

          let flattened = Nary_tree.flatten proof_tree in
          let remove_steps =
            List.filter_map
              (fun node ->
                if node_can_open_proof node || node_can_close_proof node then
                  None
                else Some (Remove node.id))
              flattened
          in

          let first_step_node =
            List.find (fun node -> node_can_open_proof node) flattened
          in

          let* oneliner_node =
            Syntax_node.syntax_node_of_string one_liner_repr
              first_step_node.range.start
          in

          let* proof_node =
            Syntax_node.syntax_node_of_string "Proof."
              first_step_node.range.end_
          in

          Ok
            (remove_steps
            @ [
                Attach (proof_node, LineAfter, first_step_node.id);
                Attach (oneliner_node, LineAfter, proof_node.id);
              ]))
  | None ->
      Error.string_to_or_error_err
        "Can't find the proof status of the proof: invalid proof"

let make_intros_explicit (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, Error.t) result =
  let token = Coq.Limits.Token.create () in
  let ( let* ) = Result.bind in

  Runner.fold_proof_with_state doc token
    (fun state acc node ->
      let* new_state = Runner.run_node token state node in
      if
        String.starts_with ~prefix:"intros." node.repr
        && not (String.contains node.repr ';')
      then
        let* old_state_vars =
          Result.map Runner.get_hypothesis_names
            (Runner.get_current_goal token state)
        in
        let* new_state_vars =
          Result.map Runner.get_hypothesis_names
            (Runner.get_current_goal token new_state)
        in
        let new_vars =
          List.filter (fun x -> not (List.mem x old_state_vars)) new_state_vars
        in
        let explicit_intro = "intros " ^ String.concat " " new_vars ^ "." in
        let* explicit_intro_node =
          Syntax_node.syntax_node_of_string explicit_intro node.range.start
        in
        let r = Replace (node.id, explicit_intro_node) in
        Ok (new_state, r :: acc)
      else Ok (new_state, acc))
    [] proof

let apply_proof_transformation
    (transformation :
      Coq_document.t ->
      Proof.proof ->
      (transformation_step list, Error.t) result) (doc : Coq_document.t) :
    (Coq_document.t, Error.t) result =
  let proofs_rec = Coq_document.get_proofs doc in
  match proofs_rec with
  | Ok proofs ->
      List.fold_left
        (fun (doc_acc : (Coq_document.t, Error.t) result) (proof : Proof.proof)
           ->
          match doc_acc with
          | Ok acc -> (
              let transformation_steps = transformation acc proof in
              match transformation_steps with
              | Ok steps ->
                  List.fold_left
                    (fun doc_acc_err step ->
                      match doc_acc_err with
                      | Ok doc ->
                          Coq_document.apply_transformation_step step doc
                      | Error err -> Error err)
                    doc_acc steps
              | Error err -> Error err)
          | Error err -> Error err)
        (Ok doc) proofs
  | Error err -> Error err

let apply_proof_tree_transformation
    (transformation :
      Coq_document.t ->
      syntaxNode nary_tree ->
      (transformation_step list, Error.t) result) (doc : Coq_document.t) :
    (Coq_document.t, Error.t) result =
  let proofs_rec = Coq_document.get_proofs doc in
  match proofs_rec with
  | Ok proofs ->
      let proof_trees =
        List.filter_map
          (fun proof -> Result.to_option (Runner.treeify_proof doc proof))
          proofs
      in
      List.fold_left
        (fun (doc_acc : (Coq_document.t, Error.t) result)
             (proof_tree : syntaxNode nary_tree) ->
          match doc_acc with
          | Ok acc -> (
              let transformation_steps = transformation acc proof_tree in
              match transformation_steps with
              | Ok steps ->
                  List.fold_left
                    (fun doc_acc_err step ->
                      match doc_acc_err with
                      | Ok doc ->
                          Coq_document.apply_transformation_step step doc
                      | Error err -> Error err)
                    doc_acc steps
              | Error err -> Error err)
          | Error err -> Error err)
        (Ok doc) proof_trees
  | Error err -> Error err
