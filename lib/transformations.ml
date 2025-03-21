open Fleche
open Proof_tree
open Proof
open Syntax_node
open Vernacexpr
open Runner

let error_location_to_string (location : Lang.Range.t) : string =
  if location.start.line = location.end_.line then
    "line "
    ^ string_of_int location.start.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character
  else
    "line "
    ^ string_of_int location.start.line
    ^ "-"
    ^ string_of_int location.end_.line
    ^ ", characters: "
    ^ string_of_int location.start.character
    ^ "-"
    ^ string_of_int location.end_.character

let depth_to_bullet_type (depth : int) =
  let bullet_number = 1 + (depth / 3) in
  match depth mod 3 with
  | 0 -> VernacBullet (Proof_bullet.Dash bullet_number)
  | 1 -> VernacBullet (Proof_bullet.Plus bullet_number)
  | 2 -> VernacBullet (Proof_bullet.Star bullet_number)
  | _ -> VernacBullet (Proof_bullet.Dash bullet_number)

let create_annotated_ast_bullet (depth : int) (range : Lang.Range.t) :
    syntaxNode =
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
  syntax_node_of_coq_ast ast_node range

let add_bullets (proof_tree : syntaxNode nary_tree) : Proof.proof =
  let rec aux (depth : int) (node : syntaxNode nary_tree) =
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
  { proposition = List.hd res; proof_steps = List.tl res; status = Proved }

let replace_by_lia (doc : Coq_document.t) (proof_tree : syntaxNode nary_tree) :
    (Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let proof = Runner.tree_to_proof proof_tree in
  let init_state = Runner.get_init_state doc proof.proposition token in
  let rec aux (st : Coq.State.t) (previous_goals : int)
      (node : syntaxNode nary_tree) : syntaxNode list =
    match node with
    | Node (x, childrens) -> (
        let lia_node =
          Result.get_ok (Syntax_node.syntax_node_of_string "lia." x.range)
        in
        let state_x = Result.get_ok (Runner.run_node token st x) in
        let new_goals = Runner.count_goals token state_x in
        let state_lia = Runner.run_node token st lia_node in
        match state_lia with
        | Ok state_uw ->
            let goals_with_lia = count_goals token state_uw in
            if goals_with_lia < previous_goals then
              if goals_with_lia = 0 then
                [ lia_node; qed_ast_node (shift_range 1 0 0 lia_node.range) ]
              else [ lia_node ]
            else x :: List.concat (List.map (aux state_x new_goals) childrens)
        | Error err ->
            x :: List.concat (List.map (aux state_x new_goals) childrens))
  in
  match init_state with
  | Ok state ->
      let head_tree = top_n 1 proof_tree in
      let tail_tree = List.hd (bottom_n 2 proof_tree) in
      let list = aux state 1 tail_tree in
      let list_head_tail = flatten head_tree @ list in
      Proof.proof_from_nodes list_head_tail
  | _ -> Error "can't create an initial state for the proof "

let fold_replace_by_lia (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) : (Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let previous_goals, steps_acc, ignore_step = acc in
        if ignore_step then (state, (previous_goals, steps_acc, ignore_step))
        else
          let state_node = Result.get_ok (Runner.run_node token state node) in
          let lia_node =
            Result.get_ok (Syntax_node.syntax_node_of_string "lia." node.range)
          in
          let new_goals = count_goals token state in
          let state_lia = Runner.run_node token state lia_node in
          match state_lia with
          | Ok state_uw ->
              let goals_with_lia = count_goals token state_uw in
              if goals_with_lia < previous_goals then
                if goals_with_lia = 0 then
                  ( state_uw,
                    ( goals_with_lia,
                      [
                        lia_node;
                        qed_ast_node (shift_range 1 0 0 lia_node.range);
                      ]
                      @ steps_acc,
                      true ) )
                else (state_uw, (new_goals, node :: steps_acc, true))
              else (state_node, (new_goals, node :: steps_acc, ignore_step))
          | Error err ->
              let res =
                (state_node, (new_goals, node :: steps_acc, ignore_step))
              in
              res)
      (1, [], false) proof_tree
  in
  match res with
  | Ok (goals, steps, _) -> Proof.proof_from_nodes (List.rev steps)
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

let fold_inspect (doc : Coq_document.t) (proof_tree : syntaxNode nary_tree) =
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
            (state_node, node :: acc)
        | _ ->
            print_endline "error getting goals";
            (state_node, node :: acc))
      [] proof_tree
  in
  ()

let fold_replace_assumption_with_apply (doc : Coq_document.t)
    (proof_tree : syntaxNode nary_tree) :
    (transformation_step list, string) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let state_node = Result.get_ok (Runner.run_node token state node) in
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
                      (Syntax_node.syntax_node_of_string repr node.range))
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

              (state_node, Replace (node.id, new_node) :: acc)
          | Error _ -> (state_node, acc)
        else (state_node, acc))
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
              let shifted = shift_node shift_value 0 0 node in
              (node, shifted :: acc_nodes, shift_value))
          (first_node, [], 0) nodes
      in
      let _, res_func, _ = res in
      Result.get_ok (proof_from_nodes (List.rev res_func))
  | None -> proof

let remove_unecessary_steps (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, string) result =
  let token = Coq.Limits.Token.create () in
  let rec aux state acc nodes =
    match nodes with
    | [] -> acc
    | x :: tail ->
        if is_doc_node_proof_intro_or_end x then aux state acc tail
        else if Runner.can_reduce_to_zero_goals state tail then
          aux state (Remove x.id :: acc) tail
        else
          let state_node = Result.get_ok (Runner.run_node token state x) in
          aux state_node acc tail
  in
  match get_init_state doc proof.proposition token with
  | Ok state ->
      let steps = aux state [] (proof_nodes proof) in
      Ok steps
  | _ -> Error "Unable to retrieve initial state"

let fold_add_time_taken (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, string) result =
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
          let comment_repr =
            "(* Time spent on this step: " ^ string_of_float time_to_run ^ " *)"
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
          let comment_node_res =
            Syntax_node.comment_syntax_node_of_string comment_content
              (Range_transformation.range_from_starting_point_and_repr
                 (shift_node 0 5 0 furthest_char_node).range.end_ comment_repr)
          in
          match comment_node_res with
          | Ok comment_node -> (new_state, Add comment_node :: acc)
          | Error _ -> (new_state, acc)
        else (new_state, acc))
      [] proof
  with
  | Ok acc -> Ok acc
  | Error err -> Error err

(* TODO move this somewhere sensible *)

let take n l =
  let[@tail_mod_cons] rec aux n l =
    match (n, l) with 0, _ | _, [] -> [] | n, x :: l -> x :: aux (n - 1) l
  in
  if n < 0 then invalid_arg "List.take";
  aux n l

let drop n l =
  let rec aux i = function
    | _x :: l when i < n -> aux (i + 1) l
    | rest -> rest
  in
  if n < 0 then invalid_arg "List.drop";
  aux 0 l

let take_while p l =
  let[@tail_mod_cons] rec aux = function
    | x :: l when p x -> x :: aux l
    | _rest -> []
  in
  aux l

let rec drop_while p = function
  | x :: l when p x -> drop_while p l
  | rest -> rest

let print_parents (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    unit =
  Hashtbl.iter
    (fun (k_idx, k_tactic) (v_idx, v_tactic) ->
      Printf.printf
        "Parent: (idx: %d, tactic: %s) -> Child: (idx: %d, tactic: %s)\n" k_idx
        k_tactic.repr v_idx v_tactic.repr)
    parents

let replace_auto_with_info_auto (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, string) result =
  let token = Coq.Limits.Token.create () in
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
  (* (node, cur_state, depth, number_children, goal_count) *)
  let print_stack =
    List.iter
      (fun (node, state, depth, num_children, goal_count, reduced_goals) ->
        print_endline
          ("stack node: " ^ node.repr ^ " depth: " ^ string_of_int depth
         ^ " n_children: " ^ string_of_int num_children ^ " goal_count: "
         ^ string_of_int goal_count ^ " reduced goals: "
          ^ string_of_bool reduced_goals))
  in

  (*

                let _, auto_steps =
              Proof_tree.depth_first_fold
                (fun (state_acc, steps_stack) (node, depth) ->
                  print_endline ("running " ^ node.repr);
                  let new_state = Runner.run_node token state_acc node in
                  print_endline "X";
                  match new_state with
                  | Ok state -> (state, (node, state, depth) :: steps_stack)
                  | Error err ->
                      let new_stack = pop_until_same_depth steps_stack depth in

                      let top_node, state, new_depth = List.hd new_stack in
                      print_endline ("popping til " ^ top_node.repr);
                      print_stack new_stack;
                      let new_state =
                        Result.get_ok (Runner.run_node token state node)
                      in

                      (new_state, (node, new_state, depth) :: new_stack))
                (before_state, []) tree_with_depths
                in

   *)
  match
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        if Option.is_empty node.ast then (state, acc)
        else
          let _ = 0 in
          print_endline ("treating : " ^ node.repr);
          let new_state = Result.get_ok (Runner.run_node token state node) in
          print_endline "new state";
          Result.map pp_goal (Runner.get_current_goal token new_state);
          print_newline ();
          if
            String.starts_with ~prefix:"auto" node.repr
            && not (String.contains node.repr ';')
          then (
            let node_args = extract node.repr in

            let info_auto = "info_auto" ^ node_args ^ "." in
            let info_auto_node =
              Result.get_ok
                (Syntax_node.syntax_node_of_string info_auto
                   (Range_transformation.range_from_starting_point_and_repr
                      node.range.start info_auto))
            in
            print_endline "here";
            let info_auto_state =
              Result.get_ok
                (Runner.run_node_with_diagnostics token state info_auto_node)
            in
            print_endline "there";
            let _, diagnostics = info_auto_state in

            let tactic_diagnostic_repr =
              Pp.string_of_ppcmds (List.nth diagnostics 1).message
            in

            let auto_tactics =
              String.split_on_char '\n' tactic_diagnostic_repr
            in
            print_endline "A";
            let intros = take_while (fun tac -> tac = "intro.") auto_tactics in
            let intros_nodes =
              List.map
                (fun repr ->
                  Result.get_ok
                    (Syntax_node.syntax_node_of_string repr
                       (Range_transformation.range_from_starting_point_and_repr
                          node.range.start repr)))
                intros
            in
            print_endline "B";
            let after_intros =
              drop_while (fun tac -> tac = "intro.") auto_tactics
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
                      (Syntax_node.syntax_node_of_string tac
                         (Range_transformation
                          .range_from_starting_point_and_repr node.range.start
                            tac)) ))
                depth_tuples
            in
            print_endline "C";
            let depth_tuple_nodes_rev_indexed =
              List.mapi
                (fun i (depth, node) -> (depth, node, i))
                depth_tuples_nodes_rev
            in

            let parents = Hashtbl.create (List.length depth_tuples_nodes_rev) in
            let default_node_depth = -1 in
            let default_node =
              Result.get_ok
                (Syntax_node.syntax_node_of_string "idtac."
                   (Range_transformation.range_from_starting_point_and_repr
                      node.range.start "idtac."))
            in
            print_endline "D";
            let default_node_tuple =
              ( default_node_depth,
                default_node,
                List.length depth_tuples_nodes_rev )
            in

            List.iteri
              (fun i (current_depth, current_node) ->
                let next_nodes = drop i depth_tuple_nodes_rev_indexed in

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
            print_endline "E";

            let tree_with_depths =
              Proof_tree.mapi
                (fun i node ->
                  let matching_tuple =
                    List.nth ((-1, "idtac") :: depth_tuples) i
                  in
                  (node, fst matching_tuple + 1))
                tree
            in
            let before_state =
              List.fold_left
                (fun state_acc node ->
                  match Runner.run_node token state_acc node with
                  | Ok new_state -> new_state
                  | Error err ->
                      print_endline (Runner.running_error_to_string err);
                      state_acc)
                state intros_nodes
            in

            print_endline "D";

            let auto_steps =
              Proof_tree.depth_first_fold_with_children
                (fun steps_stack (node, depth) children ->
                  let ( prev_node,
                        prev_state,
                        prev_depth,
                        prev_num_children,
                        prev_goal_count,
                        prev_reduced_goals ) =
                    List.hd steps_stack
                  in
                  let steps_stack =
                    if prev_depth >= depth then (
                      print_stack steps_stack;
                      let s = pop_until_prev_depth steps_stack depth in
                      let s_node, s_state, s_depth, _, _, _ = List.hd s in
                      print_endline "popping previous useless instructions";
                      print_endline ("using state from " ^ s_node.repr);
                      print_endline ("depth : " ^ string_of_int s_depth);
                      s)
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
                  print_endline "";
                  print_endline ("running node : " ^ node.repr);
                  print_endline ("depth : " ^ string_of_int depth);
                  print_endline "current stack : ";
                  print_stack steps_stack;
                  print_endline
                    ("prev goal count " ^ string_of_int prev_goal_count);
                  print_endline
                    ("prev node : " ^ prev_node.repr ^ " depth: "
                   ^ string_of_int prev_depth);

                  let number_children = List.length children in
                  let cur_state =
                    Result.get_ok (Runner.run_node token prev_state node)
                  in
                  print_endline "got the cur state";
                  let goal_count = Runner.count_goals token cur_state in
                  if number_children = 0 then
                    if goal_count < prev_goal_count then (
                      print_endline "closed a goal";
                      (node, cur_state, depth, number_children, goal_count, true)
                      :: steps_stack)
                    else (
                      print_stack steps_stack;
                      let s = pop_until_split steps_stack in
                      let s_node, s_state, s_depth, _, _, _ = List.hd s in
                      print_endline "useless branch";
                      print_endline ("using state from " ^ s_node.repr);
                      print_endline ("depth : " ^ string_of_int s_depth);
                      pop_until_split steps_stack)
                  else
                    (node, cur_state, depth, number_children, goal_count, false)
                    :: steps_stack)
                [ (default_node, before_state, -1, 0, 0, false) ]
                tree_with_depths
            in

            print_endline "F";

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
                       (shift_range i 0 0
                          (Range_transformation
                           .range_from_starting_point_and_repr node.range.start
                             repr))))
                filtered_tactics
            in
            let shifted_nodes =
              snd
                (List.fold_left_map
                   (fun acc node ->
                     let char_shift =
                       if acc != 0 then node.range.start.character else 0
                     in
                     ( acc + char_shift + String.length node.repr + 1,
                       (shift_node 0 0 (acc + char_shift)) node ))
                   0 tactic_nodes)
            in

            let add_steps = List.map (fun node -> Add node) shifted_nodes in

            (new_state, add_steps @ (Remove node.id :: acc)))
          else (new_state, acc))
      [] proof
  with
  | Ok steps -> Ok steps
  | Error err -> Error err

let make_intros_explicit (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, string) result =
  let token = Coq.Limits.Token.create () in
  match
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        let new_state = Result.get_ok (Runner.run_node token state node) in
        if
          String.starts_with ~prefix:"intros" node.repr
          && not (String.contains node.repr ';')
        then
          let old_state_vars =
            Runner.get_current_goal token state
            |> Result.get_ok |> Runner.get_hypothesis_names
          in
          let new_state_vars =
            Runner.get_current_goal token new_state
            |> Result.get_ok |> Runner.get_hypothesis_names
          in
          let new_vars =
            List.filter
              (fun x -> not (List.mem x old_state_vars))
              new_state_vars
          in
          let explicit_intro = "intros " ^ String.concat " " new_vars ^ "." in
          let explicit_intro_node =
            Result.get_ok
              (Syntax_node.syntax_node_of_string explicit_intro
                 (Range_transformation.range_from_starting_point_and_repr
                    node.range.start explicit_intro))
          in
          let r = Replace (node.id, explicit_intro_node) in
          (new_state, r :: acc)
        else (new_state, acc))
      [] proof
  with
  | Ok steps -> Ok steps
  | Error err -> Error err

let apply_proof_transformation
    (transformation :
      Coq_document.t -> Proof.proof -> (transformation_step list, string) result)
    (doc : Coq_document.t) (proof : Proof.proof) :
    (Coq_document.t, string) result =
  let proofs = Coq_document.get_proofs doc in
  List.fold_left
    (fun (doc_acc : (Coq_document.t, string) result) (proof : Proof.proof) ->
      match doc_acc with
      | Ok acc -> (
          let transformation_steps = transformation acc proof in
          match transformation_steps with
          | Ok steps ->
              List.fold_left
                (fun doc_acc_err step ->
                  match doc_acc_err with
                  | Ok doc -> Coq_document.apply_transformation_step step doc
                  | Error err -> Error err)
                doc_acc steps
          | Error err -> Error err)
      | Error err -> Error err)
    (Ok doc) proofs
