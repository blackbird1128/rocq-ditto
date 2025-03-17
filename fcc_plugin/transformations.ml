open Fleche
open Ditto
open Ditto.Proof_tree
open Ditto.Proof
open Ditto.Syntax_node
open Vernacexpr
open Runner

let error_location_to_string (location : Lang.Range.t) =
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

let add_bullets (proof_tree : syntaxNode nary_tree) : Ditto.Proof.proof =
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
    (Ditto.Proof.proof, string) result =
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
    (proof_tree : syntaxNode nary_tree) : (Ditto.Proof.proof, string) result =
  let token = Coq.Limits.Token.create () in
  let res =
    Runner.depth_first_fold_with_state doc token
      (fun state acc node ->
        let previous_goals, steps_acc, ignore_step = acc in
        if ignore_step then (state, (previous_goals, steps_acc, ignore_step))
        else if Syntax_node.is_doc_node_proof_intro_or_end node then
          (state, (previous_goals, node :: steps_acc, ignore_step))
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
        if Syntax_node.is_doc_node_proof_intro_or_end node then
          (state, node :: acc)
        else
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
        if Syntax_node.is_doc_node_proof_intro_or_end node then (state, acc)
        else
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
        if is_doc_node_proof_intro_or_end node then (state, acc)
        else
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
              "(* Time spent on this step: "
              ^ string_of_float time_to_run
              ^ " *)"
            in
            let nodes_on_same_line =
              List.filter
                (fun x ->
                  x != node && x.range.start.line = node.range.start.line)
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
let take_while p l =
  let[@tail_mod_cons] rec aux = function
    | x :: l when p x -> x :: aux l
    | _rest -> []
  in
  aux l

let rec drop_while p = function
  | x :: l when p x -> drop_while p l
  | rest -> rest

let replace_auto_with_info_auto (doc : Coq_document.t) (proof : proof) :
    (transformation_step list, string) result =
  let token = Coq.Limits.Token.create () in
  let re =
    Re.Perl.compile_pat "auto(.*?)\\."
      ~opts:[ Re.Perl.(`Multiline); Re.Perl.(`Dotall); Re.Perl.(`Ungreedy) ]
  in

  let re_in_remove = Str.regexp "(in.*)" in

  let extract text =
    match Re.exec_opt re text with
    | Some group -> Re.Group.get group 1
    | None -> "No match"
  in

  let count_leading_spaces s =
    let re = Str.regexp "^ *" in
    if Str.string_match re s 0 then String.length (Str.matched_string s) else 0
  in

  let find_last_opt (f : 'a -> bool) (l : 'a list) : 'a option =
    let rec aux (f : 'a -> bool) (l : 'a list) (acc : 'a option) =
      match l with
      | [] -> acc
      | x :: tail -> if f x then aux f tail (Some x) else aux f tail acc
    in
    aux f l None
  in

  match
    Runner.fold_proof_with_state doc token
      (fun state acc node ->
        if is_doc_node_proof_intro_or_end node then (state, acc)
        else
          let new_state = Result.get_ok (Runner.run_node token state node) in
          print_endline ("running node: " ^ node.repr);
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
            let info_auto_state =
              Result.get_ok
                (Runner.run_node_with_diagnostics token state info_auto_node)
            in
            let state, diagnostics = info_auto_state in
            print_endline
              ("number of diagnostics : "
              ^ string_of_int (List.length diagnostics));
            let tactic_diagnostic = List.nth diagnostics 1 in
            let tactic_diagnostic_repr =
              Pp.string_of_ppcmds tactic_diagnostic.message
            in
            let auto_tactics =
              String.split_on_char '\n' tactic_diagnostic_repr
            in
            let intros = take_while (fun tac -> tac = "intro.") auto_tactics in
            let rest = drop_while (fun tac -> tac = "intro.") auto_tactics in

            let depth_tuples =
              List.map (fun tac -> (count_leading_spaces tac, tac)) rest
            in
            List.iter
              (fun (depth, tac) -> Format.printf "(%d,%s)\n" depth tac)
              depth_tuples;
            let max_depth =
              List.fold_left
                (fun acc_max (depth, _) -> max acc_max depth)
                (Option.default 0
                   (Option.map fst (List.nth_opt depth_tuples 0)))
                depth_tuples
            in
            let rec loop i acc =
              if i > max_depth then acc
              else
                loop (i + 1)
                  (Option.get
                     (find_last_opt (fun (depth, _) -> depth = i) depth_tuples)
                  :: acc)
            in
            let tactics_tuple = loop 0 [] in
            let tactics =
              intros
              @ List.rev_map (fun (depth, tac) -> String.trim tac) tactics_tuple
            in
            let tactic_nodes =
              List.mapi
                (fun i repr ->
                  print_endline ("i : " ^ string_of_int i);
                  print_endline repr;
                  let cleaned_repr = Str.global_replace re_in_remove "" repr in
                  print_endline ("cleaned repr : " ^ cleaned_repr);
                  let _ =
                    match
                      Syntax_node.syntax_node_of_string cleaned_repr
                        (shift_range i 0 0
                           (Range_transformation
                            .range_from_starting_point_and_repr node.range.start
                              cleaned_repr))
                    with
                    | Ok node -> print_endline node.repr
                    | Error err -> print_endline err
                  in

                  Result.get_ok
                    (Syntax_node.syntax_node_of_string cleaned_repr
                       (shift_range i 0 0
                          (Range_transformation
                           .range_from_starting_point_and_repr node.range.start
                             cleaned_repr))))
                tactics
            in
            let shifted_nodes =
              snd
                (List.fold_left_map
                   (fun acc node ->
                     ( acc + String.length node.repr + 1,
                       (shift_node 0 0 acc) node ))
                   0 tactic_nodes)
            in

            let add_steps = List.map (fun node -> Add node) shifted_nodes in

            List.iter
              (fun node -> pp_syntax_node Format.std_formatter node)
              shifted_nodes;

            List.iter (fun tac -> Format.printf "(%s)\n" tac) tactics;
            Format.printf "max depth: %d\n" max_depth;
            Format.print_flush ();

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
        if is_doc_node_proof_intro_or_end node then (state, acc)
        else
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
