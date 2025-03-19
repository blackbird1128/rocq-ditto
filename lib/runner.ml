open Syntax_node
open Proof_tree
open Proof

type runningError =
  | Interrupted
  | Parsing of string
  | Coq of string
  | Anomaly of string
  | System of string
  | Theorem_not_found of string

let running_error_to_string = function
  | Interrupted -> Format.asprintf "Interrupted"
  | Parsing msg -> Format.asprintf "Parsing: %s" msg
  | Coq msg -> Format.asprintf "Coq: %s" msg
  | Anomaly msg -> Format.asprintf "Anomaly: %s" msg
  | System msg -> Format.asprintf "System: %s" msg
  | Theorem_not_found msg -> Format.asprintf "Theorem_not_found: %s" msg

let protect_to_result (r : ('a, 'b) Coq.Protect.E.t) :
    ('a, runningError) Result.t =
  match r with
  | { r = Interrupted; feedback = _ } -> Error Interrupted
  | { r = Completed (Error (User { msg; _ })); feedback = _ } ->
      Error (Coq (Pp.string_of_ppcmds msg))
  | { r = Completed (Error (Anomaly { msg; _ })); feedback = _ } ->
      Error (Anomaly (Pp.string_of_ppcmds msg))
  | { r = Completed (Ok r); feedback = msgs } -> Ok r

let protect_to_result_with_feedback (r : ('a, 'b) Coq.Protect.E.t) :
    ('a * 'b Coq.Message.t list, runningError * 'b Coq.Message.t list) Result.t
    =
  match r with
  | { r = Interrupted; feedback } -> Error (Interrupted, feedback)
  | { r = Completed (Error (User { msg; _ })); feedback } ->
      Error (Coq (Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Error (Anomaly { msg; _ })); feedback } ->
      Error (Anomaly (Pp.string_of_ppcmds msg), feedback)
  | { r = Completed (Ok r); feedback } -> Ok (r, feedback)

let goals ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) :
    ( (string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option,
      runningError )
    result =
  let f goals =
    let f = Coq.Goals.Reified_goal.map ~f:Pp.string_of_ppcmds in
    let g = Pp.string_of_ppcmds in
    Option.map (Coq.Goals.map ~f ~g) goals
  in

  Coq.Protect.E.map ~f (Fleche.Info.Goals.goals ~token ~st) |> protect_to_result

let message_to_diagnostic (range : Lang.Range.t) (msg : Loc.t Coq.Message.t) :
    Lang.Diagnostic.t =
  let severity, payload = msg in
  { severity; message = payload.msg; data = None; range }

(* Adaptor, should be supported in memo directly *)
let eval_no_memo ~token (st, cmd) =
  Coq.Interp.interp ~token ~intern:Vernacinterp.fs_intern ~st cmd

(* TODO, what to do with feedback, what to do with errors *)
let rec parse_execute_loop ~token ~memo pa ~msg_acc st =
  let open Coq.Protect.E.O in
  let eval = if memo then Fleche.Memo.Interp.eval else eval_no_memo in
  let* ast = Coq.Parsing.parse ~token ~st pa in
  match ast with
  | Some ast -> (
      match eval ~token (st, ast) with
      | Coq.Protect.E.
          { r = Coq.Protect.R.Completed (Ok st); feedback = messages } ->
          parse_execute_loop ~token ~memo pa ~msg_acc:(msg_acc @ messages) st
      | res -> Coq.Protect.E.map ~f:(fun x -> (x, msg_acc)) res)
  (* On EOF we return the previous state, the command was the empty string or a
     comment *)
  | None -> Coq.Protect.E.ok (st, msg_acc)

let parse_and_execute_in ~token ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let pa = Coq.Parsing.Parsable.make ?loc str in
  parse_execute_loop ~token pa st

let run_with_diagnostics ~token ?loc ?(memo = true) ~st cmds =
  Coq.State.in_stateM ~token ~st
    ~f:(parse_and_execute_in ~token ~loc ~memo ~msg_acc:[] cmds)
    st

let run_node (token : Coq.Limits.Token.t) (prev_state : Coq.State.t)
    (node : syntaxNode) : (Coq.State.t, runningError) result =
  let execution =
    let open Coq.Protect.E.O in
    let st =
      Fleche.Doc.run ~token ~memo:true ?loc:None ~st:prev_state node.repr
    in
    st
  in

  protect_to_result execution

let run_node_with_diagnostics (token : Coq.Limits.Token.t)
    (prev_state : Coq.State.t) (node : syntaxNode) :
    ( Coq.State.t * Lang.Diagnostic.t list,
      runningError * Lang.Diagnostic.t list )
    result =
  let execution =
    let open Coq.Protect.E.O in
    let st =
      run_with_diagnostics ~token ~memo:true ?loc:None ~st:prev_state node.repr
    in
    st
  in

  let res = protect_to_result_with_feedback execution in
  match res with
  | Ok x ->
      let state_msgs, messages = x in
      let state = fst state_msgs in
      let all_msgs = snd state_msgs @ messages in
      Ok (state, List.map (message_to_diagnostic node.range) all_msgs)
  | Error err ->
      let err, messages = err in
      Error (err, List.map (message_to_diagnostic node.range) messages)

let get_init_state (doc : Coq_document.t) (node : syntaxNode)
    (token : Coq.Limits.Token.t) : (Coq.State.t, runningError) result =
  let nodes_before, nodes_after = Coq_document.split_at_id node.id doc in
  let init_state = doc.initial_state in
  List.fold_left
    (fun state node ->
      match state with
      | Ok state -> run_node token state node
      | Error err -> Error err)
    (Ok init_state) (nodes_before @ [ node ])

let get_hypothesis_names (goal : string Coq.Goals.Reified_goal.t) : string list
    =
  List.concat_map
    (fun (hyp : string Coq.Goals.Reified_goal.hyp) -> hyp.names)
    goal.hyps

let get_proof_state (start_result : (Coq.State.t, Loc.t) Coq.Protect.E.t) :
    Coq.State.t =
  match protect_to_result start_result with
  | Ok run_result -> run_result
  | Error err ->
      Printf.eprintf "Error: %s\n" (running_error_to_string err);
      raise (Failure "Failed to start proof")

let count_goals (token : Coq.Limits.Token.t) (st : Coq.State.t) : int =
  let goals = goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> List.length reified_goals.goals
  | Ok None -> 0
  | Error _ -> 0

let rec proof_steps_with_goalcount (token : Coq.Limits.Token.t)
    (st : Coq.State.t) (steps : syntaxNode list) : (syntaxNode * int) list =
  match steps with
  | [] -> []
  | step :: tail ->
      let state = Fleche.Doc.run ~token ~st step.repr in
      let agent_state = get_proof_state state in
      let goal_count = count_goals token agent_state in
      (step, goal_count) :: proof_steps_with_goalcount token agent_state tail

let can_reduce_to_zero_goals (init_state : Coq.State.t)
    (nodes : syntaxNode list) =
  let token = Coq.Limits.Token.create () in
  let rec aux state acc nodes =
    match nodes with
    | [] -> Ok acc
    | x :: tail -> (
        if Syntax_node.is_doc_node_proof_intro_or_end x then
          aux state state tail
        else
          let state_node_res = run_node token state x in
          match state_node_res with
          | Ok state_node -> aux state_node state_node tail
          | Error err -> Error "")
  in
  match aux init_state init_state nodes with
  | Ok state -> count_goals token state = 0
  | Error _ -> false

let get_current_goal (token : Coq.Limits.Token.t) (state : Coq.State.t) :
    (string Coq.Goals.Reified_goal.t, string) result =
  let goals_err_opt = goals ~token ~st:state in
  match goals_err_opt with
  | Ok (Some goals) -> (
      match List.nth_opt goals.goals 0 with
      | Some goal -> Ok goal
      | None -> Error "zero goal at this state")
  | Ok None -> Error "zero goal at this state"
  | Error err -> Error (running_error_to_string err)

let print_parents (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    unit =
  Hashtbl.iter
    (fun (k_idx, k_tactic) (v_idx, v_tactic) ->
      Printf.printf
        "Parent: (idx: %d, tactic: %s) -> Child: (idx: %d, tactic: %s)\n" k_idx
        k_tactic.repr v_idx v_tactic.repr)
    parents

type parent_category = Fork | Linear

let rec pop_until_fork (prev_pars : (int * syntaxNode * parent_category) list) :
    (int * syntaxNode * parent_category) list =
  match prev_pars with
  | [] -> []
  | (_, _, cat_par) :: tail_par -> (
      match cat_par with Fork -> prev_pars | Linear -> pop_until_fork tail_par)

let rec get_parents_rec (steps_with_goals : (syntaxNode * int) list)
    (prev_goals : int) (prev_pars : (int * syntaxNode * parent_category) list)
    (idx : int) (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) =
  match steps_with_goals with
  | [] -> parents
  | (step, new_goals) :: tail -> (
      match prev_pars with
      | [] ->
          if new_goals > prev_goals then
            get_parents_rec tail new_goals
              [ (idx, step, Fork) ]
              (idx + 1) parents
          else
            get_parents_rec tail new_goals
              [ (idx, step, Linear) ]
              (idx + 1) parents
      | (idx_par, tactic_par, _) :: _ ->
          let par = (idx_par, tactic_par) in
          if new_goals < prev_goals then (
            Hashtbl.add parents par (idx, step);
            if new_goals > 0 then
              get_parents_rec tail new_goals (pop_until_fork prev_pars)
                (idx + 1) parents
            else
              get_parents_rec tail new_goals
                [ (idx, step, Linear) ]
                (idx + 1) parents)
          else if new_goals = prev_goals then (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail new_goals
              ((idx, step, Linear) :: prev_pars)
              (idx + 1) parents)
          else (
            Hashtbl.add parents par (idx, step);
            get_parents_rec tail new_goals
              ((idx, step, Fork) :: prev_pars)
              (idx + 1) parents))

let rec proof_tree_from_parents (cur_node : int * syntaxNode)
    (parents : (int * syntaxNode, int * syntaxNode) Hashtbl.t) :
    syntaxNode nary_tree =
  let _, tactic = cur_node in

  let childs = Hashtbl.find_all parents cur_node in
  Node
    ( tactic,
      List.rev_map (fun node -> proof_tree_from_parents node parents) childs )

let treeify_proof (doc : Coq_document.t) (p : proof) :
    (syntaxNode nary_tree, string) result =
  let token = Coq.Limits.Token.create () in

  match get_init_state doc p.proposition token with
  | Ok init_state ->
      let steps_with_goals =
        proof_steps_with_goalcount token init_state p.proof_steps
      in

      let parents = Hashtbl.create (List.length steps_with_goals) in
      let _ = get_parents_rec steps_with_goals 1 [] 0 parents in

      Ok
        (Node
           ( p.proposition,
             [ proof_tree_from_parents (0, List.hd p.proof_steps) parents ] ))
  | Error err -> Error "Unable to retrieve initial state"

let rec proof_tree_to_node_list (Node (value, children)) : syntaxNode list =
  value :: List.concat (List.map proof_tree_to_node_list children)

let tree_to_proof (tree : syntaxNode nary_tree) : proof =
  let nodes = proof_tree_to_node_list tree in
  let last_node_status =
    List.hd (List.rev nodes) |> proof_status_from_last_node
  in
  {
    proposition = List.hd nodes;
    proof_steps = List.tl nodes;
    status = Result.get_ok last_node_status;
  }

let previous_steps_from_tree (node : syntaxNode) (tree : syntaxNode nary_tree) =
  let nodes = proof_tree_to_node_list tree in
  let steps = List.tl nodes in
  let rec sublist_before_id lst target_id =
    match lst with
    | [] -> []
    | x :: xs ->
        if x.id = target_id then [] else x :: sublist_before_id xs target_id
  in
  sublist_before_id steps node.id

(* take a full tree and return an acc *)
(* fold over the proof while running the expr each time to get a new state *)
let rec depth_first_fold_with_state (doc : Coq_document.t)
    (token : Coq.Limits.Token.t)
    (f : Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc) (acc : 'acc)
    (tree : syntaxNode nary_tree) : ('acc, string) result =
  let rec aux (f : Coq.State.t -> 'acc -> 'a -> Coq.State.t * 'acc)
      (state : Coq.State.t) (acc : 'acc) (tree : 'a nary_tree) :
      Coq.State.t * 'acc =
    match tree with
    | Node (x, children) ->
        let state, acc = f state acc x in
        (* Fold over the children using the updated state and accumulator *)
        List.fold_left
          (fun (state, acc) child ->
            let new_state, new_acc = aux f state acc child in
            (new_state, new_acc))
          (state, acc) children
    (* Fold over the children, threading the state and updating acc *)
    (* Update state and accumulator for the current node *)
  in

  let proof = tree_to_proof tree in
  match get_init_state doc proof.proposition token with
  | Ok state -> Ok (snd (aux f state acc tree))
  | _ -> Error "Unable to retrieve initial state"

let rec fold_nodes_with_state (doc : Coq_document.t)
    (token : Coq.Limits.Token.t)
    (f : Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc)
    (init_state : Coq.State.t) (acc : 'acc) (l : syntaxNode list) : 'acc =
  let rec aux (l : syntaxNode list) (state : Coq.State.t) (acc : 'acc) =
    match l with
    | [] -> acc
    | x :: tail ->
        let res = f state acc x in
        aux tail (fst res) (snd res)
  in
  aux l init_state acc

let rec fold_proof_with_state (doc : Coq_document.t)
    (token : Coq.Limits.Token.t)
    (f : Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc) (acc : 'acc)
    (p : Proof.proof) : ('acc, string) result =
  let proof_nodes = Proof.proof_nodes p in
  let rec aux (l : syntaxNode list) (state : Coq.State.t) (acc : 'acc) =
    match l with
    | [] -> acc
    | x :: tail ->
        let res = f state acc x in
        aux tail (fst res) (snd res)
  in
  match get_init_state doc p.proposition token with
  | Ok state -> Ok (aux proof_nodes state acc)
  | _ -> Error "Unable to retrieve initial state"
