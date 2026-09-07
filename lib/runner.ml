open Syntax_node
open Proof

let goals ~(token : Coq.Limits.Token.t) ~(st : Coq.State.t) :
    ( (string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option,
      Error.t )
    result =
  let f goals =
    let f = Coq.Goals.Reified_goal.map ~f:Pp.string_of_ppcmds in
    let g = Pp.string_of_ppcmds in
    Option.map (Coq.Goals.map ~f ~g) goals
  in

  Coq.Protect.E.map ~f
    (Fleche.Info.Goals.goals ~pr:Fleche.Info.Goals.to_pp ~token ~st)
  |> Error.protect_to_result

let message_to_diagnostic (range : Code_range.t) (msg : Loc.t Coq.Message.t) :
    Lang.Diagnostic.t =
  (* TODO: remove dummy value use *)
  let lang_start_point : Lang.Point.t =
    { line = range.start.line; character = range.start.character; offset = -1 }
  in
  let lang_end_point : Lang.Point.t =
    { line = range.end_.line; character = range.end_.character; offset = -1 }
  in
  let lang_range : Lang.Range.t =
    { start = lang_start_point; end_ = lang_end_point }
  in
  let severity, payload = msg in
  { severity; message = payload.msg; data = None; range = lang_range }

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
          parse_execute_loop ~token ~memo pa
            ~msg_acc:(List.rev_append messages msg_acc)
            st
      | res -> Coq.Protect.E.map ~f:(fun x -> (x, List.rev msg_acc)) res)
  | None -> Coq.Protect.E.ok (st, List.rev msg_acc)

let parse_and_execute_in ~token ~loc tac st =
  let str = Gramlib.Stream.of_string tac in
  let pa = Coq.Parsing.Parsable.make ?loc str in
  parse_execute_loop ~token pa st

let run_with_diagnostics ~(token : Coq.Limits.Token.t) ?(loc : Loc.t option)
    ?(memo = true) ~(st : Coq.State.t) (cmds : string) :
    (Coq.State.t * Loc.t Coq.Message.t list, Loc.t) Coq.Protect.E.t =
  Coq.State.in_stateM ~token ~st
    ~f:(parse_and_execute_in ~token ~loc ~memo ~msg_acc:[] cmds)
    st

let run_node (token : Coq.Limits.Token.t) (prev_state : Coq.State.t)
    (node : Syntax_node.t) : (Coq.State.t, Error.t) result =
  Fleche.Doc.run ~token ~memo:true ~st:prev_state (repr node)
  |> Error.protect_to_result

let run_node_with_diagnostics (token : Coq.Limits.Token.t)
    (prev_state : Coq.State.t) (node : Syntax_node.t) :
    ( Coq.State.t * Lang.Diagnostic.t list,
      Error.t * Lang.Diagnostic.t list )
    result =
  let res =
    run_with_diagnostics ~token ~memo:true ~st:prev_state (repr node)
    |> Error.protect_to_result_with_feedback
  in

  match res with
  | Ok (state_msgs, messages) ->
      let state = fst state_msgs in
      let all_msgs = snd state_msgs @ messages in
      Ok (state, List.map (message_to_diagnostic node.range) all_msgs)
  | Error err ->
      let err, messages = err in
      Error (err, List.map (message_to_diagnostic node.range) messages)

let run_raw_tactic_expr (token : Coq.Limits.Token.t)
    ?(selector : Goal_select.t option) (state : Coq.State.t)
    (expr : Ltac_plugin.Tacexpr.raw_tactic_expr) =
  let selector = Option.map Goal_select_view.make selector in
  let node =
    Syntax_node.raw_tactic_expr_to_syntax_node ?selector expr Code_point.dummy
  in
  run_node token state node

let get_state_after (init_state : Coq.State.t) (token : Coq.Limits.Token.t)
    (nodes : Syntax_node.t list) : (Coq.State.t, Error.t) result =
  let open Sexplib.Std in
  let tag_error (x : Syntax_node.t) (err : Error.t) : Error.t =
    let msg =
      [%message "" ~loc:(x.range : Code_range.t) ~repr:(repr x : string)]
    in
    Error.tag_sexp err ~tag:"info" msg
  in

  let rec aux (state : Coq.State.t) = function
    | [] -> Ok state
    | x :: rest -> (
        match run_node token state x with
        | Ok new_state -> aux new_state rest
        | Error err -> Error (tag_error x err))
  in

  aux init_state nodes

let get_init_state (doc : Rocq_document.t) (node : Syntax_node.t)
    (token : Coq.Limits.Token.t) : (Coq.State.t, Error.t) result =
  let ( let* ) = Result.bind in
  let* nodes_before, _ = Rocq_document.split_at_id node.id doc in
  get_state_after doc.root_state token nodes_before

let get_hypothesis_names (goal : string Coq.Goals.Reified_goal.t) : string list
    =
  List.concat_map
    (fun (hyp : string Coq.Goals.Reified_goal.hyp) -> hyp.names)
    goal.hyps

let count_goals (st : Coq.State.t) : int =
  let goals = Fleche.Info.Goals.get_goals_unit ~st in
  match goals with None -> 0 | Some goals -> List.length goals.goals

let reified_goals_at_state (token : Coq.Limits.Token.t) (st : Coq.State.t) :
    (string Coq.Goals.Reified_goal.t list, Error.t) result =
  let goals = goals ~token ~st in
  match goals with
  | Ok (Some reified_goals) -> Ok reified_goals.goals
  | Ok None -> Ok []
  | Error err -> Error err

let proof_steps_with_goalcount (token : Coq.Limits.Token.t) (st : Coq.State.t)
    (steps : Syntax_node.t list) :
    ((int * Syntax_node.t * int) list, Error.t) result =
  let ( let* ) = Result.bind in
  let rec aux (token : Coq.Limits.Token.t) (st : Coq.State.t)
      (steps : Syntax_node.t list) =
    match steps with
    | [] -> Ok []
    | step :: tail ->
        let before_count = count_goals st in
        if is_focusing_goal step || is_closing_bracket step then
          let* aux_res = aux token st tail in
          Ok ((before_count, step, before_count) :: aux_res)
        else
          let* state = run_node token st step in

          let goal_count = count_goals state in
          let* aux_res = aux token state tail in
          Ok ((before_count, step, goal_count) :: aux_res)
  in
  aux token st steps

let can_reduce_to_zero_goals (token : Coq.Limits.Token.t)
    (init_state : Coq.State.t) (nodes : Syntax_node.t list) : bool =
  let end_state = get_state_after init_state token nodes in
  match end_state with Ok state -> count_goals state = 0 | Error _ -> false

let get_current_goal (token : Coq.Limits.Token.t) (state : Coq.State.t) :
    (string Coq.Goals.Reified_goal.t, Error.t) result =
  let goals_err_opt = goals ~token ~st:state in
  match goals_err_opt with
  | Ok (Some goals) -> (
      match List_utils.head_opt goals.goals with
      | Some goal -> Ok goal
      | None -> Error.string_to_or_error "zero goal at this state")
  | Ok None -> Error.string_to_or_error "zero goal at this state"
  | Error err -> Error err

let goal_hyps_at_state (state : Coq.State.t) (token : Coq.Limits.Token.t) :
    (string list list, Error.t) result =
  reified_goals_at_state token state
  |> Result.map (List.map get_hypothesis_names)

(* TODO: relocate somewhere better ? *)
let get_new_vars ?(keep : string list = [])
    (old_goals_vars : string list list option)
    (new_goals_vars : string list list option) : string list list option =
  match (old_goals_vars, new_goals_vars) with
  | Some old_goals_vars, Some new_goals_vars ->
      Some
        (List_utils.map2_pad
           ~pad1:(List.nth_opt old_goals_vars 0)
           (fun old_vars new_vars ->
             List.filter
               (fun x -> (not (List.mem x old_vars)) || List.mem x keep)
               new_vars)
           old_goals_vars new_goals_vars)
  | _ -> None

let is_valid_proof (token : Coq.Limits.Token.t) (doc : Rocq_document.t)
    (p : Proof.t) : bool =
  match get_init_state doc p.opening token with
  | Ok init_state -> can_reduce_to_zero_goals token init_state p.proof_steps
  | Error _ -> false

(* take a full tree and return an acc *)
(* fold over the proof while running the expr each time to get a new state *)
let depth_first_fold_with_state (doc : Rocq_document.t)
    (token : Coq.Limits.Token.t)
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (acc : 'acc)
    (tree : Syntax_node.t Nary_tree.t) : ('acc, Error.t) result =
  let ( let* ) = Result.bind in

  let rec aux (state : Coq.State.t) (acc : 'acc)
      (tree : Syntax_node.t Nary_tree.t) : (Coq.State.t * 'acc, Error.t) result
      =
    match tree with
    | Node (x, children) ->
        let* state, acc = f state acc x in
        (* Fold over the children using the updated state and accumulator *)
        List.fold_left
          (fun res_acc child ->
            let* state, acc = res_acc in
            aux state acc child)
          (Ok (state, acc))
          children
    (* Fold over the children, threading the state and updating acc *)
    (* Update state and accumulator for the current node *)
  in

  let proposition = match tree with Node (node, _) -> node in
  match get_init_state doc proposition token with
  | Ok state ->
      let* _, acc = aux state acc tree in
      Ok acc
  | Error err ->
      Error
        (Error.tag err
           ~tag:"depth_first_with_state: Unable to retrieve initial state")

let fold_nodes_with_state
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (init_state : Coq.State.t)
    (acc : 'acc) (l : Syntax_node.t list) : ('acc, Error.t) result =
  let ( let* ) = Result.bind in
  let rec aux (l : Syntax_node.t list) (state : Coq.State.t) (acc : 'acc) :
      (Coq.State.t * 'acc, Error.t) result =
    match l with
    | [] -> Ok (state, acc)
    | x :: tail ->
        let* new_state, acc = f state acc x in
        aux tail new_state acc
  in
  Result.map (fun (_, acc) -> acc) (aux l init_state acc)

let fold_proof_with_state (doc : Rocq_document.t) (token : Coq.Limits.Token.t)
    (f :
      Coq.State.t ->
      'acc ->
      Syntax_node.t ->
      (Coq.State.t * 'acc, Error.t) result) (acc : 'acc) (p : Proof.t) :
    ('acc, Error.t) result =
  let all_nodes = Proof.all_nodes p in

  match get_init_state doc p.opening token with
  | Ok state -> fold_nodes_with_state f state acc all_nodes
  | Error err ->
      Error
        (Error.tag err
           ~tag:"depth_first_with_state: Unable to retrieve initial state")
