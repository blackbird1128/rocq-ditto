val run_node :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t ->
  (Coq.State.t, Error.t) result

val run_node_with_diagnostics :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t ->
  ( Coq.State.t * Lang.Diagnostic.t list,
    Error.t * Lang.Diagnostic.t list )
  result

val run_raw_tactic_expr :
  Coq.Limits.Token.t ->
  ?selector:Goal_select.t ->
  Coq.State.t ->
  Ltac_plugin.Tacexpr.raw_tactic_expr ->
  (Coq.State.t, Error.t) result

val get_state_after :
  Coq.State.t ->
  Coq.Limits.Token.t ->
  Syntax_node.t list ->
  (Coq.State.t, Error.t) result

val get_init_state :
  Rocq_document.t ->
  Syntax_node.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t, Error.t) result

val goals :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  ((string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option, Error.t) result

val reified_goals_at_state :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  (string Coq.Goals.Reified_goal.t list, Error.t) result

val count_goals : Coq.State.t -> int

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  Syntax_node.t list ->
  ((int * Syntax_node.t * int) list, Error.t) result

val get_hypothesis_names : string Coq.Goals.Reified_goal.t -> string list

val goal_hyps_at_state :
  Coq.State.t -> Coq.Limits.Token.t -> (string list list, Error.t) result

val get_new_vars :
  ?keep:string list ->
  string list list option ->
  string list list option ->
  string list list option

val get_current_goal :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  (string Coq.Goals.Reified_goal.t, Error.t) result

val can_reduce_to_zero_goals :
  Coq.Limits.Token.t -> Coq.State.t -> Syntax_node.t list -> bool

val is_valid_proof : Coq.Limits.Token.t -> Rocq_document.t -> Proof.t -> bool

val fold_nodes_with_state :
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  Coq.State.t ->
  'acc ->
  Syntax_node.t list ->
  ('acc, Error.t) result

val fold_proof_with_state :
  Rocq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  'acc ->
  Proof.t ->
  ('acc, Error.t) result

val depth_first_fold_with_state :
  Rocq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> Syntax_node.t -> (Coq.State.t * 'acc, Error.t) result) ->
  'acc ->
  Syntax_node.t Nary_tree.t ->
  ('acc, Error.t) result
