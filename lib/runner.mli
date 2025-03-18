open Syntax_node
open Proof
open Proof_tree

type runningError =
  | Interrupted
  | Parsing of string
  | Coq of string
  | Anomaly of string
  | System of string
  | Theorem_not_found of string

val running_error_to_string : runningError -> string
val protect_to_result : ('a, 'b) Coq.Protect.E.t -> ('a, runningError) Result.t

val protect_to_result_with_feedback :
  ('a, 'b) Coq.Protect.E.t ->
  ('a * 'b Coq.Message.t list, runningError * 'b Coq.Message.t list) Result.t

val run_node :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  syntaxNode ->
  (Coq.State.t, runningError) result

val run_node_with_diagnostics :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  syntaxNode ->
  ( Coq.State.t * Lang.Diagnostic.t list,
    runningError * Lang.Diagnostic.t list )
  result

val get_init_state :
  Coq_document.t ->
  syntaxNode ->
  Coq.Limits.Token.t ->
  (Coq.State.t, runningError) result

val goals :
  token:Coq.Limits.Token.t ->
  st:Coq.State.t ->
  ( (string Coq.Goals.Reified_goal.t, string) Coq.Goals.t option,
    runningError )
  result

val get_proof_state : (Coq.State.t, Loc.t) Coq.Protect.E.t -> Coq.State.t
val count_goals : Coq.Limits.Token.t -> Coq.State.t -> int

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  syntaxNode list ->
  (syntaxNode * int) list

val get_hypothesis_names : string Coq.Goals.Reified_goal.t -> string list

val get_current_goal :
  Coq.Limits.Token.t ->
  Coq.State.t ->
  (string Coq.Goals.Reified_goal.t, string) result

val can_reduce_to_zero_goals : Coq.State.t -> syntaxNode list -> bool
val tree_to_proof : syntaxNode nary_tree -> proof

val proof_tree_from_parents :
  int * syntaxNode ->
  (int * syntaxNode, int * syntaxNode) Hashtbl.t ->
  syntaxNode nary_tree

val treeify_proof :
  Coq_document.t -> proof -> (syntaxNode nary_tree, string) result

val fold_nodes_with_state :
  Coq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc) ->
  Coq.State.t ->
  'acc ->
  syntaxNode list ->
  'acc

val fold_proof_with_state :
  Coq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc) ->
  'acc ->
  proof ->
  ('acc, string) result

val depth_first_fold_with_state :
  Coq_document.t ->
  Coq.Limits.Token.t ->
  (Coq.State.t -> 'acc -> syntaxNode -> Coq.State.t * 'acc) ->
  'acc ->
  syntaxNode nary_tree ->
  ('acc, string) result
