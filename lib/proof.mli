open Fleche
open Petanque
open Annotated_ast_node
open Proof_tree

type proof_status = Admitted | Proved | Aborted

type proof = {
  proposition : annotatedASTNode;
  proof_steps : annotatedASTNode list;
  status : proof_status;
}
(** Represents a proof in a Coq document. [proof] contains the initial
    proposition and a list of proof steps. *)

val get_names : annotatedASTNode -> string list
(** A node can have multiple names (i.e., mutual recursive definitions) *)

val proof_to_coq_script_string : proof -> string

val get_proof_name : proof -> string option
(** Retrieve the name of the proof's proposition if available.
    [get_proof_name p] returns [Some name] if the proof [p] has a proposition
    with a name, otherwise it returns [None]. *)

(* val get_tactics : proof -> string list *)

val proof_status_from_last_node :
  annotatedASTNode -> (proof_status, string) result

val get_proof_state :
  Agent.State.t Agent.Run_result.t Agent.R.t -> Agent.State.t
(** Extract the proof state from a run result. [get_proof_state start_result]
    returns the proof state [st] if the [start_result] is successful (i.e., an
    [Ok run_result]). If there's an [Error err], it prints the error message and
    raises a [Failure]. *)

val count_goals : Coq.Limits.Token.t -> Agent.State.t -> int
(** Count the number of goals in the agent's state. [count_goals token st]
    returns the number of goals in the agent's state [st] associated with the
    provided [token]. If there are no goals or an error occurs, it returns 0. *)

val print_tree : annotatedASTNode nary_tree -> string -> unit
(** Print a tree structure with indentation. [print_tree tree indent] prints a
    tree, where [tree] is an [annotatedASTNode nary_tree] and [indent] is a
    string used for indentation to represent the tree structure visually. *)

val get_init_state :
  Doc.t -> proof -> Agent.State.t Agent.Run_result.t Agent.R.t option
(** Get the initial state for a given proof in a document.
    [get_init_state doc p] returns [Some result] if the proof has a name, where
    [result] is the starting state of the agent for the theorem named after the
    proof [p] and document [doc]. If the proof does not have a name, it returns
    [None]. *)

val proof_steps_with_goalcount :
  Coq.Limits.Token.t ->
  Agent.State.t ->
  annotatedASTNode list ->
  (annotatedASTNode * int) list
(** Count the goals after applying proof steps in a given state.
    [proof_steps_with_goalcount token st steps] takes a [token], an initial
    state [st], and a list of proof steps [steps]. It returns a list of tuples
    where each tuple contains a proof step and the corresponding goal count
    after applying that step to the state. If [steps] is empty, it returns an
    empty list. *)

val treeify_proof :
  Doc.t -> proof -> (annotatedASTNode nary_tree, string) result
(** Transform a proof into an n-ary tree representation. [treeify_proof doc p]
    takes a document [doc] and a proof [p], returning an
    [(annotatedASTNode nary_tree,string)] that represents the structure of the
    proof or a string containing the reason of the error. steps branch split are
    created when the number of goal stop increasing, and match each goals. *)

val tree_to_proof : annotatedASTNode nary_tree -> proof
(** Convert an annotated AST node n-ary tree to a proof. [tree_to_proof tree]
    returns a [proof] constructed from the nodes of the given [tree]. The first
    node becomes the proposition, and the next nodes become the proof steps in
    depth first order. *)

val last_offset : proof -> int
(** Compute the last offset in a proof. [last_offset p] returns the highest
    offset of the end of ranges from the proposition and proof steps in the
    given proof [p]. *)

val proof_nodes : proof -> annotatedASTNode list
(** Extracts the nodes from a proof. [proof_nodes p] returns a list containing
    the proposition of the proof [p] followed by its proof steps. *)

val proof_from_nodes : annotatedASTNode list -> (proof, string) result
(** Create a proof from a list of annotated AST nodes. [proof_from_nodes nodes]
    takes a list of nodes and returns a proof where the first node in the list
    is used as the proposition, and the remaining nodes are the proof steps. If
    the list made of less than three nodes or the last node isn't a valid proof
    end, return an error. *)
(* TODO fix to return an error if the list is empty *)

val get_hypothesis_names : string Coq.Goals.Reified_goal.t -> string list

val get_current_goal :
  Coq.Limits.Token.t ->
  Agent.State.t ->
  (string Coq.Goals.Reified_goal.t, string) result

val fold_nodes_with_state :
  Doc.t ->
  Coq.Limits.Token.t ->
  (Petanque.Agent.State.t ->
  'acc ->
  annotatedASTNode ->
  Petanque.Agent.State.t * 'acc) ->
  Petanque.Agent.State.t ->
  'acc ->
  annotatedASTNode list ->
  'acc

val fold_proof_with_state :
  Doc.t ->
  Coq.Limits.Token.t ->
  (Petanque.Agent.State.t ->
  'acc ->
  annotatedASTNode ->
  Petanque.Agent.State.t * 'acc) ->
  'acc ->
  proof ->
  ('acc, string) result

val depth_first_fold_with_state :
  Doc.t ->
  Coq.Limits.Token.t ->
  (Petanque.Agent.State.t ->
  'acc ->
  annotatedASTNode ->
  Petanque.Agent.State.t * 'acc) ->
  'acc ->
  annotatedASTNode nary_tree ->
  ('acc, string) result
