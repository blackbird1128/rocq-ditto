open Fleche

(** Represents a proof in a Coq document. *)
type proof = { proposition : Doc.Node.Ast.t; proof_steps : Doc.Node.Ast.t list }
(** [proof] contains the initial proposition and a list of proof steps. *)

val is_doc_node_ast_tactic : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_tactic x] checks if [x] represents a tactic in the Coq document. *)

val is_doc_node_ast_proof_start : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_proof_start x] checks if [x] marks the start of a proof in the Coq document. *)

val is_doc_node_ast_proof_end : Doc.Node.Ast.t -> bool
(** [is_doc_node_ast_proof_end x] checks if [x] marks the end of a proof in the Coq document. *)

val get_proofs : Doc.Node.Ast.t list -> proof list
(** [get_proofs x] extracts all proofs from a list of Coq document nodes [x]. 
    Raises [Invalid_argument] if a proof starts but does not end or vice versa. *)
