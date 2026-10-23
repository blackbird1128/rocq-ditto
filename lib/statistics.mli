type 'a scoped_statistic =
  | ProofScope of (Rocq_document.t -> Proof.t -> ('a, Error.t) result)
  | DocScope of (Rocq_document.t -> ('a, Error.t) result)

type 'a t = {
  name : string;
  scope : 'a scoped_statistic;
  empty : 'a;
  combine : 'a -> 'a -> 'a;
  pp : Format.formatter -> 'a -> unit;
  to_json : 'a -> Yojson.Safe.t;
}

type packed = Statistic : 'a t -> packed

val run : Rocq_document.t -> 'a t -> ('a, Error.t) result
val count_induction : Rocq_document.t -> (int, Error.t) result

type proof_status_count = { proved : int; admitted : int }

val pp_proof_status_count : Format.formatter -> proof_status_count -> unit
val proof_status_count_to_json : proof_status_count -> Yojson.Safe.t
val count_proof_status : Rocq_document.t -> (proof_status_count, Error.t) result

val add_proof_status_count :
  proof_status_count -> proof_status_count -> proof_status_count

val get_lemma_names : Rocq_document.t -> (string list, Error.t) result
val get_stable_lemma_names : Rocq_document.t -> (string list, Error.t) result

type lemma = { name : string; axioms : string list }

val pp_lemma : Format.formatter -> lemma -> unit
val lemma_to_json : lemma -> Yojson.Safe.t

type printed_proof_term = { name : string; term : string }

val pp_printed_proof_term : Format.formatter -> printed_proof_term -> unit
val printed_proof_term_to_json : printed_proof_term -> Yojson.Safe.t

val get_proof_terms :
  Rocq_document.t -> (printed_proof_term list, Error.t) result

val get_lemma_and_assoc_axioms : Rocq_document.t -> (lemma list, Error.t) result
