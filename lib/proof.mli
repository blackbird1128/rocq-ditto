open Coq_document

type proof = { proposition : rangedCoqSpan; proof_steps : rangedCoqSpan list }

val is_ranged_coq_span_proof_start : rangedCoqSpan -> bool
val is_ranged_coq_span_proof_end : rangedCoqSpan -> bool
val is_ranged_coq_span_tactic : rangedCoqSpan -> bool
val get_proofs : coqDocument -> proof list
