val get_proof_local_requirements :
  Rocq_document.t -> Proof.t -> (string list, Error.t) result

val constructivisation_post :
  Rocq_document.t -> (Transforming_step.t list, Error.t) result
