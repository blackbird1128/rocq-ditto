open Proof

type stage = {
  name : string;
  build_steps : Rocq_document.t -> (transformation_step list, Error.t) result;
}

val make_stage :
  string ->
  (Rocq_document.t -> (transformation_step list, Error.t) result) ->
  stage

val apply_stage : Rocq_document.t -> stage -> (Rocq_document.t, Error.t) result

val run_pipeline :
  Rocq_document.t ->
  stage list ->
  (Rocq_document.t * transformation_step list, Error.t) result
