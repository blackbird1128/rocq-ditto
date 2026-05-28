open Proof

type stage = {
  name : string;
  build_steps : Rocq_document.t -> (transformation_step list, Error.t) result;
}

let make_stage (name : string)
    (build_steps :
      Rocq_document.t -> (transformation_step list, Error.t) result) : stage =
  { name; build_steps }

let apply_stage (doc : Rocq_document.t) (st : stage) :
    (Rocq_document.t, Error.t) result =
  let ( let* ) = Result.bind in
  let* steps = st.build_steps doc in
  Rocq_document.apply_transformations_steps steps doc

let run_pipeline (doc : Rocq_document.t) (stages : stage list) :
    (Rocq_document.t * transformation_step list, Error.t) result =
  let ( let* ) = Result.bind in
  List.fold_left
    (fun (acc : (Rocq_document.t * transformation_step list, Error.t) result) st
       ->
      let* doc_acc, steps_acc = acc in
      let* steps = st.build_steps doc_acc in
      let doc' = Rocq_document.apply_transformations_steps steps doc_acc in
      Result.product doc' (Ok (steps_acc @ steps)))
    (Ok (doc, []))
    stages
