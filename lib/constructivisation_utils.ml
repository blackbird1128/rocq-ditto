(* Ugly, temporary module, but ho well *)

let attach_node_after_pred (doc : Rocq_document.t) (node : Syntax_node.t)
    ?(reverse = false) (pred : Syntax_node.t -> bool) :
    (Transforming_step.t list, Error.t) result =
  let pred_node_opt =
    if reverse then List_utils.find_last_opt pred doc.elements
    else List.find_opt pred doc.elements
  in
  match pred_node_opt with
  | Some pred_node -> Ok [ Attach (node, LineAfter, pred_node.id) ]
  | None ->
      Error.string_to_or_error
        "No node found to attach to with provided predicate"

let attach_node_after_pred_in_file (doc : Rocq_document.t)
    (node : Syntax_node.t) (filename : string) ?(reverse = false)
    (pred : Syntax_node.t -> bool) : (Transforming_step.t list, Error.t) result
    =
  if Filename.basename doc.filename = filename then
    attach_node_after_pred doc node ~reverse pred
  else Ok []

let attach_node_after_requires (doc : Rocq_document.t) (node : Syntax_node.t) :
    (Transforming_step.t list, Error.t) result =
  attach_node_after_pred doc node ~reverse:true Syntax_node.is_require

let attach_require_to_file (doc : Rocq_document.t) ~(require_text : string)
    (filename : string) : (Transforming_step.t list, Error.t) result =
  let ( let* ) = Result.bind in
  let* require_node =
    Syntax_node.syntax_node_of_string require_text Code_point.dummy
  in
  attach_node_after_pred_in_file doc require_node filename ~reverse:true
    Syntax_node.is_require

let get_proofs_named (proofs : Proof.t list) (names : string list) :
    Proof.t list =
  List.filter
    (fun p ->
      let name = Proof.get_proof_name p |> Option.map Names.Id.to_string in
      List.exists (fun x -> Option.equal String.equal name (Some x)) names)
    proofs
