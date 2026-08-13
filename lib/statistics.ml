let count_induction_calls_in_tacexpr (x : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    int =
  Tacexpr_map.tacexpr_fold
    (fun acc expr ->
      match expr.v with
      | Ltac_plugin.Tacexpr.TacAtom
          (Ltac_plugin.Tacexpr.TacInductionDestruct (true, false, _)) ->
          acc + 1
      | _ -> acc)
    0 x

let count_induction (doc : Rocq_document.t) : (int, Error.t) result =
  let nodes = doc.elements in
  Ok
    (List.fold_left
       (fun acc node ->
         match Syntax_node.get_raw_tactic_expr node with
         | Some expr -> acc + count_induction_calls_in_tacexpr expr
         | None -> acc)
       0 nodes)
