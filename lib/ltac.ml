open Ltac_plugin

type pretty_atomic_tactic = {
  atom : Tacexpr.raw_atomic_tactic_expr;
  pretty : string option;
}

let get_raw_atomic_tactic_expr (x : Tacexpr.raw_tactic_expr) :
    Tacexpr.raw_atomic_tactic_expr option =
  match x.v with TacAtom expr -> Some expr | _ -> None
