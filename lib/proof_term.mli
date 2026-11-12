type name_ref =
  | Var of Names.Id.t
  | Const of Names.Constant.t
  | Inductive of Names.inductive
  | Constructor of Names.constructor

val constant_of_global_ref : Names.GlobRef.t -> Names.Constant.t option

val get :
  token:Coq.Limits.Token.t ->
  Coq.State.t ->
  Names.Constant.t ->
  (Constr.t option, Error.t) result

val collect_names : Constr.t -> name_ref list
