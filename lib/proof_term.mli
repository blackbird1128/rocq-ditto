val constant_of_global_ref : Names.GlobRef.t -> Names.Constant.t option

val get :
  token:Coq.Limits.Token.t ->
  Coq.State.t ->
  Names.Constant.t ->
  (Constr.t option, Error.t) result
