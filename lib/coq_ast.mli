type t = Coq.Ast.t

val to_yojson : t -> Yojson.Safe.t
val of_yojson : Yojson.Safe.t -> (Coq.Ast.t, string) result
