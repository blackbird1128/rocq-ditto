open Constrexpr

val fold : (constr_expr -> 'a -> 'a) -> 'a -> constr_expr -> 'a
val exists : (constr_expr -> bool) -> constr_expr -> bool
