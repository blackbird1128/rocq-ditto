open Sexplib.Sexp
open Proof
open Vernacexpr
open Fleche

type sexp_query =
  | Q_any
  | Q_atom of string
  | Q_field of string * sexp_query
  | Q_field_path of string list
  | Q_list_any of sexp_query
  | Q_list_exact of sexp_query list
  | Q_list_prefix of sexp_query list
  | Q_and of sexp_query list
  | Q_or of sexp_query list
  | Q_not of sexp_query
  | Q_anywhere of sexp_query

val get_proof_proposition_sexp : proof -> Sexplib.Sexp.t option
val matches : sexp_query -> Sexplib.Sexp.t -> bool
val extract_match : sexp_query -> Sexplib.Sexp.t -> Sexplib.Sexp.t option
val collect_matches : sexp_query -> Sexplib.Sexp.t -> Sexplib.Sexp.t list
val q_theorem_with_exists_conclusion : sexp_query
