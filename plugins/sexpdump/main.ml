module Lsp = Fleche_lsp
open Fleche

let pp_sexp fmt obj = Format.fprintf fmt "@[%a@\n@]" Sexplib.Sexp.pp_hum obj

let rec strip_loc_field (sexp : Sexplib.Sexp.t) : Sexplib.Sexp.t option =
  match sexp with
  | Atom _ as atom -> Some atom
  | List (Atom "loc" :: _) -> None
  | List elements -> Some (List (List.filter_map strip_loc_field elements))

let strip_loc (sexp : Sexplib.Sexp.t) : Sexplib.Sexp.t =
  match strip_loc_field sexp with Some sexp -> sexp | None -> List []

let pp_ast_sexp fmt (ast : Doc.Node.Ast.t) =
  Serlib.Ser_vernacexpr.sexp_of_vernac_control (Coq.Ast.to_coq ast.v)
  |> (if Sys.getenv_opt "SEXPDUMP_STRIP_LOCS" = None then Fun.id else strip_loc)
  |> pp_sexp fmt

let pw pp fmt ast = Format.fprintf fmt "@[%a@]" pp ast

let dump_asts pp asts =
  let f fmt asts = List.iter (pw pp fmt) asts in
  f Format.std_formatter asts

let dump_ast ~io:_ ~token:_ ~(doc : Doc.t) =
  let asts = Doc.asts doc in

  dump_asts pp_ast_sexp asts

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
