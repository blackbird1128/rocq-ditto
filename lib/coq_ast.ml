type t = Coq.Ast.t

(* XXX: Better catch the exception below, but this requires a new SerAPI
   release *)

let () = Serlib.Serlib_base.exn_on_opaque := false

let to_yojson x =
  Serlib.Ser_vernacexpr.vernac_control_to_yojson (Coq.Ast.to_coq x)

let of_yojson x =
  Fl_dynload.load_packages [ "coq-lsp.serlib.ltac" ];
  Serlib.Ser_vernacexpr.vernac_control_of_yojson x |> Result.map Coq.Ast.of_coq
