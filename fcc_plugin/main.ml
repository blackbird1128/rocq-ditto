open Fleche
open Ditto

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let asts = Doc.asts doc in
  let coq_asts =
    List.map (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v) asts
  in

  List.iter
    (fun x -> Ppvernac.pr_vernac x |> Pp.string_of_ppcmds |> print_endline)
    coq_asts;
  (* (fun x -> *)
  (*   Ppvernac.pr_vernac (Coq.Ast.to_coq *)
  (*   |> Pp.string_of_ppcmds |> print_endline) *)
  (*   asts; *)
  (* Output json *)
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.astdump" in

  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s was completed!"
    uri_str;
  ()

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
