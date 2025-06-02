open Fleche
open Ditto.Diagnostic_utils

let neat_compile ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let first_errors = List.filteri (fun i _ -> i < 5) errors in

  print_endline ("compiling " ^ uri_str ^ " ...");
  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics first_errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics first_errors
  | Doc.Completion.Yes _ ->
      if List.length errors != 0 then print_diagnostics first_errors
      else print_endline "Parsing was successful"

let main () = Theory.Register.Completed.add neat_compile
let () = main ()
