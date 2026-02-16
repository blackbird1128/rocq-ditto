open Fleche
open Ditto

let write_ocaml_list (out : out_channel) (name : string) (items : string list)
    =
  output_string out ("let " ^ name ^ " =\n  [\n");
  List.iter
    (fun item -> output_string out ("    \"" ^ item ^ "\";\n"))
    items;
  output_string out "  ]\n\n"

let generate_data_file ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl
    "[constructivisation-data-generator] processing %s ..." uri_str;

  let parsed_document = Rocq_document.parse_document doc in
  let definitions =
    List.filter Syntax_node.is_syntax_node_definition parsed_document.elements
  in

  let definitions_with_exists =
    Constructivisation.collect_definitions_containing_exists definitions
  in

  let out_path =
    match Sys.getenv_opt "CONSTRUCTIVISATION_DATA_OUT" with
    | Some path -> path
    | None -> "lib/constructivisation_data.ml"
  in

  let out_chan = open_out out_path in
  output_string out_chan
    "(* This file is generated. Do not edit by hand. *)\n\n";
  write_ocaml_list out_chan "definitions_with_exists" definitions_with_exists;
  write_ocaml_list out_chan "decidability_lemmas"
    [ "eq_dec_points"; "cong_dec"; "bet_dec"; "col_dec" ];
  close_out out_chan

let main () = Theory.Register.Completed.add generate_data_file
let () = main ()
