open Fleche
open Ditto

let write_ocaml_list (out : out_channel) (name : string) (items : string list) =
  output_string out ("let " ^ name ^ " =\n  [\n");
  List.iter (fun item -> output_string out ("    \"" ^ item ^ "\";\n")) items;
  output_string out "  ]\n\n"

let generate_data_file ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[constructivisation-data-generator] processing %s ..."
    uri_str;

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
    [
      "eq_dec_points";
      "cong_dec";
      "bet_dec";
      "col_dec";
      "out_dec";
      "midpoint_dec";
    ];
  write_ocaml_list out_chan "blacklisted_proofs"
    [
      "l4_13";
      "l4_16";
      "NCol_cases";
      "l5_1";
      "l5_2";
      "bet3__bet";
      "between_cong_3";
      "lt_diff";
      "fourth_point";
      "third_point";
      "l5_12_b";
      "l6_2";
      "bet_out__bet";
      "l6_3_2";
      "l6_4_2";
      "l6_7";
      "out2_bet_out";
      "l6_16_1";
      "out2__bet";
      "l6_11_uniqueness";
      "or_bet_out";
      "not_bet_out";
      "out_to_bet";
      "col_out2_col";
      "bet2_out_out";
      "out_bet_out_1";
      "out_bet__out";
      "Out_cases";
      "Mid_cases";
      "l7_20";
      "l7_20_bis";
      "cong_col_mid";
      "l7_22_aux";
      "l7_22";
      "midpoint_out";
      "midpoint_preserves_out";
      "col_cong_bet";
      "col_cong2_bet1";
      "col_cong2_bet2";
      "col_cong2_bet3";
      "col_cong2_bet4";
    ];
  close_out out_chan

let main () = Theory.Register.Completed.add generate_data_file
let () = main ()
