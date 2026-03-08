open Fleche
open Ditto
module StringSet = Set.Make (String)

let write_ocaml_list (out : out_channel) (name : string) (items : string list) =
  output_string out ("let " ^ name ^ " =\n  [\n");
  List.iter (fun item -> output_string out ("    \"" ^ item ^ "\";\n")) items;
  output_string out "  ]\n\n"

let constrexpr_contains_exists (x : Constrexpr.constr_expr) : bool =
  Constrexpr_fold.exists
    (fun expr ->
      match expr.v with
      | Constrexpr.CNotation (_, (_, notation_key), _) ->
          notation_key = "exists _ .. _ , _"
      | _ -> false)
    x

let collect_definitions_containing_exists (nodes : Syntax_node.t list) :
    string list =
  let rec aux nodes (acc_list : string list) (acc_set : StringSet.t) =
    match nodes with
    | [] -> List.rev acc_list
    | x :: tail -> begin
        match
          ( Syntax_node.get_definition_constrexpr x,
            Syntax_node.get_definition_name x )
        with
        | Some expr, Some name ->
            let references_prev =
              Constrexpr_utils.get_fun_names_in_constrexpr expr
              |> List.exists (fun q ->
                  StringSet.mem (Libnames.string_of_qualid q) acc_set)
            in
            if constrexpr_contains_exists expr || references_prev then
              aux tail (name :: acc_list) (StringSet.add name acc_set)
            else aux tail acc_list acc_set
        | _ -> aux tail acc_list acc_set
      end
  in
  aux nodes [] StringSet.empty

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
    collect_definitions_containing_exists definitions
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
      "line_dec";
    ];
  write_ocaml_list out_chan "blacklisted_proofs"
    [
      "l4_13";
      "l4_16";
      (* ch05 *)
      "l5_1";
      "bet3__bet";
      "between_cong_3";
      "lt_diff";
      (* ch06 out lines *)
      "bet_out__bet";
      "l6_6";
      "out2__bet";
      "l6_11_uniqueness";
      "or_bet_out";
      "not_bet_out";
      "out_to_bet";
      "out_bet__out";
      (* ch07 midpoint *)
      "l7_17";
      "l7_20";
      "l7_21";
      "l7_20_bis";
      "cong_mid2__cong";
      "cong_col_mid";
      "l7_22_aux";
      "col_cong_bet";
      "col_cong2_bet3";
      "col_cong2_bet4";
      "per_not_col";
      "perp_not_col2";
      "per_cong_mid";
      "col_per2_cases";
      "per_cong";
      (* ch9 *)
      "ts_distincts";
      "tsp_distincts";
      "l9_4_1_aux";
      "per_col_eq";
      "l9_4_1";
      "mid_two_sides";
      "os_distincts";
      "one_side_chara";
      "col_one_side_out";
      "col_two_sides_bet";
      "ts__ncol";
      "l9_30";
      "cop_per2__col";
      "cop_perp2__col";
      "col2_cop2__eq";
      "cong3_cop2__col";
      "ncop_distincts";
      (* ch10 (first goal not working as well *)
      "l10_2_uniqueness";
      "l10_2_uniqueness_spec";
      "l10_5";
      "l10_6_uniqueness_spec";
      "image_id";
      "image__midpoint";
      "osym_not_col";
      (* ch10 part 2 *)
      "cop__cong_on_bissect";
      "cop_image_in2__col";
      "l10_10_spec";
      "l10_6_uniqueness";
      "l10_10";
      "cong_cop_image__col";
      "cong_cop_per2_1";
      "per2__col";
      (* ch11 angle *)
      "conga_os__out";
      "l11_19";
      "l11_22_bet";
      "in_angle_out";
      "col_in_angle_out";
      "col_conga_col";
      "bet_in_angle_bet";
      "eq_conga_out";
      "acute_distincts";
      "obtuse_distincts";
      "acute_col__out";
      "col_obtuse__bet";
      "lea_distincts";
      "l11_44_1_b";
      "l11_47";
      "l11_60_aux";
      "mid2_orth_at2__cong";
      "cong2__ncol";
      "cong4_cop2__eq";
      "conga_cop_out_reflectl__out";
      "col_conga_cop_reflectl__col";
      "conga2_cop2__col";
      "conga2_cop2__col_1";
      "col_inangle2__out";
      "col_lta__bet";
      "col_lta__out";
      "lta_distincts";
      (* ch12 parallel *)
      "par_id";
      "par_neq1";
      "col_cop2_perp2__col";
      "col_perp2_ncol__col";
      "not_par_not_col";
      "not_par_inter_uniqueness";
      "inter_distincts";
      "acute_col_perp__out";
      "acute_col_perp__out_1";
      "not_strict_par1";
      "par_distinct";
      (* ch12 parallel inter dec *)
      "parallel_uniqueness";
      "col_par_par_col";
      (* ch13_1 *)
      "per23_preserves_bet";
      "per23_preserves_bet_inv";
      "perp2_preserves_bet13";
      (* ColR ^*)
      "per13_preserves_bet";
      "per13_preserves_bet_inv";
      "per3_preserves_bet1";
      "per3_preserves_bet2_aux";
      "per3_preserves_bet2";
      "cop4_perp_in2__col";
      "perp2_preserves_bet23";
      "l13_8";
      (* ch 13_2 *)
      "lg_cong";
    ];
  close_out out_chan

let main () = Theory.Register.Completed.add generate_data_file
let () = main ()
