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
      "perp_in_dec";
      "col2_dec";
      "is_image_spec_dec";
      "conga_dec";
      "inangle_dec";
      "same_dir_dec";
      "cop_dec";
      "inter_dec";
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
      "l6_3_2";
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
      "lg_cong_lg";
      "lg_null_instance";
      "ex_eqL";
      (* ch 13_3 *)
      "is_ang_distinct";
      "ang_sym";
      "anga_sym";
      "anga_conga_anga";
      "anga_out_anga";
      (* ch 13_4 *)
      "l13_6";
      "null_lcos_eql";
      "lcos_lg";
      "l13_7";
      "lcos_uniqueness";
      (* ch 13_5 *)
      "l13_6_bis";
      "lcos_per_anga";
      "lcos_lcos_cop__col";
      "l13_10_aux3";
      "l13_10_aux4";
      "l13_10_aux5";
      (* ch 13_6 *)
      "l13_18_2";
      (* ch 14_sum *)
      "sum_uniqueness";
      "opp0_uniqueness";
      "proj_col";
      "proj_id";
      "sum_A_B_A";
      "sum_A_B_B";
      "sum_uniquenessA";
      "sum_uniquenessB";
      "sum_cong";
      "opp_uniqueness";
      "opp_midpoint";
      "pj_uniqueness";
      "double_null_null";
      "double_not_null_not_nul";
      "diff_uniqueness";
      "sum_stable";
      "plg_to_sum";
      "diff_to_plg";
      "sum3_uniqueness";
      (* ch 14 prod *)
      "prod_uniqueness";
      "prod_null";
      "prod_O_l_eq";
      "prod_O_r_eq";
      "prod_uniquenessA";
      "prod_1_l_eq";
      (* ch 14 order *)
      "l14_36_a";
      "pos_null_neg";
      "sum_pos_pos";
      "prod_pos_pos";
      "pos_not_neg";
      "neg_not_pos";
      "opp_pos_neg";
      "opp_neg_pos";
      "pos_opp_neg";
      "not_pos_and_neg";
      "leP_asym";
      "square_pos";
      "col_pos_or_neg";
      "ltP_neg";
      "lt_diff_ps";
      (* CH 15 lengths *)
      "length_id_1";
      "length_eq_cong_1";
      "ltP_pos";
      "leP_bet";
      "length_Ar2";
      "l15_3";
      "length_uniqueness";
      "length_Ps";
      "length_not_col_null";
      "length_out";
      "image_preserves_bet1";
      "image_preserves_out";
      "project_preserves_out";
      "prod_col";
      "signeq__prod_pos";
      "pos_neg__prod_neg";
      "not_signEq_prod_neg";
      "prod_pos__signeq";
      "prod_ng___not_signeq";
      "length_pos_or_null";
      "not_neg_pos";
      "sum_pos_null";
      "length_not_neg";
      "signEq_refl";
      "square_not_neg";
      "root_uniqueness";
      "inter_tangent_circle";
      "circle_projp_between";
      "sign_dec";
      (* ch16 coordinates *)
      "Cs_not_Col";
      "Cd_Col";
      "eq_points_coordinates";
      "l16_9_1";
      "l16_9_2";
      "cong_3_2_cong_4";
      "cong_3_3_cong_5";
      "characterization_of_congruence";
      "bet_betCood_aux";
      "same_abscissa_col";
      "characterization_of_collinearity";
      "square_distance_formula";
      (* ch15 pyth rel *)
      "Ps_Col";
      "PythRel_uniqueness";
      (* perp bisect *)
      "perp_bisect_is_on_perp_bisect";
      "cong_cop2_perp_bisect_col";
      (* suma *)
      "suma_distincts";
      "trisuma_distincts";
      "sams_distincts";
      "col_suma__col";
      "per2_suma__bet";
      "acute2_suma__nbet";
      "col2_suma__col";
      "suma_suppa__bet";
      "col_trisuma__bet";
      (* quadrilaterals *)
      "midpoint_midpoint_col";
      "bet3_cong3_bet";
      "bet_double_bet";
      "bet_half_bet";
      "bet_cong_bet";
      "plgf_permut";
      "mid_plgf_aux";
      "mid_plgf";
      "midpoint_cong_uniqueness";
      "plgf_not_comm";
      "parallelogram_strict_not_col_2";
      "parallelogram_strict_not_col_4";
      "plg_col_plgf";
      "plgf_trivial_neq";
      "plgf_trivial_trans";
      "plgf3_mid";
      "cong3_id";
      "not_col_sym_not_col";
      "plgf_bet";
      (* saccheri *)
      "sac__cong";
      "conga_per2_os__cong";
      "lam_per__cong";
      "t22_7__cong";
      "t22_8__cong";
      "per_sac__rah";
      "acute_sac__aah";
      "obtuse_sac__oah";
      "saccheri_s_three_hypotheses";
      "not_rah";
      "not_oah";
      "not_aah";
      "t22_14__bet_aux";
      "t22_14__bet";
      "t22_14__rah";
      "t22_14__aah";
      "t22_14__oah";
      (* quad inter dec *)
      "plgs_cong";
      "plg_cong";
      "plg_mid_2";
      "plgf_comm2";
      "parallelogram_strict_midpoint";
      "plgf_rect_id";
      "par_cong_cong";
      "col_cong_cong";
      "not_par_pars_not_cong";
      "plg_uniqueness";
      "plgf_plgf_plgf";
      "degenerated_rect_eq";
      "rmb_cong";
      (* vector *)
      "vector_construction_uniqueness";
      "null_vector";
      "vector_uniqueness";
      "eqv_opp_null";
      "eqv_mid";
      "one_side_col_out";
      "same_dir_out";
      "same_dir_out1";
      "same_dir_null";
      "plgs_plgs_bet";
      "plgf_plgf_bet";
      "plg_plg_bet";
      "plgf_out_plgf";
      "same_dir_id";
      (* midpoints theorem *)
      "col_permut132";
      "col_permut213";
      "col_permut231";
      "col_permut312";
      "col_permut321";
      "col123_124__col134";
      "col123_124__col234";
      "triangle_par_mid";
      (* project *)
      "project_id";
      "project_par";
      "ker_col";
      "project_uniqueness";
      "project_col_eq";
      "project_preserves_bet";
      "cong_conga3_cong3";
      "eqv_project_eq_eq";
      "eqv_cong";
      "proj_distinct";
      "projp_id";
      "projp2_col";
      "col_projp_eq";
      "projp_col";
      "perp_projp2_eq";
      "col_par_projp2_eq";
      "col_2_par_projp2_cong";
    ];
  close_out out_chan

let main () = Theory.Register.Completed.add generate_data_file
let () = main ()
