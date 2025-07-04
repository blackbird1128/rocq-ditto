open Fleche
open Ditto
open Ditto.Proof
open Vernacexpr
open Ditto.Diagnostic_utils

let rec get_basic_tactic_names (tac : Ltac_plugin.Tacexpr.raw_tactic_expr) :
    string list =
  let empty_env = Environ.empty_env in
  let empty_evd = Evd.empty in
  let pp = Ltac_plugin.Pptactic.pr_raw_tactic empty_env empty_evd tac in
  match tac.v with
  | Ltac_plugin.Tacexpr.TacAtom atom -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacThen (tac1, tac2) ->
      (*x ; y can be nested*)
      get_basic_tactic_names tac1 @ get_basic_tactic_names tac2
  | Ltac_plugin.Tacexpr.TacDispatch tactics ->
      List.concat_map get_basic_tactic_names tactics
  (* [|>]*)
  | Ltac_plugin.Tacexpr.TacExtendTac (_, _, _) ->
      prerr_endline "extend tac, not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacThens (tacDistributed, tac_list) ->
      (* x;[a;b;c] *)
      get_basic_tactic_names tacDistributed
      @ List.concat_map get_basic_tactic_names tac_list
  | Ltac_plugin.Tacexpr.TacThens3parts (tac1, tac_array1, tac2, tac_array2) ->
      let tac_array1_names =
        Array.map get_basic_tactic_names tac_array1
        |> Array.map Array.of_list |> Array.to_list |> Array.concat
        |> Array.to_list
      in
      let tac_array2_names =
        Array.map get_basic_tactic_names tac_array2
        |> Array.map Array.of_list |> Array.to_list |> Array.concat
        |> Array.to_list
      in
      print_endline "tacThens3parts not handled yet";
      get_basic_tactic_names tac1
      @ tac_array1_names
      @ get_basic_tactic_names tac2
      @ tac_array2_names
  | Ltac_plugin.Tacexpr.TacFirst tac_list ->
      List.concat_map get_basic_tactic_names tac_list
  | Ltac_plugin.Tacexpr.TacSolve tac_to_tries ->
      List.concat_map get_basic_tactic_names tac_to_tries
  | Ltac_plugin.Tacexpr.TacTry expr -> get_basic_tactic_names expr
  | Ltac_plugin.Tacexpr.TacOr (tac1, tac2) ->
      get_basic_tactic_names tac1 @ get_basic_tactic_names tac2
  | Ltac_plugin.Tacexpr.TacOnce tac ->
      get_basic_tactic_names tac (* once tactic*)
  | Ltac_plugin.Tacexpr.TacExactlyOnce tac -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacIfThenCatch (_, _, _) ->
      print_endline "tacIfThenCatch not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacOrelse (tac, tac_or_else) ->
      get_basic_tactic_names tac @ get_basic_tactic_names tac_or_else
  | Ltac_plugin.Tacexpr.TacDo (_, tactic_to_do) ->
      get_basic_tactic_names tactic_to_do
  | Ltac_plugin.Tacexpr.TacTimeout (duration, tac) -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacTime (_, tacticTimed) ->
      get_basic_tactic_names tacticTimed
  | Ltac_plugin.Tacexpr.TacRepeat tactic_repeated ->
      get_basic_tactic_names tactic_repeated
  | Ltac_plugin.Tacexpr.TacProgress tac -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacAbstract (tac, _) -> get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacId msg -> [ "idtac" ]
  | Ltac_plugin.Tacexpr.TacFail (_, _, _) -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacLetIn (_, _, _) ->
      print_endline "tacLetIn not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacMatch (_, _, _) ->
      print_endline "tac match not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacMatchGoal (_, _, _) ->
      print_endline "tac match goal not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacFun l ->
      print_endline "fun call not handled yet";
      []
  | Ltac_plugin.Tacexpr.TacArg arg -> [ Pp.string_of_ppcmds pp ]
  | Ltac_plugin.Tacexpr.TacSelect (goal_select, tac) ->
      get_basic_tactic_names tac
  | Ltac_plugin.Tacexpr.TacML (_, list_tac) ->
      print_endline "what is a tac Ml ? ";
      []
  | Ltac_plugin.Tacexpr.TacAlias (_, tactics) -> [ Pp.string_of_ppcmds pp ]

let tactic_count ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  prerr_endline ("treating: " ^ uri_str);
  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  match doc.completed with
  | Doc.Completion.Stopped range_stopped ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stopped);
      print_diagnostics errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics errors
  | Doc.Completion.Yes _ ->
      let parsed_document = Coq_document.parse_document doc in

      let proofs = Result.get_ok (Coq_document.get_proofs parsed_document) in

      let proof_steps = List.concat_map (fun x -> x.proof_steps) proofs in
      let proof_tactics =
        List.filter Syntax_node.is_syntax_node_tactic proof_steps
      in

      let basic_tactics =
        List.concat_map
          (fun node ->
            let raw_args =
              Syntax_node.get_tactic_raw_generic_arguments node |> Option.get
            in
            let ltac_elements =
              Raw_gen_args_converter.raw_arguments_to_ltac_elements raw_args
              |> Option.get
            in

            get_basic_tactic_names ltac_elements.raw_tactic_expr)
          proof_tactics
      in
      let first_word_tactics =
        List.map
          (fun tac -> String.split_on_char ' ' tac |> List.hd)
          basic_tactics
      in
      List.iter print_endline first_word_tactics

let main () = Theory.Register.Completed.add tactic_count
let () = main ()
