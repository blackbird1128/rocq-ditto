open Fleche
open Sexplib.Std

let dep_program, dep_fixed_args = Rocq_version.dep_command
let dep_program_repr = String.concat " " (dep_program :: dep_fixed_args)

let run_dep_process (args : string list) : (string, Error.t) result =
  let argv = Array.of_list ((dep_program :: dep_fixed_args) @ args) in
  try
    let ic = Unix.open_process_args_in dep_program argv in
    let output = In_channel.input_all ic in
    match Unix.close_process_in ic with
    | Unix.WEXITED 0 -> Ok output
    | Unix.WEXITED n ->
        Error.format_to_or_error "%s exited with %d; output:\n%s"
          dep_program_repr n output
    | Unix.WSTOPPED signal ->
        Error.format_to_or_error "%s was stopped by signal %d" dep_program_repr
          signal
    | Unix.WSIGNALED signal ->
        Error.format_to_or_error "%s was killed by signal %d" dep_program_repr
          signal
  with Unix.Unix_error (err, func, arg) ->
    let msg = Unix.error_message err in
    Error.format_to_or_error "%s: %s (%s)" func msg arg

let coqproject_sorted_files (project : Project.t) :
    (string list, Error.t) result =
  let ( let* ) = Result.bind in
  let* output = run_dep_process [ "-f"; project.path; "-sort" ] in
  let lines = String_utils.split_by_newline output in

  match lines with
  | [] ->
      Error.format_to_or_error "Executing %s returned an empty output"
        dep_program_repr
  | [ first_line ] -> Ok (String_utils.split_words first_line)
  | _ :: _ ->
      Error.format_to_or_error
        "Executing %s returned more than a single line of output, unexpected \
         format"
        dep_program_repr

type dependency_rule = { filename : string; dependencies : string list }
[@@deriving show { with_path = false }]

(* TODO: Checks how to make it testable but not expose for a single line *)
let parse_depf_line (line : string) : (dependency_rule, Error.t) result =
  let ( let* ) = Result.bind in
  let re = Re.compile (Re.str "required_vo:") in
  let split = Re.split_delim re line in
  match split with
  | [ _; second_part ] -> (
      let words = String_utils.split_words second_part in
      match List_utils.split_last words with
      | Some (filename :: vo_dependencies, _) ->
          let* dependencies =
            List.map
              (fun x ->
                if String.ends_with ~suffix:".vo" x then
                  Ok (String.sub x 0 (String.length x - 1))
                else Error.format_to_or_error "Part: %S doesn't end with .vo" x)
              vo_dependencies
            |> List_utils.result_all
          in

          Ok { filename; dependencies }
      | _ -> Error.format_to_or_error "Malformed depedency line: %S" line)
  | _ ->
      Error.format_to_or_error "Can't split the line %S at \"required_vo:\""
        line

let parse_depf_output (output : string) : (Dependency_graph.t, Error.t) result =
  let ( let* ) = Result.bind in
  let lines =
    String_utils.split_by_newline output
    |> List.filter (fun line -> not (String.equal line ""))
  in
  let* parsed_lines = List.map parse_depf_line lines |> List_utils.result_all in
  let parents_table = Hashtbl.create (List.length parsed_lines) in
  List.iter
    (fun { filename; dependencies } ->
      let filtered_dependencies =
        List.filter (fun dep -> not (String.equal filename dep)) dependencies
      in
      (* avoid making a recursive parent table *)
      Hashtbl.replace parents_table filename filtered_dependencies)
    parsed_lines;
  Ok (Dependency_graph.of_parents_table parents_table)

let coqproject_to_dep_graph (project : Project.t) :
    (Dependency_graph.t, Error.t) result =
  let ( let* ) = Result.bind in
  let* output = run_dep_process [ "-f"; project.path ] in
  parse_depf_output output

let diagnostic_to_error (x : Lang.Diagnostic.t) : Error.t =
  let msg_string = Pp.string_of_ppcmds x.message in

  let err = Error.of_string msg_string in
  let err =
    Error.tag_arg err ~tag:"range"
      (Code_range.of_lang_range x.range)
      Code_range.sexp_of_t
  in
  Error.tag_arg err ~tag:"severity" x.severity sexp_of_int

let parse_file (io : Io.CallBack.t) (env : Doc.Env.t) (filepath : string) :
    (Doc.t, Error.t list) result =
  let token = Coq.Limits.Token.create () in

  match Lang.LUri.(File.of_uri (of_string filepath)) with
  | Error _ -> Error [ Error.of_string "Invalid uri" ]
  | Ok uri -> (
      let raw =
        Coq.Compat.Ocaml_414.In_channel.(with_open_bin filepath input_all)
      in

      let doc =
        Fleche.Doc.create ~token ~env ~uri ~languageId:"Coq" ~version:0 ~raw
      in
      let doc = Fleche.Doc.check ~io ~token ~target:Doc.Target.End ~doc () in

      match doc.completed with
      | Yes _ -> Ok doc
      | Stopped _ ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing stopped" in
          Error (err :: List.map diagnostic_to_error errors)
      | Failed _ ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing failed" in
          Error (err :: List.map diagnostic_to_error errors))
