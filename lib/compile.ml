open Fleche
open CoqProject_file

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

let rec find_coqproject_dir (dir : string) : string option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if
    Sys.file_exists (Filename.concat dir coqproject_filename)
    || Sys.file_exists (Filename.concat dir rocqproject_filename)
  then Some dir
  else if dir = "/" || dir = "." then None
  else find_coqproject_dir (Filename.dirname dir)

let rec find_coqproject_file (dir : string) : string option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some (Filename.concat dir coqproject_filename)
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some (Filename.concat dir rocqproject_filename)
  else if dir = "/" || dir = "." then None
  else find_coqproject_file (Filename.dirname dir)

let rec find_coqproject_dir_and_file (dir : string) : (string * string) option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some (dir, coqproject_filename)
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some (dir, rocqproject_filename)
  else if dir = "/" || dir = "." then None
  else find_coqproject_dir_and_file (Filename.dirname dir)

let get_workspace_folder (filepath : string) : string option =
  let dirname = Filename.dirname filepath in
  find_coqproject_dir dirname

let read_all ic =
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  loop []

let coqproject_sorted_files (coqproject_file : string) :
    (string list, Error.t) result =
  let cmd = Printf.sprintf "rocq dep -f %s -sort" coqproject_file in
  let ic = Unix.open_process_in cmd in
  let lines = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 ->
      Ok
        (List.filter
           (fun x -> String.length x > 0)
           (String.split_on_char ' ' (List.hd lines)))
  | Unix.WEXITED n ->
      Error.string_to_or_error_err
        (Printf.sprintf "coqdep exited with %d; output:\n%s" n
           (String.concat "\n" lines))
  | _ -> Error.string_to_or_error_err "coqdep terminated abnormally"

let compile_file (io : Io.CallBack.t) (env : Doc.Env.t) (filepath : string) :
    (Doc.t, Error.t) result =
  let token = Coq.Limits.Token.create () in

  match Lang.LUri.(File.of_uri (of_string filepath)) with
  | Error _ -> Error.string_to_or_error_err "Invalid uri"
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
      | Stopped stopped_range ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing stopped" in
          Error err
      | Failed failed_range ->
          let diags =
            List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes
          in
          let errors = List.filter Lang.Diagnostic.is_error diags in
          let err = Error.of_string "Parsing failed" in
          Error err)
