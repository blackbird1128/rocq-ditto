open Fleche
open Sexplib.Std

let dep_program, dep_fixed_args = Rocq_version.dep_command
let dep_program_repr = String.concat " " (dep_program :: dep_fixed_args)

let rec find_coqproject_dir_and_file (dir : string) : (string * string) option =
  let coqproject_filename = "_CoqProject" in
  let rocqproject_filename = "_RocqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then
    Some (dir, coqproject_filename)
  else if Sys.file_exists (Filename.concat dir rocqproject_filename) then
    Some (dir, rocqproject_filename)
  else if dir = "/" || dir = "." then None
  else find_coqproject_dir_and_file (Filename.dirname dir)

let find_coqproject_dir (dir : string) : string option =
  Option.map fst (find_coqproject_dir_and_file dir)

let find_coqproject_file (dir : string) : string option =
  Option.map snd (find_coqproject_dir_and_file dir)

let resolve_project_path (path : string) : (string * string, Error.t) result =
  if not (Sys.file_exists path) then
    Error.string_to_or_error
      "Please provide a path to an existing file or directory"
  else if Filesystem.is_directory path then
    match find_coqproject_dir_and_file path with
    | None -> Error.string_to_or_error "No _CoqProject or _RocqProject found"
    | Some (dir, filename) -> Ok (dir, filename)
  else
    match Filename.basename path with
    | "_CoqProject" | "_RocqProject" ->
        Ok (Filename.dirname path, Filename.basename path)
    | _ ->
        Error.string_to_or_error
          "Please provide a directory or a project file path "

let read_all (ic : in_channel) : string list =
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file -> List.rev acc
  in
  loop []

let open_dep_process (args : string list) =
  Unix.open_process_args_in dep_program
    (Array.of_list ((dep_program :: dep_fixed_args) @ args))

let coqproject_sorted_files (coqproject_file : string) :
    (string list, Error.t) result =
  let ic = open_dep_process [ "-f"; coqproject_file; "-sort" ] in

  let lines = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 -> (
      match lines with
      | [] ->
          Error.format_to_or_error "Executing %s returned an empty output"
            dep_program_repr
      | [ first_line ] -> Ok (String_utils.split_words first_line)
      | _ :: _ ->
          Error.format_to_or_error
            "Executing %s returned more than a single line of output, \
             unexpected format"
            dep_program_repr)
  | Unix.WEXITED n ->
      Error.format_to_or_error "%s exited with %d; output:\n%s" dep_program_repr
        n (String.concat "\n" lines)
  | _ -> Error.format_to_or_error "%s terminated abnormally" dep_program_repr

type dependency_graph = (string, string list) Hashtbl.t

let coqproject_to_dep_graph (coqproject_file : string) :
    (dependency_graph, Error.t) result =
  let ic = open_dep_process [ "-f"; coqproject_file ] in
  let lines = read_all ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 ->
      let re = Re.compile (Re.str "required_vo:") in
      let split = List.map (Re.split_delim re) lines in
      let filenames =
        List.map
          (fun x ->
            let hd = List.hd x in
            let filename_vo = String_utils.split_words hd |> List.hd in
            let filename =
              String.sub filename_vo 0 (String.length filename_vo - 1)
            in
            filename)
          split
      in
      let tails =
        List.map
          (fun x ->
            let tl = List.nth x 1 in
            String_utils.split_words tl)
          split
      in

      let tails_filenames =
        List.map
          (fun l ->
            List.filter_map
              (fun x ->
                if String.ends_with ~suffix:".vo" x then
                  Some (String.sub x 0 (String.length x - 1))
                else if String.ends_with ~suffix:".v" x then Some x
                else None)
              l)
          tails
      in

      let parents_table = Hashtbl.create (List.length filenames) in
      List.iteri
        (fun idx x ->
          let matching_tail =
            List.nth tails_filenames idx
            |> List.filter (fun elem_tl -> not (String.equal elem_tl x))
            (* avoid making a recursive parent table *)
          in
          Hashtbl.add parents_table x matching_tail)
        filenames;

      Ok parents_table
  | Unix.WEXITED n ->
      Error.format_to_or_error "%s exited with %d; output:\n%s" dep_program_repr
        n (String.concat "\n" lines)
  | _ -> Error.format_to_or_error "%s terminated abnormally" dep_program_repr

let coqproject_to_project_args (coqproject_file : string) :
    (string list, Error.t) result =
  let ( let* ) = Result.bind in
  let open CoqProject_file in
  let* proj =
    try Ok (read_project_file ~warning_fn:(fun _ -> ()) coqproject_file) with
    | Parsing_error err_msg | UnableToOpenProjectFile err_msg ->
        Error.string_to_or_error err_msg
    | exn -> Error (Error.of_exn exn)
  in
  Ok (coqtop_args_from_project proj)

let depgraph_to_dot_format (graph : dependency_graph) : string =
  let buf = Buffer.create (Hashtbl.length graph * 16) in
  Buffer.add_string buf "digraph G {\n";
  Buffer.add_string buf
    " rankdir=RL;\n\
    \ splines=true;\n\
    \ overlap=false;\n\
    \ concentrate=true;\n\
    \ node [shape=box, fontsize=10];\n";
  Hashtbl.iter
    (fun file neighbors ->
      let file_without_leading_slash = String_utils.remove_prefix file "/" in
      match neighbors with
      | [] ->
          Buffer.add_string buf
            (Printf.sprintf "\"%s\";\n" file_without_leading_slash)
      | neighbors ->
          List.iter
            (fun x ->
              let x_without_leading_slash = String_utils.remove_prefix x "/" in
              Buffer.add_string buf
                (Printf.sprintf "\"%s\" -> \"%s\";\n" file_without_leading_slash
                   x_without_leading_slash))
            neighbors)
    graph;
  Buffer.add_string buf "}";
  Buffer.contents buf

let get_file_dependencies (filename : string) (dep_graph : dependency_graph) :
    string list =
  let rec aux filename : string list =
    let curr_deps =
      match Hashtbl.find_opt dep_graph filename with
      | Some deps -> deps
      | None -> []
    in
    let deps = List.concat_map aux curr_deps in
    curr_deps @ deps
  in
  aux filename |> List_utils.dedup

let build_outdegrees (deps : ('a, 'a list) Hashtbl.t) : ('a, int) Hashtbl.t =
  let indeg = Hashtbl.create 128 in
  Hashtbl.iter
    (fun a prereqs ->
      Hashtbl.replace indeg a (List.length prereqs);
      List.iter
        (fun b -> if not (Hashtbl.mem indeg b) then Hashtbl.add indeg b 0)
        prereqs)
    deps;
  indeg

let build_dependents (deps : ('a, 'a list) Hashtbl.t) : ('a, 'a list) Hashtbl.t
    =
  let rev = Hashtbl.create 128 in
  Hashtbl.iter
    (fun a prereqs ->
      List.iter
        (fun b ->
          let lst = Hashtbl.find_opt rev b |> Option.default [] in
          Hashtbl.replace rev b (a :: lst))
        prereqs)
    deps;
  Hashtbl.iter
    (fun a _ -> if Hashtbl.mem rev a then () else Hashtbl.add rev a [])
    deps;
  rev

let diagnostic_to_error (x : Lang.Diagnostic.t) : Error.t =
  let msg_string = Pp.string_of_ppcmds x.message in

  let err = Error.of_string msg_string in
  let err =
    Error.tag_arg err ~tag:"range"
      (Code_range.code_range_from_lang_range x.range)
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
