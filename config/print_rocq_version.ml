let is_directory (path : string) : bool =
  try
    let stats = Unix.stat path in
    stats.Unix.st_kind = Unix.S_DIR
  with Unix.Unix_error _ -> String.ends_with ~suffix:Filename.dir_sep path

let find_executable (names : string list) =
  let cur_dir = Sys.getcwd () in
  let local_ocaml_switch_bin_dir = Filename.concat cur_dir "_opam/bin/" in
  if is_directory local_ocaml_switch_bin_dir then
    List.map (Filename.concat local_ocaml_switch_bin_dir) names
    |> List.find_opt (fun x -> Sys.file_exists x && Sys.is_regular_file x)
  else
    let rec aux = function
      | [] -> None
      | name :: rest ->
          let cmd = Printf.sprintf "which %s >/dev/null" name in
          let status = Sys.command cmd in
          if status = 0 then Some name else aux rest
    in
    aux names

let () =
  let exe_path =
    match find_executable [ "rocq"; "coqc" ] with
    | Some e -> e
    | None -> failwith "Neither 'rocq' nor 'coqc' executable found in PATH"
  in
  let exe_name = Filename.basename exe_path in

  let line =
    let ic =
      if exe_name = "coqc" then
        Unix.open_process_in (exe_path ^ " --print-version")
      else Unix.open_process_in (exe_path ^ " c --print-version")
    in
    let l = input_line ic in
    ignore (Unix.close_process_in ic);
    l
  in
  (* Extract the main version, ignoring the second part *)
  let main_version =
    match String.split_on_char ' ' line with
    | main :: _ -> main
    | _ -> failwith "Unexpected coqc version output"
  in
  let major, minor, patch =
    match String.split_on_char '.' main_version with
    | [ maj; min; pat ] ->
        (int_of_string maj, int_of_string min, int_of_string pat)
    | _ -> failwith "Unexpected main coqc version format"
  in
  let opt_comp_format = Array.exists (( = ) "--optcomp") Sys.argv in
  if opt_comp_format then (
    Printf.printf
      "[%%%%define rocq_major_version %d]\n\
       [%%%%define rocq_minor_version %d]\n\
       [%%%%define rocq_patch_version %d]\n\
       [%%%%define rocq_executable_name \"rocq\"]\n"
      major minor patch;
    Printf.printf "[%%%%define rocq_version (%d,%d,%d)]" major minor patch)
  else (
    Printf.printf
      "let major_version = %d\nlet minor_version = %d\nlet patch_version = %d\n"
      major minor patch;
    if major >= 9 then (
      print_endline
        "let executable_name = \"rocq\"\nlet dep_executable = \"rocq dep\"";
      print_endline "let ltac_ext_plugin_name = \"rocq-runtime.plugins.ltac\"";
      print_endline
        "let ltac_funid_plugin_name = \"rocq-runtime.plugins.funind\"")
    else (
      print_endline
        "let executable_name = \"coq\"\nlet dep_executable = \"coqdep\"";
      print_endline "let ltac_ext_plugin_name = \"coq-core.plugins.ltac\"";
      print_endline "let ltac_funid_plugin_name = \"coq-core.plugins.funind\""))
