let find_executable names =
  let rec aux = function
    | [] -> None
    | name :: rest ->
        let cmd = Printf.sprintf "command -v %s >/dev/null 2>&1" name in
        let status = Sys.command cmd in
        if status = 0 then Some name else aux rest
  in
  aux names

let () =
  let exe =
    match find_executable [ "rocq"; "coqc" ] with
    | Some e -> e
    | None -> failwith "Neither 'rocq' nor 'coqc' executable found in PATH"
  in

  let line =
    let ic =
      if exe = "coqc" then Unix.open_process_in "coqc --print-version"
      else Unix.open_process_in "rocq c --print-version"
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
  Printf.printf
    "let major_version = %d\nlet minor_version = %d\nlet patch_version = %d\n"
    major minor patch;
  if major >= 9 then
    print_endline
      "let executable_name = \"rocq\"\nlet dep_executable = \"rocq dep\""
  else
    print_endline
      "let executable_name = \"coq\"\nlet dep_executable = \"coqdep\""
