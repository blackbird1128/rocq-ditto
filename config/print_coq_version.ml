let () =
  let line =
    let ic = Unix.open_process_in "coqc --print-version" in
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
