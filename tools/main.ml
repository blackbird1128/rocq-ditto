open Ditto

let get_dependencies () =
  if Array.length Sys.argv != 2 then (
    Printf.eprintf "Usage: get-dependencies file";
    exit 1)
  else
    let filename = Sys.argv.(1) in
    if Filesystem.is_directory filename then (
      Printf.eprintf "Please provide a file, not a directory";
      exit 1)
    else if not (Sys.file_exists filename) then (
      Printf.eprintf "Please provide an existing file";
      exit 1)
    else ()

let () = get_dependencies ()
