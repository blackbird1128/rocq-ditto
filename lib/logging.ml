(** log a line to a file *)
let log_to_file filename line =
  let oc = open_out_gen [ Open_append; Open_creat ] 0o666 filename in
  output_string oc (line ^ "\n");
  close_out oc
