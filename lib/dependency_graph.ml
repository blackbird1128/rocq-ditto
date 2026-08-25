type t = (string, string list) Hashtbl.t

let of_parents_table (parents : (string, string list) Hashtbl.t) : t = parents
let of_seq (seq : (string * string list) Seq.t) : t = Hashtbl.of_seq seq
let to_seq (graph : t) : (string * string list) Seq.t = Hashtbl.to_seq graph

let in_graph (filename : string) (graph : t) : bool =
  Hashtbl.fold
    (fun file neighbors acc ->
      acc || String.equal filename file || List.mem filename neighbors)
    graph false

let get_file_dependencies (filename : string) (dep_graph : t) :
    (string list, Error.t) result =
  let rec aux filename : string list =
    let curr_deps =
      match Hashtbl.find_opt dep_graph filename with
      | Some deps -> deps
      | None -> []
    in
    curr_deps @ List.concat_map aux curr_deps
  in

  if in_graph filename dep_graph then Ok (aux filename |> List_utils.dedup)
  else Error.format_to_or_error "file %S isn't in the dependency graph" filename

let build_outdegrees (deps : t) : (string, int) Hashtbl.t =
  let outdeg = Hashtbl.create 128 in
  Hashtbl.iter
    (fun node neighbors ->
      Hashtbl.replace outdeg node (List.length neighbors);
      List.iter
        (fun b -> if not (Hashtbl.mem outdeg b) then Hashtbl.add outdeg b 0)
        neighbors)
    deps;
  outdeg

let build_dependents (deps : t) : (string, string list) Hashtbl.t =
  let dependents = Hashtbl.create 128 in
  Hashtbl.iter
    (fun a prereqs ->
      List.iter
        (fun b ->
          let lst = Hashtbl.find_opt dependents b |> Option.default [] in
          Hashtbl.replace dependents b (a :: lst))
        prereqs)
    deps;
  Hashtbl.iter
    (fun a neighbors ->
      List.iter
        (fun x ->
          if Hashtbl.mem dependents x then () else Hashtbl.add dependents x [])
        (a :: neighbors))
    deps;
  dependents

let to_dot_format (graph : t) : string =
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
