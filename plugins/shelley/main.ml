open Fleche
open Ditto
open Ditto.Syntax_node
open Ditto.Proof_tree
open Ditto.Diagnostic_utils

let sexp_of_syntax_node (x : syntaxNode) : Sexplib.Sexp.t =
  let open Sexplib in
  Sexp.(Atom x.repr)

let sexp_of_proof_tree (x : syntaxNode nary_tree) =
  Proof_tree.sexp_of_nary_tree sexp_of_syntax_node x

let rec simplify sexp =
  let open Sexplib.Sexp in
  match sexp with
  | List [ x ] -> simplify x
  | List xs -> List (List.map simplify xs)
  | Atom _ as a -> a

let rec print_tree ?(prefix = "") sexp =
  let open Sexplib.Sexp in
  let rec aux prefix sexp =
    match sexp with
    | Atom s -> Printf.printf "%s%s\n" prefix s
    | List lst ->
        let len = List.length lst in
        List.iteri
          (fun i x ->
            let is_last = i = len - 1 in
            let branch = if is_last then "└── " else "├── " in
            let next_prefix =
              if is_last then prefix ^ "    " else prefix ^ "│   "
            in
            match x with
            | Atom s -> Printf.printf "%s%s%s\n" prefix branch s
            | List _ ->
                Printf.printf "%s%s()\n" prefix branch;
                aux next_prefix x)
          lst
  in
  aux prefix (simplify sexp)

let neat_compile ~io ~token:_ ~(doc : Doc.t) =
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in

  let diags = List.concat_map (fun (x : Doc.Node.t) -> x.diags) doc.nodes in
  let errors = List.filter Lang.Diagnostic.is_error diags in

  let first_errors = List.filteri (fun i _ -> i < 5) errors in

  print_endline ("compiling " ^ uri_str ^ " ...");
  match doc.completed with
  | Doc.Completion.Stopped range_stop ->
      prerr_endline ("parsing stopped at " ^ Lang.Range.to_string range_stop);
      print_diagnostics first_errors
  | Doc.Completion.Failed range_failed ->
      prerr_endline ("parsing failed at " ^ Lang.Range.to_string range_failed);
      print_diagnostics first_errors
  | Doc.Completion.Yes _ -> (
      if List.length errors != 0 then print_diagnostics first_errors
      else
        let parsed_document = Coq_document.parse_document doc in
        let proofs = Coq_document.get_proofs parsed_document |> Result.get_ok in

        let steps =
          List.fold_left
            (fun step_acc proof ->
              let steps =
                Transformations.admit_proof parsed_document proof
                |> Result.get_ok
              in
              steps @ step_acc)
            [] proofs
        in
        let res =
          Coq_document.apply_transformations_steps steps parsed_document
          |> Result.get_ok
        in

        let proof_trees =
          List.map (Runner.treeify_proof res)
            (Coq_document.get_proofs res |> Result.get_ok)
        in

        List.iter
          (fun tree -> print_tree (sexp_of_proof_tree (Result.get_ok tree)))
          proof_trees;

        (* let remove_steps = *)
        (*   List.map Transformations.remove_random_step res |> Result.get_ok *)
        (* in *)
        let res =
          Transformations.apply_proof_tree_transformation
            Transformations.admit_branch_at_error res
        in

        match res with
        | Ok res ->
            let filename = Filename.remove_extension uri_str ^ "_bis.v" in
            print_endline
              ("All transformations applied, writing to file" ^ filename);

            let out = open_out filename in
            Result.fold ~ok:(output_string out)
              ~error:(fun e -> print_endline (Error.to_string_hum e))
              (Coq_document.dump_to_string res)
        | Error err -> print_endline (Error.to_string_hum err))

let main () = Theory.Register.Completed.add neat_compile
let () = main ()
