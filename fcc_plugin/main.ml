open Fleche
open Petanque
open Ditto
open Ditto.Proof
open Stack

let parse_json_list json_repr =
  match json_repr with
  | `List elements -> elements
  | _ -> failwith "Expected a JSON list"

let get_proof_state start_result =
  match start_result with
  | Ok run_result ->
      (* Access the proof state inside the Run_result record *)
      print_endline "Proof state retrieved successfully.";
      run_result
  | Error err ->
      (* Handle the error *)
      Printf.eprintf "Error: %s\n" (Agent.Error.to_string err);
      raise (Failure "Failed to start proof")

(** count the number of goalf of a state *)
let count_goals (token: Coq.Limits.Token.t) (st: Agent.State.t) : int =
    let goals = Agent.goals token st in
    match goals with 
    | Ok (Some reified_goals) ->
      List.length reified_goals.goals
    | Ok None -> 0
    | Error _ -> 0

type 'a nary_tree = Node of 'a * 'a nary_tree list | Leaf

let rec print_tree tree indent =
  match tree with
  | Leaf -> Printf.printf "%sLeaf\n" indent
  | Node (value, children) ->
      Printf.printf "%sNode(%d)\n" indent value;
      List.iter (fun child -> print_tree child (indent ^ "  ")) children

let treeify_proof_rec (token : Coq.Limits.Token.t) (st : Agent.State.t)
    (tactics : string list) (tree: string nary_tree) (num_goals: int) =
  match tactics with 
  | [] -> Leaf
  | tactic::tail -> 
    let state = Agent.run ~token ~st ~tac:tactic () in
    let agent_state = get_proof_state state in
    let proof_state = agent_state.st in
    let new_goals = count_goals token proof_state in


let treeify_proof (p : proof) (doc : Doc.t) : string nary_tree =
  let token = Coq.Limits.Token.create () in
  let proof_name_opt = Proof.get_proof_name p in
  let proof_name = Option.get proof_name_opt in
  let tactics = Proof.get_tactics p in
  let tree = Leaf in
  let init_state = Agent.start ~token ~doc ~thm:proof_name () in
  
  treeify_proof_rec token init_state tactics tree 1

let dump_ast ~io ~token:_ ~(doc : Doc.t) =
  Fl_dynload.load_packages [ "coq-lsp.serlib.ltac" ];
  let uri = doc.uri in
  let uri_str = Lang.LUri.File.to_string_uri uri in
  let lvl = Io.Level.Info in
  Io.Report.msg ~io ~lvl "[ast plugin] dumping ast for %s ..." uri_str;
  let asts = Doc.asts doc in
  let parsed_document = Coq_document.parse_document asts in

  (* print_string
     (String.concat "\n"
        (List.map
           (fun x -> Coq_document.coq_element_to_string x)
           parsed_document)); *)
  let out_file_j = Lang.LUri.File.to_string_file uri ^ ".astdump.json" in
  let proofs = Coq_document.get_proofs parsed_document in
  let theorems = Coq_document.get_theorem_names parsed_document in
  List.iter print_endline theorems;

  let th = List.hd theorems in
  let tactics = Proof.get_tactics (List.hd proofs) in
  List.iter print_endline tactics;

  let out_chan = open_out out_file_j in
  Yojson.Safe.pretty_to_channel out_chan
    (`List
      (List.map (fun (x : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson x.v) asts));

  let token = Coq.Limits.Token.create () in
  let result = Agent.start ~token ~doc ~thm:th () in
  let state = get_proof_state result in
  let proof_state = state.st in
  match Agent.goals ~token ~st:proof_state with
  | Ok (Some reified_goals) ->
      let num_goals = count_goals reified_goals in
      Printf.printf "Number of goals: %d\n" num_goals
      (* Access and display goals *)
  | Ok None -> Printf.printf "No goals remaining!\n"
  | Error e ->
      Printf.printf "Error retrieving goals: %s\n" (Agent.Error.to_string e)

(* let first_proof = List.nth proofs 0 in
   let infos = Option.get first_proof.proposition.ast_info in
   let names = Proof.get_names infos in
   List.iter print_endline names;

   let steps = Proof.get_proof_steps first_proof in
   print_endline ("length steps:" ^ string_of_int (List.length steps));
   List.iter
     (fun x ->
       if Option.has_some x then print_string (Option.get x) else print_string "")
     steps;
   () *)

(* let coq_asts =
     List.map (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v) asts
   in

   let out_file_j = Lang.LUri.File.to_string_file uri ^ ".json.astdump" in

   (* let coq_yojsons = *)
   (*   List.map (fun (x : Doc.Node.Ast.t) -> Lsp.JCoq.Ast.to_yojson x.v) asts *)
   (* in *)
   (* let ch_out = open_out out_file_j in *)
   let json_obj = Yojson.Safe.from_file out_file_j in
   let json_list = parse_json_list json_obj in
   let json_ast_results =
     List.map (fun x -> Lsp.JCoq.Ast.of_yojson x) json_list
   in
   let json_asts =
     List.map (fun x -> Coq.Ast.to_coq (Result.get_ok x)) json_ast_results
   in
   let () = assert (coq_asts = json_asts) in

   let token = Coq.Limits.Token.create () in
   let result = Agent.start ~token ~doc ~thm:"modus_ponens" () in
   let state = get_proof_state result in
   let proof_state = state.st in
   match Agent.goals ~token ~st:proof_state with
   | Ok (Some reified_goals) ->
       let num_goals = count_goals reified_goals in
       Printf.printf "Number of goals: %d\n" num_goals
       (* Access and display goals *)
   | Ok None -> Printf.printf "No goals remaining!\n"
   | Error e ->
       Printf.printf "Error retrieving goals: %s\n" (Agent.Error.to_string e) *)

(* (fun x -> *)
(*   Ppvernac.pr_vernac (Coq.Ast.to_coq *)
(*   |> Pp.string_of_ppcmds |> print_endline) *)
(*   asts; *)
(* Output json *)
(* let json_coq = Lsp.JCoq.Ast.to_yojson (List.nth asts 0).v in *)

let main () = Theory.Register.Completed.add dump_ast
let () = main ()
