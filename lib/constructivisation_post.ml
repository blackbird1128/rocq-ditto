open Transforming_step
open Constructivisation_utils

type proof_replace = {
  proof_filename : string;
  proof_name : string;
  new_proof_file : string;
  new_proof_aux : string list;
}

let ( let* ) = Result.bind

let get_proof_local_requirements (proof_doc : Rocq_document.t) (p : Proof.t) :
    (string list, Error.t) result =
  let* proof_term_opt = Proof_term.of_proof proof_doc p in
  match proof_term_opt with
  | Some proof_term ->
      let doc_modname =
        Filename.basename proof_doc.filename |> Filename.chop_extension
      in
      let name_refs = Proof_term.collect_names proof_term in

      Ok
        (List.filter_map
           (Proof_term.constant_name_in_module ~module_name:doc_modname)
           name_refs)
  | None -> Error.string_to_or_error "Could not find a proof term for the proof"

let proof_replace_to_steps (orig_doc : Rocq_document.t) (pr : proof_replace) :
    (Transforming_step.t list, Error.t) result =
  let orig_doc_filename = Filename.basename orig_doc.filename in

  if String.equal orig_doc_filename pr.proof_filename then (
    let token = Coq.Limits.Token.create () in
    let orig_doc_modname =
      Filename.basename orig_doc.filename |> Filename.chop_extension
    in
    Printf.eprintf "orig doc modname: %s\n" orig_doc_modname;

    let filepath =
      Filename.concat
        "../geocoq-support/theories/Constructive/Stability_proofs/"
        pr.new_proof_file
    in

    let* pr_doc =
      Rocq_document.parse_template ~root_state:orig_doc.root_state filepath
    in

    let pr_doc_non_self_imports =
      List.filter
        (fun node ->
          match Syntax_node.synterp_expr node with
          (* pray that someone doesnt import two things at once :] *)
          | Some (VernacRequire (_, _, [ libname ])) ->
              let l, _ = libname in
              let basename = Libnames.qualid_basename l in
              not (String.equal orig_doc_modname (Names.Id.to_string basename))
          | _ -> false)
        pr_doc.elements
    in

    let* pr_aux_proofs =
      List_utils.map_result
        (fun aux_name ->
          match Rocq_document.proof_with_name_opt aux_name pr_doc with
          | Ok (Some proof) -> Ok proof
          | _ ->
              Error.format_to_or_error
                "Could not find required auxiliary proof %S for proof %S"
                aux_name pr.proof_name)
        pr.new_proof_aux
    in

    let* pr_proof =
      match Rocq_document.proof_with_name_opt pr.proof_name pr_doc with
      | Ok (Some proof) -> Ok proof
      | _ ->
          Error.format_to_or_error "Could not find replacement proof %S in %S"
            pr.proof_name pr.new_proof_file
    in

    let* replaced_proof =
      match Rocq_document.proof_with_name_opt pr.proof_name orig_doc with
      | Ok (Some proof) -> Ok proof
      | _ ->
          Error.format_to_or_error "Could not find the proof %S in %S"
            pr.proof_name orig_doc.filename
    in

    let* replaced_proof_sections =
      Rocq_document.sections_of_node orig_doc replaced_proof.closing.node
    in
    let replaced_proof_inner_section_opt =
      replaced_proof_sections |> List_utils.head_opt
    in

    let section_close_opt =
      Option.map
        (fun (inner_section : Names.variable) ->
          let inner_section_str = Names.Id.to_string inner_section in
          Option.map snd
            (Rocq_document.get_section_nodes orig_doc inner_section_str))
        replaced_proof_inner_section_opt
      |> Option.flatten
    in

    let* section_close =
      match section_close_opt with
      | Some section_close -> Ok section_close
      | None ->
          List_utils.last orig_doc.elements
          |> Option_utils.to_result
               ~none:
                 (Error.string_to_or_error
                    "Got an empty document (this should not happen)")
    in

    let* before_section_close_state =
      Runner.get_state_before orig_doc section_close token
    in

    let synthetic_proof_name = pr.proof_name ^ "__synth" in
    let* virtual_proof_opening =
      Syntax_node.rename_theorem_node pr.proof_name synthetic_proof_name
        pr_proof.opening
    in

    let pr_aux_proofs_nodes = List.concat_map Proof.all_nodes pr_aux_proofs in

    let* synthetic_proof =
      Proof.make ~opening:virtual_proof_opening ~body:pr_proof.proof_steps
        ~closing_node:pr_proof.closing.node
    in

    let* state_after_executing_new_proof =
      Runner.run_nodes before_section_close_state token
        (pr_doc_non_self_imports @ pr_aux_proofs_nodes
        @ Proof.all_nodes synthetic_proof)
    in
    let* new_proof_globref =
      Runner.resolve_global ~token state_after_executing_new_proof
        synthetic_proof_name
    in
    let* new_proof_constant =
      Proof_term.constant_of_global_ref new_proof_globref
      |> Option_utils.to_result
           ~none:(Error.string_to_or_error "Should not happen 1")
    in
    let* new_proof_proof_term_opt =
      Proof_term.get ~token state_after_executing_new_proof new_proof_constant
    in
    let* new_proof_proof_term =
      new_proof_proof_term_opt
      |> Option_utils.to_result
           ~none:(Error.string_to_or_error "should not happen 2")
    in

    let name_refs = Proof_term.collect_names new_proof_proof_term in

    let previous_proof_names =
      List.filter_map
        (Proof_term.constant_name_in_module ~module_name:orig_doc_modname)
        name_refs
    in

    Printf.eprintf "previous_proofs:\n";
    List.iter (fun p -> Printf.eprintf "%s\n" p) previous_proof_names;

    let* orig_doc_proofs = Rocq_document.get_proofs orig_doc in

    let previous_proofs =
      get_proofs_named orig_doc_proofs previous_proof_names
    in
    (* here the previous proofs are ordered so the last one is the anchor point *)
    let* anchor_node =
      match List_utils.last previous_proofs with
      | Some last_proof -> Ok last_proof.closing.node
      | None ->
          List_utils.last orig_doc.elements
          |> Option_utils.to_result
               ~none:(Error.string_to_or_error "should not happen 3")
    in
    Printf.eprintf "anchor node: %s\n" (Syntax_node.repr anchor_node);

    let* attach_new_require_steps =
      List_utils.concat_map_result
        (fun node -> attach_node_after_requires orig_doc node)
        pr_doc_non_self_imports
    in

    let aux_proofs_attach_steps, replacement_anchor_id =
      let steps_rev, anchor_id =
        List.fold_left
          (fun (steps_rev, anchor_id) (node : Syntax_node.t) ->
            (Attach (node, LineAfter, anchor_id) :: steps_rev, node.id))
          ([], anchor_node.id) pr_aux_proofs_nodes
      in
      (List.rev steps_rev, anchor_id)
    in

    let replacement_proof_attach_steps =
      let steps_rev, _ =
        List.fold_left
          (fun (steps_rev, anchor_id) (node : Syntax_node.t) ->
            (Attach (node, LineAfter, anchor_id) :: steps_rev, node.id))
          ([], replacement_anchor_id) (Proof.all_nodes pr_proof)
      in
      List.rev steps_rev
    in

    let remove_original_proof_steps =
      List.map
        (fun (n : Syntax_node.t) -> Remove n.id)
        (Proof.all_nodes replaced_proof)
    in

    Ok
      (attach_new_require_steps @ aux_proofs_attach_steps
     @ replacement_proof_attach_steps @ remove_original_proof_steps))
  else Ok []

let constructivisation_post (doc : Rocq_document.t) :
    (Transforming_step.t list, Error.t) result =
  let sym_point_replace =
    {
      proof_filename = "Ch07_midpoint.v";
      proof_name = "symmetric_point_construction";
      new_proof_file = "SymPoint.v";
      new_proof_aux = [ "ext" ];
    }
  in
  proof_replace_to_steps doc sym_point_replace
