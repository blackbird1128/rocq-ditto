open Transforming_step
open Constructivisation_utils

type proof_replace = {
  proof_filename : string;
  proof_name : string;
  new_proof_file : string;
  new_proof_aux : string list;
  new_stability_proofs : string list;
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

let attach_after_anchor (anchor_id : Uuidm.t) (nodes : Syntax_node.t list) :
    Transforming_step.t list * Uuidm.t =
  let steps, next_anchor =
    List.fold_left
      (fun (steps_rev, anchor_id) (node : Syntax_node.t) ->
        (Attach (node, LineAfter, anchor_id) :: steps_rev, node.id))
      ([], anchor_id) nodes
  in
  (List.rev steps, next_anchor)

let get_node_section_close (doc : Rocq_document.t) (node : Syntax_node.t) :
    (Syntax_node.t, Error.t) result =
  let* node_sections = Rocq_document.sections_of_node doc node in
  let node_inner_section = node_sections |> List_utils.head_opt in
  let section_close_opt =
    Option.map
      (fun (inner_section : Names.variable) ->
        let inner_section_str = Names.Id.to_string inner_section in
        Option.map snd (Rocq_document.get_section_nodes doc inner_section_str))
      node_inner_section
    |> Option.flatten
  in
  match section_close_opt with
  | Some section_close -> Ok section_close
  | None ->
      List_utils.last doc.elements
      |> Option_utils.to_result
           ~none:(Error.string_to_or_error "Got an empty document as input")

let make_synthetic_proof (proof : Proof.t) : (Proof.t, Error.t) result =
  match Proof.get_proof_name proof with
  | Some proof_name ->
      let proof_name_str = Names.Id.to_string proof_name in
      let synthetic_proof_name = proof_name_str ^ "__synth" in
      let* synthetic_proof_opening =
        Syntax_node.rename_theorem_node proof_name_str synthetic_proof_name
          proof.opening
      in
      Proof.make ~opening:synthetic_proof_opening ~body:proof.proof_steps
        ~closing_node:proof.closing.node
  | None -> Error.string_to_or_error "Cannot create a synthetic anonymous proof"

let make_stab_hint (proof_name : string) =
  let hint_str =
    Printf.sprintf "#[global] Hint Resolve %s : stable_prop." proof_name
  in
  Syntax_node.syntax_node_of_string hint_str Code_point.dummy

let get_replacement_proof_proof_term ~(token : Coq.Limits.Token.t)
    (starting_state : Coq.State.t) (synth_proof : Proof.t)
    (synth_proof_imports : Syntax_node.t list)
    (synth_proof_aux_proofs : Proof.t list) =
  let* synth_proof_name =
    Proof.get_proof_name synth_proof
    |> Option_utils.to_result
         ~none:(Error.string_to_or_error "Got an anonymous synthetic proof")
  in
  let synth_proof_name_str = Names.Id.to_string synth_proof_name in

  let pr_aux_proofs_nodes =
    List.concat_map Proof.all_nodes synth_proof_aux_proofs
  in

  let* state_after_executing_new_proof =
    Runner.run_nodes starting_state token
      (synth_proof_imports @ pr_aux_proofs_nodes @ Proof.all_nodes synth_proof)
  in
  let* new_proof_globref =
    Runner.resolve_global ~token state_after_executing_new_proof
      synth_proof_name_str
  in
  let* new_proof_constant =
    Proof_term.constant_of_global_ref new_proof_globref
    |> Option_utils.to_result
         ~none:(Error.string_to_or_error "Should not happen 1")
  in
  let* new_proof_proof_term_opt =
    Proof_term.get ~token state_after_executing_new_proof new_proof_constant
  in

  new_proof_proof_term_opt
  |> Option_utils.to_result
       ~none:(Error.string_to_or_error "should not happen 2")

let proof_replace_to_steps (orig_doc : Rocq_document.t) (pr : proof_replace) :
    (Transforming_step.t list, Error.t) result =
  let orig_doc_filename = Filename.basename orig_doc.filename in

  if String.equal orig_doc_filename pr.proof_filename then
    let token = Coq.Limits.Token.create () in
    let orig_doc_modname =
      Filename.basename orig_doc.filename |> Filename.chop_extension
    in

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
    let pr_aux_proofs_nodes = List.concat_map Proof.all_nodes pr_aux_proofs in

    let* pr_proof =
      match Rocq_document.proof_with_name_opt pr.proof_name pr_doc with
      | Ok (Some proof) -> Ok proof
      | _ ->
          Error.format_to_or_error "Could not find replacement proof %S in %S"
            pr.proof_name pr.new_proof_file
    in

    let* pr_stability_proofs =
      List_utils.map_result
        (fun aux_name ->
          match Rocq_document.proof_with_name_opt aux_name pr_doc with
          | Ok (Some proof) -> Ok proof
          | _ ->
              Error.format_to_or_error
                "Could not find required stability proof %S for proof %S"
                aux_name pr.proof_name)
        pr.new_stability_proofs
    in

    let* pr_stability_hints =
      List_utils.map_result
        (fun proof ->
          match Proof.get_proof_name proof with
          | Some proof_name ->
              let proof_name_str = Names.Id.to_string proof_name in
              make_stab_hint proof_name_str
          | None ->
              Error.format_to_or_error
                "Could not find a name for the stability proof (this should \
                 not happen")
        pr_stability_proofs
    in

    let* replaced_proof =
      match Rocq_document.proof_with_name_opt pr.proof_name orig_doc with
      | Ok (Some proof) -> Ok proof
      | _ ->
          Error.format_to_or_error "Could not find the proof %S in %S"
            pr.proof_name orig_doc.filename
    in

    let* section_close =
      get_node_section_close orig_doc replaced_proof.closing.node
    in

    let* before_section_close_state =
      Runner.get_state_before orig_doc section_close token
    in

    let* synthetic_proof = make_synthetic_proof pr_proof in

    let* new_proof_proof_term =
      get_replacement_proof_proof_term ~token before_section_close_state
        synthetic_proof pr_doc_non_self_imports pr_aux_proofs
    in

    let name_refs = Proof_term.collect_names new_proof_proof_term in

    let previous_proof_names =
      List.filter_map
        (Proof_term.constant_name_in_module ~module_name:orig_doc_modname)
        name_refs
    in

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

    let* attach_new_require_steps =
      List_utils.concat_map_result
        (fun node -> attach_node_after_requires orig_doc node)
        pr_doc_non_self_imports
    in

    let aux_proofs_attach_steps, replacement_anchor_id =
      attach_after_anchor anchor_node.id pr_aux_proofs_nodes
    in

    let replacement_proof_attach_steps, replaced_proof_anchor =
      attach_after_anchor replacement_anchor_id (Proof.all_nodes pr_proof)
    in

    let stability_proofs_attach_steps, _ =
      attach_after_anchor replaced_proof_anchor
        (List.concat_map Proof.all_nodes pr_stability_proofs)
    in

    let hints_attach_steps, _ =
      attach_after_anchor section_close.id pr_stability_hints
    in

    let remove_original_proof_steps =
      List.map
        (fun (n : Syntax_node.t) -> Remove n.id)
        (Proof.all_nodes replaced_proof)
    in

    Ok
      (attach_new_require_steps @ aux_proofs_attach_steps
     @ replacement_proof_attach_steps @ stability_proofs_attach_steps
     @ remove_original_proof_steps @ hints_attach_steps)
  else Ok []

let constructivisation_post (doc : Rocq_document.t) :
    (Transforming_step.t list, Error.t) result =
  let sym_point_replace =
    {
      proof_filename = "Ch07_midpoint.v";
      proof_name = "symmetric_point_construction";
      new_proof_file = "SymPoint.v";
      new_proof_aux = [ "ext" ];
      new_stability_proofs =
        [
          "rightAngle_stab";
          "perpendicularAt_stab";
          "hypothesis_of_right_saccheri_quadrilaterals_stab";
        ];
    }
  in
  proof_replace_to_steps doc sym_point_replace
