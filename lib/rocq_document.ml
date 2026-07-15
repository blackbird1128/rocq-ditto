open Proof
open Fleche
open Syntax_node
open Transforming_step

type proof_state = NoProof | ProofOpened

type t = {
  filename : string;
  elements : Syntax_node.t list;
  document_repr : string;
  root_state : Coq.State.t;
}

type remove_method = LeaveBlank | ShiftNode
type shift_method = ShiftVertically | ShiftHorizontally

let pp_coq_document (fmt : Format.formatter) (doc : t) : unit =
  Format.fprintf fmt "filename: %s@ " doc.filename;
  Format.fprintf fmt "elements:@ ";

  List.iter
    (fun node ->
      Format.fprintf fmt "%a %s@ " Code_range.pp node.range (repr node))
      (* see to add id maybe ? *)
    doc.elements;

  Format.fprintf fmt "document repr: %s" doc.document_repr

let get_proofs (doc : t) : (Proof.t list, Error.t) result =
  let rec aux (nodes : Syntax_node.t list) (cur_proof_acc : Syntax_node.t list)
      (proofs_acc : (Proof.t, Error.t) result list) (cur_state : proof_state) :
      (Proof.t, Error.t) result list =
    match nodes with
    | [] -> proofs_acc
    | x :: tail -> (
        if Syntax_node.can_open_proof x then
          aux tail [ x ] proofs_acc ProofOpened
        else if Syntax_node.can_close_proof x then
          if List.is_empty cur_proof_acc then
            aux tail [] proofs_acc
              NoProof (* TODO: proper handling of Program and Obligation *)
          else
            let proof = proof_from_nodes (List.rev (x :: cur_proof_acc)) in
            aux tail [] (proof :: proofs_acc) NoProof
        else
          match cur_state with
          | NoProof -> aux tail [] proofs_acc NoProof
          | ProofOpened -> aux tail (x :: cur_proof_acc) proofs_acc ProofOpened)
  in

  let res = aux doc.elements [] [] NoProof in
  List.rev res |> List_utils.result_all

let node_representation (node : Doc.Node.t) (document : string) : string =
  String.sub document node.range.start.offset
    (node.range.end_.offset - node.range.start.offset)

let get_line_col_positions text pos : Code_point.t =
  let rec aux line col index =
    if index = pos then (line, col, index)
    else if index >= String.length text then (line, col, index)
    else if text.[index] = '\n' then aux (line + 1) 0 (index + 1)
    else aux line (col + 1) (index + 1)
  in

  let line, character, _ = aux 0 0 0 in
  (* Start from line 0, column 0, character 0 *)
  { line; character }

let mark_string_regions (s : string) : bool array =
  let n = String.length s in
  let rec loop i in_string escape acc =
    if i = n then Array.of_list (List.rev acc)
    else
      let c = s.[i] in

      if in_string then
        let acc' = true :: acc in
        if escape then loop (i + 1) true false acc'
        else begin
          match c with
          | '\\' -> loop (i + 1) true true acc'
          | '"' -> loop (i + 1) false false acc'
          | _ -> loop (i + 1) true false acc'
        end
      else
        (* Outside a string *)
        let acc' = false :: acc in
        match c with
        | '"' -> loop (i + 1) true false acc'
        | _ -> loop (i + 1) false false acc'
  in
  loop 0 false false []

let get_comments (content : string) :
    ((string * Code_range.t) list, string) result =
  let explode s =
    List.init (String.length s) (fun idx -> (idx, String.get s idx))
  in
  let repr = explode content in

  let ( let* ) = Result.bind in

  let pairwise lst =
    let rec aux acc = function
      | (a1, p1) :: (a2, p2) :: rest ->
          aux (((a1, p1), (a2, p2)) :: acc) ((a2, p2) :: rest)
      | _ -> List.rev acc
    in
    aux [] lst
  in

  let string_mask = mark_string_regions content in

  let pairs =
    pairwise repr |> List.filter (fun ((i, _), _) -> not string_mask.(i))
  in
  let* _, res =
    List.fold_left
      (fun acc pair ->
        match acc with
        | Ok (stack, res) as acc -> (
            match pair with
            | ((_, '('), (_, '*')) as x -> Ok (x :: stack, res)
            | (idx1, '*'), (idx2, ')') -> (
                match stack with
                | ((idx3, '('), (idx4, '*')) :: t ->
                    Ok (t, ((idx3, idx4), (idx1, idx2)) :: res)
                | [] ->
                    acc
                    (* we might have encountered: try (rewrite IHn in *\) for example *)
                | _ -> Error "unmatched ending comment")
            | _ -> acc)
        | Error err -> Error err)
      (Ok ([], []))
      pairs
  in

  Ok
    (List.map
       (fun ((a, _), (_, d)) ->
         let len = d - a + 1 in
         let str = String.sub content a len in

         let range : Code_range.t =
           {
             start = get_line_col_positions content a;
             end_ = get_line_col_positions content d;
           }
         in
         (str, range))
       res)

let second_node_included_in (a : Syntax_node.t) (b : Syntax_node.t) : bool =
  Code_point.compare a.range.start b.range.start <= 0
  && Code_point.compare b.range.end_ a.range.end_ <= 0

let merge_nodes (nodes : Syntax_node.t list) : Syntax_node.t list =
  let rec merge_aux (acc : Syntax_node.t list) (nodes : Syntax_node.t list) =
    match nodes with
    | [] -> List.rev acc
    | curr_node :: rest -> (
        match acc with
        | acc_node :: _ when second_node_included_in acc_node curr_node ->
            merge_aux acc rest
        | _ -> merge_aux (curr_node :: acc) rest)
  in
  merge_aux [] nodes

let parse_document (doc : Doc.t) : t =
  let nodes = doc.nodes in
  let document_repr = doc.contents.raw in
  let filename = Lang.LUri.File.to_string_uri doc.uri in

  let nodes_with_ast =
    List.filter (fun elem -> Option.has_some (Doc.Node.ast elem)) nodes
  in

  let ast_nodes =
    List.map
      (fun (node : Doc.Node.t) ->
        {
          ast = node.ast;
          range = Code_range.code_range_from_lang_range node.range;
          repr = lazy (node_representation node document_repr);
          id = Unique_id.uuid ();
          diagnostics = node.diags;
        })
      nodes_with_ast
  in

  let comments = get_comments document_repr |> Result.get_ok in

  let comments_nodes =
    List.map
      (fun comment ->
        {
          ast = None;
          range = snd comment;
          repr = lazy (fst comment);
          id = Unique_id.uuid ();
          diagnostics = [];
        })
      comments
  in

  let all_nodes =
    merge_nodes (List.sort Syntax_node.compare (ast_nodes @ comments_nodes))
  in

  { elements = all_nodes; document_repr; filename; root_state = doc.root }

let dump_sorted_elements_to_string (sorted : Syntax_node.t list) :
    (string, Error.t) result =
  let append_first (buf : Buffer.t) (node : Syntax_node.t) : unit =
    Buffer.add_string buf (String.make node.range.start.line '\n');
    Buffer.add_string buf (String.make node.range.start.character ' ');
    Buffer.add_string buf (Syntax_node.repr node)
  in

  let rec aux (nodes : Syntax_node.t list) (buf : Buffer.t)
      (prev : Syntax_node.t) : (string, Error.t) result =
    match nodes with
    | [] -> Ok (Buffer.contents buf)
    | node :: tail ->
        let line_diff = node.range.start.line - prev.range.end_.line in
        if line_diff < 0 then
          Error.format_to_or_error
            "dump_elements_to_string: node starts before previous ends (line)\n\
             prev: %s range=%s\n\
             node: %s range=%s"
            (Syntax_node.repr prev)
            (Code_range.to_string prev.range)
            (Syntax_node.repr node)
            (Code_range.to_string node.range)
        else if line_diff = 0 then
          let char_diff =
            node.range.start.character - prev.range.end_.character
          in
          if char_diff < 0 then
            Error.format_to_or_error
              "dump_elements_to_string: node starts before previous ends (char)\n\
               prev: %s range=%s\n\
               node: %s range=%s"
              (Syntax_node.repr prev)
              (Code_range.to_string prev.range)
              (Syntax_node.repr node)
              (Code_range.to_string node.range)
          else (
            Buffer.add_string buf (String.make char_diff ' ');
            Buffer.add_string buf (Syntax_node.repr node);
            aux tail buf node)
        else (
          (* moved to later line(s): newline(s) then indentation spaces *)
          Buffer.add_string buf (String.make line_diff '\n');
          Buffer.add_string buf (String.make node.range.start.character ' ');
          Buffer.add_string buf (Syntax_node.repr node);
          aux tail buf node)
  in

  match sorted with
  | [] -> Ok ""
  | first :: tail ->
      let buf = Buffer.create 256 in
      append_first buf first;
      aux tail buf first

let dump_elements_to_string (elements : Syntax_node.t list) :
    (string, Error.t) result =
  let sorted = List.sort Syntax_node.compare elements in
  dump_sorted_elements_to_string sorted

let dump_to_string (doc : t) : (string, Error.t) result =
  dump_elements_to_string doc.elements

let element_with_id_opt (element_id : Uuidm.t) (doc : t) : Syntax_node.t option
    =
  List.find_opt (fun elem -> elem.id = element_id) doc.elements

let proof_with_id_opt (proof_id : Uuidm.t) (doc : t) : Proof.t option =
  let proofs_res = get_proofs doc in
  match proofs_res with
  | Ok proofs ->
      List.find_opt (fun elem -> elem.proposition.id = proof_id) proofs
  | Error _ -> None

let proof_with_name_opt (proof_name : string) (doc : t) : Proof.t option =
  let proof_res = get_proofs doc in
  match proof_res with
  | Ok proofs ->
      List.find_opt
        (fun proof ->
          match get_proof_name proof with
          | Some name -> name = proof_name
          | None -> false)
        proofs
  | Error _ -> None

let get_ltac_outside_proofs (doc : t) : (Syntax_node.t list, Error.t) result =
  let rec scan (in_proof : bool) (acc : Syntax_node.t list) = function
    | [] -> List.rev acc
    | node :: tail ->
        if can_open_proof node then scan true acc tail
        else if can_close_proof node then scan false acc tail
        else if (not in_proof) && is_ltac node then
          scan false (node :: acc) tail
        else scan in_proof acc tail
  in
  Ok (scan false [] doc.elements)

let split_at_id (target_id : Uuidm.t) (doc : t) :
    (Syntax_node.t list * Syntax_node.t list, Error.t) result =
  let rec aux (elements : Syntax_node.t list) (acc : Syntax_node.t list) =
    match elements with
    | [] ->
        Error.string_to_or_error
          "Error: target to split at not found in the document"
    | x :: tail ->
        if x.id = target_id then Ok (List.rev acc, tail) else aux tail (x :: acc)
  in
  aux doc.elements []

let shift_block_checked (n_line : int) (n_char : int)
    (nodes : Syntax_node.t list) : (Syntax_node.t list, Error.t) result =
  if n_char = 0 then Ok (List.map (shift_node n_line n_char) nodes)
  else
    let min_char =
      List.fold_left
        (fun acc n ->
          min acc (min n.range.start.character n.range.end_.character))
        max_int nodes
    in
    if min_char + n_char < 0 then
      Error.format_to_or_error
        "Shift would create negative character positions (min_char=%d shift=%d)"
        min_char n_char
    else Ok (List.map (shift_node n_line n_char) nodes)

let remove_node_with_id (target_id : Uuidm.t) ?(remove_method = ShiftNode)
    (doc : t) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  match element_with_id_opt target_id doc with
  | None ->
      Error.format_to_or_error
        "The element with id: %s wasn't found in the document"
        (Uuidm.to_string target_id)
  | Some removed_node ->
      let* before, after = split_at_id target_id doc in
      let* shifted_after =
        match remove_method with
        | LeaveBlank -> Ok after
        | ShiftNode -> (
            match after with
            | [] -> Ok []
            | first_after :: _ ->
                let removed_start = removed_node.range.start in
                if first_after.range.start.line = removed_start.line then
                  (* Same line: close the removed node, but preserve the original separator
                     width that was between removed and first_after. *)
                  let sep =
                    first_after.range.start.character
                    - removed_node.range.end_.character
                  in
                  if sep < 0 then
                    Error.format_to_or_error
                      "remove_node_with_id(ShiftNode): overlap: after starts \
                       before removed ends\n\
                       removed=%s (%s)\n\
                       after=%s (%s)"
                      (Syntax_node.repr removed_node)
                      (Code_range.to_string removed_node.range)
                      (Syntax_node.repr first_after)
                      (Code_range.to_string first_after.range)
                  else
                    let desired_start_char = removed_start.character + sep in
                    let dc =
                      desired_start_char - first_after.range.start.character
                    in
                    if dc = 0 then Ok after
                    else
                      Ok
                        (List.map
                           (fun x ->
                             if x.range.start.line = removed_start.line then
                               shift_node 0 dc x
                             else x)
                           after)
                else
                  let dl = removed_start.line - first_after.range.start.line in
                  if dl = 0 then Ok after
                  else Ok (List.map (shift_node dl 0) after))
      in
      let elements = before @ shifted_after in
      let* document_repr = dump_sorted_elements_to_string elements in
      Ok { doc with elements; document_repr }

let insert_node (new_node : Syntax_node.t) ?(shift_method = ShiftVertically)
    (doc : t) : (t, Error.t) result =
  let ( let* ) = Result.bind in
  let* new_node = validate new_node in

  let sorted = doc.elements in
  let before, after =
    match shift_method with
    | ShiftVertically ->
        List.partition
          (fun node -> node.range.start.line < new_node.range.start.line)
          sorted
    | ShiftHorizontally ->
        List.partition
          (fun node ->
            Code_point.compare node.range.start new_node.range.start < 0)
          sorted
  in

  (* Ensure new node doesn't start before previous ends. If it does, it's an overlap. *)
  let prev_opt = List_utils.last before in
  let overlaps_prev =
    match prev_opt with
    | None -> false
    | Some prev -> not (Code_point.leq prev.range.end_ new_node.range.start)
  in

  if overlaps_prev then
    Error.format_to_or_error
      "insert_node: new node starts before previous ends\n\
       prev=%s (%s)\n\
       new=%s (%s)"
      (Syntax_node.repr (Option.get prev_opt))
      (Code_range.to_string (Option.get prev_opt).range)
      (Syntax_node.repr new_node)
      (Code_range.to_string new_node.range)
  else
    match shift_method with
    | ShiftHorizontally ->
        (* Horizontal insert must be single-line *)
        if new_node.range.start.line <> new_node.range.end_.line then
          Error.format_to_or_error
            "insert_node: ShiftHorizontally requires a single-line node, got %s"
            (Code_range.to_string new_node.range)
        else
          let line = new_node.range.start.line in
          let insert_at = new_node.range.start.character in
          let inserted_width =
            new_node.range.end_.character - new_node.range.start.character
          in
          let extra_sep =
            match after with
            | first_after :: _ ->
                if
                  first_after.range.start.line = line
                  && first_after.range.start.character = insert_at
                then 1
                else 0
            | [] -> 0
          in
          let total_shift = inserted_width + extra_sep in
          let new_after =
            if total_shift = 0 then after
            else
              List.map
                (fun x ->
                  if
                    x.range.start.line = line
                    && x.range.start.character >= insert_at
                  then Syntax_node.shift_node 0 total_shift x
                  else x)
                after
          in
          let elements = before @ (new_node :: new_after) in
          let* document_repr = dump_sorted_elements_to_string elements in
          Ok { doc with elements; document_repr }
    | ShiftVertically ->
        (* Push down only if we overlap the next node; and push by number of
           newlines inserted, not "height in lines". *)
        let needs_push =
          match after with
          | [] -> false
          | first_after :: _ ->
              not (Code_point.leq new_node.range.end_ first_after.range.start)
        in
        let* new_after =
          if not needs_push then Ok after
          else
            let delta_lines =
              new_node.range.end_.line - new_node.range.start.line
            in
            (* For vertical inserts, treat the node as occupying full lines. *)
            let push_lines = delta_lines + 1 in
            shift_block_checked push_lines 0 after
        in
        let elements = before @ (new_node :: new_after) in
        let* document_repr = dump_sorted_elements_to_string elements in
        Ok { doc with elements; document_repr }

let replace_node (target_id : Uuidm.t) (replacement : Syntax_node.t) (doc : t) :
    (t, Error.t) result =
  let ( let* ) = Result.bind in
  match element_with_id_opt target_id doc with
  | None ->
      Error.format_to_or_error "The target node with id: %s doesn't exist"
        (Uuidm.to_string target_id)
  | Some target ->
      let* replacement = validate replacement in
      let replacement =
        {
          replacement with
          range =
            Code_range.range_from_starting_point_and_repr target.range.start
              (Syntax_node.repr replacement);
        }
      in
      let* replacement = validate replacement in

      let* doc_removed =
        remove_node_with_id ~remove_method:LeaveBlank target.id doc
      in

      let is_single_line =
        replacement.range.start.line = replacement.range.end_.line
      in

      let target_is_multiline =
        target.range.start.line <> target.range.end_.line
      in
      if target_is_multiline || not is_single_line then
        let delta_lines =
          replacement.range.end_.line - target.range.end_.line
        in
        let end_char_delta =
          replacement.range.end_.character - target.range.end_.character
        in
        let sorted = doc_removed.elements in
        let before, after =
          List.partition
            (fun node ->
              Code_point.compare node.range.start replacement.range.start < 0)
            sorted
        in
        let shifted_after =
          List.map
            (fun node ->
              if node.range.start.line = target.range.end_.line then
                Syntax_node.shift_node delta_lines end_char_delta node
              else if node.range.start.line > target.range.end_.line then
                Syntax_node.shift_node delta_lines 0 node
              else node)
            after
        in
        let elements = before @ (replacement :: shifted_after) in
        let* document_repr = dump_sorted_elements_to_string elements in
        Ok { doc with elements; document_repr }
      else
        let old_width =
          target.range.end_.character - target.range.start.character
        in
        let new_width =
          replacement.range.end_.character - replacement.range.start.character
        in
        let delta = new_width - old_width in
        let sorted = doc_removed.elements in
        let before, after =
          List.partition
            (fun node ->
              Code_point.compare node.range.start replacement.range.start < 0)
            sorted
        in
        let line = replacement.range.start.line in
        let insert_at = replacement.range.start.character in
        let predicate x =
          x.range.start.line = line && x.range.start.character >= insert_at
        in
        let* shifted_after =
          if delta = 0 then Ok after
          else
            let to_shift = List.filter predicate after in
            if to_shift = [] then Ok after
            else
              let* shifted_to_shift = shift_block_checked 0 delta to_shift in
              let shifted_queue = ref shifted_to_shift in
              Ok
                (List.map
                   (fun x ->
                     if predicate x then (
                       let y = List.hd !shifted_queue in
                       shifted_queue := List.tl !shifted_queue;
                       y)
                     else x)
                   after)
        in
        let elements = before @ (replacement :: shifted_after) in
        let* document_repr = dump_sorted_elements_to_string elements in
        Ok { doc with elements; document_repr }

let replace_proof (target_id : Uuidm.t) (new_proof : Proof.t) (doc : t) :
    Transforming_step.t list option =
  match proof_with_id_opt target_id doc with
  | Some target ->
      let replacement_node =
        Replace (target.proposition.id, new_proof.proposition)
      in
      let remove_nodes =
        List.map (fun node -> Remove node.id) target.proof_steps
      in

      let attached_nodes =
        List.mapi
          (fun i node ->
            if i = 0 then Attach (node, LineAfter, new_proof.proposition.id)
            else
              let prev_node = List.nth new_proof.proof_steps (i - 1) in
              Attach (node, LineAfter, prev_node.id))
          new_proof.proof_steps
      in
      Some (remove_nodes @ (replacement_node :: attached_nodes))
  | None -> None

let apply_transformation_step (step : Transforming_step.t) (doc : t) :
    (t, Error.t) result =
  let ( let* ) = Result.bind in
  match step with
  | Remove id -> remove_node_with_id id doc
  | Replace (id, new_node) -> replace_node id new_node doc
  | Add new_node -> insert_node new_node doc
  | Attach (attached_node, attach_position, anchor_id) -> (
      match element_with_id_opt anchor_id doc with
      | None ->
          Error.format_to_or_error
            "Can't find the node with id: %s to attach (%s) to"
            (Uuidm.to_string anchor_id)
            (repr attached_node)
      | Some target -> (
          let attached_node_start_point =
            match attach_position with
            | LineBefore -> target.range.start
            (* we don't shift back as by default, equal elements are pushed after *)
            | LineAfter ->
                {
                  line = target.range.end_.line + 1;
                  character = target.range.start.character;
                }
            | SameLine -> Code_point.shift 0 1 target.range.end_
          in

          let new_node_range =
            Code_range.range_from_starting_point_and_repr
              attached_node_start_point (repr attached_node)
          in
          let new_node_range : Code_range.t =
            match attach_position with
            | SameLine -> new_node_range
            | LineAfter | LineBefore -> new_node_range
          in

          let* new_node =
            match attached_node.ast with
            | Some _ ->
                let* node =
                  Syntax_node.syntax_node_of_string (repr attached_node)
                    new_node_range.start
                in
                Ok { node with id = attached_node.id }
            | None ->
                let* node =
                  Syntax_node.comment_syntax_node_of_string (repr attached_node)
                    new_node_range.start
                in
                Ok { node with id = attached_node.id }
          in

          match attach_position with
          | SameLine -> insert_node ~shift_method:ShiftHorizontally new_node doc
          | LineAfter | LineBefore ->
              insert_node ~shift_method:ShiftVertically new_node doc))

let rec apply_transformations_steps (steps : Transforming_step.t list) (doc : t)
    : (t, Error.t) result =
  let ( let* ) = Result.bind in
  match steps with
  | [] -> Ok doc
  | step :: tail ->
      let* doc = apply_transformation_step step doc in
      apply_transformations_steps tail doc
