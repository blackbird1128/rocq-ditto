open Proof

let split_prefix (prefix : string) (s : string) =
  let plen = String.length prefix in
  if String.length s >= plen && String.sub s 0 plen = prefix then
    Some (prefix, String.sub s plen (String.length s - plen))
  else None

let rocq_to_lean (doc : Rocq_document.t) :
    (transformation_step list, Error.t) result =
  (* let proofs = Rocq_document.get_proofs doc in *)
  let require_nodes =
    List.filter Syntax_node.is_syntax_node_require doc.elements
  in
  let steps =
    List.map
      (fun (x : Syntax_node.t) ->
        match x.ast with
        | Some ast -> (
            match (Coq.Ast.to_coq ast.v).v.expr with
            | VernacSynterp synterp_expr -> (
                match synterp_expr with
                | VernacRequire (libname_qualid, export_with_cats, l) ->
                    let _ =
                      Option.map
                        (fun x -> Libnames.string_of_qualid x)
                        libname_qualid
                      |> Option.default "no name!"
                    in

                    List.map
                      (fun (qualid, _) ->
                        let qualid_str = Libnames.string_of_qualid qualid in
                        Logs.debug (fun m -> m "qualid_str: %s" qualid_str);
                        let _, postfix =
                          split_prefix "GeoCoq." qualid_str |> Option.get
                        in
                        let lean_require_str =
                          "import GeoLean.theories." ^ postfix
                        in
                        let node =
                          Syntax_node.comment_syntax_node_of_string
                            lean_require_str x.range.start
                          |> Result.get_ok
                        in
                        Replace (x.id, node))
                      l
                | _ -> [])
            | VernacSynPure _ -> [])
        | None -> [])
      require_nodes
    |> List.concat
  in

  let comment_nodes =
    List.filter (fun (x : Syntax_node.t) -> Option.is_empty x.ast) doc.elements
  in
  let (replace_comments : transformation_step list) =
    List.map
      (fun (x : Syntax_node.t) ->
        let lean_comment_node =
          Syntax_node.comment_syntax_node_of_string
            ("/-" ^ Syntax_node.repr x ^ "-/")
            x.range.start
          |> Result.get_ok
        in
        Replace (x.id, lean_comment_node))
      comment_nodes
  in

  Ok (replace_comments @ steps)
