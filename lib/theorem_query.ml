open Sexplib.Sexp
open Proof
open Vernacexpr
open Fleche

type sexp_query =
  | Q_any
  | Q_atom of string
  | Q_field of string * sexp_query
  | Q_field_path of string list
  | Q_list_any of sexp_query
  | Q_list_exact of sexp_query list
  | Q_list_prefix of sexp_query list
  | Q_and of sexp_query list
  | Q_or of sexp_query list
  | Q_not of sexp_query
  | Q_anywhere of sexp_query

let get_proof_proposition_sexp (x : proof) : Sexplib.Sexp.t option =
  let coq_ast =
    Option.map
      (fun (x : Doc.Node.Ast.t) -> Coq.Ast.to_coq x.v)
      x.proposition.ast
  in
  match coq_ast with
  | Some ast -> (
      match ast.CAst.v.expr with
      | VernacSynterp _ -> None
      | VernacSynPure expr_syn -> (
          match expr_syn with
          | Vernacexpr.VernacStartTheoremProof
              (kind, [ ((ident, univ), (args, expr)) ]) ->
              let sexp_expr =
                Serlib.Ser_vernacexpr.sexp_of_synpure_vernac_expr expr_syn
              in
              Some sexp_expr
          | _ -> None))
  | None -> None

let rec matches (q : sexp_query) (sexp : Sexplib.Sexp.t) : bool =
  print_endline ("matching " ^ Sexplib.Sexp.to_string_hum sexp);
  match (q, sexp) with
  | Q_any, _ -> true
  | Q_atom s, Atom a -> a = s
  | Q_field (key, qv), List [ Atom k; v ] ->
      print_endline "good key";
      print_endline ("key : " ^ k);
      if k = key then matches qv v else false
  | Q_field_path [], _ -> true
  | Q_field_path (k :: ks), List [ Atom k'; v ] when k = k' ->
      matches (Q_field_path ks) v
  | Q_list_any q, List l -> List.exists (matches q) l
  | Q_list_exact qs, List l ->
      List.length qs = List.length l && List.for_all2 matches qs l
  | Q_list_prefix qs, List l ->
      let len = List.length qs in
      if List.length l < len then false
      else List.for_all2 matches qs (List_utils.take len l)
  | Q_and qs, _ -> List.for_all (fun q -> matches q sexp) qs
  | Q_or qs, _ -> List.exists (fun q -> matches q sexp) qs
  | Q_not q, _ -> not (matches q sexp)
  | Q_anywhere q, sexp ->
      let rec go s =
        matches q s
        || match s with Atom _ -> false | List lst -> List.exists go lst
      in
      go sexp
  | _, _ -> false

let collect_matches (q : sexp_query) (sexp : Sexplib.Sexp.t) :
    Sexplib.Sexp.t list =
  let open Sexplib.Sexp in
  let rec collect s acc =
    let acc = if matches q s then s :: acc else acc in
    match s with
    | Atom _ -> acc
    | List l -> List.fold_left (fun fold_acc x -> collect x fold_acc) acc l
  in
  collect sexp [] |> List.rev

let q_path (keys : string list) (q : sexp_query) : sexp_query =
  List.fold_right (fun k acc -> Q_field (k, acc)) keys q

let rec q_exists_notation : sexp_query =
  q_path [ "v"; "CNotation"; "InConstrEntry" ] (Q_atom "exists _ .. _ , _")

let q_body_is_exists : sexp_query =
  Q_field
    ( "v",
      Q_field
        ( "CProdN",
          Q_list_prefix
            [
              Q_list_any (Q_atom "_");
              (* assumptions *)
              Q_field ("v", q_exists_notation) (* conclusion *);
            ] ) )

let q_theorem_with_exists_conclusion : sexp_query =
  Q_list_prefix
    [
      Q_atom "VernacStartTheoremProof";
      Q_atom "Theorem";
      Q_list_any (Q_list_any (Q_list_any (Q_list_any q_body_is_exists)));
    ]
