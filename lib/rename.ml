(** renaming an identifier is a common enough operation to justify a separated
    module *)
(* TODO: review architecture *)

let rename_name (old_name : string) (new_name : string) (name : Names.Name.t) :
    Names.Name.t =
  let old_name_cast : Names.Name.t = Name (Names.Id.of_string old_name) in
  if Names.Name.equal old_name_cast name then Name (Names.Id.of_string new_name)
  else name

let rename_id (old_name : string) (new_name : string) (x : Names.Id.t) :
    Names.Id.t =
  let old_name_id = Names.Id.of_string old_name in
  if Names.Id.equal x old_name_id then Names.Id.of_string new_name else x

let rename_lident (old_name : string) (new_name : string) (x : Names.lident) :
    Names.lident =
  CAst.map (rename_id old_name new_name) x

let rename_lname (old_name : string) (new_name : string) (x : Names.lname) :
    Names.lname =
  CAst.map (rename_name old_name new_name) x

let rename_qualid (old_name : string) (new_name : string) (x : Libnames.qualid)
    : Libnames.qualid =
  let dirpath, id = Libnames.repr_qualid x in
  let mapped_id = rename_id old_name new_name id in
  Libnames.make_qualid dirpath mapped_id

(** If [tacexpr] is exactly a TacArg(TacCall ...), rename the called qualid. *)
let rename_taccall_tacarg_in_tacexpr (old_taccall_name : string)
    (new_taccall_name : string) (tacexpr : Ltac_plugin.Tacexpr.raw_tactic_expr)
    : Ltac_plugin.Tacexpr.raw_tactic_expr =
  let open Ltac_plugin.Tacexpr in
  match tacexpr.v with
  | TacArg (TacCall call_arg) ->
      let old_call_qualid, old_call_args = call_arg.v in
      let old_call_qualid_str = Libnames.string_of_qualid old_call_qualid in
      if old_call_qualid_str = old_taccall_name then
        let new_taccall_name_qualid =
          Libnames.qualid_of_string new_taccall_name
        in
        let new_taccall = CAst.make (new_taccall_name_qualid, old_call_args) in
        TacArg (TacCall new_taccall) |> CAst.make
      else tacexpr
  | _ -> tacexpr
