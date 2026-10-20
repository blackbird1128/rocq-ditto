let with_opaque_access (full_state : Vernactypes.full_state)
    (f : Global.indirect_accessor -> 'a) : 'a =
  let open Vernactypes in
  let computation =
    typed_vernac_gen { ignore_state with opaque_access = OpaqueAccess.Access }
      (fun state ->
        let result = f state.opaque_access in
        (no_state, result))
  in
  let _, result = run computation full_state in
  result

let full_state_of_state (st : Coq.State.t) : Vernactypes.full_state =
  let (rocq_state : Vernacstate.t) = Coq.State.to_coq st in
  {
    prog = rocq_state.interp.program;
    proof = rocq_state.interp.lemmas;
    opaque_access = ();
  }

let constant_of_global_ref (gref : Names.GlobRef.t) : Names.Constant.t option =
  match gref with Names.GlobRef.ConstRef constant -> Some constant | _ -> None

let get ~(token : Coq.Limits.Token.t) (state : Coq.State.t)
    (constant : Names.Constant.t) : (Constr.t option, Error.t) result =
  Coq.State.in_state ~token ~st:state
    ~f:(fun constant ->
      let full_state = full_state_of_state state in
      let body_and_univ_opt =
        with_opaque_access full_state (fun opaque_access ->
            Global.body_of_constant opaque_access constant)
      in
      match body_and_univ_opt with
      | Some (term, _, _) -> Some term
      | None -> None)
    constant
  |> Error.protect_to_result
