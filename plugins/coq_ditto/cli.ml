let transformation_help_fun (kind : Plugin_configuration.transformation_kind) :
    Plugin_configuration.transformation_kind * string =
  let help_text =
    match kind with
    | RenameDefinition ->
        "Rename a Definition, updating the code in the file to match the new \
         name"
    | ExplicitFreshVariables ->
        "Replace calls to tactics creating fresh variables such as `intros` \
         with explicit variable names (`intros V1 V2 ... Vn`)."
    | TurnIntoOneliner ->
        "Turn all proof steps into a single tactic call using ';' and '[]' \
         tacticals."
    | ReplaceAutoWithSteps ->
        "Replace 'auto' with the expanded steps obtained from 'info_auto'."
    | FlattenGoalSelectors ->
        "Experimental: Remove goal selectors by moving and possibly \
         duplicating tactics"
    | CompressIntro -> "Compress consecutive 'intro' calls into one 'intros'."
    | ExplicitIdentInIntro ->
        "Replace calls to `intro` with `intro X` where X is the identifier \
         introduced"
    | ExplicitApply -> "Experimental: Explicit the parameters of an apply call"
    | AddProofNodeIfMissing ->
        "Add Proof. before the steps of a proof if missing"
    | RemoveProofWith ->
        "Remove all proofs containing \"Proof with X\" by replacing each \
         \"tactic...\" with \"tactic;X.\" "
    | ReplaceInductionWithDestruct ->
        "Experimental: Replace induction with destruct when no induction \
         hypothesis is generated"
    | IdProofTransformation -> "Keep the file unchanged, run on each proof."
    | IdDocTransformation ->
        "Keep the file unchanged, don't run any transformation except initial \
         parsing"
    | ConstructiviseGeocoq ->
        "Experimental Constructivisation: Transformation to use to \
         constructivise Geocoq"
    | RocqToLean -> "Experimental: Turn Rocq code to lean"
  in
  (kind, help_text)

let transformations_help =
  List.map transformation_help_fun Plugin_configuration.all_transformation_kinds

let pp_level_lowercase (fmt : Format.formatter) (level : Logs.level) : unit =
  Format.pp_print_string fmt (Logs.level_to_string (Some level))

let pp_header_no_app (fmt : Format.formatter) (level, _msg_header_opt) =
  match level with
  | Logs.App -> ()
  | _ -> Format.fprintf fmt "[%a] " pp_level_lowercase level
