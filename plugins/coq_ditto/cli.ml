open Ditto

type transformation_kind =
  | Help
  | ExplicitFreshVariables
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | FlattenGoalSelectors
  | CompressIntro
  | IdTransformation
  | ConstructivizeGeocoq
[@@deriving variants]

let camel_to_snake (s : string) : string =
  let b = Buffer.create (String.length s * 2) in
  String.iteri
    (fun i c ->
      if 'A' <= c && c <= 'Z' then (
        if i > 0 then Buffer.add_char b '_';
        Buffer.add_char b (Char.lowercase_ascii c))
      else Buffer.add_char b c)
    s;
  Buffer.contents b

let transformation_kind_to_string (kind : transformation_kind) : string =
  Variants_of_transformation_kind.to_name kind |> camel_to_snake

let transformations_list =
  let add acc var = var.Variantslib.Variant.name :: acc in
  Variants_of_transformation_kind.fold ~init:[] ~help:add
    ~explicitfreshvariables:add ~turnintooneliner:add ~compressintro:add
    ~idtransformation:add ~replaceautowithsteps:add ~flattengoalselectors:add
    ~constructivizegeocoq:add
  |> List.map camel_to_snake

let transformations_help =
  [
    ( ExplicitFreshVariables,
      "Replace calls to tactics creating fresh variables such as `intros` with \
       explicit variable names (`intros V1 V2 ... Vn`)." );
    ( TurnIntoOneliner,
      "Turn all proof steps into a single tactic call using ';' and '[]' \
       tacticals." );
    ( ReplaceAutoWithSteps,
      "Replace 'auto' with the expanded steps obtained from 'info_auo'." );
    (CompressIntro, "Compress consecutive 'intro' calls into one 'intros'.");
    ( FlattenGoalSelectors,
      "Experimental: Remove goal selectors by moving and possibly duplicating \
       tactics" );
    ( ConstructivizeGeocoq,
      "Experimental: Transformation to use to constructivize Geocoq" );
    (IdTransformation, "Keep the file unchanged.");
  ]

let help_to_string (transformation_help : (transformation_kind * string) list) :
    string =
  List.fold_left
    (fun acc (kind, help) ->
      acc ^ transformation_kind_to_string kind ^ ": " ^ help ^ "\n")
    "" transformation_help

let arg_to_transformation_kind (arg : string) :
    (transformation_kind, Error.t) result =
  let normalized = String.lowercase_ascii arg in
  if normalized = "help" then Ok Help
  else if normalized = "explicit_fresh_variables" then Ok ExplicitFreshVariables
  else if normalized = "turn_into_oneliner" then Ok TurnIntoOneliner
  else if normalized = "replace_auto_with_steps" then Ok ReplaceAutoWithSteps
  else if normalized = "compress_intro" then Ok CompressIntro
  else if normalized = "flatten_goal_selectors" then Ok FlattenGoalSelectors
  else if normalized = "constructivize_geocoq" then Ok ConstructivizeGeocoq
  else if normalized = "id_transformation" then Ok IdTransformation
  else
    Error.string_to_or_error
      ("transformation " ^ arg
     ^ " wasn't recognized as a valid transformation.\n Valid transformations: "
      ^ String.concat "\n" transformations_list)

let pp_level_lowercase (fmt : Format.formatter) (level : Logs.level) : unit =
  Format.pp_print_string fmt (Logs.level_to_string (Some level))

let pp_header_no_app fmt (level, _msg_header_opt) =
  match level with
  | Logs.App -> ()
  | _ -> Format.fprintf fmt "[%a] " pp_level_lowercase level
