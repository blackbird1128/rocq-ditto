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
  | RocqToLean
[@@deriving show { with_path = false }, enum]

type dependency_action = NoAction | CompileDependency | TransformDependency
[@@deriving show { with_path = false }, enum]

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
  show_transformation_kind kind |> camel_to_snake

let dependency_action_to_string (action : dependency_action) : string =
  show_dependency_action action |> camel_to_snake

let all_transformation_kinds =
  List.init
    (max_transformation_kind - min_transformation_kind + 1)
    (fun i -> transformation_kind_of_enum (i + min_transformation_kind))
  |> List.map Option.get

let all_dependency_action =
  List.init
    (max_dependency_action - min_dependency_action + 1)
    (fun i -> dependency_action_of_enum (i + min_dependency_action))
  |> List.map Option.get

let transformations_list =
  all_transformation_kinds
  |> List.map (fun c -> show_transformation_kind c |> camel_to_snake)

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
    (RocqToLean, "Experimental: Turn Rocq code to lean");
    (IdTransformation, "Keep the file unchanged.");
  ]

let help_to_string (transformation_help : (transformation_kind * string) list) :
    string =
  List.fold_left
    (fun acc (kind, help) ->
      acc ^ transformation_kind_to_string kind ^ ": " ^ help ^ "\n")
    "" transformation_help

let arg_to_transformation_kind arg =
  let normalized = String.lowercase_ascii arg in
  match
    List.find_opt
      (fun k -> transformation_kind_to_string k = normalized)
      all_transformation_kinds
  with
  | Some k -> Ok k
  | None ->
      Error.string_to_or_error
        ("unknown transformation: " ^ arg ^ "\nValid transformations:\n"
        ^ String.concat "\n" transformations_list)

let arg_to_dependency_action arg =
  let normalized = String.lowercase_ascii arg in
  match
    List.find_opt
      (fun action -> dependency_action_to_string action = normalized)
      all_dependency_action
  with
  | Some k -> Ok k
  | None ->
      Error.string_to_or_error
        ("unknown dependency action: " ^ arg ^ "valid actions:\n"
        ^ (List.map dependency_action_to_string all_dependency_action
          |> String.concat "\n"))

let pp_level_lowercase (fmt : Format.formatter) (level : Logs.level) : unit =
  Format.pp_print_string fmt (Logs.level_to_string (Some level))

let pp_header_no_app fmt (level, _msg_header_opt) =
  match level with
  | Logs.App -> ()
  | _ -> Format.fprintf fmt "[%a] " pp_level_lowercase level
