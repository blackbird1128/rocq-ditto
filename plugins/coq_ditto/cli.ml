open Ditto

type transformation_kind =
  | RenameDefinition
  | ExplicitFreshVariables
  | TurnIntoOneliner
  | ReplaceAutoWithSteps
  | FlattenGoalSelectors
  | CompressIntro
  | ReplaceInductionWithDestruct
  | ExplicitIdentInIntro
  | ExplicitApply
  | AddProofNodeIfMissing
  | RemoveProofWith
  | IdProofTransformation
  | IdDocTransformation
  | ConstructiviseGeocoq
  | RocqToLean
[@@deriving show { with_path = false }, enum]

type statistic_kind = CountInduction
[@@deriving show { with_path = false }, enum]

type dependencies_action =
  | NoAction
  | CompileDependencies
  | TransformDependencies
[@@deriving show { with_path = false }, enum]

type output_format = Text | Json [@@deriving show { with_path = false }]
type progress = { current_file_count : int; total_file_count : int }

type transformation_configuration = {
  progress : progress option;
  verbose : bool;
  quiet : bool;
  transformation_steps : transformation_kind list;
  reverse_order : bool;
  output_filename : string;
  save_vo : bool;
}

type statistic_configuration = {
  format : output_format;
  statistic_kind : statistic_kind;
}

type plugin_configuration =
  | StatisticAction of statistic_configuration
  | TransformationAction of transformation_configuration

type env = (string * string) list

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

let statistic_kind_to_string (kind : statistic_kind) : string =
  show_statistic_kind kind |> camel_to_snake

let dependencies_action_to_string (action : dependencies_action) : string =
  show_dependencies_action action |> camel_to_snake

let output_format_to_string (format : output_format) : string =
  show_output_format format |> camel_to_snake

let all_transformation_kinds =
  List.init
    (max_transformation_kind - min_transformation_kind + 1)
    (fun i -> transformation_kind_of_enum (i + min_transformation_kind))
  |> List.map Option.get

let all_statistic_kinds =
  List.init
    (max_statistic_kind - min_statistic_kind + 1)
    (fun i -> statistic_kind_of_enum (i + min_statistic_kind))
  |> List.map Option.get

let all_dependencies_action =
  List.init
    (max_dependencies_action - min_dependencies_action + 1)
    (fun i -> dependencies_action_of_enum (i + min_dependencies_action))
  |> List.map Option.get

let transformations_list =
  all_transformation_kinds
  |> List.map (fun c -> show_transformation_kind c |> camel_to_snake)

let statistics_list =
  all_statistic_kinds
  |> List.map (fun c -> show_statistic_kind c |> camel_to_snake)

let transformation_help_fun (kind : transformation_kind) :
    transformation_kind * string =
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
  List.map transformation_help_fun all_transformation_kinds

let transformation_help_to_string
    (transformation_help : (transformation_kind * string) list) : string =
  List.fold_left
    (fun acc (kind, help) ->
      acc ^ transformation_kind_to_string kind ^ ": " ^ help ^ "\n")
    "" transformation_help

let suggest_spelling (from : string) (choices : string list) : string option =
  let spellchecked =
    String.spellcheck (fun yield -> List.iter yield choices) from
  in
  match spellchecked with
  | [] -> None
  | possible_spell :: _ -> Some possible_spell

let arg_to_output_format (arg : string) : (output_format, Error.t) result =
  let normalized = String.lowercase_ascii arg in
  match normalized with
  | "text" -> Ok Text
  | "json" -> Ok Json
  | _ ->
      Error.format_to_or_error
        "Unknown output format: %s.\nExpected: (text|json)" normalized

let arg_to_transformation_kind (arg : string) =
  let normalized = String.lowercase_ascii arg in
  match
    List.find_opt
      (fun k -> transformation_kind_to_string k = normalized)
      all_transformation_kinds
  with
  | Some k -> Ok k
  | None -> (
      match suggest_spelling normalized transformations_list with
      | None ->
          Error.string_to_or_error
            (Printf.sprintf "unknown transformation %S; expected one of: %s" arg
               (String.concat ", " transformations_list))
      | Some possible_spell ->
          Error.string_to_or_error
            (Printf.sprintf
               "unknown transformation %S; expected one of: %s\n\n\
                Did you mean %s ?"
               arg
               (String.concat ", " transformations_list)
               possible_spell))

let arg_to_statistic_kind (arg : string) =
  let normalized = String.lowercase_ascii arg in
  match
    List.find_opt
      (fun k -> statistic_kind_to_string k = normalized)
      all_statistic_kinds
  with
  | Some k -> Ok k
  | None -> (
      match suggest_spelling normalized statistics_list with
      | None ->
          Error.string_to_or_error
            (Printf.sprintf
               "unknown statistic operation: %S; expected one of: %s" arg
               (String.concat ", " statistics_list))
      | Some possible_spell ->
          Error.string_to_or_error
            (Printf.sprintf
               "unknown statistic operation %S; expected one of : %s\n\n\
                Did you mean %s?"
               arg
               (String.concat ", " statistics_list)
               possible_spell))

let arg_to_dependencies_action (arg : string) =
  let normalized = String.lowercase_ascii arg in
  match
    List.find_opt
      (fun action -> dependencies_action_to_string action = normalized)
      all_dependencies_action
  with
  | Some k -> Ok k
  | None ->
      Error.string_to_or_error
        ("unknown dependency action: " ^ arg ^ " valid actions:\n"
        ^ (List.map dependencies_action_to_string all_dependencies_action
          |> String.concat "\n"))

let env_of_array (env_array : string array) : (env, Error.t) result =
  let env_list = Array.to_list env_array in
  let rec aux (acc : env) = function
    | [] -> Ok acc
    | x :: tail -> (
        let split = String_utils.split_at '=' x in
        match split with
        | Ok (key, value) -> aux ((key, value) :: acc) tail
        | Error _ ->
            Error.format_to_or_error
              "Malformed environment: Got %S instead of a value of the shape \
               \"key=value\""
              x)
  in
  aux [] env_list

let get_env (env : env) (key : string) : (string, Error.t) result =
  match List.assoc_opt key env with
  | Some key -> Ok key
  | None -> Error.format_to_or_error "key: %S not found in environment" key

let get_env_opt (env : env) (key : string) : string option =
  List.assoc_opt key env

let get_env_default (env : env) (key : string) ~(default : string) : string =
  match List.assoc_opt key env with Some key -> key | None -> default

let int_of_string_err (arg : string) : (int, Error.t) result =
  match int_of_string_opt arg with
  | Some integer -> Ok integer
  | None ->
      Error.format_to_or_error
        "given string %S is not a valid representation of an integer" arg

let get_env_as_bool (env : env) (key : string) : (bool, Error.t) result =
  let ( let* ) = Result.bind in
  let* env_value = get_env env key in
  match env_value with
  | "true" -> Ok true
  | "false" -> Ok false
  | _ ->
      Error.format_to_or_error
        "value %S of key %S can't be converted to a boolean" env_value key

let get_env_as_bool_default (env : env) (key : string) (default : bool) :
    (bool, Error.t) result =
  match List.assoc_opt key env with
  | Some env_val -> (
      match env_val with
      | "true" -> Ok true
      | "false" -> Ok false
      | _ ->
          Error.format_to_or_error
            "value %S of key %S can't be converted to a boolean" env_val key)
  | None -> Ok default

let parse_transformation_steps (arg : string) :
    (transformation_kind list, Error.t) result =
  let split_arg = String.split_on_char ',' arg |> List.map String.trim in
  let parsed_transformation_kinds =
    List.map arg_to_transformation_kind split_arg
  in
  if List.exists Result.is_error parsed_transformation_kinds then
    let not_recognized =
      String.concat "\n"
        (List.map
           (fun x -> Error.to_string_hum (Result.get_error x))
           ((List.filter Result.is_error) parsed_transformation_kinds))
    in
    Error.format_to_or_error
      "Transformations not recognized:\n%s\nRecognized transformations: %s"
      not_recognized
      (String.concat "\n" transformations_list)
  else Ok (List.map Result.get_ok parsed_transformation_kinds)

let statistic_configuration_of_env (env : env) :
    (statistic_configuration, Error.t) result =
  let ( let* ) = Result.bind in

  let* statistic_kind_text = get_env env "DITTO_STATISTIC" in
  let* statistic_kind = arg_to_statistic_kind statistic_kind_text in

  let output_format_text_opt = get_env_opt env "DITTO_STAT_FORMAT" in
  let* format_opt =
    match output_format_text_opt with
    | Some text -> Result.map Option.make (arg_to_output_format text)
    | None -> Ok None
  in
  let format = Option.default Text format_opt in

  Ok { statistic_kind; format }

let progress_of_env (env : env) : (progress option, Error.t) result =
  let ( let* ) = Result.bind in
  let total_file_count_text_opt = get_env_opt env "TOTAL_FILE_COUNT" in
  let current_file_count_text_opt = get_env_opt env "CURRENT_FILE_COUNT" in

  match (current_file_count_text_opt, total_file_count_text_opt) with
  | Some current_file_count_text, Some total_file_count_text ->
      let* current_file_count = int_of_string_err current_file_count_text in
      let* total_file_count = int_of_string_err total_file_count_text in
      if current_file_count < 0 then
        Error.format_to_or_error
          "Provided current file count: %d is lesser than 0" current_file_count
      else if total_file_count < 0 then
        Error.format_to_or_error "Total file count: %d is lesser than 0"
          total_file_count
      else if current_file_count <= total_file_count then
        Ok (Some { current_file_count; total_file_count })
      else
        Error.format_to_or_error
          "current file: %d is greater than total file count: %d"
          current_file_count total_file_count
  | None, None -> Ok None
  | Some _, None ->
      Error.string_to_or_error
        "CURRENT_FILE_COUNT provided but TOTAL_FILE_COUNT not found"
  | None, Some _ ->
      Error.string_to_or_error
        "TOTAL_FILE_COUNT provided but CURRENT_FILE_COUNT not found"

let transformation_configuration_of_env (env : env) :
    (transformation_configuration, Error.t) result =
  let ( let* ) = Result.bind in

  let* progress = progress_of_env env in

  let* verbose = get_env_as_bool_default env "DEBUG_LEVEL" false in
  let* quiet = get_env_as_bool_default env "QUIET" false in

  let* transformation_steps_env_val = get_env env "DITTO_TRANSFORMATION" in
  let* transformation_steps =
    parse_transformation_steps transformation_steps_env_val
  in

  let* reverse_order = get_env_as_bool_default env "REVERSE_ORDER" false in

  let* output_filename = get_env env "OUTPUT_FILENAME" in

  let* save_vo = get_env_as_bool_default env "SAVE_VO" false in

  Ok
    {
      progress;
      verbose;
      quiet;
      transformation_steps;
      reverse_order;
      output_filename;
      save_vo;
    }

let plugin_configuration_of_env (env_array : string array) :
    (plugin_configuration, Error.t) result =
  let ( let* ) = Result.bind in
  let* env = env_of_array env_array in

  let* action_text = get_env env "DITTO_ACTION" in
  let normalized_action_text = String.lowercase_ascii action_text in

  match normalized_action_text with
  | "transform" ->
      let* transformation_config = transformation_configuration_of_env env in
      Ok (TransformationAction transformation_config)
  | "statistics" ->
      let* statistic_config = statistic_configuration_of_env env in

      Ok (StatisticAction statistic_config)
  | _ ->
      Error.format_to_or_error
        "Unknown action %S, expected one of (transform|statistics)" action_text

let pp_level_lowercase (fmt : Format.formatter) (level : Logs.level) : unit =
  Format.pp_print_string fmt (Logs.level_to_string (Some level))

let pp_header_no_app (fmt : Format.formatter) (level, _msg_header_opt) =
  match level with
  | Logs.App -> ()
  | _ -> Format.fprintf fmt "[%a] " pp_level_lowercase level
