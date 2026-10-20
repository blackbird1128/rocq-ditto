open Ditto
open Plugin_configuration

type transformation_options = {
  input : string;
  output : string;
  transformation : transformation_kind;
  verbose : bool;
  quiet : bool;
  save_vo : bool;
  reverse_order : bool;
  summary : bool;
  dependencies_action : dependencies_action;
  jobs : int option;
}

type transformation_settings = {
  transformation : transformation_kind;
  verbosity : verbosity;
  save_vo : bool;
  reverse_order : bool;
  summary : bool;
}

type document_options = {
  settings : transformation_settings;
  source : string;
  source_directory : string;
  destination : string;
  dependencies_action : dependencies_action;
}

type project_options = {
  settings : transformation_settings;
  source_directory : string;
  project : Project.t;
  destination : string;
  jobs : int;
}

type statistic_options = {
  input : string;
  statistic : statistic_kind;
  format : output_format;
}

type operation =
  | TransformDocument of document_options
  | TransformProject of project_options

let resolve (args : transformation_options) : (operation, Error.t) result
    =
  let ( let* ) = Result.bind in
  let input_pathkind = Filesystem.get_pathkind args.input in

  if args.input = args.output then
    Error.string_to_or_error "Input folder is equal to output folder, aborting"
  else if
    args.dependencies_action != NoAction && input_pathkind = Filesystem.Dir
  then
    Error.string_to_or_error
      "Using a dependency action when targeting a folder doesn't make sense"
  else if Option.has_some args.jobs && input_pathkind = Filesystem.File then
    Error.string_to_or_error "Cannot use --jobs on a single file"
  else if args.verbose && args.quiet then
    Error.string_to_or_error "Cannot use both --verbose and --quiet"
  else if input_pathkind = File && Filesystem.is_directory args.output then
    Error.string_to_or_error "Output must be a filename when input is a file"
  else if input_pathkind = File && not (Sys.file_exists args.input) then
    Error.string_to_or_error "Input must be an existing file"
  else
    let* verbosity =
      Plugin_configuration.verbosity_of_flags ~verbose:args.verbose
        ~quiet:args.quiet
    in
    let transformation_settings =
      {
        transformation = args.transformation;
        verbosity;
        save_vo = args.save_vo;
        reverse_order = args.reverse_order;
        summary = args.summary;
      }
    in

    match input_pathkind with
    | File ->
        let source_directory =
          match Project.find_project args.input with
          | Some project -> Project.directory project
          | None -> Filename.dirname args.input
        in
        Ok
          (TransformDocument
             {
               settings = transformation_settings;
               source = args.input;
               source_directory;
               destination = args.output;
               dependencies_action = args.dependencies_action;
             })
    | Dir -> (
        match Project.find_project args.input with
        | None ->
            Error.format_to_or_error
              "No _CoqProject or _RocqProject file found in %s" args.input
        | Some project ->
            let jobs = Option.default 1 args.jobs in
            Ok
              (TransformProject
                 {
                   settings = transformation_settings;
                   source_directory = args.input;
                   project;
                   destination = args.output;
                   jobs;
                 }))

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
    | AddProofNodeIfMissingDoc ->
        "Experimental: Add Proof. before the steps of a proof if missing. Doc \
         version to check for optimization opportunities"
    | RemoveProofWith ->
        "Remove all proofs containing \"Proof with X\" by replacing each \
         \"tactic...\" with \"tactic;X.\" "
    | RemoveProofWithDoc ->
        "Experimental: Remove all proofs containing \"Proof with X\" by \
         replacing each \"tactic...\" with \"tactic;X.\"  Doc version to check \
         for optimization opportunities "
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
