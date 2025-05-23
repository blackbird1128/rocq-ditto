open Fleche
open CoqProject_file

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

type compilerError = IncorrectURI | ParsingStopped | ParsingFailed

let compiler_error_to_string (error : compilerError) : string =
  match error with
  | IncorrectURI -> "incorrect URI"
  | ParsingStopped -> "parsing stopped"
  | ParsingFailed -> "parsing failed"

let rec find_coqproject (dir : string) : string option =
  let coqproject_filename = "_CoqProject" in
  if Sys.file_exists (Filename.concat dir coqproject_filename) then Some dir
  else if dir = "/" then None
  else find_coqproject (Filename.dirname dir)

let get_workspace_folder (filepath : string) : string option =
  let dirname = Filename.dirname filepath in
  find_coqproject dirname

let create_vo_path_from_filepath (filepath : string) : Loadpath.vo_path =
  {
    implicit = false;
    recursive = true;
    has_ml = false;
    unix_path = Option.default (Sys.getcwd ()) (get_workspace_folder filepath);
    coq_path = Names.DirPath.make [ Names.Id.of_string "Coq" ];
  }

let cmdline_from_coqproject ~(base_cmdline : Coq.Workspace.CmdLine.t)
    ~(debug : bool) (coqproject_path : string) : Coq.Workspace.CmdLine.t =
  let open CoqProject_file in
  let to_vo_loadpath f implicit =
    let open Loadpath in
    let unix_path, coq_path = f in
    {
      has_ml = false;
      implicit;
      recursive = true;
      unix_path = unix_path.path;
      coq_path = Libnames.dirpath_of_string coq_path;
    }
  in

  let { r_includes; q_includes; ml_includes; extra_args; _ } =
    read_project_file ~warning_fn:(fun _ -> ()) coqproject_path
  in
  let ml_include_path = List.map (fun f -> f.thing.path) ml_includes in
  let vo_path = List.map (fun f -> to_vo_loadpath f.thing false) q_includes in
  let vo_load_path =
    List.append vo_path
      (List.map (fun f -> to_vo_loadpath f.thing true) r_includes)
  in
  let args = List.map (fun f -> f.thing) extra_args in
  {
    base_cmdline with
    args = base_cmdline.args @ args;
    vo_load_path = base_cmdline.vo_load_path @ vo_load_path;
    ocamlpath = base_cmdline.ocamlpath @ ml_include_path;
  }

let require_t_to_cmdline_format (require : Coq.Workspace.Require.t) :
    string option * string =
  (require.from, require.library)

let workspace_to_cmdline (workspace : Coq.Workspace.t) : Coq.Workspace.CmdLine.t
    =
  {
    coqlib = workspace.coqlib;
    coqcorelib = workspace.coqcorelib;
    findlib_config = workspace.findlib_config;
    ocamlpath = workspace.ocamlpath;
    vo_load_path = workspace.vo_load_path;
    ml_include_path = workspace.ml_include_path;
    args = [];
    require_libraries =
      List.map require_t_to_cmdline_format workspace.require_libs;
  }

let file_and_plugin_args_to_compiler_args (filepath : string)
    (io : Io.CallBack.t) (token : Coq.Limits.Token.t) (doc : Doc.t) :
    (compilerArgs, string) result =
  let token = Coq.Limits.Token.create () in
  let env = doc.env in

  match get_workspace_folder filepath with
  | None -> Error "Can't find a _CoqProject, case not handled yet"
  | Some workspace ->
      let coq_project_file = Filename.concat workspace "_CoqProject" in

      let cmdline =
        {
          (workspace_to_cmdline env.workspace) with
          vo_load_path = [ create_vo_path_from_filepath filepath ];
        }
      in
      let cmdline =
        cmdline_from_coqproject ~base_cmdline:cmdline ~debug:true
          coq_project_file
      in
      let env =
        Doc.Env.make ~init:env.init
          ~workspace:(Coq.Workspace.default ~debug:false ~cmdline)
          ~files:(Coq.Files.make ())
      in

      Ok { io; token; env }

let compile_file (cc : compilerArgs) (filepath : string) :
    (Doc.t, compilerError) result =
  let { io; token; env } = cc in

  match Lang.LUri.(File.of_uri (of_string filepath)) with
  | Error _ -> Error IncorrectURI
  | Ok uri -> (
      let raw =
        Coq.Compat.Ocaml_414.In_channel.(with_open_bin filepath input_all)
      in

      let doc = Fleche.Doc.create ~token ~env ~uri ~version:0 ~raw in
      let doc = Fleche.Doc.check ~io ~token ~target:Doc.Target.End ~doc () in

      match doc.completed with
      | Yes _ -> Ok doc
      | Stopped _ -> Error ParsingStopped
      | Failed failed_range -> Error ParsingFailed)
