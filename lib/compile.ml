open Fleche

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

type compilerError =
  | FatalCheckingError
  | CheckingStopped
  | FileNotScheduled
  | IncorrectURI
  | ParsingStopped
  | ParsingFailed

let compiler_error_to_string (error : compilerError) : string =
  match error with
  | FatalCheckingError -> "fatal checking error"
  | CheckingStopped -> "checking stopped"
  | FileNotScheduled -> "file not scheduled"
  | IncorrectURI -> "incorrect URI"
  | ParsingStopped -> "parsing stopped"
  | ParsingFailed -> "parsing failed"

let get_workspace_folder (filepath : string) : string =
  Filename.dirname filepath

let file_and_plugin_args_to_compiler_args (filepath : string)
    (io : Io.CallBack.t) (token : Coq.Limits.Token.t) (doc : Doc.t) :
    compilerArgs =
  let token = Coq.Limits.Token.create () in
  let env = doc.env in
  let workspace = env.workspace in
  List.iter
    (fun (path : Loadpath.vo_path) -> print_endline path.unix_path)
    env.workspace.vo_load_path;

  (* let root = Sys.getcwd () in *)
  (* TODO fix for stuff in multiple workspaces *)
  { io; token; env = doc.env }

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
