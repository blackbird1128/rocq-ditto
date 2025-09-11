open Fleche

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

type compilerError =
  | IncorrectURI
  | ParsingStopped of Lang.Range.t * Lang.Diagnostic.t list
  | ParsingFailed of Lang.Range.t * Lang.Diagnostic.t list

val compiler_error_to_string : compilerError -> string
val find_coqproject : string -> string option
val coqproject_sorted_files : string -> (string list, Error.t) result

val file_and_plugin_args_to_compiler_args :
  string ->
  Io.CallBack.t ->
  Coq.Limits.Token.t ->
  Doc.t ->
  (compilerArgs, string) result

val compile_file : compilerArgs -> string -> (Doc.t, compilerError) result
