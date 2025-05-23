open Fleche

type compilerArgs = {
  io : Io.CallBack.t;
  token : Coq.Limits.Token.t;
  env : Doc.Env.t;
}

type compilerError = IncorrectURI | ParsingStopped | ParsingFailed

val compiler_error_to_string : compilerError -> string

val file_and_plugin_args_to_compiler_args :
  string ->
  Io.CallBack.t ->
  Coq.Limits.Token.t ->
  Doc.t ->
  (compilerArgs, string) result

val compile_file : compilerArgs -> string -> (Doc.t, compilerError) result
