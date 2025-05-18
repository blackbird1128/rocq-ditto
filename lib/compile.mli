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

val compiler_error_to_string : compilerError -> string

val plugin_args_to_compiler_args :
  Io.CallBack.t -> Coq.Limits.Token.t -> Doc.t -> compilerArgs

val compile_file : compilerArgs -> string -> (Doc.t, compilerError) result
