(* Mostly a worse Ocaml rewrite of: github.com/ninja-build/ninja/blob/master/misc/ninja_syntax.py *)

module Path : sig
  type t = Path of string

  val v : string -> t
  val to_string : t -> string
  val escape : t -> t
  val pp : Format.formatter -> t -> unit
end

type path = Path.t
type var = string * string

type rule = {
  name : string;
  command : string;
  description : string option;
  depfile : string option;
  generator : bool; [@default false]
  pool : string option;
  restat : bool; [@default false]
  rspfile : string option;
  rspfile_content : string option;
  deps : string option;
}
[@@deriving make]

type build = {
  outputs : path list;
  implicit_outputs : path list;
  rule : string;
  inputs : path list;
  order_only : path list;
  implicit : path list;
  variables : var list;
  pool : string option;
  dyndep : path option;
}
[@@deriving make]

type stmt =
  | Comment of string
  | Variable of var
  | Pool of string * int
  | Rule of rule
  | Build of build
  | Include of path
  | Subninja of path
  | Default of path list

type t = stmt list

val comment : string -> t
val variable : string -> string -> t
val rule : rule -> t
val build : build -> t
val default : path list -> t
val empty : t
val append : t -> t -> t
val concat : t list -> t
val pp : Format.formatter -> t -> unit
val to_string : t -> string
