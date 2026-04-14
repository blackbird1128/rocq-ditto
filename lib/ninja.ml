module Path = struct
  type t = Path of string

  let v s = Path s
  let to_string (Path s) = s

  let escape (x : t) : t =
    let buf = Buffer.create (String.length (to_string x)) in
    String.iter
      (fun c ->
        match c with
        | '$' -> Buffer.add_string buf "$$"
        | ' ' -> Buffer.add_string buf "$ "
        | ':' -> Buffer.add_string buf "$:"
        | c -> Buffer.add_char buf c)
      (to_string x);
    v (Buffer.contents buf)

  let pp fmt (p : t) = Format.pp_print_string fmt (to_string (escape p))
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

let comment (s : string) : t = [ Comment s ]
let variable (k : string) (v : string) : t = [ Variable (k, v) ]
let rule (r : rule) : t = [ Rule r ]
let build (b : build) : t = [ Build b ]
let default (xs : path list) : t = [ Default xs ]
let empty : t = []
let append (a : t) (b : t) : t = a @ b
let concat (xs : t list) : t = List.concat xs

module Pp = struct
  open Format

  let pp_raw fmt s = pp_print_string fmt s
  let pp_indented_binding fmt (k, v) = fprintf fmt "  %s = %a\n" k pp_raw v

  let pp_comment fmt s =
    String.split_on_char '\n' s
    |> List.iter (fun line -> fprintf fmt "# %s\n" line)

  let pp_path_list fmt xs =
    Format.pp_print_list
      ~pp_sep:(fun fmt () -> Format.pp_print_string fmt " ")
      Path.pp fmt xs

  let pp_opt_field name pp_value fmt field =
    match field with
    | None -> ()
    | Some v -> fprintf fmt "  %s = %a\n" name pp_value v

  let pp_bool_field name fmt b = if b then fprintf fmt "  %s = 1\n" name

  let pp_rule fmt (r : rule) =
    fprintf fmt "rule %s\n" r.name;
    fprintf fmt "  command = %a\n" pp_raw r.command;
    pp_opt_field "description" pp_raw fmt r.description;
    pp_opt_field "depfile" pp_raw fmt r.depfile;
    pp_bool_field "generator" fmt r.generator;
    pp_opt_field "pool" pp_print_string fmt r.pool;
    pp_bool_field "restat" fmt r.restat;
    pp_opt_field "rspfile" pp_raw fmt r.rspfile;
    pp_opt_field "rspfile_content" pp_raw fmt r.rspfile_content;
    pp_opt_field "deps" pp_print_string fmt r.deps

  let pp_build fmt (b : build) =
    fprintf fmt "build %a" pp_path_list b.outputs;
    if b.implicit_outputs <> [] then
      fprintf fmt " | %a" pp_path_list b.implicit_outputs;
    fprintf fmt ": %s" b.rule;
    if b.inputs <> [] then fprintf fmt " %a" pp_path_list b.inputs;
    if b.implicit <> [] then fprintf fmt " | %a" pp_path_list b.implicit;
    if b.order_only <> [] then fprintf fmt " || %a" pp_path_list b.order_only;
    fprintf fmt "\n";
    List.iter (pp_indented_binding fmt) b.variables;
    (match b.pool with None -> () | Some p -> fprintf fmt "  pool = %s\n" p);
    match b.dyndep with
    | None -> ()
    | Some p -> fprintf fmt "  dyndep = %a\n" Path.pp p

  let pp_stmt fmt (stmt : stmt) =
    match stmt with
    | Comment s -> pp_comment fmt s
    | Variable (k, v) -> fprintf fmt "%s = %a\n" k pp_raw v
    | Pool (name, depth) ->
        fprintf fmt "pool %s\n" name;
        fprintf fmt "  depth = %d\n" depth
    | Rule r -> pp_rule fmt r
    | Build b -> pp_build fmt b
    | Include p -> fprintf fmt "include %a\n" Path.pp p
    | Subninja p -> fprintf fmt "subninja %a\n" Path.pp p
    | Default ps -> fprintf fmt "default %a\n" pp_path_list ps

  let pp fmt (t : t) =
    let rec loop = function
      | [] -> ()
      | [ stmt ] -> pp_stmt fmt stmt
      | stmt :: rest ->
          pp_stmt fmt stmt;
          fprintf fmt "\n";
          loop rest
    in
    loop t
end

let pp = Pp.pp
let to_string (t : t) : string = Format.asprintf "%a" pp t
