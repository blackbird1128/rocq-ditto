open Format

let pp_opt pp fmt = function None -> fprintf fmt "none" | Some x -> pp fmt x

let pp_list ?(sep = "; ") pp fmt xs =
  pp_print_list
    ~pp_sep:(fun fmt () ->
      pp_print_string fmt sep;
      pp_print_cut fmt ())
    pp fmt xs

let pp_hyp fmt (x : string Coq.Goals.Reified_goal.hyp) =
  fprintf fmt "@[<v2>{ hyp:@ ";
  fprintf fmt "type = %s@," x.ty;
  fprintf fmt "def  = %s@," (Option.default "empty" x.def);
  fprintf fmt "names = [%a]@]}" (pp_list pp_print_string) x.names

let pp_info fmt (x : Coq.Goals.Reified_goal.info) =
  let evar_str = Evar.print x.evar |> Pp.string_of_ppcmds in
  let name_str = Option.map Names.Id.to_string x.name in
  fprintf fmt "@[<v2>{ info:@ ";
  fprintf fmt "evar = %s@," evar_str;
  fprintf fmt "name = %a@]}" (pp_opt pp_print_string) name_str

let pp fmt (x : string Coq.Goals.Reified_goal.t) =
  fprintf fmt "@[<v2>{ goal:@ ";
  fprintf fmt "ty   = %s@," x.ty;
  fprintf fmt "hyps = [%a]@," (pp_list pp_hyp) x.hyps;
  fprintf fmt "info = %a@]}" pp_info x.info
