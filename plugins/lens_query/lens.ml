type ('s, 'a) lens = { get : 's -> 'a; set : 'a -> 's -> 's }

type ('s, 'a) plens = {
  get_opt : 's -> 'a option;
  set_opt : 'a -> 's -> 's option;
}

let compose (l1 : ('a, 'b) lens) (l2 : ('b, 'c) lens) : ('a, 'c) lens =
  {
    get = (fun s -> l2.get (l1.get s));
    set = (fun a s -> l1.set (l2.set a (l1.get s)) s);
  }

let compose_p (p : ('a, 'b) plens) (l : ('b, 'a) lens) : ('a, 'a) plens =
  {
    get_opt = (fun s -> Option.map l.get (p.get_opt s));
    set_opt =
      (fun a s ->
        match p.get_opt s with
        | None -> None
        | Some inner -> Some (p.set_opt (l.set a inner) s |> Option.get));
  }
