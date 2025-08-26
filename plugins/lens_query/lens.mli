type ('s, 'a) lens = { get : 's -> 'a; set : 'a -> 's -> 's }

type ('s, 'a) plens = {
  get_opt : 's -> 'a option;
  set_opt : 'a -> 's -> 's option;
}

val compose : ('a, 'b) lens -> ('b, 'c) lens -> ('a, 'c) lens
val compose_p : ('a, 'b) plens -> ('b, 'a) lens -> ('a, 'a) plens
