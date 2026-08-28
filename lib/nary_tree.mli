type 'a t = Node of 'a * 'a t list

val filter : ('a -> bool) -> 'a t -> 'a t option

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(** Compare two n-ary trees for equality. [equal equal_a tree1 tree2] returns
    [true] if [tree1] and [tree2] are structurally equal and their elements
    satisfy [equal_a]. *)

val sexp_of : ('a -> Sexplib.Sexp.t) -> 'a t -> Sexplib.Sexp.t

val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
(** [pp pp_a fmt (Node (a, children))] prints the n-ary tree with root value [a]
    and [children] using the printer [pp_a] *)

val from_parents : 'a -> ('a, 'a) Hashtbl.t -> 'a t

val add_child : 'a t -> 'a t -> 'a t
(** Add a child node to an n-ary tree. [add_child tree child] returns a new
    n-ary tree where [child] has been added to the list of children of [tree].
*)

val iter : ('a -> unit) -> 'a t -> unit

val map : ('a -> 'b) -> 'a t -> 'b t
(** Map a function over an n-ary tree. [map f tree] applies the function [f] to
    each node in the tree, producing a new tree with the results. *)

val mapi : (int -> 'a -> 'b) -> 'a t -> 'b t
(** Map a function over an n-ary tree. [mapi f tree] applies the function [f] to
    each node in the tree, producing a new tree with the results. At each call,
    the index passed correspond to the count of the currently accessed node,
    starting at zero*)

val depth_first_fold : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
(** Perform a depth-first fold over an n-ary tree. [depth_first_fold f acc tree]
    recursively applies the function [f] to each node in the tree, keeping an
    accumulator [acc] through the operations. It takes an initial accumulator
    and applies [f] to the accumulator and the value of each node in a
    depth-first order. *)

val depth_first_fold_with_children :
  ('acc -> 'a -> 'a list -> 'acc) -> 'acc -> 'a t -> 'acc

val depth_first_fold_with_children_as_trees :
  ('acc -> 'a -> 'a t list -> 'acc) -> 'acc -> 'a t -> 'acc

val depth_first_fold_map :
  ('acc -> 'a -> 'acc * 'b) -> 'acc -> 'a t -> 'acc * 'b t

val flatten : 'a t -> 'a list
(** Flatten an n-ary tree into a list. [flatten tree] returns a list of all the
    elements in [tree] in a depth-first order. *)

val flatten_map : ('a -> 'b) -> 'a t -> 'b list
(** Transform an n-ary tree into a list by applying a function [f] to each
    element. [flatten_map f tree] returns a list of results from applying [f] to
    each node in the given tree [tree] in a depth first order. *)

val top_n : int -> 'a t -> 'a t
(** Extract the top n levels of an n-ary tree. [top_n n tree] returns a new
    n-ary tree containing the root of [tree] and the first [n] levels of its
    children. If [n] is less than or equal to 0, only the root is returned with
    no children. *)

val bottom_n : int -> 'a t -> 'a t list
(** Obtain the list of sub-trees at depth [n] from the n-ary tree [tree].
    [bottom_n n tree] returns a list of sub-trees that are [n] levels below the
    root. If [n] is 0, it returns the root node in a list. *)

val root : 'a t -> 'a
(** Get the root value [x] of a tree of the shape Node([x],[children]) *)
