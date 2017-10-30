open Datatypes

module PTree :
 sig
  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  val tree_rect :
    'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
    tree -> 'a2

  type 'a t = 'a tree

  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val empty : 'a1 t

  val get : Big.big_int -> 'a1 t -> 'a1 option

  val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 t

  val append : Big.big_int -> Big.big_int -> Big.big_int

  val xmap : (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> Big.big_int -> 'a2 t

  val map : (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module PMap :
 sig
  type 'a t = 'a * 'a PTree.t

  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : Big.big_int -> 'a1 t -> 'a1

  val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> Big.big_int

  val eq : t -> t -> bool
 end

module IMap :
 functor (X:INDEXED_TYPE) ->
 sig
  type elt = X.t

  val elt_eq : X.t -> X.t -> bool

  type 'x t = 'x PMap.t

  val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val init : 'a1 -> 'a1 * 'a1 PTree.t

  val get : X.t -> 'a1 t -> 'a1

  val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

  val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
 end

module ZIndexed :
 sig
  val index : Big.big_int -> Big.big_int
 end
