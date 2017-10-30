open BinInt
open Nat0
open ZArith_dec

val zeq : Big.big_int -> Big.big_int -> bool

val zlt : Big.big_int -> Big.big_int -> bool

val zle : Big.big_int -> Big.big_int -> bool

val find_index' :
  ('a1 -> 'a1 -> bool) -> 'a1 -> Big.big_int -> 'a1 list -> Big.big_int option

val find_index : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> Big.big_int option

val proj_sumbool : bool -> bool
