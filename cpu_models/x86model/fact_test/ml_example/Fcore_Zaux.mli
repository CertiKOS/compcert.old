open BinInt
open BinPos
open Datatypes

val coq_Zeven : Big.big_int -> bool

val cond_Zopp : bool -> Big.big_int -> Big.big_int

val coq_Zpos_div_eucl_aux1 :
  Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

val coq_Zpos_div_eucl_aux :
  Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

val coq_Zfast_div_eucl :
  Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

val iter_nat : ('a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1

val iter_pos : ('a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1
