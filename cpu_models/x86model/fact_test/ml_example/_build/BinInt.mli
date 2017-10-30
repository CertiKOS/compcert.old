open BinPos
open Datatypes

module Z :
 sig
  val double : Big.big_int -> Big.big_int

  val succ_double : Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  val pos_sub : Big.big_int -> Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val opp : Big.big_int -> Big.big_int

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val pow_pos : Big.big_int -> Big.big_int -> Big.big_int

  val pow : Big.big_int -> Big.big_int -> Big.big_int

  val compare : Big.big_int -> Big.big_int -> comparison

  val leb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val eqb : Big.big_int -> Big.big_int -> bool

  val max : Big.big_int -> Big.big_int -> Big.big_int

  val min : Big.big_int -> Big.big_int -> Big.big_int

  val of_nat : Big.big_int -> Big.big_int

  val pos_div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

  val div_eucl : Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

  val div : Big.big_int -> Big.big_int -> Big.big_int

  val modulo : Big.big_int -> Big.big_int -> Big.big_int

  val div2 : Big.big_int -> Big.big_int

  val shiftl : Big.big_int -> Big.big_int -> Big.big_int

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end
