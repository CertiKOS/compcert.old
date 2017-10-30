module Nat :
 sig
  val pred : Big.big_int -> Big.big_int

  val eqb : Big.big_int -> Big.big_int -> bool

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end
