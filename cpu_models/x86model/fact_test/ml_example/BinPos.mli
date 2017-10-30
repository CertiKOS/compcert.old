open BinPosDef
open Datatypes
open Nat0

module Pos :
 sig
  val succ : Big.big_int -> Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val add_carry : Big.big_int -> Big.big_int -> Big.big_int

  val pred_double : Big.big_int -> Big.big_int

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : Big.big_int -> mask

  val sub_mask : Big.big_int -> Big.big_int -> mask

  val sub_mask_carry : Big.big_int -> Big.big_int -> mask

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val iter : ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1

  val div2 : Big.big_int -> Big.big_int

  val div2_up : Big.big_int -> Big.big_int

  val compare_cont : comparison -> Big.big_int -> Big.big_int -> comparison

  val compare : Big.big_int -> Big.big_int -> comparison

  val eqb : Big.big_int -> Big.big_int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1

  val to_nat : Big.big_int -> Big.big_int

  val of_succ_nat : Big.big_int -> Big.big_int

  val eq_dec : Big.big_int -> Big.big_int -> bool
 end
