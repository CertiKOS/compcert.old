open BinInt
open Fappli_IEEE
open Zbool

val join_bits :
  Big.big_int -> Big.big_int -> bool -> Big.big_int -> Big.big_int ->
  Big.big_int

val split_bits :
  Big.big_int -> Big.big_int -> Big.big_int ->
  (bool * Big.big_int) * Big.big_int

val bits_of_binary_float :
  Big.big_int -> Big.big_int -> binary_float -> Big.big_int

val binary_float_of_bits_aux :
  Big.big_int -> Big.big_int -> Big.big_int -> full_float

val binary_float_of_bits :
  Big.big_int -> Big.big_int -> Big.big_int -> binary_float
