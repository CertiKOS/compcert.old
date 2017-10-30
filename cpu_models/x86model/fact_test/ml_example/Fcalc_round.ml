open BinInt

(** val cond_incr : bool -> Big.big_int -> Big.big_int **)

let cond_incr b m =
  if b then Z.add m Big.one else m
