open BinInt

(** val coq_FLT_exp :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int **)

let coq_FLT_exp emin prec e =
  Z.max (Z.sub e prec) emin
