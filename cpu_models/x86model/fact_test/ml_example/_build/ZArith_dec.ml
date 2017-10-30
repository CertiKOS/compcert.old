open BinInt
open Datatypes

(** val coq_Z_lt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_dec x y =
  match Z.compare x y with
  | Lt -> true
  | _ -> false

(** val coq_Z_le_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_dec x y =
  match Z.compare x y with
  | Gt -> false
  | _ -> true

(** val coq_Z_lt_ge_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_lt_ge_dec x y =
  coq_Z_lt_dec x y

(** val coq_Z_le_gt_dec : Big.big_int -> Big.big_int -> bool **)

let coq_Z_le_gt_dec x y =
  coq_Z_le_dec x y
