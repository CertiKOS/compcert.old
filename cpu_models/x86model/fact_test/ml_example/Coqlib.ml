open BinInt
open Nat0
open ZArith_dec

(** val zeq : Big.big_int -> Big.big_int -> bool **)

let zeq =
  Z.eq_dec

(** val zlt : Big.big_int -> Big.big_int -> bool **)

let zlt =
  coq_Z_lt_ge_dec

(** val zle : Big.big_int -> Big.big_int -> bool **)

let zle =
  coq_Z_le_gt_dec

(** val find_index' :
    ('a1 -> 'a1 -> bool) -> 'a1 -> Big.big_int -> 'a1 list -> Big.big_int
    option **)

let rec find_index' eqA_dec x n = function
| [] -> None
| h :: t ->
  if eqA_dec x h
  then Some n
  else find_index' eqA_dec x (add (Big.succ Big.zero) n) t

(** val find_index :
    ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> Big.big_int option **)

let find_index eqA_dec x l =
  find_index' eqA_dec x Big.zero l

(** val proj_sumbool : bool -> bool **)

let proj_sumbool = function
| true -> true
| false -> false
