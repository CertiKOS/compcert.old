open BinPos

(** val digits2_pos : Big.big_int -> Big.big_int **)

let rec digits2_pos n =
  Big.positive_case
    (fun p ->
    Pos.succ (digits2_pos p))
    (fun p ->
    Pos.succ (digits2_pos p))
    (fun _ ->
    Big.one)
    n

(** val coq_Zdigits2 : Big.big_int -> Big.big_int **)

let coq_Zdigits2 n =
  Big.z_case
    (fun _ ->
    n)
    (fun p ->
    (digits2_pos p))
    (fun p ->
    (digits2_pos p))
    n
