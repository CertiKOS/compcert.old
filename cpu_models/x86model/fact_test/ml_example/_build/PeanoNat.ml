module Nat =
 struct
  (** val pred : Big.big_int -> Big.big_int **)

  let pred n =
    Big.nat_case
      (fun _ ->
      n)
      (fun u ->
      u)
      n

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb = Big.eq

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let rec eq_dec = Big.eq
 end
