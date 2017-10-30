open BinPos

(** val shift_pos : Big.big_int -> Big.big_int -> Big.big_int **)

let shift_pos n z =
  Pos.iter (fun x -> Big.double x) z n

(** val two_power_nat : Big.big_int -> Big.big_int **)

let two_power_nat n =
  (let rec f n0 =
     Big.nat_case
       (fun _ ->
       Big.one)
       (fun n1 -> Big.double
       (f n1))
       n0
   in f n)

(** val two_power_pos : Big.big_int -> Big.big_int **)

let two_power_pos x =
  (shift_pos x Big.one)

(** val two_p : Big.big_int -> Big.big_int **)

let two_p x =
  Big.z_case
    (fun _ ->
    Big.one)
    (fun y ->
    two_power_pos y)
    (fun _ ->
    Big.zero)
    x
