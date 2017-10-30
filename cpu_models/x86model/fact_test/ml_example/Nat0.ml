(** val add : Big.big_int -> Big.big_int -> Big.big_int **)

let rec add = Big.add

(** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

let rec mul = Big.mult

(** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

let rec sub = (fun n m -> Big.max Big.zero (Big.sub n m))

(** val max : Big.big_int -> Big.big_int -> Big.big_int **)

let rec max = Big.max

(** val min : Big.big_int -> Big.big_int -> Big.big_int **)

let rec min = Big.min
