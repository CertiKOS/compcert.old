type 'a vector = 'a array

(** val get : 'a1 vector -> Big.big_int -> 'a1 **)

let get = fun v i -> Array.unsafe_get v (Big.to_int i)


