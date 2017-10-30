open Datatypes

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OT_from_Alt =
 functor (O:OrderedTypeAlt) ->
 struct
  type t = O.t

  (** val compare : O.t -> O.t -> comparison **)

  let compare =
    O.compare

  (** val eq_dec : O.t -> O.t -> bool **)

  let eq_dec x y =
    match O.compare x y with
    | Eq -> true
    | _ -> false
 end
