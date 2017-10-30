open Datatypes

module type OrderedTypeAlt =
 sig
  type t

  val compare : t -> t -> comparison
 end

module OT_from_Alt :
 functor (O:OrderedTypeAlt) ->
 sig
  type t = O.t

  val compare : O.t -> O.t -> comparison

  val eq_dec : O.t -> O.t -> bool
 end
