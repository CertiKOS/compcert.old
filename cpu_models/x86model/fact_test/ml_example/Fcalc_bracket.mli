open BinInt
open Datatypes
open Fcore_Zaux
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

val new_location_even : Big.big_int -> Big.big_int -> location -> location

val new_location_odd : Big.big_int -> Big.big_int -> location -> location

val new_location : Big.big_int -> Big.big_int -> location -> location
