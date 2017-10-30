open BinInt
open Datatypes
open Fcore_Zaux
open Zbool

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

(** val new_location_even :
    Big.big_int -> Big.big_int -> location -> location **)

let new_location_even nb_steps k l =
  if coq_Zeq_bool k Big.zero
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact _ -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare (Z.mul (Big.double Big.one) k) nb_steps with
          | Eq ->
            (match l with
             | Coq_loc_Exact -> Eq
             | Coq_loc_Inexact _ -> Gt)
          | x -> x)

(** val new_location_odd :
    Big.big_int -> Big.big_int -> location -> location **)

let new_location_odd nb_steps k l =
  if coq_Zeq_bool k Big.zero
  then (match l with
        | Coq_loc_Exact -> l
        | Coq_loc_Inexact _ -> Coq_loc_Inexact Lt)
  else Coq_loc_Inexact
         (match Z.compare (Z.add (Z.mul (Big.double Big.one) k) Big.one)
                  nb_steps with
          | Eq ->
            (match l with
             | Coq_loc_Exact -> Lt
             | Coq_loc_Inexact l0 -> l0)
          | x -> x)

(** val new_location : Big.big_int -> Big.big_int -> location -> location **)

let new_location nb_steps =
  if coq_Zeven nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps
