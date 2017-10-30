open BinInt
open BinPos
open Bool
open Datatypes
open Fcalc_bracket
open Fcalc_round
open Fcore_FLT
open Fcore_Zaux
open Fcore_digits
open Zpower

type full_float =
| F754_zero of bool
| F754_infinity of bool
| F754_nan of bool * Big.big_int
| F754_finite of bool * Big.big_int * Big.big_int

type nan_pl = Big.big_int

type binary_float =
| B754_zero of bool
| B754_infinity of bool
| B754_nan of bool * nan_pl
| B754_finite of bool * Big.big_int * Big.big_int

type shr_record = { shr_m : Big.big_int; shr_r : bool; shr_s : bool }

val shr_m : shr_record -> Big.big_int

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : Big.big_int -> location -> shr_record

val shr : shr_record -> Big.big_int -> Big.big_int -> shr_record * Big.big_int

val shr_fexp :
  Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> location ->
  shr_record * Big.big_int

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

val choice_mode : mode -> bool -> Big.big_int -> location -> Big.big_int

val binary_overflow : Big.big_int -> Big.big_int -> mode -> bool -> full_float

val binary_round_aux :
  Big.big_int -> Big.big_int -> mode -> bool -> Big.big_int -> Big.big_int ->
  location -> full_float

val coq_Bmult :
  Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
  bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float

val shl_align :
  Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int * Big.big_int

val shl_align_fexp :
  Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int ->
  Big.big_int * Big.big_int

val binary_round :
  Big.big_int -> Big.big_int -> mode -> bool -> Big.big_int -> Big.big_int ->
  full_float

val binary_normalize :
  Big.big_int -> Big.big_int -> mode -> Big.big_int -> Big.big_int -> bool ->
  binary_float

val coq_Bplus :
  Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
  bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float

val coq_Bminus :
  Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
  bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float

val coq_Fdiv_core_binary :
  Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int ->
  (Big.big_int * Big.big_int) * location

val coq_Bdiv :
  Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
  bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float
