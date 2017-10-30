open BinInt
open Coqlib
open Datatypes
open Zpower

module Word :
 sig
  val wordsize : Big.big_int -> Big.big_int

  val modulus : Big.big_int -> Big.big_int

  val half_modulus : Big.big_int -> Big.big_int

  type int =
    Big.big_int
    (* singleton inductive, whose constructor was mkint *)

  val intval : Big.big_int -> int -> Big.big_int

  val max_unsigned : Big.big_int -> Big.big_int

  val max_signed : Big.big_int -> Big.big_int

  val min_signed : Big.big_int -> Big.big_int

  val unsigned : Big.big_int -> int -> Big.big_int

  val signed : Big.big_int -> int -> Big.big_int

  val repr : Big.big_int -> Big.big_int -> int

  val zero : Big.big_int -> int

  val one : Big.big_int -> int

  val mone : Big.big_int -> int

  val eq_dec : Big.big_int -> int -> int -> bool

  val eq : Big.big_int -> int -> int -> bool

  val lt : Big.big_int -> int -> int -> bool

  val ltu : Big.big_int -> int -> int -> bool

  val add : Big.big_int -> int -> int -> int

  val sub : Big.big_int -> int -> int -> int

  val mul : Big.big_int -> int -> int -> int

  val coq_Zdiv_round : Big.big_int -> Big.big_int -> Big.big_int

  val coq_Zmod_round : Big.big_int -> Big.big_int -> Big.big_int

  val divs : Big.big_int -> int -> int -> int

  val mods : Big.big_int -> int -> int -> int

  val divu : Big.big_int -> int -> int -> int

  val modu : Big.big_int -> int -> int -> int

  val bool_to_int : Big.big_int -> bool -> int

  val coq_Z_shift_add : bool -> Big.big_int -> Big.big_int

  val coq_Z_bin_decomp : Big.big_int -> bool * Big.big_int

  val bits_of_Z : Big.big_int -> Big.big_int -> Big.big_int -> bool

  val coq_Z_of_bits : Big.big_int -> (Big.big_int -> bool) -> Big.big_int

  val sig_cat :
    Big.big_int -> (Big.big_int -> bool) -> (Big.big_int -> bool) ->
    Big.big_int -> bool

  val sig_split1 : Big.big_int -> (Big.big_int -> bool) -> Big.big_int -> bool

  val sig_split2 : Big.big_int -> (Big.big_int -> bool) -> Big.big_int -> bool

  val bitwise_binop :
    Big.big_int -> (bool -> bool -> bool) -> int -> int -> int

  val coq_and : Big.big_int -> int -> int -> int

  val coq_or : Big.big_int -> int -> int -> int

  val xor : Big.big_int -> int -> int -> int

  val shl : Big.big_int -> int -> int -> int

  val shru : Big.big_int -> int -> int -> int

  val shr : Big.big_int -> int -> int -> int

  val rol : Big.big_int -> int -> int -> int

  val ror : Big.big_int -> int -> int -> int
 end

val size1 : Big.big_int

val size2 : Big.big_int

val size3 : Big.big_int

val size4 : Big.big_int

val size8 : Big.big_int

val size16 : Big.big_int

val size32 : Big.big_int

type int1 = Word.int

type int2 = Word.int

type int3 = Word.int

type int8 = Word.int

type int16 = Word.int

type int32 = Word.int

type int80 = Word.int
