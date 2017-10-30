open BinInt
open Coqlib
open Datatypes
open Zpower

module Word =
 struct
  (** val wordsize : Big.big_int -> Big.big_int **)

  let wordsize wordsize_minus_one =
    Big.succ wordsize_minus_one

  (** val modulus : Big.big_int -> Big.big_int **)

  let modulus wordsize_minus_one =
    two_power_nat (wordsize wordsize_minus_one)

  (** val half_modulus : Big.big_int -> Big.big_int **)

  let half_modulus wordsize_minus_one =
    Z.div (modulus wordsize_minus_one) (Big.double Big.one)

  type int =
    Big.big_int
    (* singleton inductive, whose constructor was mkint *)

  (** val intval : Big.big_int -> int -> Big.big_int **)

  let intval _ i =
    i

  (** val max_unsigned : Big.big_int -> Big.big_int **)

  let max_unsigned wordsize_minus_one =
    Z.sub (modulus wordsize_minus_one) Big.one

  (** val max_signed : Big.big_int -> Big.big_int **)

  let max_signed wordsize_minus_one =
    Z.sub (half_modulus wordsize_minus_one) Big.one

  (** val min_signed : Big.big_int -> Big.big_int **)

  let min_signed wordsize_minus_one =
    Z.opp (half_modulus wordsize_minus_one)

  (** val unsigned : Big.big_int -> int -> Big.big_int **)

  let unsigned _ n =
    n

  (** val signed : Big.big_int -> int -> Big.big_int **)

  let signed wordsize_minus_one n =
    if zlt n (half_modulus wordsize_minus_one)
    then n
    else Z.sub n (modulus wordsize_minus_one)

  (** val repr : Big.big_int -> Big.big_int -> int **)

  let repr wordsize_minus_one x =
    Z.modulo x (modulus wordsize_minus_one)

  (** val zero : Big.big_int -> int **)

  let zero wordsize_minus_one =
    repr wordsize_minus_one Big.zero

  (** val one : Big.big_int -> int **)

  let one wordsize_minus_one =
    repr wordsize_minus_one Big.one

  (** val mone : Big.big_int -> int **)

  let mone wordsize_minus_one =
    repr wordsize_minus_one (Big.opp Big.one)

  (** val eq_dec : Big.big_int -> int -> int -> bool **)

  let eq_dec _ x y =
    zeq x y

  (** val eq : Big.big_int -> int -> int -> bool **)

  let eq _ x y =
    if zeq x y then true else false

  (** val lt : Big.big_int -> int -> int -> bool **)

  let lt wordsize_minus_one x y =
    if zlt (signed wordsize_minus_one x) (signed wordsize_minus_one y)
    then true
    else false

  (** val ltu : Big.big_int -> int -> int -> bool **)

  let ltu _ x y =
    if zlt x y then true else false

  (** val add : Big.big_int -> int -> int -> int **)

  let add wordsize_minus_one x y =
    repr wordsize_minus_one (Z.add x y)

  (** val sub : Big.big_int -> int -> int -> int **)

  let sub wordsize_minus_one x y =
    repr wordsize_minus_one (Z.sub x y)

  (** val mul : Big.big_int -> int -> int -> int **)

  let mul wordsize_minus_one x y =
    repr wordsize_minus_one (Z.mul x y)

  (** val coq_Zdiv_round : Big.big_int -> Big.big_int -> Big.big_int **)

  let coq_Zdiv_round x y =
    if zlt x Big.zero
    then if zlt y Big.zero
         then Z.div (Z.opp x) (Z.opp y)
         else Z.opp (Z.div (Z.opp x) y)
    else if zlt y Big.zero then Z.opp (Z.div x (Z.opp y)) else Z.div x y

  (** val coq_Zmod_round : Big.big_int -> Big.big_int -> Big.big_int **)

  let coq_Zmod_round x y =
    Z.sub x (Z.mul (coq_Zdiv_round x y) y)

  (** val divs : Big.big_int -> int -> int -> int **)

  let divs wordsize_minus_one x y =
    repr wordsize_minus_one
      (coq_Zdiv_round (signed wordsize_minus_one x)
        (signed wordsize_minus_one y))

  (** val mods : Big.big_int -> int -> int -> int **)

  let mods wordsize_minus_one x y =
    repr wordsize_minus_one
      (coq_Zmod_round (signed wordsize_minus_one x)
        (signed wordsize_minus_one y))

  (** val divu : Big.big_int -> int -> int -> int **)

  let divu wordsize_minus_one x y =
    repr wordsize_minus_one (Z.div x y)

  (** val modu : Big.big_int -> int -> int -> int **)

  let modu wordsize_minus_one x y =
    repr wordsize_minus_one (Z.modulo x y)

  (** val bool_to_int : Big.big_int -> bool -> int **)

  let bool_to_int wordsize_minus_one = function
  | true -> one wordsize_minus_one
  | false -> zero wordsize_minus_one

  (** val coq_Z_shift_add : bool -> Big.big_int -> Big.big_int **)

  let coq_Z_shift_add b x =
    if b
    then Z.add (Z.mul (Big.double Big.one) x) Big.one
    else Z.mul (Big.double Big.one) x

  (** val coq_Z_bin_decomp : Big.big_int -> bool * Big.big_int **)

  let coq_Z_bin_decomp x =
    Big.z_case
      (fun _ -> (false,
      Big.zero))
      (fun p ->
      Big.positive_case
        (fun q -> (true,
        q))
        (fun q -> (false,
        q))
        (fun _ -> (true,
        Big.zero))
        p)
      (fun p ->
      Big.positive_case
        (fun q -> (true,
        (Z.sub (Big.opp q) Big.one)))
        (fun q -> (false, (Big.opp
        q)))
        (fun _ -> (true, (Big.opp
        Big.one)))
        p)
      x

  (** val bits_of_Z : Big.big_int -> Big.big_int -> Big.big_int -> bool **)

  let rec bits_of_Z n x =
    Big.nat_case
      (fun _ _ ->
      false)
      (fun m ->
      let (b, y) = coq_Z_bin_decomp x in
      let f = bits_of_Z m y in
      (fun i -> if zeq i Big.zero then b else f (Z.sub i Big.one)))
      n

  (** val coq_Z_of_bits :
      Big.big_int -> (Big.big_int -> bool) -> Big.big_int **)

  let rec coq_Z_of_bits n f =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun m ->
      coq_Z_shift_add (f Big.zero)
        (coq_Z_of_bits m (fun i -> f (Z.add i Big.one))))
      n

  (** val sig_cat :
      Big.big_int -> (Big.big_int -> bool) -> (Big.big_int -> bool) ->
      Big.big_int -> bool **)

  let sig_cat m sig1 sig2 i =
    if zlt i (Z.of_nat m) then sig2 i else sig1 (Z.sub i (Z.of_nat m))

  (** val sig_split1 :
      Big.big_int -> (Big.big_int -> bool) -> Big.big_int -> bool **)

  let sig_split1 m sig0 i =
    sig0 (Z.add i (Z.of_nat m))

  (** val sig_split2 :
      Big.big_int -> (Big.big_int -> bool) -> Big.big_int -> bool **)

  let sig_split2 m sig0 i =
    if zlt i (Z.of_nat m) then sig0 i else false

  (** val bitwise_binop :
      Big.big_int -> (bool -> bool -> bool) -> int -> int -> int **)

  let bitwise_binop wordsize_minus_one f x y =
    let fx = bits_of_Z (wordsize wordsize_minus_one) x in
    let fy = bits_of_Z (wordsize wordsize_minus_one) y in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        f (fx i) (fy i)))

  (** val coq_and : Big.big_int -> int -> int -> int **)

  let coq_and wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one (&&) x y

  (** val coq_or : Big.big_int -> int -> int -> int **)

  let coq_or wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one (||) x y

  (** val xor : Big.big_int -> int -> int -> int **)

  let xor wordsize_minus_one x y =
    bitwise_binop wordsize_minus_one xorb x y

  (** val shl : Big.big_int -> int -> int -> int **)

  let shl wordsize_minus_one x y =
    let fx = bits_of_Z (wordsize wordsize_minus_one) x in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i -> fx (Z.sub i y)))

  (** val shru : Big.big_int -> int -> int -> int **)

  let shru wordsize_minus_one x y =
    let fx = bits_of_Z (wordsize wordsize_minus_one) x in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i -> fx (Z.add i y)))

  (** val shr : Big.big_int -> int -> int -> int **)

  let shr wordsize_minus_one x y =
    repr wordsize_minus_one (Z.div (signed wordsize_minus_one x) (two_p y))

  (** val rol : Big.big_int -> int -> int -> int **)

  let rol wordsize_minus_one x y =
    let fx = bits_of_Z (wordsize wordsize_minus_one) x in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.modulo (Z.sub i y) (Z.of_nat (wordsize wordsize_minus_one)))))

  (** val ror : Big.big_int -> int -> int -> int **)

  let ror wordsize_minus_one x y =
    let fx = bits_of_Z (wordsize wordsize_minus_one) x in
    repr wordsize_minus_one
      (coq_Z_of_bits (wordsize wordsize_minus_one) (fun i ->
        fx (Z.modulo (Z.add i y) (Z.of_nat (wordsize wordsize_minus_one)))))
 end

(** val size1 : Big.big_int **)

let size1 =
  Big.zero

(** val size2 : Big.big_int **)

let size2 =
  Big.succ Big.zero

(** val size3 : Big.big_int **)

let size3 =
  Big.succ (Big.succ Big.zero)

(** val size4 : Big.big_int **)

let size4 =
  Big.succ (Big.succ (Big.succ Big.zero))

(** val size8 : Big.big_int **)

let size8 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))

(** val size16 : Big.big_int **)

let size16 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ Big.zero))))))))))))))

(** val size32 : Big.big_int **)

let size32 =
  Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))))))))))))))))))

type int1 = Word.int

type int2 = Word.int

type int3 = Word.int

type int8 = Word.int

type int16 = Word.int

type int32 = Word.int

type int80 = Word.int
