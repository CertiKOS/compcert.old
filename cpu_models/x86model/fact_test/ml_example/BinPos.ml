open BinPosDef
open Datatypes
open Nat0

module Pos =
 struct
  (** val succ : Big.big_int -> Big.big_int **)

  let rec succ = Big.succ

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec add = Big.add

  (** val add_carry : Big.big_int -> Big.big_int -> Big.big_int **)

  and add_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (add_carry p q))
        (fun q -> Big.double
        (add_carry p q))
        (fun _ -> Big.doubleplusone
        (succ p))
        y)
      (fun p ->
      Big.positive_case
        (fun q -> Big.double
        (add_carry p q))
        (fun q -> Big.doubleplusone
        (add p q))
        (fun _ -> Big.double
        (succ p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.doubleplusone
        (succ q))
        (fun q -> Big.double
        (succ q))
        (fun _ -> Big.doubleplusone
        Big.one)
        y)
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let rec pred_double x =
    Big.positive_case
      (fun p -> Big.doubleplusone (Big.double
      p))
      (fun p -> Big.doubleplusone
      (pred_double p))
      (fun _ ->
      Big.one)
      x

  type mask = Pos.mask =
  | IsNul
  | IsPos of Big.big_int
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos Big.one
  | IsPos p -> IsPos (Big.doubleplusone p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (Big.double p)
  | x0 -> x0

  (** val double_pred_mask : Big.big_int -> mask **)

  let double_pred_mask x =
    Big.positive_case
      (fun p -> IsPos (Big.double (Big.double
      p)))
      (fun p -> IsPos (Big.double
      (pred_double p)))
      (fun _ ->
      IsNul)
      x

  (** val sub_mask : Big.big_int -> Big.big_int -> mask **)

  let rec sub_mask x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask p q))
        (fun q ->
        succ_double_mask (sub_mask p q))
        (fun _ -> IsPos (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun _ ->
        IsNeg)
        (fun _ ->
        IsNeg)
        (fun _ ->
        IsNul)
        y)
      x

  (** val sub_mask_carry : Big.big_int -> Big.big_int -> mask **)

  and sub_mask_carry x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun q ->
        double_mask (sub_mask p q))
        (fun _ -> IsPos
        (pred_double p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        double_mask (sub_mask_carry p q))
        (fun q ->
        succ_double_mask (sub_mask_carry p q))
        (fun _ ->
        double_pred_mask p)
        y)
      (fun _ ->
      IsNeg)
      x

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub = fun n m -> Big.max Big.one (Big.sub n m)

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec mul = Big.mult

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Big.big_int -> 'a1 **)

  let rec iter f x n =
    Big.positive_case
      (fun n' ->
      f (iter f (iter f x n') n'))
      (fun n' ->
      iter f (iter f x n') n')
      (fun _ ->
      f x)
      n

  (** val div2 : Big.big_int -> Big.big_int **)

  let div2 p =
    Big.positive_case
      (fun p0 ->
      p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p

  (** val div2_up : Big.big_int -> Big.big_int **)

  let div2_up p =
    Big.positive_case
      (fun p0 ->
      succ p0)
      (fun p0 ->
      p0)
      (fun _ ->
      Big.one)
      p

  (** val compare_cont :
      comparison -> Big.big_int -> Big.big_int -> comparison **)

  let rec compare_cont = fun c x y -> Big.compare_case c Lt Gt x y

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = fun x y -> Big.compare_case Eq Lt Gt x y

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb p q =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        (fun _ ->
        false)
        q)
      (fun p0 ->
      Big.positive_case
        (fun _ ->
        false)
        (fun q0 ->
        eqb p0 q0)
        (fun _ ->
        false)
        q)
      (fun _ ->
      Big.positive_case
        (fun _ ->
        false)
        (fun _ ->
        false)
        (fun _ ->
        true)
        q)
      p

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    Big.positive_case
      (fun p0 ->
      op a (iter_op op p0 (op a a)))
      (fun p0 ->
      iter_op op p0 (op a a))
      (fun _ ->
      a)
      p

  (** val to_nat : Big.big_int -> Big.big_int **)

  let to_nat x =
    iter_op Nat0.add x (Big.succ Big.zero)

  (** val of_succ_nat : Big.big_int -> Big.big_int **)

  let rec of_succ_nat n =
    Big.nat_case
      (fun _ ->
      Big.one)
      (fun x ->
      succ (of_succ_nat x))
      n

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let rec eq_dec p y0 =
    Big.positive_case
      (fun p0 ->
      Big.positive_case
        (fun p1 ->
        eq_dec p0 p1)
        (fun _ ->
        false)
        (fun _ ->
        false)
        y0)
      (fun p0 ->
      Big.positive_case
        (fun _ ->
        false)
        (fun p1 ->
        eq_dec p0 p1)
        (fun _ ->
        false)
        y0)
      (fun _ ->
      Big.positive_case
        (fun _ ->
        false)
        (fun _ ->
        false)
        (fun _ ->
        true)
        y0)
      p
 end
