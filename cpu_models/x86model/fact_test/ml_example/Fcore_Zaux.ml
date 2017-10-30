open BinInt
open BinPos
open Datatypes

(** val coq_Zeven : Big.big_int -> bool **)

let coq_Zeven n =
  Big.z_case
    (fun _ ->
    true)
    (fun p ->
    Big.positive_case
      (fun _ ->
      false)
      (fun _ ->
      true)
      (fun _ ->
      false)
      p)
    (fun p ->
    Big.positive_case
      (fun _ ->
      false)
      (fun _ ->
      true)
      (fun _ ->
      false)
      p)
    n

(** val cond_Zopp : bool -> Big.big_int -> Big.big_int **)

let cond_Zopp b m =
  if b then Z.opp m else m

(** val coq_Zpos_div_eucl_aux1 :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let rec coq_Zpos_div_eucl_aux1 a b =
  Big.positive_case
    (fun _ ->
    Z.pos_div_eucl a b)
    (fun b' ->
    Big.positive_case
      (fun a' ->
      let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
      (q, (Z.add (Z.mul (Big.double Big.one) r) Big.one)))
      (fun a' ->
      let (q, r) = coq_Zpos_div_eucl_aux1 a' b' in
      (q, (Z.mul (Big.double Big.one) r)))
      (fun _ -> (Big.zero,
      a))
      a)
    (fun _ -> (a,
    Big.zero))
    b

(** val coq_Zpos_div_eucl_aux :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let coq_Zpos_div_eucl_aux a b =
  match Pos.compare a b with
  | Eq -> (Big.one, Big.zero)
  | Lt -> (Big.zero, a)
  | Gt -> coq_Zpos_div_eucl_aux1 a b

(** val coq_Zfast_div_eucl :
    Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let coq_Zfast_div_eucl a b =
  Big.z_case
    (fun _ -> (Big.zero,
    Big.zero))
    (fun a' ->
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun b' ->
      coq_Zpos_div_eucl_aux a' b')
      (fun b' ->
      let (q, r) = coq_Zpos_div_eucl_aux a' b' in
      (Big.z_case
         (fun _ -> ((Z.opp q),
         Big.zero))
         (fun _ -> ((Z.opp (Z.add q Big.one)),
         (Z.add b r)))
         (fun _ -> ((Z.opp (Z.add q Big.one)),
         (Z.add b r)))
         r))
      b)
    (fun a' ->
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun b' ->
      let (q, r) = coq_Zpos_div_eucl_aux a' b' in
      (Big.z_case
         (fun _ -> ((Z.opp q),
         Big.zero))
         (fun _ -> ((Z.opp (Z.add q Big.one)),
         (Z.sub b r)))
         (fun _ -> ((Z.opp (Z.add q Big.one)),
         (Z.sub b r)))
         r))
      (fun b' ->
      let (q, r) = coq_Zpos_div_eucl_aux a' b' in (q, (Z.opp r)))
      b)
    a

(** val iter_nat : ('a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)

let rec iter_nat f n x =
  Big.nat_case
    (fun _ ->
    x)
    (fun n' ->
    iter_nat f n' (f x))
    n

(** val iter_pos : ('a1 -> 'a1) -> Big.big_int -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  Big.positive_case
    (fun n' ->
    iter_pos f n' (iter_pos f n' (f x)))
    (fun n' ->
    iter_pos f n' (iter_pos f n' x))
    (fun _ ->
    f x)
    n
