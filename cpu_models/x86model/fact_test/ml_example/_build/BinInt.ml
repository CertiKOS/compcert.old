open BinPos
open Datatypes

module Z =
 struct
  (** val double : Big.big_int -> Big.big_int **)

  let double x =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p -> (Big.double
      p))
      (fun p -> Big.opp (Big.double
      p))
      x

  (** val succ_double : Big.big_int -> Big.big_int **)

  let succ_double x =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p -> (Big.doubleplusone
      p))
      (fun p -> Big.opp
      (Pos.pred_double p))
      x

  (** val pred_double : Big.big_int -> Big.big_int **)

  let pred_double x =
    Big.z_case
      (fun _ -> Big.opp
      Big.one)
      (fun p ->
      (Pos.pred_double p))
      (fun p -> Big.opp (Big.doubleplusone
      p))
      x

  (** val pos_sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec pos_sub x y =
    Big.positive_case
      (fun p ->
      Big.positive_case
        (fun q ->
        double (pos_sub p q))
        (fun q ->
        succ_double (pos_sub p q))
        (fun _ -> (Big.double
        p))
        y)
      (fun p ->
      Big.positive_case
        (fun q ->
        pred_double (pos_sub p q))
        (fun q ->
        double (pos_sub p q))
        (fun _ ->
        (Pos.pred_double p))
        y)
      (fun _ ->
      Big.positive_case
        (fun q -> Big.opp (Big.double
        q))
        (fun q -> Big.opp
        (Pos.pred_double q))
        (fun _ ->
        Big.zero)
        y)
      x

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add = Big.add

  (** val opp : Big.big_int -> Big.big_int **)

  let opp = Big.opp

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub = Big.sub

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul = Big.mult

  (** val pow_pos : Big.big_int -> Big.big_int -> Big.big_int **)

  let pow_pos z =
    Pos.iter (mul z) Big.one

  (** val pow : Big.big_int -> Big.big_int -> Big.big_int **)

  let pow x y =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      pow_pos x p)
      (fun _ ->
      Big.zero)
      y

  (** val compare : Big.big_int -> Big.big_int -> comparison **)

  let compare = Big.compare_case Eq Lt Gt

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let rec eqb x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun _ ->
        false)
        (fun _ ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun q ->
        Pos.eqb p q)
        (fun _ ->
        false)
        y)
      (fun p ->
      Big.z_case
        (fun _ ->
        false)
        (fun _ ->
        false)
        (fun q ->
        Pos.eqb p q)
        y)
      x

  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)

  let max = Big.max

  (** val min : Big.big_int -> Big.big_int -> Big.big_int **)

  let min = Big.min

  (** val of_nat : Big.big_int -> Big.big_int **)

  let of_nat n =
    Big.nat_case
      (fun _ ->
      Big.zero)
      (fun n0 ->
      (Pos.of_succ_nat n0))
      n

  (** val pos_div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

  let rec pos_div_eucl a b =
    Big.positive_case
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Big.double Big.one) r) Big.one in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Big.double Big.one) r in
      if ltb r' b
      then ((mul (Big.double Big.one) q), r')
      else ((add (mul (Big.double Big.one) q) Big.one), (sub r' b)))
      (fun _ ->
      if leb (Big.double Big.one) b
      then (Big.zero, Big.one)
      else (Big.one, Big.zero))
      a

  (** val div_eucl :
      Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

  let div_eucl a b =
    Big.z_case
      (fun _ -> (Big.zero,
      Big.zero))
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun _ ->
        pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun _ -> ((opp (add q Big.one)),
           (add b r)))
           (fun _ -> ((opp (add q Big.one)),
           (add b r)))
           r))
        b)
      (fun a' ->
      Big.z_case
        (fun _ -> (Big.zero,
        Big.zero))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        (Big.z_case
           (fun _ -> ((opp q),
           Big.zero))
           (fun _ -> ((opp (add q Big.one)),
           (sub b r)))
           (fun _ -> ((opp (add q Big.one)),
           (sub b r)))
           r))
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

  (** val div : Big.big_int -> Big.big_int -> Big.big_int **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : Big.big_int -> Big.big_int -> Big.big_int **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val div2 : Big.big_int -> Big.big_int **)

  let div2 z =
    Big.z_case
      (fun _ ->
      Big.zero)
      (fun p ->
      Big.positive_case
        (fun _ ->
        (Pos.div2 p))
        (fun _ ->
        (Pos.div2 p))
        (fun _ ->
        Big.zero)
        p)
      (fun p -> Big.opp
      (Pos.div2_up p))
      z

  (** val shiftl : Big.big_int -> Big.big_int -> Big.big_int **)

  let shiftl a n =
    Big.z_case
      (fun _ ->
      a)
      (fun p ->
      Pos.iter (mul (Big.double Big.one)) a p)
      (fun p ->
      Pos.iter div2 a p)
      n

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec x y =
    Big.z_case
      (fun _ ->
      Big.z_case
        (fun _ ->
        true)
        (fun _ ->
        false)
        (fun _ ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun p0 ->
        Pos.eq_dec x0 p0)
        (fun _ ->
        false)
        y)
      (fun x0 ->
      Big.z_case
        (fun _ ->
        false)
        (fun _ ->
        false)
        (fun p0 ->
        Pos.eq_dec x0 p0)
        y)
      x
 end
