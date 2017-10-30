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

(** val shr_m : shr_record -> Big.big_int **)

let shr_m x = x.shr_m

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (Big.z_case
     (fun _ -> { shr_m = Big.zero; shr_r = false; shr_s =
     s0 })
     (fun p0 ->
     Big.positive_case
       (fun p -> { shr_m = p; shr_r = true; shr_s =
       s0 })
       (fun p -> { shr_m = p; shr_r = false; shr_s =
       s0 })
       (fun _ -> { shr_m = Big.zero; shr_r = true; shr_s =
       s0 })
       p0)
     (fun p0 ->
     Big.positive_case
       (fun p -> { shr_m = (Big.opp p); shr_r = true; shr_s =
       s0 })
       (fun p -> { shr_m = (Big.opp p); shr_r = false; shr_s =
       s0 })
       (fun _ -> { shr_m = Big.zero; shr_r = true; shr_s =
       s0 })
       p0)
     m)

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Coq_loc_Inexact Gt else Coq_loc_Inexact Eq
  else if shr_s0 then Coq_loc_Inexact Lt else Coq_loc_Exact

(** val shr_record_of_loc : Big.big_int -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr :
    shr_record -> Big.big_int -> Big.big_int -> shr_record * Big.big_int **)

let shr mrs e n =
  Big.z_case
    (fun _ -> (mrs,
    e))
    (fun p -> ((iter_pos shr_1 p mrs),
    (Z.add e n)))
    (fun _ -> (mrs,
    e))
    n

(** val shr_fexp :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> location ->
    shr_record * Big.big_int **)

let shr_fexp prec emax =
  let emin = Z.sub (Z.sub (Big.doubleplusone Big.one) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun m e l ->
  shr (shr_record_of_loc m l) e (Z.sub (fexp (Z.add (coq_Zdigits2 m) e)) e))

type mode =
| Coq_mode_NE
| Coq_mode_ZR
| Coq_mode_DN
| Coq_mode_UP
| Coq_mode_NA

(** val choice_mode :
    mode -> bool -> Big.big_int -> location -> Big.big_int **)

let choice_mode m sx mx lx =
  match m with
  | Coq_mode_NE ->
    cond_incr
      (match lx with
       | Coq_loc_Exact -> false
       | Coq_loc_Inexact c ->
         (match c with
          | Eq -> negb (coq_Zeven mx)
          | Lt -> false
          | Gt -> true)) mx
  | Coq_mode_ZR -> mx
  | Coq_mode_DN ->
    cond_incr
      (match lx with
       | Coq_loc_Exact -> false
       | Coq_loc_Inexact _ -> sx) mx
  | Coq_mode_UP ->
    cond_incr
      (match lx with
       | Coq_loc_Exact -> false
       | Coq_loc_Inexact _ -> negb sx) mx
  | Coq_mode_NA ->
    cond_incr
      (match lx with
       | Coq_loc_Exact -> false
       | Coq_loc_Inexact c ->
         (match c with
          | Lt -> false
          | _ -> true)) mx

(** val binary_overflow :
    Big.big_int -> Big.big_int -> mode -> bool -> full_float **)

let binary_overflow prec emax m s =
  if match m with
     | Coq_mode_ZR -> false
     | Coq_mode_DN -> s
     | Coq_mode_UP -> negb s
     | _ -> true
  then F754_infinity s
  else F754_finite (s,
         (Big.z_case
            (fun _ ->
            Big.one)
            (fun p ->
            p)
            (fun _ ->
            Big.one)
            (Z.sub
              (Big.z_case
                 (fun _ ->
                 Big.one)
                 (fun p ->
                 Z.pow_pos (Big.double Big.one) p)
                 (fun _ ->
                 Big.zero)
                 prec) Big.one)), (Z.sub emax prec))

(** val binary_round_aux :
    Big.big_int -> Big.big_int -> mode -> bool -> Big.big_int -> Big.big_int
    -> location -> full_float **)

let binary_round_aux prec emax mode0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec emax mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec emax
      (choice_mode mode0 sx mrs'.shr_m (loc_of_shr_record mrs')) e'
      Coq_loc_Exact
  in
  (Big.z_case
     (fun _ -> F754_zero
     sx)
     (fun m ->
     if Z.leb e'' (Z.sub emax prec)
     then F754_finite (sx, m, e'')
     else binary_overflow prec emax mode0 sx)
     (fun _ -> F754_nan (false,
     Big.one))
     mrs''.shr_m)

(** val coq_Bmult :
    Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
    bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float **)

let coq_Bmult prec emax mult_nan m x y =
  let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
  (match x with
   | B754_zero sx ->
     (match y with
      | B754_zero sy -> B754_zero (xorb sx sy)
      | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
      | _ -> f (mult_nan x y))
   | B754_infinity sx ->
     (match y with
      | B754_infinity sy -> B754_infinity (xorb sx sy)
      | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
      | _ -> f (mult_nan x y))
   | B754_nan (_, _) -> f (mult_nan x y)
   | B754_finite (sx, mx, ex) ->
     (match y with
      | B754_zero sy -> B754_zero (xorb sx sy)
      | B754_infinity sy -> B754_infinity (xorb sx sy)
      | B754_nan (_, _) -> f (mult_nan x y)
      | B754_finite (sy, my, ey) ->
        (match binary_round_aux prec emax m (xorb sx sy) (Pos.mul mx my)
                 (Z.add ex ey) Coq_loc_Exact with
         | F754_zero s -> B754_zero s
         | F754_infinity s -> B754_infinity s
         | F754_nan (b, pl) -> B754_nan (b, pl)
         | F754_finite (s, m0, e) -> B754_finite (s, m0, e))))

(** val shl_align :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int * Big.big_int **)

let shl_align mx ex ex' =
  Big.z_case
    (fun _ -> (mx,
    ex))
    (fun _ -> (mx,
    ex))
    (fun d -> ((shift_pos d mx),
    ex'))
    (Z.sub ex' ex)

(** val shl_align_fexp :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int ->
    Big.big_int * Big.big_int **)

let shl_align_fexp prec emax =
  let emin = Z.sub (Z.sub (Big.doubleplusone Big.one) emax) prec in
  let fexp = coq_FLT_exp emin prec in
  (fun mx ex -> shl_align mx ex (fexp (Z.add (digits2_pos mx) ex)))

(** val binary_round :
    Big.big_int -> Big.big_int -> mode -> bool -> Big.big_int -> Big.big_int
    -> full_float **)

let binary_round prec emax m sx mx ex =
  let (mz, ez) = shl_align_fexp prec emax mx ex in
  binary_round_aux prec emax m sx mz ez Coq_loc_Exact

(** val binary_normalize :
    Big.big_int -> Big.big_int -> mode -> Big.big_int -> Big.big_int -> bool
    -> binary_float **)

let binary_normalize prec emax mode0 m e szero =
  Big.z_case
    (fun _ -> B754_zero
    szero)
    (fun m0 ->
    match binary_round prec emax mode0 false m0 e with
    | F754_zero s -> B754_zero s
    | F754_infinity s -> B754_infinity s
    | F754_nan (b, pl) -> B754_nan (b, pl)
    | F754_finite (s, m1, e0) -> B754_finite (s, m1, e0))
    (fun m0 ->
    match binary_round prec emax mode0 true m0 e with
    | F754_zero s -> B754_zero s
    | F754_infinity s -> B754_infinity s
    | F754_nan (b, pl) -> B754_nan (b, pl)
    | F754_finite (s, m1, e0) -> B754_finite (s, m1, e0))
    m

(** val coq_Bplus :
    Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
    bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float **)

let coq_Bplus prec emax plus_nan m x y =
  let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
  (match x with
   | B754_zero sx ->
     (match y with
      | B754_zero sy ->
        if eqb sx sy
        then x
        else (match m with
              | Coq_mode_DN -> B754_zero true
              | _ -> B754_zero false)
      | B754_nan (_, _) -> f (plus_nan x y)
      | _ -> y)
   | B754_infinity sx ->
     (match y with
      | B754_infinity sy -> if eqb sx sy then x else f (plus_nan x y)
      | B754_nan (_, _) -> f (plus_nan x y)
      | _ -> x)
   | B754_nan (_, _) -> f (plus_nan x y)
   | B754_finite (sx, mx, ex) ->
     (match y with
      | B754_zero _ -> x
      | B754_infinity _ -> y
      | B754_nan (_, _) -> f (plus_nan x y)
      | B754_finite (sy, my, ey) ->
        let ez = Z.min ex ey in
        binary_normalize prec emax m
          (Z.add (cond_Zopp sx (fst (shl_align mx ex ez)))
            (cond_Zopp sy (fst (shl_align my ey ez)))) ez
          (match m with
           | Coq_mode_DN -> true
           | _ -> false)))

(** val coq_Bminus :
    Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
    bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float **)

let coq_Bminus prec emax minus_nan m x y =
  coq_Bplus prec emax minus_nan m x
    (match y with
     | B754_zero sx -> B754_zero (negb sx)
     | B754_infinity sx -> B754_infinity (negb sx)
     | B754_nan (sx, plx) -> B754_nan (sx, plx)
     | B754_finite (sx, mx, ex) -> B754_finite ((negb sx), mx, ex))

(** val coq_Fdiv_core_binary :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int
    -> (Big.big_int * Big.big_int) * location **)

let coq_Fdiv_core_binary prec m1 e1 m2 e2 =
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e = Z.sub e1 e2 in
  (Big.z_case
     (fun _ ->
     let (q, r) = coq_Zfast_div_eucl m1 m2 in
     ((q, e), (new_location m2 r Coq_loc_Exact)))
     (fun p ->
     let m = Z.shiftl m1 p in
     let e' = Z.add e (Big.opp p) in
     let (q, r) = coq_Zfast_div_eucl m m2 in
     ((q, e'), (new_location m2 r Coq_loc_Exact)))
     (fun _ ->
     let (q, r) = coq_Zfast_div_eucl m1 m2 in
     ((q, e), (new_location m2 r Coq_loc_Exact)))
     (Z.sub (Z.add d2 prec) d1))

(** val coq_Bdiv :
    Big.big_int -> Big.big_int -> (binary_float -> binary_float ->
    bool * nan_pl) -> mode -> binary_float -> binary_float -> binary_float **)

let coq_Bdiv prec emax div_nan m x y =
  let f = fun pl -> B754_nan ((fst pl), (snd pl)) in
  (match x with
   | B754_zero sx ->
     (match y with
      | B754_infinity sy -> B754_zero (xorb sx sy)
      | B754_finite (sy, _, _) -> B754_zero (xorb sx sy)
      | _ -> f (div_nan x y))
   | B754_infinity sx ->
     (match y with
      | B754_zero sy -> B754_infinity (xorb sx sy)
      | B754_finite (sy, _, _) -> B754_infinity (xorb sx sy)
      | _ -> f (div_nan x y))
   | B754_nan (_, _) -> f (div_nan x y)
   | B754_finite (sx, mx, ex) ->
     (match y with
      | B754_zero sy -> B754_infinity (xorb sx sy)
      | B754_infinity sy -> B754_zero (xorb sx sy)
      | B754_nan (_, _) -> f (div_nan x y)
      | B754_finite (sy, my, ey) ->
        (match let (p, lz) = coq_Fdiv_core_binary prec mx ex my ey in
               let (mz, ez) = p in
               (Big.z_case
                  (fun _ -> F754_nan (false,
                  Big.one))
                  (fun mz0 ->
                  binary_round_aux prec emax m (xorb sx sy) mz0 ez lz)
                  (fun _ -> F754_nan (false,
                  Big.one))
                  mz) with
         | F754_zero s -> B754_zero s
         | F754_infinity s -> B754_infinity s
         | F754_nan (b, pl) -> B754_nan (b, pl)
         | F754_finite (s, m0, e) -> B754_finite (s, m0, e))))
