open BinInt
open Fappli_IEEE
open Zbool

(** val join_bits :
    Big.big_int -> Big.big_int -> bool -> Big.big_int -> Big.big_int ->
    Big.big_int **)

let join_bits mw ew s m e =
  Z.add
    (Z.shiftl
      (Z.add
        (if s
         then (Big.z_case
                 (fun _ ->
                 Big.one)
                 (fun p ->
                 Z.pow_pos (Big.double Big.one) p)
                 (fun _ ->
                 Big.zero)
                 ew)
         else Big.zero) e) mw) m

(** val split_bits :
    Big.big_int -> Big.big_int -> Big.big_int ->
    (bool * Big.big_int) * Big.big_int **)

let split_bits mw ew x =
  let mm =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      Z.pow_pos (Big.double Big.one) p)
      (fun _ ->
      Big.zero)
      mw
  in
  let em =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      Z.pow_pos (Big.double Big.one) p)
      (fun _ ->
      Big.zero)
      ew
  in
  (((Z.leb (Z.mul mm em) x), (Z.modulo x mm)), (Z.modulo (Z.div x mm) em))

(** val bits_of_binary_float :
    Big.big_int -> Big.big_int -> binary_float -> Big.big_int **)

let bits_of_binary_float mw ew =
  let emax =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      Z.pow_pos (Big.double Big.one) p)
      (fun _ ->
      Big.zero)
      (Z.sub ew Big.one)
  in
  let prec = Z.add mw Big.one in
  let emin = Z.sub (Z.sub (Big.doubleplusone Big.one) emax) prec in
  (fun x ->
  match x with
  | B754_zero sx -> join_bits mw ew sx Big.zero Big.zero
  | B754_infinity sx ->
    join_bits mw ew sx Big.zero
      (Z.sub
        (Big.z_case
           (fun _ ->
           Big.one)
           (fun p ->
           Z.pow_pos (Big.double Big.one) p)
           (fun _ ->
           Big.zero)
           ew) Big.one)
  | B754_nan (sx, n) ->
    join_bits mw ew sx n
      (Z.sub
        (Big.z_case
           (fun _ ->
           Big.one)
           (fun p ->
           Z.pow_pos (Big.double Big.one) p)
           (fun _ ->
           Big.zero)
           ew) Big.one)
  | B754_finite (sx, mx, ex) ->
    let m =
      Z.sub mx
        (Big.z_case
           (fun _ ->
           Big.one)
           (fun p ->
           Z.pow_pos (Big.double Big.one) p)
           (fun _ ->
           Big.zero)
           mw)
    in
    if Z.leb Big.zero m
    then join_bits mw ew sx m (Z.add (Z.sub ex emin) Big.one)
    else join_bits mw ew sx mx Big.zero)

(** val binary_float_of_bits_aux :
    Big.big_int -> Big.big_int -> Big.big_int -> full_float **)

let binary_float_of_bits_aux mw ew =
  let emax =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p ->
      Z.pow_pos (Big.double Big.one) p)
      (fun _ ->
      Big.zero)
      (Z.sub ew Big.one)
  in
  let prec = Z.add mw Big.one in
  let emin = Z.sub (Z.sub (Big.doubleplusone Big.one) emax) prec in
  (fun x ->
  let (p, ex) = split_bits mw ew x in
  let (sx, mx) = p in
  if coq_Zeq_bool ex Big.zero
  then (Big.z_case
          (fun _ -> F754_zero
          sx)
          (fun px -> F754_finite (sx, px,
          emin))
          (fun _ -> F754_nan (false,
          Big.one))
          mx)
  else if coq_Zeq_bool ex
            (Z.sub
              (Big.z_case
                 (fun _ ->
                 Big.one)
                 (fun p0 ->
                 Z.pow_pos (Big.double Big.one) p0)
                 (fun _ ->
                 Big.zero)
                 ew) Big.one)
       then (Big.z_case
               (fun _ -> F754_infinity
               sx)
               (fun plx -> F754_nan (sx,
               plx))
               (fun _ -> F754_nan (false,
               Big.one))
               mx)
       else (Big.z_case
               (fun _ -> F754_nan (false,
               Big.one))
               (fun px -> F754_finite (sx, px,
               (Z.sub (Z.add ex emin) Big.one)))
               (fun _ -> F754_nan (false,
               Big.one))
               (Z.add mx
                 (Big.z_case
                    (fun _ ->
                    Big.one)
                    (fun p0 ->
                    Z.pow_pos (Big.double Big.one) p0)
                    (fun _ ->
                    Big.zero)
                    mw))))

(** val binary_float_of_bits :
    Big.big_int -> Big.big_int -> Big.big_int -> binary_float **)

let binary_float_of_bits mw ew x =
  match binary_float_of_bits_aux mw ew x with
  | F754_zero s -> B754_zero s
  | F754_infinity s -> B754_infinity s
  | F754_nan (b, pl) -> B754_nan (b, pl)
  | F754_finite (s, m, e) -> B754_finite (s, m, e)
