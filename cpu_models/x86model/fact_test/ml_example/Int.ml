open BinInt

module type Int =
 sig
  type t

  val i2z : t -> Big.big_int

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> bool

  val ge_lt_dec : t -> t -> bool

  val eq_dec : t -> t -> bool
 end

module Z_as_Int =
 struct
  type t = Big.big_int

  (** val _0 : Big.big_int **)

  let _0 =
    Big.zero

  (** val _1 : Big.big_int **)

  let _1 =
    Big.one

  (** val _2 : Big.big_int **)

  let _2 =
    (Big.double Big.one)

  (** val _3 : Big.big_int **)

  let _3 =
    (Big.doubleplusone Big.one)

  (** val add : Big.big_int -> Big.big_int -> Big.big_int **)

  let add =
    Z.add

  (** val opp : Big.big_int -> Big.big_int **)

  let opp =
    Z.opp

  (** val sub : Big.big_int -> Big.big_int -> Big.big_int **)

  let sub =
    Z.sub

  (** val mul : Big.big_int -> Big.big_int -> Big.big_int **)

  let mul =
    Z.mul

  (** val max : Big.big_int -> Big.big_int -> Big.big_int **)

  let max =
    Z.max

  (** val eqb : Big.big_int -> Big.big_int -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : Big.big_int -> Big.big_int -> bool **)

  let ltb =
    Z.ltb

  (** val leb : Big.big_int -> Big.big_int -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : Big.big_int -> Big.big_int -> bool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : Big.big_int -> Big.big_int -> bool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in if b then true else false

  (** val ge_lt_dec : Big.big_int -> Big.big_int -> bool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in if b then false else true

  (** val i2z : t -> Big.big_int **)

  let i2z n =
    n
 end
