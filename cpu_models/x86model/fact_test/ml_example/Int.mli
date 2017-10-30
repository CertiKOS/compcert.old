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

module Z_as_Int :
 sig
  type t = Big.big_int

  val _0 : Big.big_int

  val _1 : Big.big_int

  val _2 : Big.big_int

  val _3 : Big.big_int

  val add : Big.big_int -> Big.big_int -> Big.big_int

  val opp : Big.big_int -> Big.big_int

  val sub : Big.big_int -> Big.big_int -> Big.big_int

  val mul : Big.big_int -> Big.big_int -> Big.big_int

  val max : Big.big_int -> Big.big_int -> Big.big_int

  val eqb : Big.big_int -> Big.big_int -> bool

  val ltb : Big.big_int -> Big.big_int -> bool

  val leb : Big.big_int -> Big.big_int -> bool

  val eq_dec : Big.big_int -> Big.big_int -> bool

  val gt_le_dec : Big.big_int -> Big.big_int -> bool

  val ge_lt_dec : Big.big_int -> Big.big_int -> bool

  val i2z : t -> Big.big_int
 end
