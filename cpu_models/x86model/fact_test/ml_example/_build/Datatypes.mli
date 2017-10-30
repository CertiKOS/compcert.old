val xorb : bool -> bool -> bool

val negb : bool -> bool

type ('a, 'b) sum =
| Coq_inl of 'a
| Coq_inr of 'b

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> Big.big_int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type coq_CompareSpecT =
| CompEqT
| CompLtT
| CompGtT

val coq_CompareSpec2Type : comparison -> coq_CompareSpecT
