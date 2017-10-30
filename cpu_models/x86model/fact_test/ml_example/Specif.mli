type 'a coq_sig =
  'a
  (* singleton inductive, whose constructor was exist *)

val projT1 : ('a1*'a2) -> 'a1

val projT2 : ('a1*'a2) -> 'a2


