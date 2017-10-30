type 'a coq_sig =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val projT1 : ('a1*'a2) -> 'a1 **)

let projT1 = function
| a,_ -> a

(** val projT2 : ('a1*'a2) -> 'a2 **)

let projT2 = function
| _,h -> h


