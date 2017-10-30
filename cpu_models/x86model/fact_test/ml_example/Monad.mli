type __ = Obj.t

type 'm coq_Monad = { coq_Return : (__ -> __ -> 'm);
                      coq_Bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val coq_Return : 'a1 coq_Monad -> 'a2 -> 'a1

val coq_Bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

val coq_OptionMonad : __ option coq_Monad
