type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type 'm coq_Monad = { coq_Return : (__ -> __ -> 'm);
                      coq_Bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

(** val coq_Return : 'a1 coq_Monad -> 'a2 -> 'a1 **)

let coq_Return monad x =
  let { coq_Return = return; coq_Bind = _ } = monad in Obj.magic return __ x

(** val coq_Bind : 'a1 coq_Monad -> 'a1 -> ('a2 -> 'a1) -> 'a1 **)

let coq_Bind monad x x0 =
  let { coq_Return = _; coq_Bind = bind } = monad in
  Obj.magic bind __ __ x x0

(** val coq_OptionMonad : __ option coq_Monad **)

let coq_OptionMonad =
  { coq_Return = (fun _ x -> Some x); coq_Bind = (fun _ _ c f ->
    match c with
    | Some v -> f v
    | None -> None) }
