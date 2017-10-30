open Datatypes

module PTree =
 struct
  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> 'a1 option -> 'a1 tree -> 'a2 -> 'a2) -> 'a1
      tree -> 'a2 **)

  let rec tree_rect f f0 = function
  | Leaf -> f
  | Node (t1, o, t2) -> f0 t1 (tree_rect f f0 t1) o t2 (tree_rect f f0 t2)

  type 'a t = 'a tree

  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec eq eqA a b =
    match a with
    | Leaf ->
      (match b with
       | Leaf -> true
       | Node (_, _, _) -> false)
    | Node (t0, o, t1) ->
      (match b with
       | Leaf -> false
       | Node (t2, o0, t3) ->
         if eq eqA t0 t2
         then if match o with
                 | Some x ->
                   (match o0 with
                    | Some a2 -> eqA x a2
                    | None -> false)
                 | None ->
                   (match o0 with
                    | Some _ -> false
                    | None -> true)
              then eq eqA t1 t3
              else false
         else false)

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val get : Big.big_int -> 'a1 t -> 'a1 option **)

  let rec get i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (Big.positive_case
       (fun ii ->
       get ii r)
       (fun ii ->
       get ii l)
       (fun _ ->
       o)
       i)

  (** val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec set i v = function
  | Leaf ->
    (Big.positive_case
       (fun ii -> Node (Leaf, None,
       (set ii v Leaf)))
       (fun ii -> Node ((set ii v Leaf), None,
       Leaf))
       (fun _ -> Node (Leaf, (Some v),
       Leaf))
       i)
  | Node (l, o, r) ->
    (Big.positive_case
       (fun ii -> Node (l, o,
       (set ii v r)))
       (fun ii -> Node ((set ii v l), o,
       r))
       (fun _ -> Node (l, (Some v),
       r))
       i)

  (** val append : Big.big_int -> Big.big_int -> Big.big_int **)

  let rec append i j =
    Big.positive_case
      (fun ii -> Big.doubleplusone
      (append ii j))
      (fun ii -> Big.double
      (append ii j))
      (fun _ ->
      j)
      i

  (** val xmap :
      (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> Big.big_int -> 'a2 t **)

  let rec xmap f m i =
    match m with
    | Leaf -> Leaf
    | Node (l, o, r) ->
      Node ((xmap f l (append i (Big.double Big.one))),
        (match o with
         | Some y -> Some (f i y)
         | None -> None), (xmap f r (append i (Big.doubleplusone Big.one))))

  (** val map : (Big.big_int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    xmap f m Big.one
 end

module PMap =
 struct
  type 'a t = 'a * 'a PTree.t

  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let eq x a b =
    let x0 = PTree.eq x in
    let (x1, x2) = a in
    let (a1, t0) = b in if x x1 a1 then x0 x2 t0 else false

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init x =
    (x, PTree.empty)

  (** val get : Big.big_int -> 'a1 t -> 'a1 **)

  let get i m =
    match PTree.get i (snd m) with
    | Some x -> x
    | None -> fst m

  (** val set : Big.big_int -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)

  let set i x m =
    ((fst m), (PTree.set i x (snd m)))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    ((f (fst m)), (PTree.map (fun _ -> f) (snd m)))
 end

module type INDEXED_TYPE =
 sig
  type t

  val index : t -> Big.big_int

  val eq : t -> t -> bool
 end

module IMap =
 functor (X:INDEXED_TYPE) ->
 struct
  type elt = X.t

  (** val elt_eq : X.t -> X.t -> bool **)

  let elt_eq =
    X.eq

  type 'x t = 'x PMap.t

  (** val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let eq x a b =
    PMap.eq x a b

  (** val init : 'a1 -> 'a1 * 'a1 PTree.t **)

  let init x =
    PMap.init x

  (** val get : X.t -> 'a1 t -> 'a1 **)

  let get i m =
    PMap.get (X.index i) m

  (** val set : X.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t **)

  let set i v m =
    PMap.set (X.index i) v m

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map f m =
    PMap.map f m
 end

module ZIndexed =
 struct
  (** val index : Big.big_int -> Big.big_int **)

  let index z =
    Big.z_case
      (fun _ ->
      Big.one)
      (fun p -> Big.double
      p)
      (fun p -> Big.doubleplusone
      p)
      z
 end
