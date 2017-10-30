open Datatypes
open List0
open MSetAVL
open Regexp
open Xform

type __ = Obj.t

module type RESETXFORM =
 sig
  type elt = REOrderedTypeAlt.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> Big.big_int

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool

  val re_set_type : t -> xtype

  type rs_xf_pair = t*xform

  type re_xf_pair = regexp*xform

  val union_xform : xtype -> rs_xf_pair -> rs_xf_pair -> rs_xf_pair

  val empty_xform : xtype -> rs_xf_pair

  val singleton_xform : regexp -> rs_xf_pair

  val add_xform : xtype -> re_xf_pair -> rs_xf_pair -> rs_xf_pair

  val fold_xform :
    xtype -> (re_xf_pair -> 'a1 -> 'a1) -> rs_xf_pair -> 'a1 -> 'a1

  val set_cat_re : t -> regexp -> t

  val cat_re_xform : xtype -> rs_xf_pair -> regexp -> rs_xf_pair

  val equal_xform : t -> t -> xform

  val re_set_extract_nil : t -> xt_interp list
 end

module RawRESet = Make(REOrderedType)

module Raw = RawRESet.Raw

module E =
 struct
  type t = REOrderedTypeAlt.t

  (** val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison **)

  let compare =
    REOrderedTypeAlt.compare

  (** val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool **)

  let eq_dec =
    REOrderedType.eq_dec
 end

type elt = REOrderedTypeAlt.t

type t_ =
  Raw.t
  (* singleton inductive, whose constructor was Mkt *)

(** val this : t_ -> Raw.t **)

let this t0 =
  t0

type t = t_

(** val mem : elt -> t -> bool **)

let mem x s =
  Raw.mem x (this s)

(** val add : elt -> t -> t **)

let add x s =
  Raw.add x (this s)

(** val remove : elt -> t -> t **)

let remove x s =
  Raw.remove x (this s)

(** val singleton : elt -> t **)

let singleton x =
  Raw.singleton x

(** val union : t -> t -> t **)

let union s s' =
  Raw.union (this s) (this s')

(** val inter : t -> t -> t **)

let inter s s' =
  Raw.inter (this s) (this s')

(** val diff : t -> t -> t **)

let diff s s' =
  Raw.diff (this s) (this s')

(** val equal : t -> t -> bool **)

let equal s s' =
  Raw.equal (this s) (this s')

(** val subset : t -> t -> bool **)

let subset s s' =
  Raw.subset (this s) (this s')

(** val empty : t **)

let empty =
  Raw.empty

(** val is_empty : t -> bool **)

let is_empty s =
  Raw.is_empty (this s)

(** val elements : t -> elt list **)

let elements s =
  Raw.elements (this s)

(** val choose : t -> elt option **)

let choose s =
  Raw.choose (this s)

(** val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1 **)

let fold f s =
  Raw.fold f (this s)

(** val cardinal : t -> Big.big_int **)

let cardinal s =
  Raw.cardinal (this s)

(** val filter : (elt -> bool) -> t -> t **)

let filter f s =
  Raw.filter f (this s)

(** val for_all : (elt -> bool) -> t -> bool **)

let for_all f s =
  Raw.for_all f (this s)

(** val exists_ : (elt -> bool) -> t -> bool **)

let exists_ f s =
  Raw.exists_ f (this s)

(** val partition : (elt -> bool) -> t -> t * t **)

let partition f s =
  let p = Raw.partition f (this s) in ((fst p), (snd p))

(** val eq_dec : t -> t -> bool **)

let eq_dec s0 s'0 =
  let b = Raw.equal s0 s'0 in if b then true else false

(** val compare : t -> t -> comparison **)

let compare s s' =
  Raw.compare (this s) (this s')

(** val min_elt : t -> elt option **)

let min_elt s =
  Raw.min_elt (this s)

(** val max_elt : t -> elt option **)

let max_elt s =
  Raw.max_elt (this s)

type re_xf_pair = regexp*xform

(** val tree_to_regexp : Raw.tree -> regexp **)

let rec tree_to_regexp = function
| Raw.Leaf -> Coq_rZero
| Raw.Node (_, lft, r, rgt) ->
  Coq_rAlt ((tree_to_regexp lft), (Coq_rAlt (r, (tree_to_regexp rgt))))

(** val tree_type : Raw.tree -> xtype **)

let tree_type t0 =
  regexp_type (tree_to_regexp t0)

type tree_xf_pair = Raw.tree*xform

(** val re_set_type : t -> xtype **)

let re_set_type rs =
  tree_type (this rs)

type rs_xf_pair = t*xform

(** val tree_extract_nil : Raw.tree -> xt_interp list **)

let rec tree_extract_nil = function
| Raw.Leaf -> []
| Raw.Node (_, l, x, r) ->
  let vl = tree_extract_nil l in
  let vx = regexp_extract_nil x in
  let vr = tree_extract_nil r in
  app (map (fun x0 -> Obj.magic (Coq_inl x0)) vl)
    (app (map (fun x0 -> Obj.magic (Coq_inr (Coq_inl x0))) vx)
      (map (fun x0 -> Obj.magic (Coq_inr (Coq_inr x0))) vr))

(** val re_set_extract_nil : t -> xt_interp list **)

let re_set_extract_nil s =
  tree_extract_nil (this s)

(** val empty_xform : __ -> rs_xf_pair **)

let empty_xform _ =
  empty,Xzero

(** val singleton_xform : regexp -> rs_xf_pair **)

let singleton_xform r =
  (singleton r),(match xmatch Xzero (xmatch Xid Xzero) with
                 | Xzero -> Xzero
                 | x -> Xcons (x, (xcoerce Xempty)))

(** val create_xform :
    Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair **)

let create_xform l fl x fx r fr =
  (Raw.Node
    ((Int.Z_as_Int.add (Int.Z_as_Int.max (Raw.height l) (Raw.height r))
       Big.one), l, x, r)),(xmatch fl (xmatch fx fr))

(** val find_xform : Raw.tree -> regexp -> xform **)

let rec find_xform t0 r =
  match t0 with
  | Raw.Leaf -> assert false (* absurd case *)
  | Raw.Node (_, ltree, r', rtree) ->
    (match REOrderedTypeAlt.compare r r' with
     | Eq -> xcomp Xinl Xinr
     | Lt -> let x = find_xform ltree r in xcomp x Xinl
     | Gt -> let x = find_xform rtree r in xcomp x (xcomp Xinr Xinr))

(** val inject_xform_tree : Raw.tree -> Raw.tree -> xform **)

let rec inject_xform_tree t1 t2 =
  match t1 with
  | Raw.Leaf -> Xzero
  | Raw.Node (_, t_left0, r, t_right0) ->
    xmatch (inject_xform_tree t_left0 t2)
      (xmatch (find_xform t2 r) (inject_xform_tree t_right0 t2))

(** val inject_xform : RawRESet.t -> RawRESet.t -> xform **)

let inject_xform s1 s2 =
  inject_xform_tree s1 s2

(** val equal_xform : RawRESet.t -> RawRESet.t -> xform **)

let equal_xform s1 s2 =
  inject_xform s1 s2

type ctxt =
| Hole
| LeftNode of Int.Z_as_Int.t * ctxt * REOrderedTypeAlt.t * Raw.tree
| RightNode of Int.Z_as_Int.t * Raw.tree * REOrderedTypeAlt.t * ctxt

(** val ctxt_rect :
    'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree
    -> 'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt ->
    'a1 -> 'a1) -> ctxt -> 'a1 **)

let rec ctxt_rect f f0 f1 = function
| Hole -> f
| LeftNode (t0, c0, t1, t2) -> f0 t0 c0 (ctxt_rect f f0 f1 c0) t1 t2
| RightNode (t0, t1, t2, c0) -> f1 t0 t1 t2 c0 (ctxt_rect f f0 f1 c0)

(** val ctxt_rec :
    'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree
    -> 'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt ->
    'a1 -> 'a1) -> ctxt -> 'a1 **)

let rec ctxt_rec f f0 f1 = function
| Hole -> f
| LeftNode (t0, c0, t1, t2) -> f0 t0 c0 (ctxt_rec f f0 f1 c0) t1 t2
| RightNode (t0, t1, t2, c0) -> f1 t0 t1 t2 c0 (ctxt_rec f f0 f1 c0)

(** val fill : ctxt -> Raw.tree -> Raw.tree **)

let rec fill c t0 =
  match c with
  | Hole -> t0
  | LeftNode (i, c', x, r) -> Raw.Node (i, (fill c' t0), x, r)
  | RightNode (i, l, x, c') -> Raw.Node (i, l, x, (fill c' t0))

(** val fill_ctxt : ctxt -> ctxt -> ctxt **)

let rec fill_ctxt c1 c2 =
  match c1 with
  | Hole -> c2
  | LeftNode (i, c, x, r) -> LeftNode (i, (fill_ctxt c c2), x, r)
  | RightNode (i, l, x, c) -> RightNode (i, l, x, (fill_ctxt c c2))

(** val cast : 'a1 -> 'a2 **)

let cast x =
  Obj.magic x

(** val find_subtree' : Raw.tree -> ctxt -> xform **)

let rec find_subtree' t1 = function
| Hole -> Xid
| LeftNode (_, c1', _, _) -> xcomp (find_subtree' t1 c1') Xinl
| RightNode (_, _, _, c1') -> xcomp (find_subtree' t1 c1') (xcomp Xinr Xinr)

(** val find_subtree : Raw.tree -> Raw.tree -> ctxt -> xform **)

let find_subtree _ t1 c1 =
  xcoerce (find_subtree' t1 c1)

(** val assert_false_xform :
    Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair **)

let assert_false_xform l fl x fx r fr =
  create_xform l fl x fx r fr

(** val bal_xform :
    Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair **)

let bal_xform l fl x fx r fr =
  let hl = Raw.height l in
  let hr = Raw.height r in
  if Int.Z_as_Int.ltb (Int.Z_as_Int.add hr (Big.double Big.one)) hl
  then (match l with
        | Raw.Leaf -> assert_false_xform l fl x fx r fr
        | Raw.Node (_, ll, lx, lr) ->
          if Int.Z_as_Int.leb (Raw.height lr) (Raw.height ll)
          then let r',fr' =
                 create_xform lr (xcomp (xcomp Xinr Xinr) fl) x fx r fr
               in
               create_xform ll (xcomp Xinl fl) lx
                 (xcomp (xcomp Xinl Xinr) fl) r' fr'
          else (match lr with
                | Raw.Leaf -> assert_false_xform l fl x fx r fr
                | Raw.Node (_, lrl, lrx, lrr) ->
                  let l',fl' =
                    create_xform ll (xcomp Xinl fl) lx
                      (xcomp (xcomp Xinl Xinr) fl) lrl
                      (xcomp (xcomp Xinl (xcomp Xinr Xinr)) fl)
                  in
                  let r',fr' =
                    create_xform lrr
                      (xcomp (xcomp Xinr (xcomp Xinr (xcomp Xinr Xinr))) fl)
                      x fx r fr
                  in
                  create_xform l' fl' lrx
                    (xcomp (xcomp Xinl (xcomp Xinr (xcomp Xinr Xinr))) fl) r'
                    fr'))
  else if Int.Z_as_Int.ltb (Int.Z_as_Int.add hl (Big.double Big.one)) hr
       then (match r with
             | Raw.Leaf -> assert_false_xform l fl x fx r fr
             | Raw.Node (_, rl, rx, rr) ->
               if Int.Z_as_Int.leb (Raw.height rl) (Raw.height rr)
               then let l',f' = create_xform l fl x fx rl (xcomp Xinl fr) in
                    create_xform l' f' rx (xcomp (xcomp Xinl Xinr) fr) rr
                      (xcomp (xcomp Xinr Xinr) fr)
               else (match rl with
                     | Raw.Leaf -> assert_false_xform l fl x fx r fr
                     | Raw.Node (_, rll, rlx, rlr) ->
                       let l',fl' =
                         create_xform l fl x fx rll
                           (xcomp (xcomp Xinl Xinl) fr)
                       in
                       let r',fr' =
                         create_xform rlr
                           (xcomp (xcomp Xinr (xcomp Xinr Xinl)) fr) rx
                           (xcomp (xcomp Xinl Xinr) fr) rr
                           (xcomp (xcomp Xinr Xinr) fr)
                       in
                       create_xform l' fl' rlx
                         (xcomp (xcomp Xinl (xcomp Xinr Xinl)) fr) r' fr'))
       else create_xform l fl x fx r fr

(** val add_xform_tree :
    regexp -> xform -> Raw.tree -> xform -> Raw.tree*xform **)

let rec add_xform_tree x f1 s f2 =
  match s with
  | Raw.Leaf ->
    (Raw.Node (Big.one, Raw.Leaf, x,
      Raw.Leaf)),(xcomp (xmatch Xzero (xmatch Xid Xzero)) f1)
  | Raw.Node (h, l, y, r) ->
    (match REOrderedTypeAlt.compare x y with
     | Eq ->
       (Raw.Node (h, l, y,
         r)),(xmatch (xcomp Xinl f2)
               (xmatch
                 (xcomp
                   (match xcomp (xcomp Xinl Xinr) f2 with
                    | Xzero -> Xzero
                    | Xfst -> xpair_fst f1
                    | x0 ->
                      (match f1 with
                       | Xzero -> Xzero
                       | x1 -> Xpair (x0, x1)))
                   (xopt (xfoldr (Xcons (Xfst, (xcoerce Xsnd))) Xsnd Xfst)))
                 (xcomp (xcomp Xinr Xinr) f2)))
     | Lt ->
       let l',f' = add_xform_tree x f1 l (xcomp Xinl f2) in
       bal_xform l' f' y (xcomp (xcomp Xinl Xinr) f2) r
         (xcomp (xcomp Xinr Xinr) f2)
     | Gt ->
       let r',f' = add_xform_tree x f1 r (xcomp (xcomp Xinr Xinr) f2) in
       bal_xform l (xcomp Xinl f2) y (xcomp (xcomp Xinl Xinr) f2) r' f')

(** val join_xform :
    Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform ->
    Raw.tree*xform **)

let rec join_xform l x =
  match l with
  | Raw.Leaf -> add_xform_tree
  | Raw.Node (lh, ll, lx, lr) ->
    (fun x0 fx ->
      let rec join_aux r x1 =
        match r with
        | Raw.Leaf -> add_xform_tree x0 fx (Raw.Node (lh, ll, lx, lr)) x
        | Raw.Node (rh, rl, rx, rr) ->
          if Int.Z_as_Int.ltb (Int.Z_as_Int.add rh Int.Z_as_Int._2) lh
          then let r',fr' =
                 join_xform lr (xcomp (xcomp Xinr Xinr) x) x0 fx (Raw.Node
                   (rh, rl, rx, rr)) x1
               in
               bal_xform ll (xcomp Xinl x) lx (xcomp (xcomp Xinl Xinr) x) r'
                 fr'
          else if Int.Z_as_Int.ltb (Int.Z_as_Int.add lh Int.Z_as_Int._2) rh
               then let l',fl' = join_aux rl (xcomp Xinl x1) in
                    bal_xform l' fl' rx (xcomp (xcomp Xinl Xinr) x1) rr
                      (xcomp (xcomp Xinr Xinr) x1)
               else create_xform (Raw.Node (lh, ll, lx, lr)) x x0 fx
                      (Raw.Node (rh, rl, rx, rr)) x1
      in join_aux)

type triple_xform = { t_left : Raw.tree; t_left_xform : xform;
                      t_in : xform option; t_right : Raw.tree;
                      t_right_xform : xform }

(** val t_left : xtype -> regexp -> triple_xform -> Raw.tree **)

let t_left _ _ x = x.t_left

(** val t_left_xform : xtype -> regexp -> triple_xform -> xform **)

let t_left_xform _ _ x = x.t_left_xform

(** val t_in : xtype -> regexp -> triple_xform -> xform option **)

let t_in _ _ x = x.t_in

(** val t_right : xtype -> regexp -> triple_xform -> Raw.tree **)

let t_right _ _ x = x.t_right

(** val t_right_xform : xtype -> regexp -> triple_xform -> xform **)

let t_right_xform _ _ x = x.t_right_xform

(** val split_xform : regexp -> Raw.tree -> xform -> triple_xform **)

let rec split_xform x s f =
  match s with
  | Raw.Leaf ->
    { t_left = Raw.Leaf; t_left_xform = Xzero; t_in = None; t_right =
      Raw.Leaf; t_right_xform = Xzero }
  | Raw.Node (_, l, y, r) ->
    (match REOrderedTypeAlt.compare x y with
     | Eq ->
       { t_left = l; t_left_xform = (xcomp Xinl f); t_in = (Some
         (xcomp (xcomp Xinl Xinr) f)); t_right = r; t_right_xform =
         (xcomp (xcomp Xinr Xinr) f) }
     | Lt ->
       let { t_left = ll; t_left_xform = fll; t_in = opt; t_right = rl;
         t_right_xform = frl } = split_xform x l (xcomp Xinl f)
       in
       let r',fr' =
         join_xform rl frl y (xcomp (xcomp Xinl Xinr) f) r
           (xcomp (xcomp Xinr Xinr) f)
       in
       { t_left = ll; t_left_xform = fll; t_in = opt; t_right = r';
       t_right_xform = fr' }
     | Gt ->
       let { t_left = rl; t_left_xform = frl; t_in = opt; t_right = rr;
         t_right_xform = frr } = split_xform x r (xcomp (xcomp Xinr Xinr) f)
       in
       let l',fl' =
         join_xform l (xcomp Xinl f) y (xcomp (xcomp Xinl Xinr) f) rl frl
       in
       { t_left = l'; t_left_xform = fl'; t_in = opt; t_right = rr;
       t_right_xform = frr })

(** val union_xform_tree :
    Raw.tree -> xform -> Raw.tree -> xform -> Raw.tree*xform **)

let rec union_xform_tree s1 x s2 f2 =
  match s1 with
  | Raw.Leaf -> s2,f2
  | Raw.Node (i, l1, x1, r1) ->
    (match s2 with
     | Raw.Leaf -> (Raw.Node (i, l1, x1, r1)),x
     | Raw.Node (_, _, _, _) ->
       let { t_left = l2'; t_left_xform = fl2'; t_in = opt; t_right = r2';
         t_right_xform = fr2' } = split_xform x1 s2 f2
       in
       let l',fl' = union_xform_tree l1 (xcomp Xinl x) l2' fl2' in
       let r',fr' = union_xform_tree r1 (xcomp (xcomp Xinr Xinr) x) r2' fr2'
       in
       let xf1 = xcomp (xcomp Xinl Xinr) x in
       let xf =
         match opt with
         | Some fother ->
           xcomp
             (match xf1 with
              | Xzero -> Xzero
              | Xfst -> xpair_fst fother
              | x0 ->
                (match fother with
                 | Xzero -> Xzero
                 | x2 -> Xpair (x0, x2)))
             (xopt (xfoldr (Xcons (Xfst, (xcoerce Xsnd))) Xsnd Xfst))
         | None -> xf1
       in
       join_xform l' fl' x1 xf r' fr')

(** val add_xform : re_xf_pair -> rs_xf_pair -> rs_xf_pair **)

let add_xform refx rs =
  let x,fx = refx in
  let s,fs = rs in
  let p = add_xform_tree x fx s fs in let t',ft' = p in t',ft'

(** val union_xform : rs_xf_pair -> rs_xf_pair -> rs_xf_pair **)

let union_xform rs1 rs2 =
  let s1,f1 = rs1 in
  let s2,f2 = rs2 in
  let p = union_xform_tree s1 f1 s2 f2 in let t0,f0 = p in t0,f0

(** val fold_tree_xform :
    (re_xf_pair -> 'a1 -> 'a1) -> Raw.tree -> xform -> 'a1 -> 'a1 **)

let rec fold_tree_xform f s x v =
  match s with
  | Raw.Leaf -> v
  | Raw.Node (_, l, x0, r) ->
    fold_tree_xform f r (xcomp (xcomp Xinr Xinr) x)
      (f (x0,(xcomp (xcomp Xinl Xinr) x))
        (fold_tree_xform f l (xcomp Xinl x) v))

(** val fold_xform :
    (re_xf_pair -> 'a1 -> 'a1) -> rs_xf_pair -> 'a1 -> 'a1 **)

let fold_xform comb rx a =
  let s1,f1 = rx in fold_tree_xform comb s1 f1 a

(** val map_xform : (re_xf_pair -> re_xf_pair) -> rs_xf_pair -> rs_xf_pair **)

let map_xform f s =
  fold_xform (fun x -> add_xform (f x)) s (empty,Xzero)

(** val set_cat_re : RawRESet.t -> regexp -> RawRESet.t **)

let set_cat_re s r = match r with
| Coq_rEps -> s
| Coq_rZero -> RawRESet.empty
| _ ->
  RawRESet.fold (fun r1 s' -> RawRESet.add (Coq_rCat (r1, r)) s') s
    RawRESet.empty

(** val simple_cat_re_xform : rs_xf_pair -> regexp -> rs_xf_pair **)

let simple_cat_re_xform s r =
  map_xform (fun xf ->
    let x,f = xf in
    (Coq_rCat (x,
    r)),(xcomp
          (match xcomp Xfst f with
           | Xzero -> Xzero
           | x0 -> Xpair (Xsnd, x0)) (xmapenv (Xpair (Xsnd, Xfst))))) s

(** val cat_re_xform : rs_xf_pair -> regexp -> rs_xf_pair **)

let cat_re_xform s = function
| Coq_rEps ->
  let raw_set,f = s in raw_set,(xcomp f (xmap (Xpair (Xid, Xunit))))
| Coq_rZero -> RawRESet.empty,Xzero
| x -> simple_cat_re_xform s x
