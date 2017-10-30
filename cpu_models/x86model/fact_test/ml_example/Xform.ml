open Datatypes
open List0
open ParserArg

type __ = Obj.t

type xtype =
| Coq_xUnit_t
| Coq_xChar_t
| Coq_xVoid_t
| Coq_xPair_t of xtype * xtype
| Coq_xSum_t of xtype * xtype
| Coq_xList_t of xtype

type xt_interp = __

type xform =
| Xid
| Xzero
| Xcomp of xform * xform
| Xchar of X86_PARSER_ARG.char_p
| Xunit
| Xempty
| Xpair of xform * xform
| Xfst
| Xsnd
| Xinl
| Xinr
| Xmatch of xform * xform
| Xcons of xform * xform
| Xfoldr of xform * xform * xform

(** val xinterp : xform -> xt_interp -> xt_interp **)

let rec xinterp = function
| Xid -> (fun x0 -> x0)
| Xzero -> Obj.magic (fun _ -> assert false (* absurd case *))
| Xcomp (f1, f2) ->
  let f1' = xinterp f1 in let f2' = xinterp f2 in (fun x0 -> f2' (f1' x0))
| Xchar c -> (fun _ -> Obj.magic c)
| Xunit -> (fun _ -> Obj.magic ())
| Xempty -> (fun _ -> Obj.magic [])
| Xpair (f1, f2) ->
  let f1' = xinterp f1 in
  let f2' = xinterp f2 in (fun x0 -> Obj.magic ((f1' x0), (f2' x0)))
| Xfst -> Obj.magic fst
| Xsnd -> Obj.magic snd
| Xinl -> Obj.magic (fun x0 -> Coq_inl x0)
| Xinr -> Obj.magic (fun x0 -> Coq_inr x0)
| Xmatch (f1, f2) ->
  let f1' = xinterp f1 in
  let f2' = xinterp f2 in
  (fun x0 ->
  match Obj.magic x0 with
  | Coq_inl x1 -> f1' x1
  | Coq_inr x2 -> f2' x2)
| Xcons (f1, f2) ->
  let f1' = xinterp f1 in
  let f2' = xinterp f2 in
  (fun x0 -> Obj.magic ((f1' x0) :: (Obj.magic f2' x0)))
| Xfoldr (f1, f2, f3) ->
  let f1' = xinterp f1 in
  let f2' = xinterp f2 in
  let f3' = xinterp f3 in
  (fun x0 ->
  fold_right (fun a b -> Obj.magic f1' (a, b)) (f2' x0) (Obj.magic f3' x0))

(** val xcoerce : xform -> xform **)

let xcoerce x =
  x

(** val xchar : X86_PARSER_ARG.char_p -> xform **)

let xchar c =
  Xchar c

(** val xpair_fst : xform -> xform **)

let xpair_fst = function
| Xzero -> Xzero
| Xfst -> Xpair ((xcoerce Xfst), Xfst)
| Xsnd -> xcoerce Xid
| x -> Xpair ((xcoerce Xfst), x)

(** val xmatch_inl : xform -> xform **)

let xmatch_inl = function
| Xinl -> Xmatch (Xinl, (xcoerce Xinl))
| Xinr -> xcoerce Xid
| x -> Xmatch (Xinl, (xcoerce x))

(** val xmatch_empty : xform -> xform **)

let xmatch_empty = function
| Xempty -> Xempty
| x -> Xmatch (Xempty, (xcoerce x))

(** val xmatch : xform -> xform -> xform **)

let xmatch x1 x2 =
  match x1 with
  | Xempty -> xmatch_empty x2
  | Xinl -> xmatch_inl x2
  | x -> Xmatch (x, x2)

(** val xcomp_pair : xform -> xform -> xform -> xform **)

let rec xcomp_pair x2 x11 x12 =
  match x2 with
  | Xid -> xcoerce (Xpair (x11, x12))
  | Xzero ->
    Xcomp
      ((match x11 with
        | Xzero -> Xzero
        | Xfst -> xpair_fst x12
        | x ->
          (match x12 with
           | Xzero -> Xzero
           | x0 -> Xpair (x, x0))), (xcoerce Xzero))
  | Xchar c -> Xchar c
  | Xunit -> Xunit
  | Xempty -> Xempty
  | Xpair (x21, x22) ->
    (match xcomp_pair x21 x11 x12 with
     | Xzero -> Xzero
     | Xfst -> xpair_fst (xcomp_pair x22 x11 x12)
     | x ->
       (match xcomp_pair x22 x11 x12 with
        | Xzero -> Xzero
        | x0 -> Xpair (x, x0)))
  | Xfst -> xcoerce x11
  | Xsnd -> xcoerce x12
  | x ->
    Xcomp
      ((match x11 with
        | Xzero -> Xzero
        | Xfst -> xpair_fst x12
        | x0 ->
          (match x12 with
           | Xzero -> Xzero
           | x1 -> Xpair (x0, x1))), (xcoerce x))

(** val xcomp_inl : xform -> xform **)

let xcomp_inl = function
| Xid -> xcoerce Xinl
| Xchar c -> Xchar c
| Xunit -> Xunit
| Xempty -> Xempty
| Xinl -> Xcomp (Xinl, (xcoerce Xinl))
| Xmatch (x21, _) -> xcoerce x21
| x -> Xcomp (Xinl, (xcoerce x))

(** val xcomp_inr : xform -> xform **)

let xcomp_inr = function
| Xid -> xcoerce Xinr
| Xchar c -> Xchar c
| Xunit -> Xunit
| Xempty -> Xempty
| Xinr -> Xcomp (Xinr, (xcoerce Xinr))
| Xmatch (_, x22) -> xcoerce x22
| x -> Xcomp (Xinr, (xcoerce x))

(** val xcomp_empty : xform -> xform **)

let xcomp_empty = function
| Xid -> xcoerce Xempty
| Xchar c -> Xchar c
| Xunit -> Xunit
| Xempty -> Xempty
| x -> Xcomp (Xempty, (xcoerce x))

(** val xcomp_cons : xform -> xform -> xform -> xform **)

let xcomp_cons x2 x11 x12 =
  match x2 with
  | Xid -> xcoerce (Xcons (x11, x12))
  | Xzero ->
    Xcomp
      ((match x11 with
        | Xzero -> Xzero
        | x ->
          (match x12 with
           | Xzero -> Xzero
           | x0 -> Xcons (x, (xcoerce x0)))), (xcoerce Xzero))
  | Xchar c -> Xchar c
  | Xunit -> Xunit
  | Xempty -> Xempty
  | x ->
    Xcomp
      ((match x11 with
        | Xzero -> Xzero
        | x0 ->
          (match x12 with
           | Xzero -> Xzero
           | x1 -> Xcons (x0, (xcoerce x1)))), (xcoerce x))

(** val xfoldr' : xform -> xform -> xform -> xform **)

let rec xfoldr' x3 x x0 =
  match x3 with
  | Xzero -> Xzero
  | Xempty -> x0
  | Xmatch (x31, x32) ->
    Xmatch ((xfoldr' x31 x (Xcomp (Xinl, x0))),
      (xfoldr' x32 x (Xcomp (Xinr, x0))))
  | Xcons (x31, x32) ->
    Xcomp
      ((match xcoerce x31 with
        | Xzero -> Xzero
        | Xfst -> xpair_fst (xfoldr' x32 (xcoerce x) x0)
        | x1 ->
          (match xfoldr' x32 (xcoerce x) x0 with
           | Xzero -> Xzero
           | x2 -> Xpair (x1, x2))), x)
  | x1 -> Xfoldr (x, x0, (xcoerce x1))

(** val xfoldr : xform -> xform -> xform -> xform **)

let xfoldr x1 x2 x3 =
  xfoldr' x3 x1 x2

(** val xcomp_r : xform -> xform -> xform **)

let rec xcomp_r x2 x =
  match x2 with
  | Xid -> x
  | Xchar c -> Xchar c
  | Xunit -> Xunit
  | Xempty -> Xempty
  | Xpair (x21, x22) ->
    (match xcomp_r x21 x with
     | Xzero -> Xzero
     | Xfst -> xpair_fst (xcomp_r x22 x)
     | x0 ->
       (match xcomp_r x22 x with
        | Xzero -> Xzero
        | x1 -> Xpair (x0, x1)))
  | Xcons (x21, x22) ->
    (match xcomp_r x21 x with
     | Xzero -> Xzero
     | x0 ->
       (match xcomp_r x22 x with
        | Xzero -> Xzero
        | x1 -> Xcons (x0, (xcoerce x1))))
  | Xfoldr (x21, x22, x23) -> xfoldr x21 (xcomp_r x22 x) (xcomp_r x23 x)
  | x0 -> Xcomp (x, x0)

(** val xcomp : xform -> xform -> xform **)

let rec xcomp x1 x =
  match x1 with
  | Xid -> x
  | Xzero -> Xzero
  | Xcomp (x11, x12) -> xcomp x11 (xcomp x12 x)
  | Xempty -> xcomp_empty x
  | Xpair (x11, x12) -> xcomp_pair x x11 x12
  | Xinl -> xcomp_inl x
  | Xinr -> xcomp_inr x
  | Xmatch (x11, x12) -> xmatch (xcomp x11 x) (xcomp x12 x)
  | Xcons (x11, x12) -> xcomp_cons x x11 x12
  | x0 -> xcomp_r x x0

(** val xcomp' : xform -> xform -> xform **)

let rec xcomp' x2 x =
  match x2 with
  | Xcomp (x21, x22) -> xcomp' x22 (xcomp' x21 x)
  | Xpair (x21, x22) ->
    (match xcomp' x21 x with
     | Xzero -> Xzero
     | Xfst -> xpair_fst (xcomp' x22 x)
     | x0 ->
       (match xcomp' x22 x with
        | Xzero -> Xzero
        | x1 -> Xpair (x0, x1)))
  | Xcons (x21, x22) ->
    (match xcomp' x21 x with
     | Xzero -> Xzero
     | x0 ->
       (match xcomp' x22 x with
        | Xzero -> Xzero
        | x1 -> Xcons (x0, (xcoerce x1))))
  | Xfoldr (x21, x22, x23) -> xfoldr x21 (xcomp' x22 x) (xcomp' x23 x)
  | x0 -> xcomp x x0

(** val xopt : xform -> xform **)

let rec xopt = function
| Xcomp (x1, x2) -> xcomp' (xopt x2) (xopt x1)
| Xpair (x1, x2) ->
  (match xopt x1 with
   | Xzero -> Xzero
   | Xfst -> xpair_fst (xopt x2)
   | x0 ->
     (match xopt x2 with
      | Xzero -> Xzero
      | x3 -> Xpair (x0, x3)))
| Xmatch (x1, x2) -> xmatch (xopt x1) (xopt x2)
| Xcons (x1, x2) ->
  (match xopt x1 with
   | Xzero -> Xzero
   | x0 ->
     (match xopt x2 with
      | Xzero -> Xzero
      | x3 -> Xcons (x0, (xcoerce x3))))
| Xfoldr (x1, x2, x3) -> xfoldr (xopt x1) (xopt x2) (xopt x3)
| x0 -> x0

(** val xmap : xform -> xform **)

let xmap f =
  xopt
    (xfoldr
      (match xcomp Xfst f with
       | Xzero -> Xzero
       | x -> Xcons (x, (xcoerce Xsnd))) Xempty Xid)

(** val xmapenv : xform -> xform **)

let xmapenv f =
  xopt
    (xcomp
      (xfoldr
        (match xcomp Xsnd Xfst with
         | Xzero -> Xzero
         | Xfst ->
           xpair_fst
             (match xcomp
                      (match xcomp Xsnd Xfst with
                       | Xzero -> Xzero
                       | Xfst -> xpair_fst Xfst
                       | x -> Xpair (x, Xfst)) f with
              | Xzero -> Xzero
              | x ->
                (match xcomp Xsnd Xsnd with
                 | Xzero -> Xzero
                 | x0 -> Xcons (x, (xcoerce x0))))
         | x ->
           (match xcomp
                    (match xcomp Xsnd Xfst with
                     | Xzero -> Xzero
                     | Xfst -> xpair_fst Xfst
                     | x0 -> Xpair (x0, Xfst)) f with
            | Xzero -> Xzero
            | x0 ->
              (match xcomp Xsnd Xsnd with
               | Xzero -> Xzero
               | x1 -> Xpair (x, (Xcons (x0, (xcoerce x1)))))))
        (xpair_fst Xempty) Xsnd) Xsnd)

(** val xcross : __ -> xform **)

let xcross _ =
  xopt
    (xcomp
      (xcomp (Xpair (Xsnd, Xfst))
        (xmapenv (xcomp (Xpair (Xsnd, Xfst)) (xmapenv Xid))))
      (xopt
        (xfoldr (xopt (xfoldr (Xcons (Xfst, (xcoerce Xsnd))) Xsnd Xfst))
          Xempty Xid)))
