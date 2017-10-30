open Datatypes
open Grammar
open GrammarType
open Monad

type bigrammar =
| Eps
| Zero
| Char of char_p
| Any
| Cat of bigrammar * bigrammar
| Alt of bigrammar * bigrammar
| Star of bigrammar
| Map of ((interp -> interp) * (interp -> interp option)) * bigrammar

(** val pretty_print : bigrammar -> interp -> char_p list option **)

let rec pretty_print = function
| Eps -> (fun _ -> Some [])
| Zero -> (fun _ -> None)
| Char c ->
  (fun c' -> if char_dec c (Obj.magic c') then Some (c :: []) else None)
| Any -> (fun c -> Some ((Obj.magic c) :: []))
| Cat (g1, g2) ->
  (fun p ->
    coq_Bind (Obj.magic coq_OptionMonad)
      (pretty_print g1 (fst (Obj.magic p))) (fun s1 ->
      coq_Bind (Obj.magic coq_OptionMonad)
        (pretty_print g2 (snd (Obj.magic p))) (fun s2 ->
        coq_Return (Obj.magic coq_OptionMonad) (app s1 s2))))
| Alt (g1, g2) ->
  (fun v ->
    match Obj.magic v with
    | Coq_inl x1 -> pretty_print g1 x1
    | Coq_inr x2 -> pretty_print g2 x2)
| Star g0 ->
  let rec loop v =
    match Obj.magic v with
    | [] -> Some []
    | hd :: tl ->
      coq_Bind (Obj.magic coq_OptionMonad) (pretty_print g0 hd) (fun s' ->
        match s' with
        | [] -> None
        | _ :: _ ->
          coq_Bind (Obj.magic coq_OptionMonad) (Obj.magic loop tl) (fun s ->
            coq_Return (Obj.magic coq_OptionMonad) (app s' s)))
  in loop
| Map (fi, g0) ->
  (fun v ->
    coq_Bind (Obj.magic coq_OptionMonad) (snd (Obj.magic fi) v) (fun x ->
      pretty_print g0 x))

(** val empty : bigrammar **)

let empty =
  Eps

(** val map :
    bigrammar -> ((interp -> interp) * (interp -> interp option)) -> bigrammar **)

let map g fi =
  Map (fi, g)

(** val seq : bigrammar -> bigrammar -> bigrammar **)

let seq p1 p2 =
  Cat (p1, p2)

(** val alt : bigrammar -> bigrammar -> bigrammar **)

let alt p1 p2 =
  Alt (p1, p2)

type index = Big.big_int

type bgr_tree =
| BLeaf of index * bigrammar * (interp -> interp)
| BNode of index * bgr_tree * bgr_tree

(** val comb_bigrammar : bgr_tree -> bigrammar **)

let rec comb_bigrammar = function
| BLeaf (_, g, _) -> g
| BNode (_, gt1, gt2) ->
  let g1 = comb_bigrammar gt1 in let g2 = comb_bigrammar gt2 in alt g1 g2

(** val comb_map : bgr_tree -> interp -> interp **)

let rec comb_map = function
| BLeaf (_, _, m) -> m
| BNode (_, gt1, gt2) ->
  let m1 = comb_map gt1 in
  let m2 = comb_map gt2 in
  (fun v ->
  match Obj.magic v with
  | Coq_inl v1 -> m1 v1
  | Coq_inr v2 -> m2 v2)

type tmember =
| MLeaf
| MLTree of tmember
| MRTree of tmember

(** val inv_case : tmember -> interp -> interp **)

let rec inv_case m v =
  match m with
  | MLeaf -> v
  | MLTree m' -> Obj.magic (Coq_inl (inv_case m' v))
  | MRTree m' -> Obj.magic (Coq_inr (inv_case m' v))

(** val inv_case_some : tmember -> interp -> interp option **)

let inv_case_some m v =
  Some (inv_case m v)

(** val perm2 : bigrammar -> bigrammar -> bigrammar **)

let perm2 p1 p2 =
  map (alt (seq p1 p2) (seq p2 p1)) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (a, b) = y in Obj.magic (a, b)
    | Coq_inr y -> let (b, a) = y in Obj.magic (a, b)), (fun u ->
    let (a, b) = Obj.magic u in Some (Obj.magic (Coq_inl (a, b)))))

(** val option_perm : bigrammar -> bigrammar **)

let option_perm p1 =
  map (alt empty p1) ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic None
    | Coq_inr v1 -> Obj.magic (Some v1)), (fun u ->
    match Obj.magic u with
    | Some v1 -> Some (Obj.magic (Coq_inr v1))
    | None -> Some (Obj.magic (Coq_inl ()))))

(** val option_perm2 : bigrammar -> bigrammar -> bigrammar **)

let option_perm2 p1 p2 =
  map (alt empty (alt (seq p1 (option_perm p2)) (seq p2 (option_perm p1))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic (None, None)
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 -> let (a, ob) = y0 in Obj.magic ((Some a), ob)
       | Coq_inr y0 -> let (b, oa) = y0 in Obj.magic (oa, (Some b)))),
    (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | Some a ->
       Some (Obj.magic (Coq_inr (Coq_inl (a, (snd (Obj.magic u))))))
     | None ->
       (match y0 with
        | Some b -> Some (Obj.magic (Coq_inr (Coq_inr (b, None))))
        | None -> Some (Obj.magic (Coq_inl ()))))))

(** val option_perm3 : bigrammar -> bigrammar -> bigrammar -> bigrammar **)

let option_perm3 p1 p2 p3 =
  map
    (alt (alt empty (seq p1 (option_perm2 p2 p3)))
      (alt (seq p2 (option_perm2 p1 p3)) (seq p3 (option_perm2 p1 p2))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      (match y with
       | Coq_inl _ -> Obj.magic (None, (None, None))
       | Coq_inr y0 ->
         let (a, y1) = y0 in
         let (ob, oc) = y1 in Obj.magic ((Some a), (ob, oc)))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         let (b, y1) = y0 in
         let (oa, oc) = y1 in Obj.magic (oa, ((Some b), oc))
       | Coq_inr y0 ->
         let (c, y1) = y0 in
         let (oa, ob) = y1 in Obj.magic (oa, (ob, (Some c))))), (fun u ->
    let (oa, u1) = Obj.magic u in
    let (ob, oc) = u1 in
    (match oa with
     | Some a ->
       Some (Obj.magic (Coq_inl (Coq_inr (a, (snd (Obj.magic u))))))
     | None ->
       (match ob with
        | Some b -> Some (Obj.magic (Coq_inr (Coq_inl (b, (oa, oc)))))
        | None ->
          (match oc with
           | Some c -> Some (Obj.magic (Coq_inr (Coq_inr (c, (oa, ob)))))
           | None -> Some (Obj.magic (Coq_inl (Coq_inl ()))))))))

(** val option_perm2_variation : bigrammar -> bigrammar -> bigrammar **)

let option_perm2_variation p1 p2 =
  map (alt p2 (perm2 p1 p2)) ((fun v ->
    match Obj.magic v with
    | Coq_inl b -> Obj.magic (None, b)
    | Coq_inr y -> let (a, b) = y in Obj.magic ((Some a), b)), (fun u ->
    let (y, b) = Obj.magic u in
    (match y with
     | Some a -> Some (Obj.magic (Coq_inr (a, b)))
     | None -> Some (Obj.magic (Coq_inl b)))))

(** val option_perm3_variation :
    bigrammar -> bigrammar -> bigrammar -> bigrammar **)

let option_perm3_variation p1 p2 p3 =
  map
    (alt (seq p1 (option_perm2_variation p2 p3))
      (alt (seq p2 (option_perm2_variation p1 p3))
        (seq p3 (option_perm2 p1 p2)))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (a, y0) = y in let (ob, c) = y0 in Obj.magic ((Some a), (ob, c))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         let (b, y1) = y0 in
         let (oa, c) = y1 in Obj.magic (oa, ((Some b), c))
       | Coq_inr y0 ->
         let (c, y1) = y0 in let (oa, ob) = y1 in Obj.magic (oa, (ob, c)))),
    (fun u ->
    let (oa, u1) = Obj.magic u in
    let (ob, c) = u1 in
    (match oa with
     | Some a -> Some (Obj.magic (Coq_inl (a, (ob, c))))
     | None ->
       (match ob with
        | Some b -> Some (Obj.magic (Coq_inr (Coq_inl (b, (None, c)))))
        | None -> Some (Obj.magic (Coq_inr (Coq_inr (c, (None, None)))))))))

(** val bigrammar_to_grammar : bigrammar -> grammar **)

let rec bigrammar_to_grammar = function
| Eps -> Grammar.Eps
| Zero -> Grammar.Zero
| Char c -> Grammar.Char c
| Any -> Grammar.Any
| Cat (g1, g2) ->
  Grammar.Cat ((bigrammar_to_grammar g1), (bigrammar_to_grammar g2))
| Alt (g1, g2) ->
  Grammar.Alt ((bigrammar_to_grammar g1), (bigrammar_to_grammar g2))
| Star g0 -> Grammar.Star (bigrammar_to_grammar g0)
| Map (fi, g0) -> Grammar.Map ((fst fi), (bigrammar_to_grammar g0))
