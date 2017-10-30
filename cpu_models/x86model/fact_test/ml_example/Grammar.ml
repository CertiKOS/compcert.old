open Datatypes
open GrammarType
open List0
open Regexp
open Xform

type grammar =
| Eps
| Zero
| Char of char_p
| Any
| Cat of grammar * grammar
| Alt of grammar * grammar
| Star of grammar
| Map of (interp -> interp) * grammar

type fixfn = xt_interp -> interp

(** val re_and_fn : regexp -> fixfn -> regexp*fixfn **)

let re_and_fn r f =
  r,f

(** val split_grammar : grammar -> regexp*fixfn **)

let rec split_grammar = function
| Eps -> re_and_fn Coq_rEps (fun x -> x)
| Zero ->
  re_and_fn Coq_rZero (Obj.magic (fun _ -> assert false (* absurd case *)))
| Char c -> re_and_fn (Coq_rChar c) (fun x -> x)
| Any -> re_and_fn Coq_rAny (fun x -> x)
| Cat (g1, g2) ->
  let ag1,f1 = split_grammar g1 in
  let ag2,f2 = split_grammar g2 in
  re_and_fn (Coq_rCat (ag1, ag2)) (fun p ->
    Obj.magic ((f1 (fst (Obj.magic p))), (f2 (snd (Obj.magic p)))))
| Alt (g1, g2) ->
  let ag1,f1 = split_grammar g1 in
  let ag2,f2 = split_grammar g2 in
  re_and_fn (Coq_rAlt (ag1, ag2)) (fun s ->
    match Obj.magic s with
    | Coq_inl x -> Obj.magic (Coq_inl (f1 x))
    | Coq_inr y -> Obj.magic (Coq_inr (f2 y)))
| Star g0 ->
  let ag,f = split_grammar g0 in
  re_and_fn (Coq_rStar ag) (fun xs -> Obj.magic map f xs)
| Map (f1, g0) ->
  let ag,f2 = split_grammar g0 in re_and_fn ag (fun x -> f1 (f2 x))
