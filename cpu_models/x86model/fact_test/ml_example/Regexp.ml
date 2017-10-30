open Datatypes
open List0
open OrdersAlt
open ParserArg
open Xform

type regexp =
| Coq_rEps
| Coq_rZero
| Coq_rChar of X86_PARSER_ARG.char_p
| Coq_rAny
| Coq_rCat of regexp * regexp
| Coq_rAlt of regexp * regexp
| Coq_rStar of regexp

(** val regexp_type : regexp -> xtype **)

let rec regexp_type = function
| Coq_rEps -> Coq_xUnit_t
| Coq_rZero -> Coq_xVoid_t
| Coq_rCat (pg1, pg2) -> Coq_xPair_t ((regexp_type pg1), (regexp_type pg2))
| Coq_rAlt (pg1, pg2) -> Coq_xSum_t ((regexp_type pg1), (regexp_type pg2))
| Coq_rStar pg0 -> Coq_xList_t (regexp_type pg0)
| _ -> Coq_xChar_t

(** val regexp_extract_nil : regexp -> xt_interp list **)

let rec regexp_extract_nil = function
| Coq_rEps -> (Obj.magic ()) :: []
| Coq_rCat (ag1, ag2) ->
  Obj.magic list_prod (regexp_extract_nil ag1) (regexp_extract_nil ag2)
| Coq_rAlt (ag1, ag2) ->
  app (map (fun x -> Obj.magic (Coq_inl x)) (regexp_extract_nil ag1))
    (map (fun x -> Obj.magic (Coq_inr x)) (regexp_extract_nil ag2))
| Coq_rStar _ -> (Obj.magic []) :: []
| _ -> []

(** val compare_re : regexp -> regexp -> comparison **)

let rec compare_re r1 r2 =
  match r1 with
  | Coq_rEps ->
    (match r2 with
     | Coq_rEps -> Eq
     | _ -> Lt)
  | Coq_rZero ->
    (match r2 with
     | Coq_rEps -> Gt
     | Coq_rZero -> Eq
     | _ -> Lt)
  | Coq_rChar c1 ->
    (match r2 with
     | Coq_rEps -> Gt
     | Coq_rZero -> Gt
     | Coq_rChar c2 -> X86_PARSER_ARG.char_cmp c1 c2
     | _ -> Lt)
  | Coq_rAny ->
    (match r2 with
     | Coq_rEps -> Gt
     | Coq_rZero -> Gt
     | Coq_rChar _ -> Gt
     | Coq_rAny -> Eq
     | _ -> Lt)
  | Coq_rCat (r11, r12) ->
    (match r2 with
     | Coq_rCat (r21, r22) ->
       let cp = compare_re r11 r21 in
       (match cp with
        | Eq -> compare_re r12 r22
        | _ -> cp)
     | Coq_rAlt (_, _) -> Lt
     | Coq_rStar _ -> Lt
     | _ -> Gt)
  | Coq_rAlt (r11, r12) ->
    (match r2 with
     | Coq_rAlt (r21, r22) ->
       let cp = compare_re r11 r21 in
       (match cp with
        | Eq -> compare_re r12 r22
        | _ -> cp)
     | Coq_rStar _ -> Lt
     | _ -> Gt)
  | Coq_rStar r11 ->
    (match r2 with
     | Coq_rStar r21 -> compare_re r11 r21
     | _ -> Gt)

module REOrderedTypeAlt =
 struct
  type t = regexp

  (** val compare : regexp -> regexp -> comparison **)

  let compare =
    compare_re
 end

module REOrderedType = OT_from_Alt(REOrderedTypeAlt)
