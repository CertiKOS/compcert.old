open Basics
open Coqlib
open Datatypes
open Grammar
open GrammarType
open List0
open MSetsMore
open Nat0
open RESet
open Regexp
open Specif
open Vector
open Xform

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module RES = RESet

type rs_xf_pair = RES.rs_xf_pair

type re_xf_pair = RES.re_xf_pair

(** val erase : rs_xf_pair -> RES.t **)

let erase rx =
  projT1 rx

(** val nullable : regexp -> bool*xform **)

let rec nullable = function
| Coq_rEps -> true,(Xcons (Xid, (xcoerce Xempty)))
| Coq_rCat (r1, r2) ->
  let x,f1 = nullable r1 in
  if x
  then let x0,f2 = nullable r2 in
       if x0
       then true,(xcomp
                   (match f1 with
                    | Xzero -> Xzero
                    | Xfst -> xpair_fst f2
                    | x1 ->
                      (match f2 with
                       | Xzero -> Xzero
                       | x2 -> Xpair (x1, x2))) (xcross __))
       else false,Xzero
  else false,Xzero
| Coq_rAlt (r1, r2) ->
  let x,f1 = nullable r1 in
  if x
  then let x0,f2 = nullable r2 in
       if x0
       then true,(xcomp
                   (match xcomp f1 (xmap Xinl) with
                    | Xzero -> Xzero
                    | Xfst -> xpair_fst (xcomp f2 (xmap Xinr))
                    | x1 ->
                      (match xcomp f2 (xmap Xinr) with
                       | Xzero -> Xzero
                       | x2 -> Xpair (x1, x2)))
                   (xopt (xfoldr (Xcons (Xfst, (xcoerce Xsnd))) Xsnd Xfst)))
       else true,(xcomp f1 (xmap Xinl))
  else let x0,f2 = nullable r2 in
       if x0 then true,(xcomp f2 (xmap Xinr)) else false,Xzero
| Coq_rStar _ -> true,(Xcons (Xempty, (xcoerce Xempty)))
| _ -> false,Xzero

(** val pdrv : char_p -> regexp -> rs_xf_pair **)

let rec pdrv a = function
| Coq_rChar b ->
  if char_dec a b
  then let rs,f = RES.singleton_xform Coq_rEps in
       rs,(xcomp f (xmap (xchar a)))
  else RES.empty_xform __
| Coq_rAny ->
  let rs,f = RES.singleton_xform Coq_rEps in rs,(xcomp f (xmap (xchar a)))
| Coq_rCat (r1, r2) ->
  let rxc = RES.cat_re_xform (pdrv a r1) r2 in
  let x,fnull = nullable r1 in
  if x
  then let rs2,f2 = pdrv a r2 in
       RES.union_xform rxc
         (rs2,(xcomp f2
                (xcomp
                  (match xcomp Xunit fnull with
                   | Xzero -> Xzero
                   | Xfst -> xpair_fst Xid
                   | x0 -> Xpair (x0, Xid)) (xcross __))))
  else rxc
| Coq_rAlt (r1, r2) ->
  let rs1,f1 = pdrv a r1 in
  let rs2,f2 = pdrv a r2 in
  RES.union_xform (rs1,(xcomp f1 (xmap Xinl))) (rs2,(xcomp f2 (xmap Xinr)))
| Coq_rStar r1 ->
  let rsc,fc = RES.cat_re_xform (pdrv a r1) (Coq_rStar r1) in
  rsc,(xcomp fc (xmap (Xcons (Xfst, (xcoerce Xsnd)))))
| _ -> RES.empty_xform __

(** val pdrv_rex : char_p -> re_xf_pair -> rs_xf_pair **)

let pdrv_rex a = function
| r,f ->
  let rs,frs = pdrv a r in
  rs,(xcomp frs
       (xcomp (xmap f)
         (xopt
           (xfoldr (xopt (xfoldr (Xcons (Xfst, (xcoerce Xsnd))) Xsnd Xfst))
             Xempty Xid))))

(** val pdrv_set : char_p -> rs_xf_pair -> rs_xf_pair **)

let pdrv_set a rx =
  RES.fold_xform (fun rex rx1 -> RES.union_xform (pdrv_rex a rex) rx1) rx
    (RES.empty_xform __)

(** val wpdrv : char_p list -> rs_xf_pair -> rs_xf_pair **)

let rec wpdrv s rx =
  match s with
  | [] -> rx
  | a :: s' -> let rs,f = pdrv_set a rx in wpdrv s' (rs,(xopt f))

(** val wpdrv_re_set : char_p list -> RES.t -> rs_xf_pair **)

let wpdrv_re_set s rs =
  wpdrv s (rs,(Xcons (Xid, (xcoerce Xempty))))

module POW = ListPowerSet(RES)

module RESetSet =
 struct
  module Raw = POW.MM.Raw

  module E =
   struct
    type t = RES.t

    (** val eq_dec : t -> t -> bool **)

    let eq_dec =
      RES.eq_dec
   end

  type elt = RES.t

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

  (** val get_element : Big.big_int -> t -> elt option **)

  let get_element n s =
    nth_error (elements s) n

  (** val get_index : elt -> t -> Big.big_int option **)

  let get_index e s =
    find_index E.eq_dec e (elements s)

  (** val add_set : t -> t -> t **)

  let add_set s1 s2 =
    fold add s2 s1
 end

module RESS = RESetSet

type state = RES.t

type states = RESS.t

type wf_state = state

type wf_states = states

(** val cardinal_wfs : wf_states -> Big.big_int **)

let cardinal_wfs ss =
  RESS.cardinal ss

type wfs_xf_pair = wf_state*xform

(** val wpdrv_wf : char_p list -> wf_state -> wfs_xf_pair **)

let wpdrv_wf w s =
  (erase (wpdrv_re_set w s)),(projT2 (wpdrv_re_set w s))

(** val add_wfs : wf_state -> wf_states -> wf_states **)

let add_wfs s ss =
  RESS.add s ss

(** val get_index_wfs : wf_state -> wf_states -> Big.big_int option **)

let get_index_wfs s ss =
  RESS.get_index s ss

(** val get_index_wfs2 : wf_state -> wf_states -> Big.big_int option **)

let get_index_wfs2 s ss =
  let gi = get_index_wfs s ss in
  (match gi with
   | Some n -> Some n
   | None -> None)

(** val get_element_wfs : Big.big_int -> wf_states -> RESS.elt option **)

let get_element_wfs n ss =
  RESS.get_element n ss

(** val get_element_wfs2 : Big.big_int -> wf_states -> wf_state option **)

let get_element_wfs2 n ss =
  let ge = get_element_wfs n ss in
  (match ge with
   | Some rs -> Some rs
   | None -> None)

(** val get_state : Big.big_int -> wf_states -> RES.t **)

let get_state n ss =
  match get_element_wfs2 n ss with
  | Some s -> s
  | None -> RES.empty

type entry_t = { next_state : Big.big_int; next_xform : xform }

(** val next_state :
    regexp -> Big.big_int -> wf_states -> entry_t -> Big.big_int **)

let next_state _ _ _ x = x.next_state

(** val next_xform :
    regexp -> Big.big_int -> wf_states -> entry_t -> xform **)

let next_xform _ _ _ x = x.next_xform

type entries_t = entry_t list

type transition_t = { row_num : Big.big_int; row_entries : entries_t;
                      row_nils : xt_interp list }

(** val row_num : regexp -> wf_states -> transition_t -> Big.big_int **)

let row_num _ _ x = x.row_num

(** val row_entries : regexp -> wf_states -> transition_t -> entries_t **)

let row_entries _ _ x = x.row_entries

(** val row_nils : regexp -> wf_states -> transition_t -> xt_interp list **)

let row_nils _ _ x = x.row_nils

type transitions_t = transition_t list

type coq_DFA = { dfa_num_states : Big.big_int; dfa_states : wf_states;
                 dfa_transition : transitions_t }

(** val dfa_num_states : regexp -> coq_DFA -> Big.big_int **)

let dfa_num_states _ x = x.dfa_num_states

(** val dfa_states : regexp -> coq_DFA -> wf_states **)

let dfa_states _ x = x.dfa_states

(** val dfa_transition : regexp -> coq_DFA -> transitions_t **)

let dfa_transition _ x = x.dfa_transition

type ventries_t = entry_t vector

type vtransition_t = { vrow_num : Big.big_int; vrow_entries : ventries_t;
                       vrow_nils : xt_interp list }

(** val vrow_entries : regexp -> wf_states -> vtransition_t -> ventries_t **)

let vrow_entries _ _ x = x.vrow_entries

(** val vrow_nils : regexp -> wf_states -> vtransition_t -> xt_interp list **)

let vrow_nils _ _ x = x.vrow_nils

type vtransitions_t = vtransition_t vector

type vDFA = { vdfa_num_states : Big.big_int; vdfa_states : wf_states;
              vdfa_transition : vtransitions_t }

(** val vdfa_states : regexp -> vDFA -> wf_states **)

let vdfa_states _ x = x.vdfa_states

(** val vdfa_transition : regexp -> vDFA -> vtransitions_t **)

let vdfa_transition _ x = x.vdfa_transition

(** val transition_to_vtransition :
    wf_states -> transition_t -> vtransition_t **)

let transition_to_vtransition _ t0 =
  { vrow_num = t0.row_num; vrow_entries = (Array.of_list t0.row_entries);
    vrow_nils = t0.row_nils }

(** val dfa_to_vdfa : coq_DFA -> vDFA **)

let dfa_to_vdfa d =
  { vdfa_num_states = d.dfa_num_states; vdfa_states = d.dfa_states;
    vdfa_transition =
    (Array.of_list
      (map (transition_to_vtransition d.dfa_states) d.dfa_transition)) }

(** val gen_backward_xform : wf_state -> wf_states -> Big.big_int -> xform **)

let gen_backward_xform s ss' n =
  RES.equal_xform (get_state n ss') s

type gen_row_ret_t = wf_states*(entries_t*__)

(** val gen_row' :
    wf_state -> Big.big_int -> wf_states -> token_id -> gen_row_ret_t **)

let rec gen_row' s n ss tid =
  Big.nat_case
    (fun _ ->
    ss,([],__))
    (fun n' ->
    let s1,f1 = wpdrv_wf (token_id_to_chars tid) s in
    (match get_index_wfs2 s1 ss with
     | Some s0 ->
       let ss',r = gen_row' s n' ss (Nat0.add (Big.succ Big.zero) tid) in
       let entries,_ = r in
       let f_back = gen_backward_xform s1 ss' s0 in
       let e = { next_state = s0; next_xform =
         (xopt (xcomp f_back (xcoerce f1))) }
       in
       ss',((e :: entries),__)
     | None ->
       let ss',r =
         gen_row' s n' (add_wfs s1 ss) (Nat0.add (Big.succ Big.zero) tid)
       in
       let entries,_ = r in
       let e = { next_state = (cardinal_wfs ss); next_xform = (xcoerce f1) }
       in
       ss',((e :: entries),__)))
    n

(** val gen_row : wf_state -> wf_states -> gen_row_ret_t **)

let gen_row s ss =
  gen_row' s num_tokens ss Big.zero

(** val coerce_entry : entry_t -> entry_t **)

let coerce_entry e =
  { next_state = e.next_state; next_xform = e.next_xform }

(** val coerce_nils : xt_interp -> xt_interp **)

let coerce_nils v =
  v

(** val coerce_transitions :
    wf_states -> wf_states -> transitions_t -> transitions_t **)

let coerce_transitions _ _ ts =
  map (fun t0 -> { row_num = t0.row_num; row_entries =
    (map coerce_entry t0.row_entries); row_nils =
    (map coerce_nils t0.row_nils) }) ts

(** val cons_transition :
    Big.big_int -> wf_states -> entries_t -> transition_t **)

let cons_transition n ss entries =
  { row_num = n; row_entries = entries; row_nils =
    (RES.re_set_extract_nil (get_state n ss)) }

(** val build_table_func :
    (wf_states*(transitions_t*Big.big_int)) -> wf_states*transitions_t **)

let rec build_table_func x =
  let ss = projT1 x in
  let rows = projT1 (projT2 x) in
  let next_state0 = projT2 (projT2 x) in
  let build_table0 = fun ss0 rows0 next_state1 ->
    let y = ss0,(rows0,next_state1) in build_table_func y
  in
  let filtered_var = get_element_wfs2 next_state0 ss in
  (match filtered_var with
   | Some s0 ->
     let filtered_var0 = gen_row s0 ss in
     let ss',s = filtered_var0 in
     let entries,_ = s in
     build_table0 ss'
       (app (coerce_transitions ss ss' rows)
         ((cons_transition next_state0 ss' entries) :: []))
       (Nat0.add (Big.succ Big.zero) next_state0)
   | None -> ss,rows)

(** val build_table :
    wf_states -> transitions_t -> Big.big_int -> wf_states*transitions_t **)

let build_table ss rows next_state0 =
  build_table_func (ss,(rows,next_state0))

(** val ini_state : regexp -> wf_state **)

let ini_state r =
  singleton r

(** val ini_states : regexp -> wf_states **)

let ini_states r =
  RESS.singleton (ini_state r)

(** val build_transition_table : regexp -> wf_states*transitions_t **)

let build_transition_table r =
  build_table (ini_states r) [] Big.zero

(** val build_dfa : regexp -> coq_DFA **)

let build_dfa r =
  let ss,table = build_transition_table r in
  { dfa_num_states = (cardinal_wfs ss); dfa_states = ss; dfa_transition =
  table }

(** val build_vdfa : regexp -> vDFA **)

let build_vdfa r =
  dfa_to_vdfa (build_dfa r)

(** val coerce_dom : (xt_interp -> 'a1) -> xt_interp -> 'a1 **)

let coerce_dom f =
  f

type naiveParserState = { rx_nps : rs_xf_pair;
                          fixup_nps : (xt_interp -> interp) }

(** val rx_nps : xtype -> coq_type -> naiveParserState -> rs_xf_pair **)

let rx_nps _ _ x = x.rx_nps

(** val fixup_nps :
    xtype -> coq_type -> naiveParserState -> xt_interp -> interp **)

let fixup_nps _ _ x = x.fixup_nps

(** val naive_parse_token :
    naiveParserState -> token_id -> naiveParserState * interp list **)

let naive_parse_token nps tk =
  let rs,f = wpdrv (token_id_to_chars tk) nps.rx_nps in
  let v = RES.re_set_extract_nil rs in
  ({ rx_nps = (rs,f); fixup_nps = nps.fixup_nps },
  (flat_map (compose (Obj.magic map nps.fixup_nps) (xinterp f)) v))

(** val initial_naive_parser_state : grammar -> naiveParserState **)

let initial_naive_parser_state g =
  let r,f = split_grammar g in
  { rx_nps = (RES.singleton_xform r); fixup_nps = (coerce_dom f) }

type re_set_fixfn = xt_interp -> __ list

type instParserState = { dfa_ps : coq_DFA; row_ps : Big.big_int;
                         fixup_ps : re_set_fixfn }

(** val dfa_ps : coq_type -> regexp -> instParserState -> coq_DFA **)

let dfa_ps _ _ x = x.dfa_ps

(** val row_ps : coq_type -> regexp -> instParserState -> Big.big_int **)

let row_ps _ _ x = x.row_ps

(** val fixup_ps : coq_type -> regexp -> instParserState -> re_set_fixfn **)

let fixup_ps _ _ x = x.fixup_ps

type dfa_builder_tp = regexp -> coq_DFA

type wf_dfa_builder = dfa_builder_tp

(** val build_dfa_wf_builder : wf_dfa_builder **)

let build_dfa_wf_builder =
  build_dfa

(** val coerce_dfa : coq_DFA -> coq_DFA **)

let coerce_dfa x =
  x

(** val initial_parser_state' :
    wf_dfa_builder -> grammar -> instParserState **)

let initial_parser_state' db g =
  let r,f = split_grammar g in
  let f1 = projT2 (RES.singleton_xform r) in
  { dfa_ps = (coerce_dfa (db r)); row_ps = Big.zero; fixup_ps =
  (coerce_dom (compose (Obj.magic map f) (xinterp f1))) }

(** val initial_parser_state : grammar -> instParserState **)

let initial_parser_state g =
  initial_parser_state' build_dfa_wf_builder g

(** val coerce : 'a1 -> 'a2 **)

let coerce x =
  Obj.magic x

(** val nth_error2 : 'a1 list -> Big.big_int -> 'a1 option **)

let nth_error2 l n =
  let ne = nth_error l n in
  (match ne with
   | Some e -> Some e
   | None -> None)

(** val parse_token :
    instParserState -> token_id -> instParserState * interp list **)

let parse_token ps tk =
  match nth_error2 ps.dfa_ps.dfa_transition ps.row_ps with
  | Some s ->
    (match nth_error2 s.row_entries tk with
     | Some s0 ->
       let next_i = s0.next_state in
       let next_fixup = coerce_dom ps.fixup_ps in
       let g =
         compose (Obj.magic flat_map next_fixup) (xinterp s0.next_xform)
       in
       let vs0 =
         match nth_error2 ps.dfa_ps.dfa_transition next_i with
         | Some s1 -> coerce s1.row_nils
         | None -> []
       in
       let vs' = flat_map g vs0 in
       ({ dfa_ps = ps.dfa_ps; row_ps = next_i; fixup_ps = g }, vs')
     | None -> assert false (* absurd case *))
  | None -> assert false (* absurd case *)

(** val ps_extract_nil : instParserState -> __ list **)

let ps_extract_nil ps =
  flat_map ps.fixup_ps
    (RES.re_set_extract_nil (get_state ps.row_ps ps.dfa_ps.dfa_states))

(** val parse_tokens :
    instParserState -> token_id list -> (token_id
    list * instParserState) * interp list **)

let rec parse_tokens ps = function
| [] -> (([], ps), (ps_extract_nil ps))
| tk :: rest ->
  let pair = parse_token ps tk in
  (match snd pair with
   | [] -> parse_tokens (fst pair) rest
   | i :: l -> ((rest, (fst pair)), (i :: l)))

type vinstParserState = { vdfa_ps : vDFA; vrow_ps : Big.big_int;
                          vfixup_ps : re_set_fixfn }

(** val vdfa_ps : coq_type -> regexp -> vinstParserState -> vDFA **)

let vdfa_ps _ _ x = x.vdfa_ps

(** val vrow_ps : coq_type -> regexp -> vinstParserState -> Big.big_int **)

let vrow_ps _ _ x = x.vrow_ps

(** val vfixup_ps : coq_type -> regexp -> vinstParserState -> re_set_fixfn **)

let vfixup_ps _ _ x = x.vfixup_ps

type vdfa_builder_tp = regexp -> vDFA

type wf_vdfa_builder = vdfa_builder_tp

(** val build_vdfa_wf_builder : wf_vdfa_builder **)

let build_vdfa_wf_builder =
  build_vdfa

(** val vinitial_parser_state' :
    wf_vdfa_builder -> grammar -> vinstParserState **)

let vinitial_parser_state' db g =
  let r,f = split_grammar g in
  let f1 = projT2 (RES.singleton_xform r) in
  { vdfa_ps = (db r); vrow_ps = Big.zero; vfixup_ps =
  (coerce_dom (compose (Obj.magic map f) (xinterp f1))) }

(** val vinitial_parser_state : grammar -> vinstParserState **)

let vinitial_parser_state g =
  vinitial_parser_state' build_vdfa_wf_builder g

(** val flat_map' : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map' f = function
| [] -> []
| x :: t0 ->
  (match t0 with
   | [] -> f x
   | _ :: _ -> app (f x) (flat_map' f t0))

(** val compose_flat_map :
    ('a1 -> 'a2 list) -> ('a3 -> 'a1 list) -> 'a3 -> 'a2 list **)

let compose_flat_map f g x =
  flat_map' f (g x)

(** val vparse_token :
    vinstParserState -> token_id -> vinstParserState*xt_interp list **)

let vparse_token ps tk =
  let row = get ps.vdfa_ps.vdfa_transition ps.vrow_ps in
  let e = get row.vrow_entries tk in
  let next_i = e.next_state in
  let next_fixup = coerce_dom ps.vfixup_ps in
  let g = compose_flat_map next_fixup (Obj.magic xinterp e.next_xform) in
  let row' = get ps.vdfa_ps.vdfa_transition next_i in
  let vs0 = coerce row'.vrow_nils in
  { vdfa_ps = ps.vdfa_ps; vrow_ps = next_i; vfixup_ps = g },vs0

(** val vps_extract_nil : vinstParserState -> __ list **)

let vps_extract_nil ps =
  flat_map' ps.vfixup_ps
    (RES.re_set_extract_nil (get_state ps.vrow_ps ps.vdfa_ps.vdfa_states))

(** val vparse_tokens :
    coq_type -> regexp -> vinstParserState -> token_id list -> (token_id
    list * vinstParserState) * interp list **)

let rec vparse_tokens t0 r ps = function
| [] -> (([], ps), (vps_extract_nil ps))
| tk :: rest ->
  let pair = vparse_token ps tk in
  let ps2,vs = pair in
  (match vs with
   | [] -> vparse_tokens t0 r ps2 rest
   | _ :: _ -> ((rest, ps2), (flat_map ps2.vfixup_ps vs)))
