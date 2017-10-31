Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

Set Implicit Arguments.

(** * Semantic interface of languages *)

Definition query: Type := list val * mem.
Definition reply: Type := val * mem.


(** * Calling conventions *)

Record callconv :=
  mk_callconv {
    world: Type;
    match_senv:
      world -> Senv.t -> Senv.t -> Prop;
    match_query:
      world -> query -> query -> Prop;
    match_reply:
      world -> query -> query -> reply -> reply -> Prop;
  }.

(** ** Expected properties of external call steps *)

Definition loc_not_writable (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Writable.

Record extcall_step_valid sg (vargs: list val) m1 vres m2 :=
  {
    ecv_well_typed:
      Val.has_type vres (proj_sig_res sg);
    ecv_valid_block b:
      Mem.valid_block m1 b ->
      Mem.valid_block m2 b;
    ecv_max_perm b ofs p:
      Mem.valid_block m1 b ->
      Mem.perm m2 b ofs Max p ->
      Mem.perm m1 b ofs Max p;
    ecv_readonly:
      Mem.unchanged_on (loc_not_writable m1) m1 m2;
  }.

Definition extcall_valid sg (q: query) (r: reply) :=
  let '(vargs, m) := q in
  let '(vres, m') := r in
  extcall_step_valid sg vargs m vres m'.

(** ** Equality passes *)

Definition cc_id :=
  {|
    world := unit;
    match_senv w := eq;
    match_query w := eq;
    match_reply w q1 q2 := eq;
  |}.

(** ** Extension passes *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Definition cc_extends :=
  {|
    world := unit;
    match_senv w := eq;
    match_query w :=
      fun '(vargs1, m1) '(vargs2, m2) =>
        Val.lessdef_list vargs1 vargs2 /\
        Mem.extends m1 m2;
    match_reply w :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        Val.lessdef vres1 vres2 /\
        Mem.extends m1' m2' /\
        Mem.unchanged_on (loc_out_of_bounds m1) m2 m2';
  |}.

Lemma match_query_extends w vargs1 m1 vargs2 m2:
  match_query cc_extends w (vargs1, m1) (vargs2, m2) ->
  Mem.extends m1 m2 /\
  Val.lessdef_list vargs1 vargs2.
Proof.
  inversion 1; subst.
  tauto.
Qed.

Lemma match_query_extends_intro w vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  match_query cc_extends w (vargs1, m1) (vargs2, m2).
Proof.
  constructor; eauto.
Qed.

Lemma match_reply_extends_intro w vargs1 m1 vres1 m1' vargs2 m2 vres2 m2':
  Val.lessdef vres1 vres2 ->
  Mem.extends m1' m2' ->
  Mem.unchanged_on (loc_out_of_bounds m1) m2 m2' ->
  match_reply cc_extends w (vargs1, m1) (vargs2, m2) (vres1, m1') (vres2, m2').
Proof.
  constructor; simpl; auto.
Qed.

Hint Resolve match_query_extends_intro.
Hint Resolve match_reply_extends_intro.

(** ** Injection passes *)

Definition symbols_inject (f: meminj) (ge1 ge2: Senv.t): Prop :=
   (forall id, Senv.public_symbol ge2 id = Senv.public_symbol ge1 id)
/\ (forall id b1 b2 delta,
     f b1 = Some(b2, delta) -> Senv.find_symbol ge1 id = Some b1 ->
     delta = 0 /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall id b1,
     Senv.public_symbol ge1 id = true -> Senv.find_symbol ge1 id = Some b1 ->
     exists b2, f b1 = Some(b2, 0) /\ Senv.find_symbol ge2 id = Some b2)
/\ (forall b1 b2 delta,
     f b1 = Some(b2, delta) ->
     Senv.block_is_volatile ge2 b2 = Senv.block_is_volatile ge1 b1).

Definition loc_unmapped (f: meminj) (b: block) (ofs: Z): Prop :=
  f b = None.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Definition inject_separated (f f': meminj) (m1 m2: mem): Prop :=
  forall b1 b2 delta,
  f b1 = None -> f' b1 = Some(b2, delta) ->
  ~Mem.valid_block m1 b1 /\ ~Mem.valid_block m2 b2.

Definition cc_inject :=
  {|
    world := meminj;
    match_senv := symbols_inject;
    match_query f :=
      fun '(vargs1, m1) '(vargs2, m2) =>
        Val.inject_list f vargs1 vargs2 /\
        Mem.inject f m1 m2;
    match_reply f :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        exists f',
          Val.inject f' vres1 vres2 /\
          Mem.inject f' m1' m2' /\
          Mem.unchanged_on (loc_unmapped f) m1 m1' /\
          Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' /\
          inject_incr f f' /\
          inject_separated f f' m1 m2;
  |}.

Lemma match_query_inject f vargs1 m1 vargs2 m2:
  match_query cc_inject f (vargs1, m1) (vargs2, m2) ->
  Mem.inject f m1 m2 /\
  Val.inject_list f vargs1 vargs2.
Proof.
  simpl.
  tauto.
Qed.

Lemma match_query_inject_intro f vargs1 m1 vargs2 m2:
  Val.inject_list f vargs1 vargs2 ->
  Mem.inject f m1 m2 ->
  match_query cc_inject f (vargs1, m1) (vargs2, m2).
Proof.
  simpl.
  tauto.
Qed.

Lemma match_reply_inject_intro f f' vargs1 m1 vres1 m1' vargs2 m2 vres2 m2':
  Mem.inject f' m1' m2' ->
  Val.inject f' vres1 vres2 ->
  Mem.unchanged_on (loc_unmapped f) m1 m1' ->
  Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' ->
  inject_incr f f' ->
  inject_separated f f' m1 m2 ->
  match_reply cc_inject f (vargs1, m1) (vargs2, m2) (vres1, m1') (vres2, m2').
Proof.
  simpl.
  exists f'.
  tauto.
Qed.

(** This is usedful as a hint to resolve the premices of
  [match_reply_inject_intro]. *)

Lemma same_inject_separated f m1 m2:
  inject_separated f f m1 m2.
Proof.
  congruence.
Qed.

Hint Resolve same_inject_separated.

Lemma match_reply_inject_intro_same f vargs1 m1 vres1 vargs2 m2 vres2:
  Mem.inject f m1 m2 ->
  Val.inject f vres1 vres2 ->
  match_reply cc_inject f (vargs1, m1) (vargs2, m2) (vres1, m1) (vres2, m2).
Proof.
  simpl.
  exists f.
  intuition.
Qed.

Hint Resolve match_query_inject_intro.
Hint Resolve match_reply_inject_intro.
Hint Resolve match_reply_inject_intro_same.

Global Opaque match_query.
Global Opaque match_reply.
