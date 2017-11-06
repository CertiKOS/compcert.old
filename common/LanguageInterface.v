Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

(** * Semantic interface of languages *)

Definition query: Type := list val * mem.
Definition reply: Type := val * mem.

Definition dummy_query: query := (nil, Mem.empty).

(** * Calling conventions *)

(** ** Definition *)

Record callconv :=
  mk_callconv {
    world_def: Type;
    dummy_world_def: world_def;
    match_senv:
      world_def -> Senv.t -> Senv.t -> Prop;
    match_query_def:
      world_def -> query -> query -> Prop;
    match_reply_def:
      world_def -> query -> query -> reply -> reply -> Prop;
    match_dummy_query_def:
      match_query_def dummy_world_def dummy_query dummy_query;
  }.

Record world (cc: callconv) :=
  mk_world {
    world_proj :> world_def cc;
    world_query_l: query;
    world_query_r: query;
    world_match_query: match_query_def cc world_proj world_query_l world_query_r;
  }.

Program Definition dummy_world {cc: callconv}: world cc :=
  mk_world cc _ _ _ (match_dummy_query_def cc).

Inductive match_query (cc: callconv): world cc -> query -> query -> Prop :=
  match_query_intro w q1 q2 Hq:
    match_query cc (mk_world cc w q1 q2 Hq) q1 q2.

Inductive match_reply (cc: callconv): world cc -> reply -> reply -> Prop :=
  match_reply_intro w q1 q2 r1 r2 Hq:
    match_reply_def cc w q1 q2 r1 r2 ->
    match_reply cc (mk_world cc w q1 q2 Hq) r1 r2.

Lemma match_query_injective cc w q q1 q2:
  match_query cc w q q1 ->
  match_query cc w q q2 ->
  q2 = q1.
Proof.
  intros H1 H2.
  destruct H1; inv H2.
  reflexivity.
Qed.

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

Program Definition cc_id :=
  {|
    world_def := unit;
    dummy_world_def := tt;
    match_senv w := eq;
    match_query_def w := eq;
    match_reply_def w q1 q2 := eq;
  |}.

Lemma match_cc_id q:
  exists w,
    match_query cc_id w q q /\
    forall r1 r2,
      match_reply cc_id w r1 r2 ->
      r1 = r2.
Proof.
  exists (mk_world cc_id tt q q eq_refl).
  split.
  - constructor.
  - inversion 1.
    congruence.
Qed.

(** ** Extension passes *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Program Definition cc_extends :=
  {|
    world_def := unit;
    dummy_world_def := tt;
    match_senv w := eq;
    match_query_def w :=
      fun '(vargs1, m1) '(vargs2, m2) =>
        Val.lessdef_list vargs1 vargs2 /\
        Mem.extends m1 m2;
    match_reply_def w :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        Val.lessdef vres1 vres2 /\
        Mem.extends m1' m2' /\
        Mem.unchanged_on (loc_out_of_bounds m1) m2 m2';
  |}.
Next Obligation.
  split.
  - constructor.
  - apply Mem.extends_refl.
Qed.

Lemma match_cc_extends vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  exists w,
    match_query cc_extends w (vargs1, m1) (vargs2, m2) /\
    forall vres1 m1' vres2 m2',
      match_reply cc_extends w (vres1, m1') (vres2, m2') ->
      Val.lessdef vres1 vres2 /\
      Mem.extends m1' m2' /\
      Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof.
  intros Hm Hvargs.
  assert (Hq: match_query_def cc_extends tt (vargs1, m1) (vargs2, m2)).
  {
    simpl.
    eauto.
  }
  exists (mk_world cc_extends tt _ _ Hq).
  split.
  - constructor.
  - intros.
    inv H.
    assumption.
Qed.

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

Program Definition cc_inject :=
  {|
    world_def := meminj;
    dummy_world_def := Mem.flat_inj (Mem.nextblock Mem.empty);
    match_senv := symbols_inject;
    match_query_def f :=
      fun '(vargs1, m1) '(vargs2, m2) =>
        Val.inject_list f vargs1 vargs2 /\
        Mem.inject f m1 m2;
    match_reply_def f :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        exists f',
          Val.inject f' vres1 vres2 /\
          Mem.inject f' m1' m2' /\
          Mem.unchanged_on (loc_unmapped f) m1 m1' /\
          Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' /\
          inject_incr f f' /\
          inject_separated f f' m1 m2;
  |}.
Next Obligation.
  split.
  - constructor.
  - apply (Mem.neutral_inject Mem.empty).
    apply Mem.empty_inject_neutral.
Qed.

Lemma match_cc_inject f vargs1 m1 vargs2 m2:
  Val.inject_list f vargs1 vargs2 ->
  Mem.inject f m1 m2 ->
  exists w,
    match_query cc_inject w (vargs1, m1) (vargs2, m2) /\
    forall vres1 m1' vres2 m2',
      match_reply cc_inject w (vres1, m1') (vres2, m2') ->
      exists f',
        Val.inject f' vres1 vres2 /\
        Mem.inject f' m1' m2' /\
        Mem.unchanged_on (loc_unmapped f) m1 m1' /\
        Mem.unchanged_on (loc_out_of_reach f m1) m2 m2' /\
        inject_incr f f' /\
        inject_separated f f' m1 m2.
Proof.
  intros Hvargs Hm.
  assert (Hq: match_query_def cc_inject f (vargs1, m1) (vargs2, m2)).
  {
    simpl.
    eauto.
  }
  exists (mk_world cc_inject _ _ _ Hq).
  split.
  - econstructor.
  - intros vres1 m1' vres2 m2' Hr.
    inv Hr.
    assumption.
Qed.
