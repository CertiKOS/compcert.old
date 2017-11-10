Require Import String.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.

(** * Semantic interface of languages *)

Record language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
    dummy_query: query;
  }.

Arguments dummy_query {_}.

Definition li_c :=
  {|
    query := string * signature * list val * mem;
    reply := val * mem;
    dummy_query := (EmptyString, signature_main, nil, Mem.empty);
  |}.

Definition li_wp :=
  {|
    query := unit;
    reply := int;
    dummy_query := tt;
  |}.

Definition li_empty :=
  {|
    query := unit;
    reply := Empty_set;
    dummy_query := tt;
  |}.

(** XXX temporary fix: external functions are identified with a [string],
  but internal functions use [AST.ident]. To work around this
  discrepancy, we introduce the following mapping. *)
Parameter str2ident : string -> ident.

(** * Calling conventions *)

(** ** Definition *)

Record callconv T1 T2 :=
  mk_callconv {
    world_def: Type;
    dummy_world_def: world_def;
    match_senv:
      world_def -> Senv.t -> Senv.t -> Prop;
    match_query_def:
      world_def -> query T1 -> query T2 -> Prop;
    match_reply_def:
      world_def -> query T1 -> query T2 -> reply T1 -> reply T2 -> Prop;
    match_dummy_query_def:
      match_query_def dummy_world_def dummy_query dummy_query;
  }.

Record world {T1 T2} (cc: callconv T1 T2) :=
  mk_world {
    world_proj :> world_def T1 T2 cc;
    world_query_l: query T1;
    world_query_r: query T2;
    world_match_query:
      match_query_def T1 T2 cc world_proj world_query_l world_query_r;
  }.

Arguments mk_world {T1 T2} cc _ _ _ _.

Program Definition dummy_world {T1 T2 cc}: world cc :=
  mk_world cc _ _ _ (match_dummy_query_def T1 T2 cc).

Inductive match_query {T1 T2} cc: world cc -> query T1 -> query T2 -> Prop :=
  match_query_intro w q1 q2 Hq:
    match_query cc (mk_world cc w q1 q2 Hq) q1 q2.

Inductive match_reply {T1 T2} cc: world cc -> reply T1 -> reply T2 -> Prop :=
  match_reply_intro w q1 q2 r1 r2 Hq:
    match_reply_def T1 T2 cc w q1 q2 r1 r2 ->
    match_reply cc (mk_world cc w q1 q2 Hq) r1 r2.

Lemma match_query_determ {T1 T2} (cc: callconv T1 T2) w q q1 q2:
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

Definition extcall_valid (q: query li_c) (r: reply li_c) :=
  let '(id, sg, vargs, m) := q in
  let '(vres, m') := r in
  extcall_step_valid sg vargs m vres m'.

(** ** Equality passes *)

Program Definition cc_id {T}: callconv T T :=
  {|
    world_def := unit;
    dummy_world_def := tt;
    match_senv w := eq;
    match_query_def w := eq;
    match_reply_def w q1 q2 := eq;
  |}.

Lemma match_cc_id {T} q:
  exists w,
    match_query (@cc_id T) w q q /\
    forall r1 r2,
      match_reply (@cc_id T) w r1 r2 ->
      r1 = r2.
Proof.
  exists (mk_world cc_id tt q q eq_refl).
  split.
  - constructor.
  - inversion 1.
    congruence.
Qed.

Lemma match_query_cc_id {T} w q1 q2:
  match_query (@cc_id T) w q1 q2 ->
  q1 = q2.
Proof.
  destruct 1.
  assumption.
Qed.

Lemma match_reply_cc_id {T} w r:
  match_reply (@cc_id T) w r r.
Proof.
  destruct w.
  repeat constructor.
Qed.

(** ** Extension passes *)

Definition loc_out_of_bounds (m: mem) (b: block) (ofs: Z) : Prop :=
  ~Mem.perm m b ofs Max Nonempty.

Program Definition cc_extends: callconv li_c li_c :=
  {|
    world_def := unit;
    dummy_world_def := tt;
    match_senv w := eq;
    match_query_def w :=
      fun '(id1, sg1, vargs1, m1) '(id2, sg2, vargs2, m2) =>
        id1 = id2 /\
        sg1 = sg2 /\
        Val.lessdef_list vargs1 vargs2 /\
        Mem.extends m1 m2;
    match_reply_def w :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        Val.lessdef vres1 vres2 /\
        Mem.extends m1' m2' /\
        Mem.unchanged_on (loc_out_of_bounds m1) m2 m2';
  |}.
Next Obligation.
  intuition.
  apply Mem.extends_refl.
Qed.

Lemma match_cc_extends id sg vargs1 m1 vargs2 m2:
  Mem.extends m1 m2 ->
  Val.lessdef_list vargs1 vargs2 ->
  exists w,
    match_query cc_extends w (id, sg, vargs1, m1) (id, sg, vargs2, m2) /\
    forall vres1 m1' vres2 m2',
      match_reply cc_extends w (vres1, m1') (vres2, m2') ->
      Val.lessdef vres1 vres2 /\
      Mem.extends m1' m2' /\
      Mem.unchanged_on (loc_out_of_bounds m1) m2 m2'.
Proof.
  intros Hm Hvargs.
  assert (Hq: match_query_def _ _ cc_extends tt (id,sg,vargs1,m1) (id,sg,vargs2,m2)).
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

(** *** Rectangular diagram *)

Program Definition cc_inject: callconv li_c li_c :=
  {|
    world_def := meminj;
    dummy_world_def := Mem.flat_inj (Mem.nextblock Mem.empty);
    match_senv := symbols_inject;
    match_query_def f :=
      fun '(id1, sg1, vargs1, m1) '(id2, sg2, vargs2, m2) =>
        id1 = id2 /\
        sg1 = sg2 /\
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
  intuition.
  apply (Mem.neutral_inject Mem.empty).
  apply Mem.empty_inject_neutral.
Qed.

Lemma match_cc_inject id sg f vargs1 m1 vargs2 m2:
  Val.inject_list f vargs1 vargs2 ->
  Mem.inject f m1 m2 ->
  exists w,
    match_query cc_inject w (id, sg, vargs1, m1) (id, sg, vargs2, m2) /\
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
  assert (match_query_def _ _ cc_inject f (id,sg,vargs1,m1) (id,sg,vargs2,m2)).
  {
    simpl.
    eauto.
  }
  exists (mk_world cc_inject _ _ _ H).
  split.
  - econstructor.
  - intros vres1 m1' vres2 m2' Hr.
    inv Hr.
    assumption.
Qed.

(** *** Triangular diagram *)

(** The triangular diagram requires the initial memories and arguments
  to be identical. They need to be "inject_neutral". *)

Inductive cc_inject_triangle_mq: meminj -> query li_c -> query li_c -> Prop :=
  cc_inject_triangle_mq_intro id sg vargs m:
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    cc_inject_triangle_mq
      (Mem.flat_inj (Mem.nextblock m))
      (id, sg, vargs, m)
      (id, sg, vargs, m).

(** The execution is allowed to extend this self-injection, so that
  the replies may be different. Note that there are no unmapped or
  out-of-reach locations in the initial memory, so that the
  [Mem.unchanged_on] constraints in [cc_inject] are automatically
  satisfied in [cc_inject_triangle]. *)

Program Definition cc_inject_triangle: callconv li_c li_c :=
  {|
    world_def := meminj;
    dummy_world_def := Mem.flat_inj (Mem.nextblock Mem.empty);
    match_senv := symbols_inject;
    match_query_def := cc_inject_triangle_mq;
    match_reply_def f :=
      fun '(vargs1, m1) '(vargs2, m2) '(vres1, m1') '(vres2, m2') =>
        exists f',
          Val.inject f' vres1 vres2 /\
          Mem.inject f' m1' m2' /\
          inject_incr f f' /\
          inject_separated f f' m1 m2;
  |}.
Next Obligation.
  rewrite <- Mem.nextblock_empty.
  constructor; intuition.
  apply Mem.empty_inject_neutral.
Qed.

Definition cc_inject_triangle_id (w: world cc_inject_triangle) :=
  let '(id, sg, vargs, m) := world_query_l _ w in id.

Definition cc_inject_triangle_sg (w: world cc_inject_triangle) :=
  let '(id, sg, vargs, m) := world_query_l _ w in sg.

Definition cc_inject_triangle_args (w: world cc_inject_triangle) :=
  let '(id, sg, vargs, m) := world_query_l _ w in vargs.

Definition cc_inject_triangle_mem (w: world cc_inject_triangle) :=
  let '(id, sg, vargs, m) := world_query_l _ w in m.

(** The following lemma and tactic are used in simulation proofs for
  initial states, as a way to inverse the [match_query] hypothesis. *)

Lemma match_query_cc_inject_triangle (P: _ -> _ -> _ -> _ -> _ -> _ -> Prop):
  (forall id sg vargs m,
    Val.inject_list (Mem.flat_inj (Mem.nextblock m)) vargs vargs ->
    Mem.inject_neutral (Mem.nextblock m) m ->
    P id sg vargs m (id, sg, vargs, m) (id, sg, vargs, m)) ->
  (forall w q1 q2,
    match_query cc_inject_triangle w q1 q2 ->
    P (cc_inject_triangle_id w)
      (cc_inject_triangle_sg w)
      (cc_inject_triangle_args w)
      (cc_inject_triangle_mem w)
      q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq.
  destruct Hq.
  apply H; auto.
Qed.

Ltac match_query_cc_inject_triangle :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern
    (cc_inject_triangle_id w),
    (cc_inject_triangle_sg w),
    (cc_inject_triangle_args w),
    (cc_inject_triangle_mem w),
    q1, q2;
  revert w q1 q2 Hq;
  apply match_query_cc_inject_triangle.

(** The following lemma is used in simulation proofs for final states,
  to show that corresponding replies are related. *)

Lemma match_reply_cc_inject_triangle w f' vres1 m1' vres2 m2':
  let m := cc_inject_triangle_mem w in
  let f := Mem.flat_inj (Mem.nextblock m) in
  Val.inject f' vres1 vres2 ->
  Mem.inject f' m1' m2' ->
  inject_incr f f' ->
  inject_separated f f' m m ->
  match_reply cc_inject_triangle w (vres1, m1') (vres2, m2').
Proof.
  intros.
  subst m f.
  destruct w as [f q1 q2 Hq].
  destruct Hq as [id sg vargs m Hvargs Hm].
  unfold cc_inject_triangle_mem in *.
  simpl in *.
  constructor.
  simpl.
  eauto 10.
Qed.
