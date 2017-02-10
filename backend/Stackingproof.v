(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for the translation from Linear to Mach. *)

(** This file proves semantic preservation for the [Stacking] pass. *)

Require Import Coqlib Errors.
Require Import Integers AST Linking.
Require Import Setoid.
Require Import Values Memory Separation Events Globalenvs Smallstep.
Require Import LTL Op Locations Linear Mach.
Require Import Bounds Conventions Stacklayout Lineartyping.
Require Import Stacking.
Require Import EraseArgs.

Local Open Scope sep_scope.

Definition match_prog (p: Linear.program) (tp: Mach.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

(** * Basic properties of the translation *)

Lemma typesize_typesize:
  forall ty, AST.typesize ty = 4 * Locations.typesize ty.
Proof.
  destruct ty; auto.
Qed.

Remark size_type_chunk:
  forall ty, size_chunk (chunk_of_type ty) = AST.typesize ty.
Proof.
  destruct ty; reflexivity.
Qed.

Remark align_type_chunk:
  forall ty, align_chunk (chunk_of_type ty) = 4 * Locations.typealign ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma slot_outgoing_argument_valid:
  forall f ofs ty sg,
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) -> slot_valid f Outgoing ofs ty = true.
Proof.
  intros. exploit loc_arguments_acceptable_2; eauto. intros [A B].
  unfold slot_valid. unfold proj_sumbool.
  rewrite zle_true by omega.
  rewrite pred_dec_true by auto.
  auto.
Qed.

Lemma load_result_inject:
  forall j ty v v',
  Val.inject j v v' -> Val.has_type v ty -> Val.inject j v (Val.load_result (chunk_of_type ty) v').
Proof.
  destruct 1; intros; auto; destruct ty; simpl; try contradiction; econstructor; eauto.
Qed.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable return_address_offset: Mach.function -> Mach.code -> int -> Prop.

Hypothesis return_address_offset_exists:
  forall f sg ros c,
  is_tail (Mcall sg ros :: c) (fn_code f) ->
  exists ofs, return_address_offset f c ofs.

Variable prog: Linear.program.
Variable tprog: Mach.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Section WITHINITSP.

Variables init_sp' init_ra: val.
Let step := Mach.step init_sp' init_ra return_address_offset.

Section FRAME_PROPERTIES.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.

Lemma unfold_transf_function:
  tf = Mach.mkfunction
         f.(Linear.fn_sig)
         (transl_body f fe)
         fe.(fe_size)
         (Int.repr fe.(fe_ofs_link))
         (Int.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. congruence.
  intros; discriminate.
Qed.

Lemma transf_function_well_typed:
  wt_function f = true.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb. auto. intros; discriminate.
Qed.

Lemma size_no_overflow: fe.(fe_size) <= Int.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Int.max_unsigned (fe_size (make_env (function_bounds f)))).
  intros; discriminate.
  intros. unfold fe. unfold b. omega.
  intros; discriminate.
Qed.

Remark bound_stack_data_stacksize:
  f.(Linear.fn_stacksize) <= b.(bound_stack_data).
Proof.
  unfold b, function_bounds, bound_stack_data. apply Zmax1.
Qed.

(** * Memory assertions used to describe the contents of stack frames *)

Local Opaque Z.add Z.mul Z.divide.

(** Accessing the stack frame using [load_stack] and [store_stack]. *)

Lemma contains_get_stack:
  forall spec m ty sp ofs,
  m |= contains (chunk_of_type ty) sp ofs spec ->
  exists v, load_stack m (Vptr sp Int.zero) ty (Int.repr ofs) = Some v /\ spec v.
Proof.
  intros. unfold load_stack. 
  replace (Val.add (Vptr sp Int.zero) (Vint (Int.repr ofs))) with (Vptr sp (Int.repr ofs)).
  eapply loadv_rule; eauto.
  simpl. rewrite Int.add_zero_l; auto.
Qed.

Lemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= hasvalue (chunk_of_type ty) sp ofs v ->
  load_stack m (Vptr sp Int.zero) ty (Int.repr ofs) = Some v.
Proof.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). congruence.
Qed.

Lemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= contains (chunk_of_type ty) sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      store_stack m (Vptr sp Int.zero) ty (Int.repr ofs) v = Some m'
  /\ m' |= contains (chunk_of_type ty) sp ofs spec ** P.
Proof.
  intros. unfold store_stack. 
  replace (Val.add (Vptr sp Int.zero) (Vint (Int.repr ofs))) with (Vptr sp (Int.repr ofs)).
  eapply storev_rule; eauto.
  simpl. rewrite Int.add_zero_l; auto.
Qed.

(** [contains_locations j sp pos bound sl ls] is a separation logic assertion
  that holds if the memory area at block [sp], offset [pos], size [4 * bound],
  reflects the values of the stack locations of kind [sl] given by the
  location map [ls], up to the memory injection [j].

  Two such [contains_locations] assertions will be used later, one to
  reason about the values of [Local] slots, the other about the values of
  [Outgoing] slots. *)

Program Definition contains_locations (j: meminj) (sp: block) (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Int.modulus /\
    Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.load (chunk_of_type ty) m sp (pos + 4 * ofs) = Some v
           /\ Val.inject j (ls (S sl ofs ty)) v;
  m_footprint := fun b ofs =>
    b = sp /\ pos <= ofs < pos + 4 * bound
  ;
  m_invar_weak := false
|}.
Next Obligation.
  intuition auto. 
- red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
- exploit H4; eauto. intros (v & A & B). exists v; split; auto.
  eapply Mem.load_unchanged_on; eauto.
  simpl; intros. rewrite size_type_chunk, typesize_typesize in H8. 
  split; auto. omega.
Qed.
Next Obligation.
  eauto with mem.
Qed.

Remark valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m sp pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) sp (pos + 4 * ofs) p.
Proof.
  intros; split.
- red; intros. apply Mem.perm_implies with Freeable; auto with mem. 
  apply H0. rewrite size_type_chunk, typesize_typesize in H4. omega.
- rewrite align_type_chunk. apply Z.divide_add_r. 
  apply Zdivide_trans with 8; auto.
  exists (8 / (4 * typealign ty)); destruct ty; reflexivity.
  apply Z.mul_divide_mono_l. auto.
Qed.

Lemma get_location:
  forall m j sp pos bound sl ls ofs ty,
  m |= contains_locations j sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
     load_stack m (Vptr sp Int.zero) ty (Int.repr (pos + 4 * ofs)) = Some v
  /\ Val.inject j (ls (S sl ofs ty)) v.
Proof.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. intros (v & U & V). exists v; split; auto.
  unfold load_stack; simpl. rewrite Int.add_zero_l, Int.unsigned_repr; auto.
  unfold Int.max_unsigned. generalize (typesize_pos ty). omega.
Qed.

Lemma set_location:
  forall m j sp pos bound sl ls P ofs ty v v',
  m |= contains_locations j sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Int.zero) ty (Int.repr (pos + 4 * ofs)) v' = Some m'
  /\ m' |= contains_locations j sp pos bound sl (Locmap.set (S sl ofs ty) v ls) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct Mem.valid_access_store as [m' STORE]. 
  eapply valid_access_location; eauto. 
  assert (PERM: Mem.range_perm m' sp pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto with mem. }
  exists m'; split.
- unfold store_stack; simpl. rewrite Int.add_zero_l, Int.unsigned_repr; eauto.
  unfold Int.max_unsigned. generalize (typesize_pos ty). omega.
- simpl. intuition auto.
+ unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) (S sl ofs0 ty0)); [|destruct (Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  eapply Mem.load_store_similar_2; eauto. omega. 
  inv H3; destruct (chunk_of_type ty); simpl; econstructor; eauto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X; eapply Mem.load_store_other; eauto.
  destruct d. congruence. right. rewrite ! size_type_chunk, ! typesize_typesize. omega.
* (* overlapping locations *)
  destruct (Mem.valid_access_load m' (chunk_of_type ty0) sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem. 
  eapply valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto. 
  cut (Mem.strong_unchanged_on (m_footprint P) m m').
  {
    destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
  }
  eapply Mem.store_strong_unchanged_on; eauto.
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. omega.
Qed.

Lemma initial_locations:
  forall j sp pos bound P sl ls m,
  m |= range sp pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (S sl ofs ty) = Vundef) ->
  m |= contains_locations j sp pos bound sl ls ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem. 
  destruct (Mem.valid_access_load m (chunk_of_type ty) sp (pos + 4 * ofs)) as [v LOAD].
  eapply valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed.

Lemma contains_locations_exten:
  forall ls ls' j sp pos bound sl,
  (forall ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j sp pos bound sl ls').
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. rewrite H. eauto.
Qed.

Lemma contains_locations_incr:
  forall j j' sp pos bound sl ls,
  inject_incr j j' ->
  massert_imp (contains_locations j sp pos bound sl ls)
              (contains_locations j' sp pos bound sl ls).
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. exploit H5; eauto. intros (v & A & B). exists v; eauto.
Qed.

(** [contains_callee_saves j sp pos rl ls] is a memory assertion that holds
  if block [sp], starting at offset [pos], contains the values of the
  callee-save registers [rl] as given by the location map [ls],
  up to the memory injection [j].  The memory layout of the registers in [rl]
  is the same as that implemented by [save_callee_save_rec]. *)

Fixpoint contains_callee_saves (j: meminj) (sp: block) (pos: Z) (rl: list mreg) (ls: locset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      contains (chunk_of_type ty) sp pos1 (fun v => Val.inject j (ls (R r)) v)
      ** contains_callee_saves j sp (pos1 + sz) rl ls
  end.

Lemma contains_callee_saves_invar_weak rl :
  forall j sp pos ls,
    m_invar_weak (contains_callee_saves j sp pos rl ls) = false.
Proof.
  induction rl; simpl; auto.
Qed.

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Local Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel.

Local Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel.

Lemma contains_callee_saves_incr:
  forall j j' sp ls,
  inject_incr j j' ->
  forall rl pos,
  massert_imp (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j' sp pos rl ls).
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_1; auto. apply contains_imp. eauto.
Qed.

Lemma contains_callee_saves_exten:
  forall j sp ls ls' rl pos,
  (forall r, In r rl -> ls' (R r) = ls (R r)) ->
  massert_eqv (contains_callee_saves j sp pos rl ls)
              (contains_callee_saves j sp pos rl ls').
Proof.
  induction rl as [ | r1 rl]; simpl; intros.
- reflexivity.
- apply sepconj_morph_2; auto. rewrite H by auto. reflexivity.
Qed.

(** Separation logic assertions describing the stack frame at [sp].
  It must contain:
  - the values of the [Local] stack slots of [ls], as per [contains_locations]
  - the values of the [Outgoing] stack slots of [ls], as per [contains_locations]
  - the [parent] pointer representing the back link to the caller's frame
  - the [retaddr] pointer representing the saved return address
  - the initial values of the used callee-save registers as given by [ls0],
    as per [contains_callee_saves].

In addition, we use a nonseparating conjunction to record the fact that
we have full access rights on the stack frame, except the part that
represents the Linear stack data. *)

Definition frame_contents_1 (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
    contains_locations j sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations j sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** hasvalue Mint32 sp fe.(fe_ofs_link) parent
 ** hasvalue Mint32 sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents (j: meminj) (sp: block) (ls ls0: locset) (parent retaddr: val) :=
  mconj (frame_contents_1 j sp ls ls0 parent retaddr)
        (range sp 0 fe.(fe_stack_data) **
         range sp (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

Lemma frame_contents_invar_weak j sp ls ls0 parent retaddr:
  m_invar_weak (frame_contents j sp ls ls0 parent retaddr) = false.
Proof.
  simpl.
  rewrite contains_callee_saves_invar_weak.
  reflexivity.
Qed.

(** Accessing components of the frame. *)

Lemma frame_get_local:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Int.zero) ty (Int.repr (offset_local fe ofs)) = Some v
  /\ Val.inject j (ls (S Local ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_outgoing:
  forall ofs ty j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
     load_stack m (Vptr sp Int.zero) ty (Int.repr (offset_arg ofs)) = Some v
  /\ Val.inject j (ls (S Outgoing ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  eapply get_location; eauto. 
Qed.

Lemma frame_get_parent:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Int.zero) Tint (Int.repr fe.(fe_ofs_link)) = Some parent.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H. 
  eapply hasvalue_get_stack; eauto.
Qed.

Lemma frame_get_retaddr:
  forall j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  load_stack m (Vptr sp Int.zero) Tint (Int.repr fe.(fe_ofs_retaddr)) = Some retaddr.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick4 in H. 
  eapply hasvalue_get_stack; eauto.
Qed.

(** Assigning a [Local] or [Outgoing] stack slot. *)

Lemma frame_set_local:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Int.zero) ty (Int.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Local ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1. 
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

Lemma frame_set_outgoing:
  forall ofs ty v v' j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.inject j v v' ->
  exists m',
     store_stack m (Vptr sp Int.zero) ty (Int.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents j sp (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP. 
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  assert (forall i k p, Mem.perm m sp i k p -> Mem.perm m' sp i k p).
  {  intros. unfold store_stack in A; simpl in A. eapply Mem.perm_store_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

(** Invariance by change of location maps. *)

Lemma frame_contents_exten:
  forall ls ls0 ls' ls0' j sp parent retaddr P m,
  (forall sl ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp ls' ls0' parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite  <- contains_callee_saves_exten by eauto.
  assumption.
Qed.

(** Invariance by assignment to registers. *)

Corollary frame_set_reg:
  forall r v j sp ls ls0 parent retaddr m P,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.set (R r) v ls) ls0 parent retaddr ** P.
Proof.
  intros. apply frame_contents_exten with ls ls0; auto.
Qed.

Corollary frame_undef_regs:
  forall j sp ls ls0 parent retaddr m P rl,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (LTL.undef_regs rl ls) ls0 parent retaddr ** P.
Proof.
Local Opaque sepconj.
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto. 
Qed.

Corollary frame_set_regpair:
  forall j sp ls0 parent retaddr m P p v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setpair p v ls) ls0 parent retaddr ** P.
Proof.
  intros. destruct p; simpl.
  apply frame_set_reg; auto.
  apply frame_set_reg; apply frame_set_reg; auto.
Qed.

Corollary frame_set_res:
  forall j sp ls0 parent retaddr m P res v ls,
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  m |= frame_contents j sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
Proof.
  induction res; simpl; intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed.

(** Invariance by change of memory injection. *)

Lemma frame_contents_incr:
  forall j sp ls ls0 parent retaddr m P j',
  m |= frame_contents j sp ls ls0 parent retaddr ** P ->
  inject_incr j j' ->
  m |= frame_contents j' sp ls ls0 parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- (contains_locations_incr j j') by auto.
  rewrite <- (contains_locations_incr j j') by auto.
  erewrite  <- contains_callee_saves_incr by eauto.
  assumption.
Qed.

(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (j: meminj) (ls: locset) (rs: regset) : Prop :=
  forall r, Val.inject j (ls (R r)) (rs r).

(** Agreement over locations *)

Record agree_locs (ls ls0: locset) : Prop :=
  mk_agree_locs {

    (** Unused registers have the same value as in the caller *)
    agree_unused_reg:
       forall r, ~(mreg_within_bounds b r) -> ls (R r) = ls0 (R r);

    (** Incoming stack slots have the same value as the
        corresponding Outgoing stack slots in the caller *)
    agree_incoming:
       forall ofs ty,
       In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters f.(Linear.fn_sig))) ->
       ls (S Incoming ofs ty) = ls0 (S Outgoing ofs ty)
}.

(** Auxiliary predicate used at call points *)

Definition agree_callee_save (ls ls0: locset) : Prop :=
  forall l,
  match l with
  | R r => is_callee_save r = true
  | S _ _ _ => True
  end ->
  ls l = ls0 l.

(** ** Properties of [agree_regs]. *)

(** Values of registers *)

Lemma agree_reg:
  forall j ls rs r,
  agree_regs j ls rs -> Val.inject j (ls (R r)) (rs r).
Proof.
  intros. auto.
Qed.

Lemma agree_reglist:
  forall j ls rs rl,
  agree_regs j ls rs -> Val.inject_list j (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall j ls rs r v v',
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_pair:
  forall j p v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setpair p v ls) (set_pair p v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_regs_set_reg; auto.
- apply agree_regs_set_reg. apply agree_regs_set_reg; auto. 
  apply Val.hiword_inject; auto. apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_set_res:
  forall j res v v' ls rs,
  agree_regs j ls rs ->
  Val.inject j v v' ->
  agree_regs j (Locmap.setres res v ls) (set_res res v' rs).
Proof.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_inject; auto.
  apply Val.loword_inject; auto.
Qed.

Lemma agree_regs_exten:
  forall j ls rs ls' rs',
  agree_regs j ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs j ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]].
  rewrite A. constructor.
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall j rl ls rs,
  agree_regs j ls rs ->
  agree_regs j (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall j ls rs sl ofs ty v,
  agree_regs j ls rs ->
  agree_regs j (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation by increasing memory injections *)

Lemma agree_regs_inject_incr:
  forall j ls rs j',
  agree_regs j ls rs -> inject_incr j j' -> agree_regs j' ls rs.
Proof.
  intros; red; intros; eauto with stacking.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall j ls rs,
  agree_regs j ls rs ->
  agree_regs j (call_regs ls) rs.
Proof.
  intros.
  unfold call_regs; intros; red; intros; auto.
Qed.

(** ** Properties of [agree_locs] *)

(** Preservation under assignment of machine register. *)

Lemma agree_locs_set_reg:
  forall ls ls0 r v,
  agree_locs ls ls0 ->
  mreg_within_bounds b r ->
  agree_locs (Locmap.set (R r) v ls) ls0.
Proof.
  intros. inv H; constructor; auto; intros.
  rewrite Locmap.gso. auto. red. intuition congruence.
Qed.

Lemma caller_save_reg_within_bounds:
  forall r,
  is_callee_save r = false -> mreg_within_bounds b r.
Proof.
  intros; red; intros. congruence.
Qed.

Lemma agree_locs_set_pair:
  forall ls0 p v ls,
  agree_locs ls ls0 ->
  forall_rpair (fun r => is_callee_save r = false) p ->
  agree_locs (Locmap.setpair p v ls) ls0.
Proof.
  intros.
  destruct p; simpl in *.
  apply agree_locs_set_reg; auto. apply caller_save_reg_within_bounds; auto.
  destruct H0.
  apply agree_locs_set_reg; auto. apply agree_locs_set_reg; auto.
  apply caller_save_reg_within_bounds; auto. apply caller_save_reg_within_bounds; auto. 
Qed.

Lemma agree_locs_set_res:
  forall ls0 res v ls,
  agree_locs ls ls0 ->
  (forall r, In r (params_of_builtin_res res) -> mreg_within_bounds b r) ->
  agree_locs (Locmap.setres res v ls) ls0.
Proof.
  induction res; simpl; intros.
- eapply agree_locs_set_reg; eauto.
- auto.
- apply IHres2; auto using in_or_app.
Qed.

Lemma agree_locs_undef_regs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> mreg_within_bounds b r) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  induction regs; simpl; intros.
  auto.
  apply agree_locs_set_reg; auto.
Qed.

Lemma agree_locs_undef_locs_1:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  (forall r, In r regs -> is_callee_save r = false) ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_regs; eauto.
  intros. apply caller_save_reg_within_bounds. auto.
Qed.

Lemma agree_locs_undef_locs:
  forall ls0 regs ls,
  agree_locs ls ls0 ->
  existsb is_callee_save regs = false ->
  agree_locs (LTL.undef_regs regs ls) ls0.
Proof.
  intros. eapply agree_locs_undef_locs_1; eauto. 
  intros. destruct (is_callee_save r) eqn:CS; auto. 
  assert (existsb is_callee_save regs = true).
  { apply existsb_exists. exists r; auto. }
  congruence.
Qed.

(** Preservation by assignment to local slot *)

Lemma agree_locs_set_slot:
  forall ls ls0 sl ofs ty v,
  agree_locs ls ls0 ->
  slot_writable sl = true ->
  agree_locs (Locmap.set (S sl ofs ty) v ls) ls0.
Proof.
  intros. destruct H; constructor; intros.
- rewrite Locmap.gso; auto. red; auto.
- rewrite Locmap.gso; auto. red. left. destruct sl; discriminate.
Qed.

(** Preservation at return points (when [ls] is changed but not [ls0]). *)

Lemma agree_locs_return:
  forall ls ls0 ls',
  agree_locs ls ls0 ->
  agree_callee_save ls' ls ->
  agree_locs ls' ls0.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite H0; auto.
Qed.

(** Preservation at tailcalls (when [ls0] is changed but not [ls]). *)

Lemma agree_locs_tailcall:
  forall ls ls0 ls0',
  agree_locs ls ls0 ->
  agree_callee_save ls0 ls0' ->
  agree_locs ls ls0'.
Proof.
  intros. red in H0. inv H; constructor; auto; intros.
- rewrite <- H0; auto. unfold mreg_within_bounds in H. tauto.
- rewrite <- H0; auto.
Qed.

(** ** Properties of [agree_callee_save]. *)

Lemma agree_callee_save_return_regs:
  forall ls1 ls2,
  agree_callee_save (return_regs ls1 ls2) ls1.
Proof.
  intros; red; intros.
  unfold return_regs. destruct l; auto. rewrite H; auto.
Qed.

Lemma agree_callee_save_set_result:
  forall sg v ls1 ls2,
  agree_callee_save ls1 ls2 ->
  agree_callee_save (Locmap.setpair (loc_result sg) v ls1) ls2.
Proof.
  intros; red; intros. rewrite Locmap.gpo. apply H; auto. 
  assert (X: forall r, is_callee_save r = false -> Loc.diff l (R r)).
  { intros. destruct l; auto. simpl; congruence. }
  generalize (loc_result_caller_save sg). destruct (loc_result sg); simpl; intuition auto.
Qed.

(** ** Properties of destroyed registers. *)

Definition no_callee_saves (l: list mreg) : Prop :=
  existsb is_callee_save l = false.

Remark destroyed_by_op_caller_save:
  forall op, no_callee_saves (destroyed_by_op op).
Proof.
  unfold no_callee_saves; destruct op; reflexivity.
Qed.

Remark destroyed_by_load_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_load chunk addr).
Proof.
  unfold no_callee_saves; destruct chunk; reflexivity.
Qed.

Remark destroyed_by_store_caller_save:
  forall chunk addr, no_callee_saves (destroyed_by_store chunk addr).
Proof.
  unfold no_callee_saves; destruct chunk; reflexivity.
Qed.

Remark destroyed_by_cond_caller_save:
  forall cond, no_callee_saves (destroyed_by_cond cond).
Proof.
  unfold no_callee_saves; destruct cond; reflexivity.
Qed.

Remark destroyed_by_jumptable_caller_save:
  no_callee_saves destroyed_by_jumptable.
Proof.
  red; reflexivity.
Qed.

Remark destroyed_by_setstack_caller_save:
  forall ty, no_callee_saves (destroyed_by_setstack ty).
Proof.
  unfold no_callee_saves; destruct ty; reflexivity.
Qed.

Remark destroyed_at_function_entry_caller_save:
  no_callee_saves destroyed_at_function_entry.
Proof.
  red; reflexivity.
Qed.

Hint Resolve destroyed_by_op_caller_save destroyed_by_load_caller_save
    destroyed_by_store_caller_save
    destroyed_by_cond_caller_save destroyed_by_jumptable_caller_save
    destroyed_at_function_entry_caller_save: stacking.

Remark destroyed_by_setstack_function_entry:
  forall ty, incl (destroyed_by_setstack ty) destroyed_at_function_entry.
Proof.
Local Transparent destroyed_by_setstack destroyed_at_function_entry.
  unfold incl; destruct ty; simpl; tauto.
Qed.

Remark transl_destroyed_by_op:
  forall op e, destroyed_by_op (transl_op e op) = destroyed_by_op op.
Proof.
  intros; destruct op; reflexivity.
Qed.

Remark transl_destroyed_by_load:
  forall chunk addr e, destroyed_by_load chunk (transl_addr e addr) = destroyed_by_load chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

Remark transl_destroyed_by_store:
  forall chunk addr e, destroyed_by_store chunk (transl_addr e addr) = destroyed_by_store chunk addr.
Proof.
  intros; destruct chunk; reflexivity.
Qed.

(** * Correctness of saving and restoring of callee-save registers *)

(** The following lemmas show the correctness of the register saving
  code generated by [save_callee_save]: after this code has executed,
  the register save areas of the current frame do contain the
  values of the callee-save registers used by the function. *)

Section SAVE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls: locset.

Hypothesis ls_temp_undef:
  forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: forall r, Val.has_type (ls (R r)) (mreg_type r).

Lemma save_callee_save_rec_correct:
  forall k l pos rs m P,
  (forall r, In r l -> is_callee_save r = true) ->
  m |= range sp pos (size_callee_save_area_rec l pos) ** P ->
  agree_regs j ls rs ->
  exists rs', exists m',
     star step tge
        (State cs fb (Vptr sp Int.zero) (save_callee_save_rec l pos k) rs m)
     E0 (State cs fb (Vptr sp Int.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp pos l ls ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs j ls rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b) .
Proof.
  induction l as [ | r l]; simpl; intros until P; intros CS SEP AG.
- exists rs, m. 
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto. 
  auto.
- set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (SZREC: pos1 + sz <= size_callee_save_area_rec l (pos1 + sz)) by (apply size_callee_save_area_rec_incr).
  assert (POS1: pos <= pos1) by (apply align_le; auto).
  assert (AL1: (align_chunk (chunk_of_type ty) | pos1)).
  { unfold pos1. apply Zdivide_trans with sz.
    unfold sz; rewrite <- size_type_chunk. apply align_size_chunk_divides.
    apply align_divides; auto. }
  apply range_drop_left with (mid := pos1) in SEP; [ | omega ].
  apply range_split with (mid := pos1 + sz) in SEP; [ | omega ].
  unfold sz at 1 in SEP. rewrite <- size_type_chunk in SEP.
  apply range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.inject j (ls (R r)) v') (rs r)).
  eexact SEP.
  apply load_result_inject; auto. apply wt_ls. 
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs j ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite undef_regs_other by auto. apply AG. }
  rewrite sep_swap in SEP. 
  exploit (IHl (pos1 + sz) rs1 m1); eauto.
  intros (rs2 & m2 & A & B & C & D & VALID).
  exists rs2, m2. 
  split. eapply star_left; eauto. constructor. exact STORE. auto. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. unfold store_stack in STORE; simpl in STORE. eapply Mem.perm_store_1; eauto.
  split. auto.
  unfold store_stack, Val.add, Mem.storev in STORE.
  eauto with mem.
Qed.

End SAVE_CALLEE_SAVE.

Remark LTL_undef_regs_same:
  forall r rl ls, In r rl -> LTL.undef_regs rl ls (R r) = Vundef.
Proof.
  induction rl; simpl; intros. contradiction.
  unfold Locmap.set. destruct (Loc.eq (R a) (R r)). auto.
  destruct (Loc.diff_dec (R a) (R r)); auto.
  apply IHrl. intuition congruence.
Qed.

Remark LTL_undef_regs_others:
  forall r rl ls, ~In r rl -> LTL.undef_regs rl ls (R r) = ls (R r).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. intuition. red. intuition.
Qed.

Remark LTL_undef_regs_slot:
  forall sl ofs ty rl ls, LTL.undef_regs rl ls (S sl ofs ty) = ls (S sl ofs ty).
Proof.
  induction rl; simpl; intros. auto.
  rewrite Locmap.gso. apply IHrl. red; auto.
Qed.

Remark undef_regs_type:
  forall ty l rl ls,
  Val.has_type (ls l) ty -> Val.has_type (LTL.undef_regs rl ls l) ty.
Proof.
  induction rl; simpl; intros.
- auto.
- unfold Locmap.set. destruct (Loc.eq (R a) l). red; auto.
  destruct (Loc.diff_dec (R a) l); auto. red; auto.
Qed.

Lemma save_callee_save_correct:
  forall j ls ls0 rs sp cs fb k m P,
  m |= range sp fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  agree_callee_save ls ls0 ->
  agree_regs j ls rs ->
  let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) in
  let rs1 := undef_regs destroyed_at_function_entry rs in
  exists rs', exists m',
     star step tge
        (State cs fb (Vptr sp Int.zero) (save_callee_save fe k) rs1 m)
     E0 (State cs fb (Vptr sp Int.zero) k rs' m')
  /\ m' |= contains_callee_saves j sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs j ls1 rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b ) .
Proof.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1.
  exploit (save_callee_save_rec_correct j cs fb sp ls1).
- intros. unfold ls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. unfold ls1. apply undef_regs_type. apply TY. 
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- clear SEP. intros (rs' & m' & EXEC & SEP & PERMS & AG' & VALID).
  exists rs', m'. 
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten j sp ls0 ls1). exact SEP.
  intros. apply b.(used_callee_save_prop) in H.
    unfold ls1. rewrite LTL_undef_regs_others. unfold call_regs. 
    apply AGCS; auto.
    red; intros.
    assert (existsb is_callee_save destroyed_at_function_entry = false)
       by  (apply destroyed_at_function_entry_caller_save).
    assert (existsb is_callee_save destroyed_at_function_entry = true).
    { apply existsb_exists. exists r; auto. }
    congruence.
  split. exact PERMS.
  split. exact AG'.
  exact VALID.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)

Lemma function_prologue_correct:
  forall j ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P,
  agree_regs j ls rs ->
  agree_callee_save ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.alloc m1 0 f.(Linear.fn_stacksize) = (m2, sp) ->
  Val.has_type parent Tint -> Val.has_type ra Tint ->
  m1' |= minjection j m1 ** globalenv_inject ge j ** P ->
  exists j', exists rs', exists m2', exists sp', exists m3', exists m4', exists m5',
     Mem.alloc m1' 0 tf.(fn_stacksize) = (m2', sp')
  /\ store_stack m2' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) parent = Some m3'
  /\ store_stack m3' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) ra = Some m4'
  /\ star step tge
         (State cs fb (Vptr sp' Int.zero) (save_callee_save fe k) rs1 m4')
      E0 (State cs fb (Vptr sp' Int.zero) k rs' m5')
  /\ agree_regs j' ls1 rs'
  /\ agree_locs ls1 ls0
  /\ m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P
  /\ j' sp = Some(sp', fe.(fe_stack_data))
  /\ inject_incr j j'
  /\ inject_separated j j' m1 m1'
  /\ (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)
  /\ (forall b, Mem.valid_block m1' b -> Mem.valid_block m5' b)
  /\ (forall b o k p, Mem.perm m1' b o k p -> Mem.perm m5' b o k p).
Proof.
  intros until P; intros AGREGS AGCS WTREGS LS1 RS1 ALLOC TYPAR TYRA SEP.
  rewrite unfold_transf_function.
  unfold fn_stacksize, fn_link_ofs, fn_retaddr_ofs.
  (* Stack layout info *)
Local Opaque b fe.
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto. simpl. 
  intros LAYOUT1 LAYOUT2.
  (* Allocation step *)
  destruct (Mem.alloc m1' 0 (fe_size fe)) as [m2' sp'] eqn:ALLOC'.
  exploit alloc_parallel_rule_2.
  eexact SEP. eexact ALLOC. eexact ALLOC'. 
  instantiate (1 := fe_stack_data fe). tauto.
  reflexivity. 
  instantiate (1 := fe_stack_data fe + bound_stack_data b). rewrite Z.max_comm. reflexivity.
  generalize (bound_stack_data_pos b) size_no_overflow; omega.
  tauto.
  tauto.
  clear SEP. intros (j' & SEP & INCR & SAME & INJSEP).
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
    m2' |= mconj (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                 (range sp' 0 (fe_stack_data fe) ** range sp' (fe_stack_data fe + bound_stack_data b) (fe_size fe))
           ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  apply (frame_env_separated b) in SEP. replace (make_env b) with fe in SEP by auto.
  (* Store of parent *)
  rewrite sep_swap3 in SEP. 
  apply (range_contains Mint32) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = parent) parent (fun _ => True) m2' Tint).
  eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m3' & STORE_PARENT & SEP).
  rewrite sep_swap3 in SEP.
  (* Store of return address *)
  rewrite sep_swap4 in SEP.
  apply (range_contains Mint32) in SEP; [|tauto].
  exploit (contains_set_stack (fun v' => v' = ra) ra (fun _ => True) m3' Tint).
  eexact SEP. apply Val.load_result_same; auto.
  clear SEP; intros (m4' & STORE_RETADDR & SEP).
  rewrite sep_swap4 in SEP.
  (* Saving callee-save registers *)
  rewrite sep_swap5 in SEP.
  exploit (save_callee_save_correct j' ls ls0 rs); eauto.
  apply agree_regs_inject_incr with j; auto.
  replace (LTL.undef_regs destroyed_at_function_entry (call_regs ls)) with ls1 by auto.
  replace (undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & SAVE_CS & SEP & PERMS & AGREGS' & VALID).
  rewrite sep_swap5 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Local). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  exploit (initial_locations j'). eexact SEP. tauto. 
  instantiate (1 := Outgoing). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents j' sp' ls1 ls0 parent ra ** minjection j' m2 ** globalenv_inject ge j' ** P).
  { eapply frame_mconj. eexact SEPCONJ. 
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    assert (forall ofs k p, Mem.perm m2' sp' ofs k p -> Mem.perm m5' sp' ofs k p).
    { intros. apply PERMS. 
      unfold store_stack in STORE_PARENT, STORE_RETADDR.
      simpl in STORE_PARENT, STORE_RETADDR.
      eauto using Mem.perm_store_1. }
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  clear SEP SEPCONJ.
(* Conclusions *)
  exists j', rs2, m2', sp', m3', m4', m5'.
  split. auto.
  split. exact STORE_PARENT.
  split. exact STORE_RETADDR.
  split. eexact SAVE_CS.
  split. exact AGREGS'.
  split. rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold call_regs. apply AGCS. 
    unfold mreg_within_bounds in H; tauto.
    unfold call_regs. apply AGCS. auto.
  split. exact SEPFINAL.
  split. exact SAME.
  split. exact INCR.
  split. exact INJSEP.
  split. eauto with mem.
  split. unfold store_stack, Val.add, Mem.storev in * ; eauto with mem.
  intros.
  eapply PERMS.
  unfold store_stack, Val.add, Mem.storev in * ; eauto with mem.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: block.
Variable ls0: locset.
Variable m: mem.

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> Val.inject j (ls0 (R r)) (rs r).

Lemma restore_callee_save_rec_correct:
  forall l ofs rs k,
  m |= contains_callee_saves j sp ofs l ls0 ->
  agree_unused ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs',
    star step tge
      (State cs fb (Vptr sp Int.zero) (restore_callee_save_rec l ofs k) rs m)
   E0 (State cs fb (Vptr sp Int.zero) k rs' m)
  /\ (forall r, In r l -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
  induction l as [ | r l]; simpl; intros.
- (* base case *)
  exists rs. intuition auto. apply star_refl.
- (* inductive case *)
  set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (ofs1 := align ofs sz).
  assert (SZPOS: sz > 0) by (apply AST.typesize_pos).
  assert (OFSLE: ofs <= ofs1) by (apply align_le; auto).
  assert (BOUND: mreg_within_bounds b r) by eauto.
  exploit contains_get_stack.
    eapply sep_proj1; eassumption.
  intros (v & LOAD & SPEC).
  exploit (IHl (ofs1 + sz) (rs#r <- v)).
    eapply sep_proj2; eassumption.
    red; intros. rewrite Regmap.gso. auto. intuition congruence.
    eauto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eapply star_step; eauto. 
    econstructor. exact LOAD. traceEq.
  split. intros.
    destruct (In_dec mreg_eq r0 l). auto. 
    assert (r = r0) by tauto. subst r0.
    rewrite C by auto. rewrite Regmap.gss. exact SPEC.
  split. intros. 
    rewrite C by tauto. apply Regmap.gso. intuition auto.
  exact D.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall m j sp ls ls0 pa ra P rs k cs fb,
  m |= frame_contents j sp ls ls0 pa ra ** P ->
  agree_unused j ls0 rs ->
  exists rs',
    star step tge
       (State cs fb (Vptr sp Int.zero) (restore_callee_save fe k) rs m)
    E0 (State cs fb (Vptr sp Int.zero) k rs' m)
  /\ (forall r,
        is_callee_save r = true -> Val.inject j (ls0 (R r)) (rs' r))
  /\ (forall r,
        is_callee_save r = false -> rs' r = rs r).
Proof.
  intros.
  unfold frame_contents, frame_contents_1 in H. 
  apply mconj_proj1 in H. rewrite ! sep_assoc in H. apply sep_pick5 in H. 
  exploit restore_callee_save_rec_correct; eauto.
  intros; unfold mreg_within_bounds; auto.
  intros (rs' & A & B & C & D).
  exists rs'.
  split. eexact A.
  split; intros.
  destruct (In_dec mreg_eq r (used_callee_save b)).
  apply B; auto.
  rewrite C by auto. apply H0. unfold mreg_within_bounds; tauto.
  apply C. red; intros. apply (used_callee_save_prop b) in H2. congruence.
Qed.

(** As a corollary, we obtain the following correctness result for
  the execution of a function epilogue (reloading of used callee-save
  registers + reloading of the link and return address + freeing
  of the frame). *)

Lemma function_epilogue_correct:
  forall m' j sp' ls ls0 pa ra P m rs sp m1 k cs fb,
  m' |= frame_contents j sp' ls ls0 pa ra ** minjection j m ** P ->
  agree_regs j ls rs ->
  agree_locs ls ls0 ->
  j sp = Some(sp', fe.(fe_stack_data)) ->
  Mem.free m sp 0 f.(Linear.fn_stacksize) = Some m1 ->
  exists rs1, exists m1',
     load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_link_ofs) = Some pa
  /\ load_stack m' (Vptr sp' Int.zero) Tint tf.(fn_retaddr_ofs) = Some ra
  /\ Mem.free m' sp' 0 tf.(fn_stacksize) = Some m1'
  /\ star step tge
       (State cs fb (Vptr sp' Int.zero) (restore_callee_save fe k) rs m')
    E0 (State cs fb (Vptr sp' Int.zero) k rs1 m')
  /\ agree_regs j (return_regs ls0 ls) rs1
  /\ agree_callee_save (return_regs ls0 ls) ls0
  /\ m1' |= minjection j m1 ** P.
Proof.
  intros until fb; intros SEP AGR AGL INJ FREE.
  (* Can free *)
  exploit free_parallel_rule.
    rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP.
    eexact FREE.
    eexact INJ.
    auto. rewrite Z.max_comm; reflexivity.
  intros (m1' & FREE' & SEP').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
    eexact SEP.
    instantiate (1 := rs). 
    red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  intros (rs' & LOAD_CS & CS & NCS).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  exploit (hasvalue_get_stack Tint). eapply sep_pick3; eexact SEP. intros LOAD_LINK.
  exploit (hasvalue_get_stack Tint). eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  rewrite unfold_transf_function; simpl.
  exists rs', m1'.
  split. assumption.
  split. assumption.
  split. assumption.
  split. eassumption.
  split. red; unfold return_regs; intros. 
    destruct (is_callee_save r) eqn:C.
    apply CS; auto.
    rewrite NCS by auto. apply AGR.
  split. red; unfold return_regs; intros.
    destruct l; auto. rewrite H; auto.
  assumption.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariants *)

(** This is the memory assertion that captures the contents of the stack frames
  mentioned in the call stacks. *)

Variable init_ls: locset.

Fixpoint stack_contents (j: meminj) (cs: list Linear.stackframe) (cs': list Mach.stackframe) : massert :=
  match cs, cs' with
  | nil, nil => pure True
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb (Vptr sp' _) ra c' :: cs' =>
      frame_contents f j sp' ls (parent_locset init_ls cs) (parent_sp init_sp' cs') (parent_ra init_ra cs')
      ** stack_contents j cs cs'
  | _, _ => pure False
  end.

Lemma stack_contents_invar_weak cs :
  forall j cs' , m_invar_weak (stack_contents j cs cs') = false.
Proof.
  induction cs; destruct cs' ; simpl; auto.
  + destruct a; auto.
  + destruct a; auto.
    destruct s; auto.
    destruct sp0; auto.
    match goal with
        [ |- context [m_invar_weak (?U ** ?V)] ] =>
        replace (m_invar_weak (U ** V))
                with (m_invar_weak U || m_invar_weak V)
          by reflexivity
    end.
    rewrite frame_contents_invar_weak.
    simpl.
    auto.
Qed.

(** [match_stacks] captures additional properties (not related to memory)
  of the Linear and Mach call stacks. *)

Variable init_sg: signature.

Variable init_sp: val.

Definition args_out_of_bounds sp l m :=
  forall b o,
    sp = Vptr b o ->
    forall of ty,
      List.In (Locations.S Outgoing of ty) l ->
      let ofs := Int.unsigned (Int.add o (Int.repr (fe_ofs_arg + 4 * of))) in
      forall o,
        ofs <= o < (ofs + size_chunk (chunk_of_type ty)) ->
        loc_out_of_bounds m b o.

Definition init_args_out_of_bounds sg :=
  args_out_of_bounds init_sp (regs_of_rpairs (loc_arguments sg)).

(** [CompCertX:test-compcert-protect-stack-arg] In whole-program settings, [init_sp = Vzero], so the following hypotheses are trivially true. 
    In non-whole-program settings, the following two hypotheses are provided by the caller's assembly semantics, which maintains the well-typedness of the assembly register set as an invariant. *)
Hypothesis init_sp_int: Val.has_type init_sp Tint.
Hypothesis init_ra_int: Val.has_type init_ra Tint.

(** [CompCertX:test-compcert-protect-stack-arg] The following lemma restores the whole-program setting, which assumes that the first callee has no stack-allocated arguments. *)
Lemma tailcall_possible_extcall_arg :
  forall sg,
    tailcall_possible sg ->
    forall j m',
    forall sl of ty,
      List.In (Locations.S sl of ty) (regs_of_rpairs (loc_arguments sg)) ->
      forall rs,
      exists v, extcall_arg rs m' init_sp (S sl of ty) v /\ Val.inject j (init_ls (S sl of ty)) v
.
Proof.
  unfold tailcall_possible. intros. exploit H; eauto. simpl. contradiction.
Qed.

Lemma tailcall_possible_out_of_bounds :
  forall sg,
    tailcall_possible sg ->
    forall m,
      init_args_out_of_bounds sg m.
Proof.
  intros sg H m.
  unfold init_args_out_of_bounds.
  intros b o H0 of ty H1 o0 H2.
  specialize (H _ H1).
  contradiction.
Qed.

Inductive match_stacks (j: meminj):
  list Linear.stackframe -> list stackframe -> signature -> signature -> Prop :=
| match_stacks_empty:
    forall sg
      (TP: tailcall_possible sg \/ sg = init_sg),
      match_stacks j nil nil sg sg
| match_stacks_cons:
    forall f sp ls c cs fb sp' ra c' cs' sg trf
      isg 
      (TAIL: is_tail c (Linear.fn_code f))
      (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
      (TRF: transf_function f = OK trf)
      (TRC: transl_code (make_env (function_bounds f)) c = c')
      (INJ: j sp = Some(sp', (fe_stack_data (make_env (function_bounds f)))))
      (INJ_UNIQUE: forall b delta, j b = Some (sp', delta) -> b = sp)
      (TY_RA: Val.has_type ra Tint)
      (AGL: agree_locs f ls (parent_locset init_ls cs))
      (ARGS: forall ofs ty,
          In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
          slot_within_bounds (function_bounds f) Outgoing ofs ty)
      (* (SP_NOT_INIT: forall b o, init_sp = Vptr b o -> b <> sp) *)
      (*   (SP'_NOT_GLOBAL: Ple (Genv.genv_next tge) sp') *)
      (STK: match_stacks j cs cs' (Linear.fn_sig f) isg),
      match_stacks j
                   (Linear.Stackframe f (Vptr sp Int.zero) ls c :: cs)
                   (Stackframe fb (Vptr sp' Int.zero) ra c' :: cs')
                   sg isg.

(** Invariance with respect to change of memory injection. *)

Lemma stack_contents_change_meminj:
  forall m j j', inject_incr j j' ->
  forall cs cs' P,
  m |= stack_contents j cs cs' ** P ->
  m |= stack_contents j' cs cs' ** P.
Proof.
Local Opaque sepconj.
  induction cs as [ | [] cs]; destruct cs' as [ | [] cs']; simpl; intros; auto.
  destruct sp0; auto.
  rewrite sep_assoc in H0 |- * .
  apply frame_contents_incr with (j := j); auto.
  rewrite sep_swap. apply IHcs. rewrite sep_swap. assumption.
Qed.

Lemma match_stacks_change_meminj:
  forall j j', inject_incr j j' ->
          (exists m m',
              inject_separated j j' m m' /\
              (forall b b' delta, j b = Some (b', delta) -> Mem.valid_block m' b')(*  /\ *)
              (* (forall b, Mem.valid_block m b -> Mem.valid_block m' b) *)) ->
  forall cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  match_stacks j' cs cs' sg isg.
Proof.
  induction 3; intros.
- constructor; auto.
- econstructor; eauto.
  destruct H0 as (m & m' & (H0 & VB)).
  intros.
  destruct (j b) eqn:?.
  + destruct p. exploit H. eauto. intros.
    assert (b0 = sp') by congruence. subst. eapply INJ_UNIQUE in Heqo. auto.
  + generalize (H0 _ _ _ Heqo H2).
    intros (A & B).
    apply VB in INJ. congruence. 
Qed.

(** Invariance with respect to change of signature. *)

Definition args_in_bounds sp l m :=
  exists m_, free_extcall_args sp m l = Some m_.

Definition init_args_in_bounds sg :=
  args_in_bounds init_sp' (regs_of_rpairs (loc_arguments sg)).

Lemma tailcall_possible_in_bounds:
  forall sg,
    tailcall_possible sg ->
    forall m,
      init_args_in_bounds sg m.
Proof.
  intros sg H m.
  unfold init_args_in_bounds, args_in_bounds.
  red in H.
  revert H.
  induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto.
  intros H.
  unfold free_extcall_arg.
  destruct a.
  {
    eapply IHl; eauto.
    intros l0 H1.
    eapply H; eauto.
  }
  destruct sl; try (eapply IHl; eauto; intros; eapply H; eauto).
  exfalso. specialize (H _ (or_introl _ (eq_refl _))).
  contradiction.
Qed.  

Lemma match_stacks_change_sig:
  forall sg1 j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  tailcall_possible sg1 ->
  match_stacks j cs cs' sg1
               match cs with
                   nil => sg1
                 | _ => isg
               end.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto. intros. elim (H0 _ H1).
Qed.

(** Typing properties of [match_stacks]. *)

Hypothesis init_sp'_int: Val.has_type init_sp' Tint.

Lemma match_stacks_type_sp:
  forall j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  Val.has_type (parent_sp init_sp' cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

Lemma match_stacks_type_retaddr:
  forall j cs cs' sg isg,
  match_stacks j cs cs' sg isg ->
  Val.has_type (parent_ra init_ra cs') Tint.
Proof.
  induction 1; simpl; auto.
Qed.

(** Validity of memory blocks *)

Lemma match_stacks_sp_valid:
  forall m,
    (forall b o,
       init_sp' = Vptr b o ->
       Mem.valid_block m b) ->
  forall
    j cs cs' sg isg,
    match_stacks j cs cs' sg isg ->
    m |= stack_contents j cs cs' ->
    forall b o,
      parent_sp init_sp' cs' = Vptr b o ->
      Mem.valid_block m b.
Proof.
  induction 2; eauto.
  simpl stack_contents.
  intros H1 b o H2.
  simpl in H2.
  inv H2.
  exploit frame_get_retaddr; eauto.
  unfold load_stack, Val.add, Mem.loadv.
  intros.
  eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies.
  + eapply Mem.load_valid_access; eauto.
  + constructor.
Qed.

Hypothesis init_sp'_not_global:
  forall b o,
    init_sp' = Vptr b o ->
    Ple (Genv.genv_next tge) b.

(* Lemma match_stacks_sp_not_global: *)
(*   forall *)
(*     j cs cs' sg isg, *)
(*     match_stacks j cs cs' sg isg -> *)
(*     forall b o, *)
(*       parent_sp init_sp' cs' = Vptr b o -> *)
(*       Ple (Genv.genv_next tge) b. *)
(* Proof. *)
(*   induction 1; simpl; eauto; intros. inv H0. congruence. *)
(* Qed. *)

(** * Syntactic properties of the translation *)

(** Preservation of code labels through the translation. *)

Section LABELS.

Remark find_label_save_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (save_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Remark find_label_restore_callee_save:
  forall lbl l ofs k,
  Mach.find_label lbl (restore_callee_save_rec l ofs k) = Mach.find_label lbl k.
Proof.
  induction l; simpl; auto.
Qed.

Lemma transl_code_eq:
  forall fe i c, transl_code fe (i :: c) = transl_instr fe i (transl_code fe c).
Proof.
  unfold transl_code; intros. rewrite list_fold_right_eq. auto.
Qed.

Lemma find_label_transl_code:
  forall fe lbl c,
  Mach.find_label lbl (transl_code fe c) =
    option_map (transl_code fe) (Linear.find_label lbl c).
Proof.
  induction c; simpl; intros.
- auto.
- rewrite transl_code_eq.
  destruct a; unfold transl_instr; auto.
  destruct s; simpl; auto.
  destruct s; simpl; auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
  simpl. destruct (peq lbl l). reflexivity. auto.
  unfold restore_callee_save. rewrite find_label_restore_callee_save. auto.
Qed.

Lemma transl_find_label:
  forall f tf lbl c,
  transf_function f = OK tf ->
  Linear.find_label lbl f.(Linear.fn_code) = Some c ->
  Mach.find_label lbl tf.(Mach.fn_code) =
    Some (transl_code (make_env (function_bounds f)) c).
Proof.
  intros. rewrite (unfold_transf_function _ _ H).  simpl.
  unfold transl_body. unfold save_callee_save. rewrite find_label_save_callee_save.
  rewrite find_label_transl_code. rewrite H0. reflexivity.
Qed.

End LABELS.

(** Code tail property for Linear executions. *)

Lemma find_label_tail:
  forall lbl c c',
  Linear.find_label lbl c = Some c' -> is_tail c' c.
Proof.
  induction c; simpl.
  intros; discriminate.
  intro c'. case (Linear.is_label lbl a); intros.
  injection H; intro; subst c'. auto with coqlib.
  auto with coqlib.
Qed.

(** Code tail property for translations *)

Lemma is_tail_save_callee_save:
  forall l ofs k,
  is_tail k (save_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_restore_callee_save:
  forall l ofs k,
  is_tail k (restore_callee_save_rec l ofs k).
Proof.
  induction l; intros; simpl. auto with coqlib.
  constructor; auto. 
Qed.

Lemma is_tail_transl_instr:
  forall fe i k,
  is_tail k (transl_instr fe i k).
Proof.
  intros. destruct i; unfold transl_instr; auto with coqlib.
  destruct s; auto with coqlib.
  destruct s; auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
  unfold restore_callee_save.  eapply is_tail_trans. 2: apply is_tail_restore_callee_save. auto with coqlib.
Qed.

Lemma is_tail_transl_code:
  forall fe c1 c2, is_tail c1 c2 -> is_tail (transl_code fe c1) (transl_code fe c2).
Proof.
  induction 1; simpl. auto with coqlib.
  rewrite transl_code_eq.
  eapply is_tail_trans. eauto. apply is_tail_transl_instr.
Qed.

Lemma is_tail_transf_function:
  forall f tf c,
  transf_function f = OK tf ->
  is_tail c (Linear.fn_code f) ->
  is_tail (transl_code (make_env (function_bounds f)) c) (fn_code tf).
Proof.
  intros. rewrite (unfold_transf_function _ _ H). simpl.
  unfold transl_body, save_callee_save. 
  eapply is_tail_trans. 2: apply is_tail_save_callee_save.
  apply is_tail_transl_code; auto.
Qed.

(** * Semantic preservation *)

(** Preservation / translation of global symbols and functions. *)

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_match TRANSF).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_match TRANSF).

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof. apply senv_preserved. Qed.

Lemma functions_translated:
  forall v f,
  Genv.find_funct ge v = Some f ->
  exists tf,
  Genv.find_funct tge v = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_transf_partial TRANSF).

Lemma function_ptr_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma sig_preserved:
  forall f tf, transf_fundef f = OK tf -> Mach.funsig tf = Linear.funsig f.
Proof.
  intros until tf; unfold transf_fundef, transf_partial_fundef.
  destruct f; intros; monadInv H.
  rewrite (unfold_transf_function _ _ EQ). auto.
  auto.
Qed.

Lemma find_function_translated:
  forall j ls rs m ros f,
  agree_regs j ls rs ->
  m |= globalenv_inject ge j ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG [bound [_ [?????]]] FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m0). rewrite EQ. intro INJ. inv INJ.
  rewrite DOMAIN in H2. inv H2. simpl. auto. eapply FUNCTIONS; eauto.
- destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  rewrite symbols_preserved. auto.
Qed.

(** Preservation of the arguments to an external call. *)

(** Special case: external arguments to initial function *)

(* Definition init_args_linear sg m := *)
(*   forall sl of ty, *)
(*     List.In (Locations.S sl of ty) (regs_of_rpairs (loc_arguments sg)) -> *)
(*     forall rs, *)
(*       extcall_arg rs m init_sp (S sl of ty) (init_ls (S sl of ty)). *)

Definition init_args_mach j sg m' :=
  forall sl of ty,
    List.In (Locations.S sl of ty) (regs_of_rpairs (loc_arguments sg)) ->
    forall rs,
    exists v,
      extcall_arg rs m' init_sp' (S sl of ty) v /\
      Val.inject j (init_ls (S sl of ty)) v.

(* Section INIT_EXTERNAL_ARGUMENTS. *)

(* Variables m m' : mem. *)
(* Variable j: meminj. *)
(* Hypothesis SEP: m' |= minjection j m. *)
(* Hypothesis init_sp_inj: Val.inject j init_sp init_sp' . *)
(* Variable sg: signature. *)
(* Hypothesis Hm: init_args_mach j sg m'. *)

(* Lemma init_args_linear_to_mach: *)
(*   init_args_mach j sg m' . *)
(* Proof. *)
(*   simpl in SEP. *)
(*   red. *)
(*   intros sl of ty H rs. *)
(*   apply Hm in H. *)
(*   specialize (H rs). *)
(*   inv H. *)
(*   unfold load_stack in H4. *)
(*   exploit Mem.loadv_inject; eauto. *)
(*   { *)
(*     eapply Val.add_inject; eauto. *)
(*   } *)
(*   destruct 1 as (v2 & Hv2 & INJ). *)
(*   esplit. *)
(*   split; eauto. *)
(*   constructor. *)
(*   assumption. *)
(* Qed. *)

(* End INIT_EXTERNAL_ARGUMENTS. *)

(** General case *)

Section EXTERNAL_ARGUMENTS.

Variable j: meminj.
Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Variable isg: signature.
Hypothesis MS: match_stacks j cs cs' sg isg.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs j ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset init_ls cs).
Variable m': mem.
Hypothesis SEP: m' |= stack_contents j cs cs'.

Hypothesis init_args: init_args_mach j isg m' .

Lemma transl_external_argument:
  forall l,
  In l (regs_of_rpairs (loc_arguments sg)) ->
  exists v, extcall_arg rs m' (parent_sp init_sp' cs') l v /\ Val.inject j (ls l) v.
Proof.
  intros.
  assert (loc_argument_acceptable l) by (apply loc_arguments_acceptable_2 with sg; auto).
  destruct l; red in H0.
- exists (rs r); split. constructor. auto.
- destruct sl; try contradiction.
  inv MS.
  + destruct TP as [TP|TP].
    * elim (TP _ H).
    * subst isg. simpl in *.
      red in AGCS. rewrite AGCS; auto.
  + simpl in SEP. simpl.
    assert (slot_valid f Outgoing pos ty = true).
    { destruct H0. unfold slot_valid, proj_sumbool. 
      rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. }
    assert (slot_within_bounds (function_bounds f) Outgoing pos ty) by eauto.
    exploit frame_get_outgoing; eauto. intros (v & A & B).
    exists v; split.
    constructor. exact A. red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_argument_2:
  forall p,
  In p (loc_arguments sg) ->
  exists v, extcall_arg_pair rs m' (parent_sp init_sp' cs') p v /\ Val.inject j (Locmap.getpair p ls) v.
Proof.
  intros. destruct p as [l | l1 l2].
- destruct (transl_external_argument l) as (v & A & B). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists v; split; auto. constructor; auto. 
- destruct (transl_external_argument l1) as (v1 & A1 & B1). eapply in_regs_of_rpairs; eauto; simpl; auto.
  destruct (transl_external_argument l2) as (v2 & A2 & B2). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists (Val.longofwords v1 v2); split. 
  constructor; auto.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
      list_forall2 (extcall_arg_pair rs m' (parent_sp init_sp' cs')) locs vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) locs) vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument_2; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
      extcall_arguments rs m' (parent_sp init_sp' cs') sg vl
   /\ Val.inject_list j (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) vl.
Proof.
  unfold extcall_arguments.
  apply transl_external_arguments_rec.
  auto with coqlib.
Qed.

End EXTERNAL_ARGUMENTS.

(** Preservation of the arguments to a builtin. *)

Section BUILTIN_ARGUMENTS.

Variable f: Linear.function.
Let b := function_bounds f.
Let fe := make_env b.
Variable tf: Mach.function.
Hypothesis TRANSF_F: transf_function f = OK tf.
Variable j: meminj.
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset.
Variables sp sp': block.
Variables parent retaddr: val.
Hypothesis INJ: j sp = Some(sp', fe.(fe_stack_data)).
Hypothesis AGR: agree_regs j ls rs.
Hypothesis SEP: m' |= frame_contents f j sp' ls ls0 parent retaddr ** minjection j m ** globalenv_inject ge j.

Lemma transl_builtin_arg_correct:
  forall a v,
  eval_builtin_arg ge ls (Vptr sp Int.zero) m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg ge rs (Vptr sp' Int.zero) m' (transl_builtin_arg fe a) v'
  /\ Val.inject j v v'.
Proof.
  assert (SYMB: forall id ofs, Val.inject j (Senv.symbol_address ge id ofs) (Senv.symbol_address ge id ofs)).
  { assert (G: meminj_preserves_globals ge j).
    { eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eexact SEP. }
    intros; unfold Senv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol ge id) eqn:FS; auto.
    destruct G. econstructor. eauto. rewrite Int.add_zero; auto. }
Local Opaque fe.
  induction 1; simpl; intros VALID BOUNDS.
- assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + exists (rs r); auto with barg.
  + exploit frame_get_local; eauto. intros (v & A & B). 
    exists v; split; auto. constructor; auto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- set (ofs' := Int.add ofs (Int.repr (fe_stack_data fe))).
  apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  instantiate (1 := Val.add (Vptr sp' Int.zero) (Vint ofs')). 
  simpl. rewrite ! Int.add_zero_l. econstructor; eauto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto. 
- econstructor; split; eauto with barg.
  unfold Val.add. rewrite ! Int.add_zero_l. econstructor; eauto.
- apply sep_proj2 in SEP. apply sep_proj1 in SEP. exploit loadv_parallel_rule; eauto.
  intros (v' & A & B). exists v'; auto with barg.
- econstructor; split; eauto with barg. 
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_inject; auto.
Qed.

Lemma transl_builtin_args_correct:
  forall al vl,
  eval_builtin_args ge ls (Vptr sp Int.zero) m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args ge rs (Vptr sp' Int.zero) m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.inject_list j vl vl'.
Proof.
  induction 1; simpl; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End BUILTIN_ARGUMENTS.

(** [CompCertX:test-compcert-protect-stack-arg] We have to prove that
the memory injection introduced by the compilation pass is independent
of the initial memory i.e. it does not inject new blocks into blocks
already existing in the initial memory. This is stronger than
[meminj_preserves_globals], which only preserves blocks associated to
the global environment. *)

Section WITHMEMINIT.
Variable init_m: mem.

(** The proof of semantic preservation relies on simulation diagrams
  of the following form:
<<
           st1 --------------- st2
            |                   |
           t|                  +|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  Matching between source and target states is defined by [match_states]
  below.  It implies:
- Satisfaction of the separation logic assertions that describe the contents 
  of memory.  This is a separating conjunction of facts about:
-- the current stack frame
-- the frames in the call stack
-- the injection from the Linear memory state into the Mach memory state
-- the preservation of the global environment.
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs].
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Variable init_j: meminj.

Variable init_m' : mem.
Hypothesis genv_next_le_m_init_next': Ple (Genv.genv_next tge) (Mem.nextblock init_m').

Require Linear2.

Definition state_mem (s: Linear.state) :=
  match s with
  | Linear.State stack f sp c rs m => m
  | Linear.Callstate stack f rs m => m
  | Linear.Returnstate stack rs m => m
  end.

Definition has_at_most_one_antecedent (j: meminj) P :=
  forall b' o' (EQ: P = Vptr b' o')
    b1 b2 delta1 delta2
    (J1: j b1 = Some (b', delta1))
    (J2: j b2 = Some (b', delta2)),
    b1 = b2.

Definition block_prop P v :=
  match v with
    Vptr b o => P b
  | _ => True
  end.

Lemma has_at_most_one_antecedent_incr:
  forall j j' (INCR: inject_incr j j')
    m m' (SEP: inject_separated j j' m m')
    v (HAMOA: has_at_most_one_antecedent j v)
    (BP: block_prop (Mem.valid_block m') v),
    has_at_most_one_antecedent j' v.
Proof.
  red; intros. subst. red in HAMOA.
  specialize (HAMOA _ _ eq_refl).
  destruct (j b1) eqn:?. destruct p.
  destruct (j b2) eqn:?. destruct p.
  erewrite INCR in J1; eauto.
  erewrite INCR in J2; eauto.
  inv J1; inv J2.
  eapply HAMOA; eauto.
  generalize (SEP _ _ _ Heqo0 J2). intros (A & B); elim B. apply BP.
  generalize (SEP _ _ _ Heqo J1). intros (A & B); elim B. apply BP.
Qed.

Inductive match_states: Linear2.state -> Mach.state -> Prop :=
| match_states_intro:
    forall sg_,
    forall cs f sp c ls m cs' fb sp' rs m' j tf 
        (STACKS: match_stacks j cs cs' f.(Linear.fn_sig) sg_)
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_locs f ls (parent_locset init_ls cs))
        (INJSP: j sp = Some(sp', fe_stack_data (make_env (function_bounds f))))
        (INJUNIQUE: forall b delta, j b = Some (sp', delta) -> b = sp)
        (INJ_INIT_SP: Val.inject j init_sp init_sp' )
        (HAMOA: has_at_most_one_antecedent j init_sp')
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp')
        (* (INJ_INCR: inject_incr init_j j) *)
        (* (INIT_M_VALID: forall b, Mem.valid_block init_m b -> Mem.valid_block m b) *)
        (* (INIT_M'_VALID: forall b, Mem.valid_block init_m' b -> Mem.valid_block m' b) *)
        (* (INJ_SEP: inject_separated init_j j init_m init_m' ) *)
        (INIT_ARGS: init_args_mach j sg_ m')
        (TAIL: is_tail c (Linear.fn_code f))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.State cs f (Vptr sp Int.zero) c ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')
        (SP_NOT_INIT: forall b o, init_sp' = Vptr b o -> b <> sp')
        (* (SP_VALID: forall b o, init_sp = Vptr b o -> Mem.valid_block m b) *)
        (* (SP'_NOT_GLOBAL: Ple (Genv.genv_next tge) sp') *)

        (SEP: m' |= frame_contents f j sp' ls (parent_locset init_ls cs) (parent_sp init_sp' cs') (parent_ra init_ra cs')
                 ** stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states s2_ 
                   (Mach.State cs' fb (Vptr sp' Int.zero) (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:
      forall sg_,
      forall cs f ls m cs' fb rs m' j tf 
        (STACKS: match_stacks j cs cs' (Linear.funsig f) sg_)
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Callstate cs f ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')

        (INJ_INIT_SP: Val.inject j init_sp init_sp' )
        (HAMOA: has_at_most_one_antecedent j init_sp')
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp')
        (* (INJ_INCR: inject_incr init_j j) *)
        (* (INIT_M_VALID: forall b, Mem.valid_block init_m b -> Mem.valid_block m b) *)
        (* (INIT_M'_VALID: forall b, Mem.valid_block init_m' b -> Mem.valid_block m' b) *)
        (* (INJ_SEP: inject_separated init_j j init_m init_m' ) *)
        (INIT_ARGS: init_args_mach j sg_ m')
        (* (SP_VALID: forall b o, init_sp = Vptr b o -> Mem.valid_block m b) *)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states s2_ (Mach.Callstate cs' fb rs m')
  | match_states_return:
      forall sg_,
      forall cs ls m cs' rs m' j sg 
        (STACKS: match_stacks j cs cs' sg sg_)
        (AGREGS: agree_regs j ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Returnstate cs ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (Hsome_init_args: init_args_in_bounds sg_ m')
        (INJ_INIT_SP: Val.inject j init_sp init_sp' )
        (HAMOA: has_at_most_one_antecedent j init_sp')
        (ISP'VALID: block_prop (Mem.valid_block m') init_sp')
        (* (INJ_INCR: inject_incr init_j j) *)
        (* (INIT_M_VALID: forall b, Mem.valid_block init_m b -> Mem.valid_block m b) *)
        (* (INIT_M'_VALID: forall b, Mem.valid_block init_m' b -> Mem.valid_block m' b) *)
        (* (INJ_SEP: inject_separated init_j j init_m init_m' ) *)
        (INIT_ARGS: init_args_mach j sg_ m')
        (* (SP_VALID: forall b o, init_sp = Vptr b o -> Mem.valid_block m b) *)
        (SEP: m' |= stack_contents j cs cs'
                 ** minjection j m
                 ** globalenv_inject ge j),
      match_states s2_
                  (Mach.Returnstate cs' rs m').

(** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
Local Add Relation massert massert_imp
  reflexivity proved by massert_imp_refl
  transitivity proved by massert_imp_trans
as massert_imp_prel2.

Local Add Relation massert massert_eqv
  reflexivity proved by massert_eqv_refl
  symmetry proved by massert_eqv_sym
  transitivity proved by massert_eqv_trans
as massert_eqv_prel2.

Hypothesis init_sp_not_Vundef: init_sp <> Vundef.

Lemma Ple_Plt:
  forall a b,
    (forall c, Plt c a -> Plt c b) ->
    Ple a b.
Proof.
  intros a b H.
  destruct (peq a xH).
  + subst a. xomega.
  + exploit Ppred_Plt; eauto.
    intros H0.
    specialize (H _ H0).
    exploit Pos.succ_pred; eauto.
    intro K.
    xomega.
Qed.
Lemma perm_free m b lo hi m':
  Mem.free m b lo hi = Some m' ->
  forall b' o' k p,
    Mem.perm m' b' o' k p <->
    (
      (~ (b' = b /\ lo <= o' < hi)) /\
      Mem.perm m b' o' k p
    ).
Proof.
  intros H b' o' k p.
  assert (~ (b' = b /\ lo <= o' < hi) -> Mem.perm m b' o' k p -> Mem.perm m' b' o' k p) as H0.
  {
    intro H0.
    eapply Mem.perm_free_1; eauto.
    destruct (peq b' b); try tauto.
    subst.
    intuition xomega.
  }
  assert (b' = b /\ lo <= o' < hi -> ~ Mem.perm m' b' o' k p) as H1.
  {
    destruct 1; subst; eapply Mem.perm_free_2; eauto.
  }
  generalize (Mem.perm_free_3 _ _ _ _ _ H b' o' k p).
  tauto.
Qed.

Lemma init_args_in_bounds_perm sg m m':
  (forall b o_, init_sp' = Vptr b o_ -> forall o k p, Mem.perm m b o k p -> Mem.perm m' b o k p) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  unfold init_args_in_bounds, args_in_bounds.
  generalize init_sp'.
  intros sp H H0.
  destruct H0 as (m_ & H0).
  revert m m' H m_ H0.
  induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto.
  intros m m' H m_.
  unfold free_extcall_arg.
  destruct a; eauto.
  destruct sl; eauto.
  destruct sp; try discriminate.
  set (o := Int.unsigned (Int.add i (Int.repr (fe_ofs_arg + 4 * pos)))).
  destruct (
      Mem.free m b o (o + size_chunk (chunk_of_type ty))
    ) eqn:FREE; try discriminate.
  intros H0.
  generalize FREE. intro FREE1.
  apply Mem.free_range_perm in FREE1.
  unfold Mem.range_perm in FREE1.
  generalize (fun ofs J => H _ _ (eq_refl _) _ _ _ (FREE1 ofs J)).
  clear FREE1. intro FREE2.
  apply Mem.range_perm_free in FREE2.
  destruct FREE2 as (m2 & FREE2).
  rewrite FREE2.
  eapply IHl; try eassumption.
  inversion 1; subst b0 o_.
  intros o0 k p.
  erewrite perm_free by eassumption.
  intros H2.
  erewrite perm_free by eassumption.
  specialize (H _ _ (eq_refl _) o0 k p).
  tauto.
Qed.

Lemma init_args_in_bounds_store sg chunk m b o v m':
  Mem.store chunk m b o v = Some m' ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intro K.
  apply init_args_in_bounds_perm.
  intros b0 o_ H o0 k p.
  eauto using Mem.perm_store_1.
Qed.

Lemma init_args_in_bounds_storev sg chunk m bo v m':
  Mem.storev chunk m bo v = Some m' ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  destruct bo; try discriminate.
  apply init_args_in_bounds_store.
Qed.

Lemma init_args_out_of_bounds_store sg chunk m b o v m':
  Mem.store chunk m b o v = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m'.
Proof.
  unfold init_args_out_of_bounds, args_out_of_bounds.
  intros H H0 b0 o0 H1 of ty H2 o1 H3.
  intro ABSURD.
  eapply Mem.perm_store_2 in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Lemma init_args_out_of_bounds_storev sg chunk m addr v m':
  Mem.storev chunk m addr v = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m'.
Proof.
  destruct addr; try discriminate.
  apply init_args_out_of_bounds_store.
Qed.

Lemma init_args_out_of_bounds_free sg m b lo hi m' :
  Mem.free m b lo hi = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m' .
Proof.
  unfold init_args_out_of_bounds, args_out_of_bounds.
  intros H H0 b0 o H1 of ty H2 o0 H3.
  intro ABSURD.
  eapply Mem.perm_free_3 in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Lemma init_args_in_bounds_free m b lo hi m' sg:
  Mem.free m b lo hi = Some m' ->
  (forall b' o', init_sp' = Vptr b' o' -> b' <> b) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intros H H0.
  apply init_args_in_bounds_perm.
  intros b0 o_ H1 o k p.
  specialize (H0 _ _ H1).
  clear H1.
  intros H1.
  erewrite perm_free by eassumption.
  tauto.
Qed.

Lemma init_args_in_bounds_alloc m lo hi b m' sg:
  Mem.alloc m lo hi = (m', b) ->
  init_args_in_bounds sg m ->
  init_args_in_bounds sg m'.
Proof.
  intros H.
  apply init_args_in_bounds_perm.
  intros b0 o_ H0 o k p.
  eapply Mem.perm_alloc_1; eauto.
Qed.


Lemma eval_addressing_lessdef_strong:
  forall sp1 sp2 addr vl1 vl2 v1,
    Val.lessdef_list vl1 vl2 ->
    Val.lessdef sp1 sp2 ->
    eval_addressing ge sp1 addr vl1 = Some v1 ->
    exists v2, eval_addressing ge sp2 addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. rewrite val_inject_list_lessdef in H.
  assert (exists v2 : val,
             eval_addressing ge sp2 addr vl2 = Some v2
             /\ Val.inject (fun b => Some(b, 0)) v1 v2).
  eapply eval_addressing_inj with (sp1 := sp1).
  intros. rewrite <- val_inject_lessdef; auto.
  rewrite <- val_inject_lessdef; auto.
  eauto. auto. 
  destruct H2 as [v2 [A B]]. exists v2; split; auto. rewrite val_inject_lessdef; auto. 
Qed.

Lemma reglist_lessdef rs1 rs2
      (LESSDEF: forall r, Val.lessdef (rs1 r) (rs2 r))
      l:
  Val.lessdef_list (reglist rs1 l) (reglist rs2 l).
Proof.
  induction l; simpl; auto.
Qed.



Ltac constr_match_states :=
  econstructor; match goal with
                  |- Linear2.state_lower _ = _ =>
                  symmetry; eassumption
                | |- _ => idtac
                end.

Lemma init_args_out_of_bounds_external_call sg_ ef args m_ t vl m'_ :
  (forall b o, init_sp = Vptr b o -> Mem.valid_block m_ b) ->
  external_call ef ge args m_ t vl m'_ ->
  forall j m m' sg ll lm ,
    match_stacks j ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.inject j m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds, args_out_of_bounds.
  intros VB H j m m' sg ll lm H0 H1 H2 H3 b o H4 of ty H5 o0 H6.
  intro ABSURD.
  eapply H3; eauto.
  eapply external_call_max_perm; eauto. 
Qed.

Lemma block_prop_impl (P Q: block -> Prop) v:
  (forall b, P b -> Q b) ->
  block_prop P v -> block_prop Q v.
Proof.
  destruct v; auto. simpl. intuition.
Qed.

(* Lemma init_args_in_bounds_external_call sg_ ef args m_ t vl m'1  *)
(*       (EC: external_call ef ge args m_ t vl m'1) *)
(*       j m m' *)
(*       (GI: m' |= globalenv_inject ge j) *)
(*       (INJUNIQ: forall b1 o, init_sp = Vptr b1 o -> *)
(*                         forall b delta, j b1 = Some (b, delta) -> *)
(*                                    forall b2 delta2, j b2 = Some (b, delta2) -> *)
(*                                                 b1 = b2) *)
(*       (EXT: Mem.extends m_ m) *)
(*       (IAL: init_args_mach j sg_ m') *)
(*       (MINJ: Mem.inject j m m') *)
(*       (VINJ: Val.inject j init_sp init_sp') *)
(*       (IAOOB: init_args_out_of_bounds sg_ m) *)
(*       ll lm sg *)
(*       (MS: match_stacks j ll lm sg sg_) *)
(*       args' *)
(*       (INJ_ARGS: Val.inject_list j args args') *)
(*       vl' m'2 *)
(*       (EC2: external_call ef ge args' m' t vl' m'2) *)
(*       (IAIB: init_args_in_bounds sg_ m'): *)
(*   init_args_in_bounds sg_ m'2. *)
(* Proof. *)
(*   destruct IAIB as (m_' & IAIB). *)
(*   generalize (Mem.extends_inject_compose _ _ _ _ EXT MINJ). *)
(*   intros MINJ'. *)
(*   revert EC2. *)
(*   exploit external_call_mem_inject_gen ; eauto. eapply meminj_preserves_globals_symbols_inject'. *)
(*   eapply globalenv_inject_preserves_globals. eauto. *)
(*   destruct 1 as (_ & res'_ & m'2_ & EC2 & _ & _ & _ & UNCHANGED & _ & _). *)
(*   intros EC2'. *)
(*   exploit external_call_determ. *)
(*   eexact EC2. *)
(*   eexact EC2'. *)
(*   destruct 1 as (_ & INJ). *)
(*   specialize (INJ (eq_refl _)). *)
(*   destruct INJ; subst. *)

(*   assert (forall b o (EQsp': init_sp = Vptr b o) *)
(*             of ty (IN: In (S Outgoing of ty) (regs_of_rpairs (loc_arguments sg_))), *)
(*             let ofs := Int.unsigned (Int.add o (Int.repr (fe_ofs_arg + 4 * of))) in *)
(*             forall o' (RNG: ofs <= o' < ofs + size_chunk (chunk_of_type ty)) *)
(*               k p (PERM: Mem.perm m b o' k p), *)
(*               Mem.perm m' b o' k p) *)
(*     as PERM. *)
(*   { *)
(*     intros b o EQsp' of ty IN ofs o' RNG k p PERM. *)
(*     (* intros b o H8 of ty H9 ofs o' H10 k p H11. *) *)
(*     rewrite EQsp' in VINJ; inv VINJ. *)
(*     eapply Mem.perm_unchanged_on; eauto. *)
(*     { *)
(*       unfold init_args_out_of_bounds in IAOOB. *)
(*       unfold args_out_of_bounds in IAOOB. *)
(*       unfold loc_out_of_reach. *)
(*       intros b0 delta0 INJb0 PERM0. *)
(*       specialize (INJUNIQ _ _ eq_refl _ _ H1 _ _ INJb0). subst. *)
(*       eapply IAOOB. eauto. *)
(*       eauto. *)
(*       2: eapply Mem.perm_inject; eauto. *)
(*       revert RNG. revert EQsp'. *)
(*       rewrite INJb0 in H2; inv H2. unfold ofs in *. *)
(*       clear; intros. omega.  *)

(*       (* rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta)). *) *)
(*       (* rewrite <- Int.add_assoc. *) *)
(*       (* erewrite Mem.address_inject. clear; intros. omega. *) *)
(*       (* 3: apply INJb0. apply MINJ. *) *)

(*       (* red in IAL. *) *)
(*       (* specialize ( IAL _ _ _ IN (Regmap.init Vundef)). inv IAL. *) *)
(*       (* unfold load_stack in H3. *) *)
(*       (* Opaque Z.mul. *) *)
(*       (* simpl in H3. *) *)
(*       (* apply Mem.load_valid_access in H3. *) *)
(*       (* destruct H3. apply H. destruct ty; simpl; omega. *) *)
(*     } *)
(*     congruence. *)
(*   } *)

(*   revert PERM IAIB. *)
(*   revert external_calls_prf. *)
(*   generalize perm_free. *)
(*   clear. *)
(*   unfold init_args_in_bounds. *)
(*   generalize init_sp'. intro sp. *)
(*   revert m' m'2. *)
(*   generalize (regs_of_rpairs (loc_arguments sg_)). *)
(*   clear sg_. *)
(*   intro l. *)
(*   unfold args_in_bounds. *)
(*   intros m' m'_  PF compiler_config PERM IAIB. *)
(*   rename m_' into m_. *)
(*   revert m' m'_ PERM m_ IAIB. *)
(*   revert l. *)
(*   induction l. *)
(*   { *)
(*     intros. *)
(*     simpl. *)
(*     eauto. *)
(*   } *)
(*   intros m' m'_ PERM m_. *)
(*   simpl. *)
(*   unfold free_extcall_arg. *)
(*   simpl In in PERM. *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   destruct sp; try discriminate. *)
(*   set (ofs := Int.unsigned (Int.add i (Int.repr (fe_ofs_arg + 4 * pos)))). *)
(*   destruct (Mem.free m' b ofs (ofs + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate. *)
(*   generalize (Mem.free_range_perm _ _ _ _ _ FREE). *)
(*   unfold Mem.range_perm. *)
(*   intro RANGE. *)
(*   generalize (fun o K => PERM _ _ (eq_refl _) _ _ (or_introl _ (eq_refl _)) o K _ _ (RANGE _ K)). *)
(*   clear RANGE. intro RANGE. *)
(*   apply Mem.range_perm_free in RANGE. *)
(*   fold ofs in RANGE. *)
(*   destruct RANGE as (m2 & Hm2). *)
(*   rewrite Hm2. *)
(*   eapply IHl; eauto. *)
(*   intros b0 o H of ty0 H0 o' H1 k p H2. *)
(*   inversion H; clear H; subst b0 o. *)
(*   erewrite PF by eassumption. *)
(*   erewrite PF in H2 by eassumption. *)
(*   destruct H2. *)
(*   split; eauto. *)
(* Qed. *)


Ltac trim H :=
  match type of H with
    ?A -> ?B =>
    let x := fresh in
    assert ( x : A ); [ clear H
                      | specialize (H x) ]
  end.


(* Lemma free_extcall_args_inject_right: *)
(*   forall j f sp ls c cs fb sp' ra c' cs' sg sg_ *)
(*     (MS: match_stacks j (Linear.Stackframe f (Vptr sp Int.zero) ls c :: cs) *)
(*                       (Stackframe fb (Vptr sp' Int.zero) ra c' :: cs') sg sg_) *)
(*     (* init_args_out_of_bounds sg_ m_ -> *) *)
(*     m_ m m' *)
(*     (EXT: Mem.extends m_ m) *)
(*     (MINJ: Mem.inject j m m') *)
(*     m'_ *)
(*     (FEA: free_extcall_args (Vptr sp' Int.zero) m' (regs_of_rpairs (loc_arguments sg)) = Some m'_) *)
(*     (* (VINJ: Val.inject j init_sp init_sp') *) *)
(*     (* (HAMOA: has_at_most_one_antecedent j init_sp') *) *)
(*     (* (IAL: init_args_linear sg_ m_) *) *)
(*     (* (BND: 4 * size_arguments sg <= Int.max_unsigned)   *) *)
(*     ros (INCALL: In (Lcall sg ros) (Linear.fn_code f)) *)

(*     (BOUND_: forall ofs p, Mem.perm m_ sp ofs Max p -> *)
(*                       0 <= ofs < Linear.fn_stacksize f), *)
(*   Mem.inject j m_ m'_. *)
(* Proof. *)
(*   intros j f sp ls c cs fb sp' ra c' cs' sg sg_ MS m_ m m' EXT MINJ m'_ FEA ros INCALL BOUND_. *)
(*   generalize (Mem.extends_inject_compose _ _ _ _ EXT MINJ). *)
(*   revert FEA. *)
(*   cut (forall l2 l1, regs_of_rpairs (loc_arguments sg) = l1 ++ l2 -> free_extcall_args (Vptr sp' Int.zero) m' l2 = Some m'_ -> Mem.inject j m_ m' -> Mem.inject j m_ m'_). *)
(*   { *)
(*     clear. *)
(*     intros H1 H3 H2. *)
(*     eapply H1 with (l1 := nil); eauto. simpl. eauto. *)
(*   } *)
(*   inversion MS. subst. clear MS.  *)
(*   (* internal arguments *) *)
(*   clear STK. *)
(*   rename INJ_UNIQUE into UNIQ. *)
  
(*   (* generalize (agree_bounds _ _ _ _ _ _ _ _ _ _  FRM). intro BOUND_. *) *)
(*   (* assert (forall ofs p, *) *)
(*   (*           Mem.perm m_ sp ofs Max p -> *) *)
(*   (*           0 <= ofs < Linear.fn_stacksize f) as BOUND. *) *)
(*   (* { *) *)
(*   (*   intros ofs p H3. *) *)
(*   (*   eapply BOUND_. *) *)
(*   (*   eapply Mem.perm_extends; eauto. *) *)
(*   (* } *) *)
(*   (* clear BOUND_. *) *)

(*   intro l2. clear MINJ. *)
(*   revert m' m'_. simpl. *)
(*   induction l2. *)
(*   { *)
(*     simpl. *)
(*     congruence. *)
(*   } *)
(*   intros m' m'_ l1 H H0 H1. *)
(*   simpl in H0. *)
(*   unfold free_extcall_arg in H0. *)
(*   assert (regs_of_rpairs (loc_arguments sg) = (l1 ++ a :: nil) ++ l2) as EQ. *)
(*   { *)
(*     rewrite app_ass; assumption. *)
(*   } *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   rewrite Int.add_commut in H0. *)
(*   rewrite Int.add_zero in H0. *)
(*   assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN. *)
(*   { *)
(*     rewrite H. *)
(*     apply in_or_app. *)
(*     simpl; auto. *)
(*   } *)
(*   specialize (ARGS _ _ IN). *)
(*   assert (slot_valid f Outgoing pos ty = true) as VALID. *)
(*   { *)
(*     (* duplicate proof from transl_external_argument *) *)
(*     exploit loc_arguments_acceptable_2; eauto. intros [A B].  *)
(*     unfold slot_valid. unfold proj_sumbool. rewrite zle_true. *)
(*     destruct (Zdivide_dec (typealign ty) pos (typealign_pos ty)); auto. omega. *)
(*   } *)


(*   (* exploit index_arg_valid; eauto. *) *)
(*   (* intro IVALID. *) *)
(*   (* exploit offset_of_index_no_overflow; eauto. *) *)
(*   (* unfold offset_of_index. *) *)
(*   (* intro NO_OVERFLOW. *) *)
(*   (* rewrite NO_OVERFLOW in H0. *) *)

(*   rewrite Int.unsigned_repr in H0. *)
(*   set (o := fe_ofs_arg + 4 * pos). *)
(*   fold o in H0. *)
(*   destruct (Mem.free m' sp' o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate. *)
(*   exploit Mem.free_right_inject; eauto. *)
(*   intros b1 delta ofs k p H2 H3 H4. *)
(*   specialize (UNIQ _ _ H2). *)
(*   destruct UNIQ. *)
(*   subst. *)
(*   apply Mem.perm_max in H3. Opaque fe_stack_data. *)
(*   rewrite INJ in H2; inv H2. *)
(*   generalize (BOUND_ _ _ H3). *)

(*   cut (o + size_chunk (chunk_of_type ty) <= fe_stack_data (make_env (function_bounds f))). omega. *)
(*   unfold o in *; simpl in *. *)
  
(*   generalize (loc_arguments_bounded _ _ _ IN). *)

(*   intros. *)
(*   exploit frame_env_separated'. *)
(*   intros (_ & _ & _ & _ & _ & _ & G). *)
(*   etransitivity. 2: apply G. *)
(*   transitivity (4 * size_arguments sg). *)
(*   rewrite size_type_chunk, typesize_typesize. omega. *)
(*   apply Z.mul_le_mono_nonneg_l. *)
(*   omega. *)
(*   eapply size_arguments_bound. *)
(*   eauto. *)

  

(*   simpl. *)
(*   unfold slot_within_bounds in ARGS. *)
(*   split. unfold slot_valid in VALID. destruct (zle 0 pos). omega. simpl in VALID. congruence. *)

(*   transitivity (4 * pos + 4 * typesize ty). *)
(*   generalize (typesize_pos ty). omega. *)
(*   transitivity (4 * size_arguments sg). *)
(*   generalize (loc_arguments_bounded _ _ _ IN). *)
(*   omega. *)
(*   auto. *)

(*   intros. *)
(*   exploit frame_env_separated'. *)
(*   intros (A & B & C & D & E & F & G). *)
(*   exploit frame_env_range. intros ( J & I ). *)
(*   etransitivity. 2: eapply size_no_overflow; eauto. *)
(*   etransitivity. 2: apply I. *)
(*   etransitivity. *)
(*   apply Z.mul_le_mono_nonneg_l. *)
(*   omega. *)
(*   eapply size_arguments_bound. *)
(*   eauto. *)
(*   etransitivity. apply G. *)
(*   generalize (bound_stack_data_pos (function_bounds f)). *)
(*   omega. *)
(* Qed. *)

(* Definition args_linear sg m sp ls := *)
(*   forall sl ofs ty (IN: In (S sl ofs ty) (regs_of_rpairs (loc_arguments sg))) *)
(*     rs, extcall_arg rs m sp (S sl ofs ty) (ls (S sl ofs ty)). *)

Definition linear_parent_sp isp ll :=
  match ll with
    nil => isp
  | Linear.Stackframe f isp ls c :: cs => isp
  end.

Definition linear_parent_ls ils ll :=
  match ll with
    nil => ils
  | Linear.Stackframe f isp ls c :: cs => ls
  end.

Definition args_mach j sg ls sp' m' := 
  forall sl pos ty
    (IN : In (S sl pos ty) (regs_of_rpairs (loc_arguments sg)))
    rs,
  exists v : val,
    extcall_arg rs m' sp' (S sl pos ty) v /\
    Val.inject j (ls (S sl pos ty)) v.
 

(* Lemma free_extcall_args_inject_right' j m m' sg_ ll lm sg m'_ : *)
(*   match_stacks j ll lm sg sg_  -> *)
(*   (* args_out_of_bounds (parent_sp init_sp' lm) (regs_of_rpairs (loc_arguments sg)) m'_ -> *) *)
(*   args_mach j sg (parent_locset init_ls ll) (parent_sp init_sp' lm) m' ->  *)
(*   (* Mem.extends m_ m -> *) *)
(*   Mem.inject j m m' -> *)
(*   free_extcall_args (parent_sp init_sp' lm) m' (regs_of_rpairs (loc_arguments sg)) = Some m'_ -> *)
(*   forall (VINJ: Val.inject j init_sp init_sp') *)
(*     (HAMOA: has_at_most_one_antecedent j (parent_sp init_sp' lm)) *)
(*     (* (IAL: init_args_linear sg_ m_) *), *)
(*   Mem.inject j m m'_. *)
(* Proof. *)
(*   intros MS AL MINJ FEA VINJ HAMOA. *)
(*   cut (forall pos ty (IN: In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) *)
(*          sp' o (EQsp: parent_sp init_sp' lm = Vptr sp' o) *)
(*          sp delta (JSP: j sp = Some (sp', delta)) *)
(*          ofs *)
(*          (RNG: Int.unsigned (Int.add o (Int.repr (4 * pos))) <= ofs *)
(*                < Int.unsigned (Int.add o (Int.repr (4 * pos))) + size_chunk (chunk_of_type ty)) *)
(*          k p (PERM: Mem.perm m sp (ofs-delta) k p), *)
(*           False). *)
(*   { *)
(*     clear AL. intros PERMS. revert m m' m'_ PERMS FEA MINJ. *)
(*     generalize (regs_of_rpairs (loc_arguments sg)). *)
(*     induction l; simpl; intros; eauto. *)
(*     - inv FEA; auto. *)
(*     - destruct (free_extcall_arg (parent_sp init_sp' lm) m' a) eqn:?; try discriminate. *)
(*       eapply IHl. 2: eauto. eauto.  *)
(*       unfold free_extcall_arg in Heqo. *)
(*       destruct a; try now (inv Heqo; eauto). *)
(*       destruct sl; try now (inv Heqo; eauto). *)
(*       destruct (parent_sp init_sp' lm) eqn:?; try now (inv Heqo; eauto).  *)
(*       eapply Mem.free_right_inject. eauto. eauto. *)
(*       intros b1 delta ofs k p JB1 PERM RNG. *)
(*       eapply (PERMS _ _ (or_introl eq_refl) _ _ eq_refl _ _ JB1 (ofs+delta)); eauto. *)
(*       replace (ofs + delta - delta) with ofs by omega; eauto. *)
(*   } *)
(*   intros pos ty IN sp' o EQsp sp delta JSP ofs RNG k p PERM. *)
(*   Opaque Z.mul. *)
(*   inv MS. *)
(*   - simpl in *. *)
(*     inv VINJ; try congruence. inv H2. *)
(*     specialize (HAMOA _ _ eq_refl _ _ _ _ H JSP). subst.  *)
(*     rewrite JSP in H; inv H.  *)
(*     eapply AOOB. eauto. *)
(*     instantiate (1 := ofs - delta0). *)
(*     revert RNG. *)
(*     rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta0)). *)
(*     rewrite <- Int.add_assoc. *)
(*     erewrite Mem.address_inject. simpl. clear; intros. omega. *)
(*     3: apply JSP. eauto. *)
(*     red in AL. *)
(*     exploit AL. eauto. intro IAL'. inv IAL'. *)
(*     unfold load_stack in H2. *)
(*     Opaque Z.mul. *)
(*     simpl in H2. *)
(*     apply Mem.load_valid_access in H2. *)
(*     destruct H2. *)
(*     eapply Mem.perm_extends. eauto. apply H. destruct ty; simpl; omega. *)
(*     eapply Mem.perm_implies. *)
(*     eapply Mem.perm_max. eauto. constructor. *)

(*   - simpl in *. inv EQsp. *)
(*     rewrite Int.add_zero_l in *. *)
(*     generalize (INJ_UNIQUE _ _ JSP). intro; subst. *)
(*     rewrite INJ in JSP; inv JSP. *)

(*     generalize (AOOB _ _ eq_refl _ _ IN). *)
(*     simpl. unfold loc_out_of_bounds. *)
(*     intros RNG'. *)
(*     eapply RNG'. rewrite Int.add_zero_l. eauto. *)
(*     red in AL. *)
(*     exploit AL. eauto. intro IAL'. inv IAL'. *)
(*     unfold load_stack in H2. *)
(*     Opaque Z.mul. *)
(*     simpl in H2. *)
(*     apply Mem.load_valid_access in H2. *)
(*     destruct H2. *)
(*     eapply Mem.perm_implies. *)
(*     eapply Mem.perm_max.  *)
(*     apply H. rewrite Int.add_zero_l. auto. constructor. *)
(*     Unshelve. exact (Regmap.init Vundef). *)
(*     exact (Regmap.init Vundef). *)
(* Qed. *)


(* Lemma free_extcall_args_inject_right' j m m' sg_ ll lm sg m_ m'_ : *)
(*   match_stacks j ll lm sg sg_  -> *)
(*   init_args_out_of_bounds sg_ m_ -> *)
(*   Mem.extends m_ m -> *)
(*   Mem.inject j m m' -> *)
(*   free_extcall_args (parent_sp init_sp' lm) m' (regs_of_rpairs (loc_arguments sg)) = Some m'_ -> *)
(*   forall (VINJ: Val.inject j init_sp init_sp') *)
(*     (HAMOA: has_at_most_one_antecedent j init_sp') *)
(*     (IAL: init_args_linear sg_ m_), *)
(*   Mem.inject j m_ m'_. *)
(* Proof. *)
(*   intros H H0 H1 H2 H3 VINJ HAMOA IAL. *)
(*   generalize (Mem.extends_inject_compose _ _ _ _ H1 H2). *)
(*   cut (forall pos ty (IN: In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) *)
(*          sp' o (EQsp: parent_sp init_sp' lm = Vptr sp' o) *)
(*          sp delta (JSP: j sp = Some (sp', delta)) *)
(*          ofs *)
(*          (RNG: Int.unsigned (Int.add o (Int.repr (4 * pos))) <= ofs *)
(*                < Int.unsigned (Int.add o (Int.repr (4 * pos))) + size_chunk (chunk_of_type ty)) *)
(*          k p (PERM: Mem.perm m_ sp (ofs-delta) k p), *)
(*           False). *)
(*   { *)
(*     clear IAL H2. intros H4 H5. revert m m' m'_ H1 H3 H4 H5. *)
(*     generalize (regs_of_rpairs (loc_arguments sg)). *)
(*     induction l; simpl; intros; eauto. *)
(*     - inv H3; auto. *)
(*     - destruct (free_extcall_arg (parent_sp init_sp' lm) m' a) eqn:?; try discriminate. *)
(*       eapply IHl. eauto. eauto. eauto.  *)
(*       unfold free_extcall_arg in Heqo. *)
(*       destruct a; try now (inv Heqo; eauto). *)
(*       destruct sl; try now (inv Heqo; eauto). *)
(*       destruct (parent_sp init_sp' lm) eqn:?; try now (inv Heqo; eauto).  *)
(*       eapply Mem.free_right_inject. eauto. eauto. *)
(*       intros b1 delta ofs k p JB1 PERM RNG. *)
(*       eapply (H4 _ _ (or_introl eq_refl) _ _ eq_refl _ _ JB1 (ofs+delta)); eauto. *)
(*       replace (ofs + delta - delta) with ofs by omega; eauto. *)
(*   } *)
(*   - intros pos ty IN sp' o EQsp sp delta JSP ofs RNG k p PERM. *)
(*     inv H. *)
(*     + simpl in *. *)
(*       inv VINJ; try congruence. symmetry in H5. *)
(*       specialize (H0 _ _ H5). revert H5; inv H6; intro H5. *)
(*       specialize (HAMOA _ _ eq_refl _ _ _ _ H JSP). revert H5. subst. *)
(*       rewrite JSP in H; inv H. intro H5. *)
(*       eapply H0. eauto. *)
(*       Focus 2. *)
(*       eapply Mem.perm_implies. *)
(*       eapply Mem.perm_max. eauto. constructor. *)
(*       revert RNG.  *)
(*       rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta0)). *)
(*       rewrite <- Int.add_assoc. *)
(*       erewrite Mem.address_inject. simpl. clear; intros. omega. *)
(*       3: apply JSP. eauto. *)
(*       red in IAL. *)
(*       exploit IAL. eauto. intro IAL'. inv IAL'. *)
(*       unfold load_stack in H7. *)
(*       Opaque Z.mul. *)
(*       simpl in H7. *)
(*       apply Mem.load_valid_access in H7. *)
(*       destruct H7. *)
(*       eapply Mem.perm_extends. eauto. apply H. destruct ty; simpl; omega. *)
(*     + simpl in *. inv EQsp. *)
(*       rewrite Int.add_zero_l in *. *)
(*       generalize (INJ_UNIQUE _ _ JSP). intro; subst. *)
      
      
(*       apply H7. *)

(*         in PERM. *)
(*       + *)

(*         eapply IHl. 3:eauto. *)
(*       { *)
(*         inv H. *)
(*         - subst; simpl in *. *)
(*           inv VINJ; try congruence. revert H7. inv H8. *)
(*           clear init_sp'_int init_sp'_not_global. *)
(*           red in HAMOA. *)
(*           specialize (HAMOA _ _ eq_refl _ _ _ _ H JB1). subst. *)
(*           rewrite H in JB1; inv JB1. clearbody step. *)
(*       } *)


(*       2: eapply Mem.perm_extends. *)
(*       simpl in RNG. *)

(*   } *)
(*   revert H3. *)
(*   cut (forall l2 l1, regs_of_rpairs (loc_arguments sg) = l1 ++ l2 -> free_extcall_args (parent_sp init_sp' lm) m' l2 = Some m'_ -> Mem.inject j m_ m' -> Mem.inject j m_ m'_). *)
(*   { *)
(*     clear H1 H2. *)
(*     intros H1 H3 H2. *)
(*     eapply H1 with (l1 := nil); eauto. simpl. eauto. *)
(*   } *)
(*   inversion H; subst; simpl parent_sp in * |- * . *)
(*   { (* initial arguments *) *)
(*     clear H1 H2. *)
(*     clear H TP. *)
(*     intro l2. *)
(*     revert m' m'_. *)
(*     induction l2. *)
(*     { *)
(*       simpl. *)
(*       congruence. *)
(*     } *)
(*     intros m' m'_ l1 H H6 H7. *)
(*     assert (regs_of_rpairs (loc_arguments sg_) = (l1 ++ a :: nil) ++ l2) as EQ. *)
(*     { *)
(*       rewrite app_ass; assumption. *)
(*     } *)
(*     generalize (fun m' m'_ => IHl2 m' m'_ _ EQ). *)
(*     clear IHl2. intro IHl2. *)
(*     simpl in H6. *)
(*     unfold free_extcall_arg in H6. *)
(*     destruct a; eauto. *)
(*     destruct sl; eauto. *)
(*     destruct init_sp' eqn:SP; try discriminate. *)
(*     set (o := Int.unsigned (Int.add i (Int.repr (fe_ofs_arg + 4 * pos)))). *)
(*     fold o in H6. *)
(*     destruct (Mem.free m' b o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate. *)
(*     exploit Mem.free_right_inject; eauto. *)
(*     intros b1 delta ofs k p H8 H9 H10. *)
(*     revert SP. *)
(*     intros SP. *)
(*     red in H0. red in H0. *)
(*     inv VINJ; try congruence. *)
(*     assert (b0 = b1). *)
(*     { *)
(*       exploit HAMOA. eauto. apply H4. apply H8. auto. *)
(*     } *)
(*     specialize (H0 _ _ eq_refl pos ty). trim H0. *)
(*     rewrite EQ. rewrite ! in_app. simpl; auto. red in H0. *)
(*     eapply Mem.perm_implies in H9. *)
(*     eapply Mem.perm_max in H9. subst. eapply H0 in H9; eauto. *)
(*     revert H10; unfold o. revert H3. *)
(*     rewrite H8 in H4; inv H4. intro H3. *)

(*     rewrite Int.add_assoc. rewrite (Int.add_commut (Int.repr delta0)). *)
(*     rewrite <- Int.add_assoc. *)
(*     erewrite Mem.address_inject. clear; intros. omega. *)
(*     3: apply H8. apply H7. *)

(*     red in IAL. *)
(*     exploit IAL. *)
(*     rewrite EQ. rewrite ! in_app. simpl; auto. intro IAL'. inv IAL'. *)
(*     unfold load_stack in H10. *)
(*     Opaque Z.mul. *)
(*     simpl in H10. *)
(*     apply Mem.load_valid_access in H10. *)
(*     destruct H10. apply H1. destruct ty; simpl; omega. *)
(*     constructor. *)
(*   } *)
(*   (* internal arguments *) *)
(*   clear STK. *)
(*   rename INJ_UNIQUE into UNIQ. *)
  
(*   (* generalize (agree_bounds _ _ _ _ _ _ _ _ _ _  FRM). intro BOUND_. *) *)
(*   (* assert (forall ofs p, *) *)
(*   (*           Mem.perm m_ sp ofs Max p -> *) *)
(*   (*           0 <= ofs < Linear.fn_stacksize f) as BOUND. *) *)
(*   (* { *) *)
(*   (*   intros ofs p H3. *) *)
(*   (*   eapply BOUND_. *) *)
(*   (*   eapply Mem.perm_extends; eauto. *) *)
(*   (* } *) *)
(*   (* clear BOUND_. *) *)
(*   clear m H1 H2 H. *)
(*   intro l2. *)
(*   revert m' m'_. simpl. *)
(*   induction l2. *)
(*   { *)
(*     simpl. *)
(*     congruence. *)
(*   } *)
(*   rename H0 into OOB. *)
(*   intros m' m'_ l1 H H0 H1. *)
(*   simpl in H0. *)
(*   unfold free_extcall_arg in H0. *)
(*   assert (regs_of_rpairs (loc_arguments sg) = (l1 ++ a :: nil) ++ l2) as EQ. *)
(*   { *)
(*     rewrite app_ass; assumption. *)
(*   } *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   rewrite Int.add_commut in H0. *)
(*   rewrite Int.add_zero in H0. *)
(*   assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN. *)
(*   { *)
(*     rewrite H. *)
(*     apply in_or_app. *)
(*     simpl; auto. *)
(*   } *)
(*   specialize (ARGS _ _ IN). *)
(*   assert (slot_valid f Outgoing pos ty = true) as VALID. *)
(*   { *)
(*     (* duplicate proof from transl_external_argument *) *)
(*     exploit loc_arguments_acceptable_2; eauto. intros [A B]. *)
(*     unfold slot_valid. unfold proj_sumbool. rewrite zle_true. *)
(*     destruct (Zdivide_dec (typealign ty) pos (typealign_pos ty)); auto. omega. *)
(*   } *)


(*   (* exploit index_arg_valid; eauto. *) *)
(*   (* intro IVALID. *) *)
(*   (* exploit offset_of_index_no_overflow; eauto. *) *)
(*   (* unfold offset_of_index. *) *)
(*   (* intro NO_OVERFLOW. *) *)
(*   (* rewrite NO_OVERFLOW in H0. *) *)

(*   rewrite Int.unsigned_repr in H0. *)
(*   set (o := fe_ofs_arg + 4 * pos). *)
(*   fold o in H0. *)
(*   destruct (Mem.free m' sp' o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate. *)
(*   exploit Mem.free_right_inject; eauto. *)
(*   intros b1 delta ofs k p H2 H3 H4. *)
(*   specialize (UNIQ _ _ H2). *)
(*   destruct UNIQ. *)
(*   subst. *)
(*   apply Mem.perm_max in H3. Opaque fe_stack_data. *)
(*   rewrite INJ in H2; inv H2. *)

(*   generalize (OOB *)



(*   admit. *)
  

(*   simpl. *)
(*   unfold slot_within_bounds in ARGS. *)
(*   split. unfold slot_valid in VALID. destruct (zle 0 pos). omega. simpl in VALID. congruence. *)

(*   transitivity (4 * pos + 4 * typesize ty). *)
(*   generalize (typesize_pos ty). omega. *)
(*   transitivity (4 * size_arguments sg). *)
(*   generalize (loc_arguments_bounded _ _ _ IN). *)
(*   omega. *)
(*   auto. *)

(* Qed. *)

(* Lemma args_always_in_bounds j m_ m' sg_ ll lm sg *)
(*       (MS: match_stacks j ll lm sg sg_) *)
(*       (AL: args_linear sg m_ (linear_parent_sp init_sp ll) (linear_parent_ls init_ls ll)) *)
(*       (INJ: Mem.inject j m_ m') *)
(*       (AIB: init_args_in_bounds sg_ m'): *)
(*   args_in_bounds (parent_sp init_sp' lm) (regs_of_rpairs (loc_arguments sg)) m'. *)
(* Proof. *)
(*   inv MS. *)
(*   - simpl. auto. *)
(*   - simpl in *. *)

(*     cut (forall l2 l1, *)
(*             regs_of_rpairs (loc_arguments sg) = l1 ++ l2 -> *)
(*             forall m', *)
(*               (forall o ty, *)
(*                   In (S Outgoing o ty) l2 -> *)
(*                   let of := Int.unsigned (Int.add Int.zero (Int.repr (fe_ofs_arg + 4 * o))) *)
(*                   in *)
(*                   forall ofs, *)
(*                     of <= ofs < of + size_chunk (chunk_of_type ty) -> *)
(*                     0 <= ofs < fe_size (make_env (function_bounds f)) -> *)
(*                     ofs < fe_stack_data (make_env (function_bounds f)) \/ *)
(*                     fe_stack_data (make_env (function_bounds f)) + *)
(*                     Linear.fn_stacksize f <= ofs -> *)
(*                     Mem.perm m' sp' ofs Cur Freeable) -> *)
(*               args_in_bounds (Vptr sp' Int.zero) l2 m'). *)
(*     { *)
(*       intro A.  eapply (A _ nil). reflexivity. *)
(*       intros pos ty IN o ofs RNG RNG' EXCL. *)
(*       exploit AL. eauto. intro EA. inv EA. unfold load_stack in H2; simpl in H2. *)
(*       apply Mem.load_valid_access in H2. destruct H2. *)
(*       rewrite Int.add_zero_l in *. *)
(*     } *)


(* Qed. *)

(* Lemma free_extcall_args_external_call sg_ ef args m_ t vl m'_ : *)
(*   external_call ef ge args m_ t vl m'_ -> *)
(*   forall j m m', *)
(*     Mem.extends m_ m -> *)
(*     Mem.inject j m m' -> *)

(*     (* init_args_out_of_bounds sg_ m_ -> *) *)
(*     forall ll lm, *)
(*       match_stacks j ll lm (ef_sig ef) sg_ -> *)
(*      args_out_of_bounds (linear_parent_sp init_sp ll) (regs_of_rpairs (loc_arguments (ef_sig ef))) m_ -> *)
(*        args_linear (ef_sig ef) m_ (linear_parent_sp init_sp ll) (linear_parent_ls init_ls ll) -> *)
(*        Val.inject j init_sp init_sp' -> *)
(*        has_at_most_one_antecedent j (parent_sp init_sp' lm) ->  *)
(*       forall args', *)
(*         Val.inject_list j args args' -> *)
(*         (* init_args_in_bounds sg_ m' -> *) *)
(*         exists m'_, *)
(*           free_extcall_args (parent_sp init_sp' lm) m' (regs_of_rpairs (loc_arguments (ef_sig ef))) = Some m'_ /\ *)
(*           exists t2 res2 m2, *)
(*             external_call ef ge args' m'_ t2 res2 m2. *)
(* Proof. *)
(*   intros H j m m' H0 H1 ll lm H2 H3 H4 H5 H6 args' H7. *)

  

(*   (* intros H j m m' H0 H1 H2 ll lm H3 args' H4 H5. *) *)
(*   esplit. *)
(*   split; eauto. *)
(*   exploit free_extcall_args_inject_right'; eauto. *)
(*   intros H7. *)
(*   exploit external_call_mem_inject' ; eauto using match_stacks_preserves_globals. *)
(*   destruct 1 as (? & ? & ? & ? & _). *)
(*   eauto. *)
(* Qed. *)

Theorem transf_step_correct:
  forall s1 t s2, Linear2.step ge s1 t s2 ->
  forall (WTS: wt_state init_ls (Linear2.state_lower s1)) s1' (MS: match_states s1 s1'),
  exists s2', plus step tge s1' t s2' /\ match_states s2 s2'.
Proof.
  induction 1;
    clear step_ge_eq_before step_ge_eq_after.
 inversion step_low; subst; intros;
  inv MS; (try congruence);
  (repeat
  match goal with
      K1: _ = Linear2.state_lower ?s1,
      K2: Linear2.state_lower ?s1 = _
      |- _ =>
      rewrite K2 in K1;
        symmetry in K1;
        inv K1
  end);
  try rewrite transl_code_eq;
  try (generalize (function_is_within_bounds f _ (is_tail_in TAIL));
       intro BOUND; simpl in BOUND);
  unfold transl_instr.
 
- (* Lgetstack *)
  destruct BOUND as [BOUND1 BOUND2].
  exploit wt_state_getstack; eauto. intros SV.
  unfold destroyed_by_getstack; destruct sl.
+ (* Lgetstack, local *)
  exploit frame_get_local; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. exact A.
  econstructor.
  4: apply agree_regs_set_reg; eauto.
  4: apply agree_locs_set_reg; eauto.
  all: eauto with mem.
  eapply is_tail_cons_left; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1). rewrite Hs2.
  inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
  congruence.

+ (* Lgetstack, incoming *)
  unfold slot_valid in SV. InvBooleans.
  exploit incoming_slot_in_parameters; eauto. intros IN_ARGS.
  inversion STACKS; clear STACKS.
  { (* arguments to entrypoint *)
     subst. destruct TP as [TP | TP] .
    + elim (TP _ IN_ARGS).
    + 
      
      assert (init_args_mach j init_sg m') as INIT_ARGS_MACH.
      { subst;  auto. } 
      exploit frame_get_parent; eauto.
      intro PARST. Opaque Z.mul bound_outgoing. 
      subst.
      exploit INIT_ARGS_MACH. eauto. instantiate (1 := Regmap.init Vundef). intros (v & EA & EAinj).
      esplit.
      split.
      {
        eapply plus_one.
        econstructor; eauto.
        exploit unfold_transf_function; eauto.
        intro; subst tf; eauto.
        simpl. inv EA. eauto.
      }
      constr_match_states.
      constructor; auto. all: eauto with mem.
      * apply agree_regs_set_reg; auto.
        change (rs0 # temp_for_parent_frame <- Vundef)
        with (undef_regs (destroyed_by_getstack Incoming) rs0).
        eapply agree_regs_undef_regs; eauto.
        erewrite agree_incoming. eauto. eauto. eauto.
      * apply agree_locs_set_reg; eauto.
        apply agree_locs_set_reg; eauto.
        apply caller_save_reg_within_bounds.
        reflexivity. 
      * eapply is_tail_cons_left; eauto.
      * revert Hno_init_args.
        generalize (Linear2.state_invariant s1). rewrite Hs2.
        inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
      * congruence.
  }
  {
    subst sg isg.
    subst s cs'.
    exploit frame_get_outgoing.
    apply sep_proj2 in SEP. simpl in SEP. rewrite sep_assoc in SEP. eexact SEP.
    eapply ARGS; eauto.
    eapply slot_outgoing_argument_valid; eauto.
    intros (v & A & B).
    econstructor; split.
    - apply plus_one. eapply exec_Mgetparam; eauto. 
      rewrite (unfold_transf_function _ _ TRANSL). unfold fn_link_ofs.
      eapply frame_get_parent. eexact SEP.
    - constr_match_states.
      now (econstructor; eauto).
      all: eauto.
      * apply agree_regs_set_reg; auto.
        change (rs0 # temp_for_parent_frame <- Vundef)
        with (undef_regs (destroyed_by_getstack Incoming) rs0).
        eapply agree_regs_undef_regs; eauto.
        erewrite agree_incoming. eauto. eauto. eauto.
      * apply agree_locs_set_reg; eauto.
        apply agree_locs_set_reg; eauto.
        apply caller_save_reg_within_bounds.
        reflexivity. 
      * eapply is_tail_cons_left; eauto.
      * revert Hno_init_args.
        generalize (Linear2.state_invariant s1). rewrite Hs2.
        inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
      * congruence.
  }
+ (* Lgetstack, outgoing *)
  exploit frame_get_outgoing; eauto. intros (v & A & B).
  econstructor; split.
  apply plus_one. apply exec_Mgetstack. exact A.
  constr_match_states. all: eauto with coqlib.
  apply agree_regs_set_reg; auto.
  apply agree_locs_set_reg; auto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
  congruence.
  
- (* Lsetstack *)
  exploit wt_state_setstack; eauto. intros (SV & SW).
  set (ofs' := match sl with
               | Local => offset_local (make_env (function_bounds f)) ofs
               | Incoming => 0 (* dummy *)
               | Outgoing => offset_arg ofs
               end).
  eapply frame_undef_regs with (rl := destroyed_by_setstack ty) in SEP.
  assert (A: exists m'',
              store_stack m' (Vptr sp' Int.zero) ty (Int.repr ofs') (rs0 src) = Some m''
           /\ m'' |= frame_contents f j sp' (Locmap.set (S sl ofs ty) (rs (R src))
                                               (LTL.undef_regs (destroyed_by_setstack ty) rs))
                                            (parent_locset init_ls s) (parent_sp init_sp' cs') (parent_ra init_ra cs')
                  ** stack_contents j s cs' ** minjection j m ** globalenv_inject ge j).
  { unfold ofs'; destruct sl; try discriminate.
    eapply frame_set_local; eauto.
    eapply frame_set_outgoing; eauto. }
  clear SEP; destruct A as (m'' & STORE & SEP).
  econstructor; split.
  apply plus_one. destruct sl; try discriminate.
    econstructor. eexact STORE. eauto.
    econstructor. eexact STORE. eauto.
  constr_match_states. all: eauto with coqlib. 
  apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
  apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
  + eapply block_prop_impl; try eassumption.
    unfold store_stack, Val.add, Mem.storev in STORE. eauto with mem.
  + red; intros.
    exploit INIT_ARGS; eauto. instantiate (1 := Regmap.init Vundef).
    intros (v & A & B). inv A; econstructor; split; eauto.
    constructor. unfold store_stack, load_stack, Val.add, Mem.loadv, Mem.storev in *.
    clearbody step. destruct init_sp'; try discriminate.
    erewrite Mem.load_store_other; eauto.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
  + congruence.
  + unfold store_stack in STORE. eapply init_args_in_bounds_storev; eauto.

- (* Lop *)
  assert (OP_INJ:
            exists v',
              eval_operation ge (Vptr sp' Int.zero)
                             (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v' /\
              Val.inject j v v').
  {
    eapply eval_operation_inject; eauto.
    eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
    apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. exact SEP.
  }
  destruct OP_INJ as [v' [A B]].
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := v'). rewrite <- A. apply eval_operation_preserved.
    exact symbols_preserved. eauto.
  + constr_match_states. all: eauto with coqlib.
    * apply agree_regs_set_reg; auto.
      rewrite transl_destroyed_by_op.  apply agree_regs_undef_regs; auto.
    * apply agree_locs_set_reg; auto. apply agree_locs_undef_locs. auto. apply destroyed_by_op_caller_save.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.
    * apply frame_set_reg. apply frame_undef_regs. exact SEP. 

- (* Lload *)
  assert (ADDR_INJ:
            exists a',
              eval_addressing ge (Vptr sp' Int.zero)
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.inject j a a').
  {
    eapply eval_addressing_inject; eauto.
    eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
  }
  destruct ADDR_INJ as [a' [A B]]. 
  exploit loadv_parallel_rule.
  apply sep_proj2 in SEP. apply sep_proj2 in SEP. apply sep_proj1 in SEP. eexact SEP.
  eauto. eauto. 
  intros [v' [C D]].
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
  + constr_match_states. all: eauto with coqlib.
    * apply agree_regs_set_reg. rewrite transl_destroyed_by_load. apply agree_regs_undef_regs; auto. auto.
    * apply agree_locs_set_reg. apply agree_locs_undef_locs. auto. apply destroyed_by_load_caller_save. auto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.

- (* Lstore *)
  assert (STORE_INJ:
            exists a',
              eval_addressing ge (Vptr sp' Int.zero)
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.inject j a a').
  {
    eapply eval_addressing_inject; eauto.
    eapply globalenv_inject_preserves_globals. eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
    eapply agree_reglist; eauto.
  }
  destruct STORE_INJ as [a' [A B]].
  rewrite sep_swap3 in SEP.
  exploit storev_parallel_rule.
  eexact SEP.
  eauto.
  eauto.
  apply AGREGS.
  rename SEP into SEP_init.
  intros (m1' & C & SEP).
  rewrite sep_swap3 in SEP.
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
  + constr_match_states. all: eauto with coqlib.
    * rewrite transl_destroyed_by_store. apply agree_regs_undef_regs; auto.
    * apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
    * eapply block_prop_impl; try eassumption.
      destruct a' ; try discriminate. simpl in *. eauto with mem.
    * { 
        revert Hno_init_args.
        generalize (Linear2.state_invariant s1).
        rewrite Hs2.
        inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.
        intro OOB.
        red. intros sl ofs ty IN rs2.
        generalize (INIT_ARGS _ _ _ IN rs2). intros (v & EA & VINJ) .
        inv EA; eexists; split. constructor; auto. 2: eauto.
        unfold load_stack, Val.add, Mem.loadv, Mem.storev in * |- * .
        clearbody step. destruct init_sp'; try discriminate.
        destruct a0; try discriminate.
        destruct a'; try discriminate.
        erewrite Mem.load_store_other; eauto.
        red in OOB. inv INJ_INIT_SP; try congruence. 
        specialize (OOB _ _ eq_refl _ _ IN).
        unfold loc_out_of_bounds in OOB.

        match goal with
          |- ?b0 <> ?b2 \/ ?a <= ?b \/ ?c <= ?d =>
          destruct (eq_block b0 b2); 
            [subst; destruct (zle a b);
             [ now auto
             | destruct (zle c d);
               [ now auto | ] ]
            | now auto ]
        end.
        exfalso.

        exploit eval_addressing_lessdef_strong. 
        2 : apply sp_lessdef. 
        apply reglist_lessdef. eauto.
        eauto.  intros (v2 & EA & LD).
        inv LD. 
        exploit Mem.store_valid_access_3. eexact H5.
        destruct (eq_block b1 b3). subst.

        intros (RP & _).
        eapply OOB. 2: eapply Mem.perm_implies.
        2: eapply Mem.perm_cur_max. 2: eapply RP. 3: constructor.
        instantiate (1 := Int.unsigned i1 - delta). omega.
        red in A, OOB.


        revert OOB g g0.
        generalize (Int.add i (Int.repr (4*ofs))). intros.


        (* -----i0--i1-i0+--i1+------------ *)
        (* ------i1---i0--i1+ i0+---------------------- *)

        assert (exists o,
                   Int.unsigned i1 <= o < Int.unsigned i1 + size_chunk (chunk_of_type ty) /\
                   Int.unsigned i0 <= o < Int.unsigned i0 + size_chunk chunk).
        {
          exists (Z.max (Int.unsigned i1) (Int.unsigned i0)).
          repeat split.
          apply Zmax_bound_l; auto. apply Zle_refl.
          rewrite Zmax_spec.
          Ltac destr :=
            match goal with
              |- context [match ?a with _ => _ end] => destruct a eqn:?
            end.
          destr. destruct ty; simpl; omega.
          omega.
          apply Zmax_bound_r. omega.
          rewrite Zmax_spec; destr. omega. destruct chunk; simpl; omega.
        }
        destruct H as (o & C & D).
        generalize (A _ D) (OOB _ C).
        clear - memory_model_prf. intros A B. apply B. eapply Mem.perm_implies.
        apply Mem.perm_cur_max. eauto. constructor.
      }
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.



      eapply init_args_out_of_bounds_storev; eauto.
    * congruence.
    * eapply init_args_in_bounds_storev; eauto.
    * eapply frame_undef_regs; eauto.

- (* Lcall *)
  exploit find_function_translated; eauto.
    eapply sep_proj2. eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST. intros [ra D].
  econstructor; split.
  + apply plus_one. econstructor; eauto.
  + constr_match_states; eauto. 
    * econstructor; eauto with coqlib.
      simpl; auto.
      intros; red.
      apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
      apply loc_arguments_bounded; auto.
    * simpl; red; auto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.
    * simpl. rewrite sep_assoc. exact SEP.

- (* Ltailcall *)
  rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  clear SEP. intros (rs1 & m1' & P & Q & R & S & T & U & SEP).
  inv Hinit_ls.
  rewrite sep_swap in SEP.
  exploit find_function_translated; eauto. 
    eapply sep_proj2. eapply sep_proj2. eexact SEP.
  intros [bf [tf' [A [B C]]]].
  econstructor; split.
  + eapply plus_right. eexact S. econstructor; eauto. traceEq.
  + assert (TAILCALL: tailcall_possible (Linear.funsig f')).
    {
      apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
    }
    exploit match_stacks_change_sig. eauto. eauto.
    intros MS'.
    constr_match_states.  all: eauto. subst; eauto. 
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      destr. 
      clear H1. subst.
      intros _.
      clear - TAILCALL. red; red; intros.
      apply TAILCALL in H0. easy.
      eapply init_args_out_of_bounds_free; eauto.
    * congruence.
    * destr.  
      -- eapply tailcall_possible_in_bounds; eauto.
      -- eapply init_args_in_bounds_free; eauto.
         clearbody step. clear H1. intros; subst.
         revert H; inv INJ_INIT_SP.
         generalize (SP_NOT_INIT _ _ eq_refl).
         intros NEQ _ ->.
         apply NEQ. eapply INJUNIQUE; eauto. congruence.
    * eapply block_prop_impl; try eassumption.
      eauto with mem. 

    * (* init_args_linear *)
      clear H1.
      inv STACKS.
      -- red.
         intros sl of ty H1 rs2.
         elim (TAILCALL _ H1).
      -- red.
         intros sl of ty H rs2.
         apply INIT_ARGS in H.
         specialize (H rs2).
         inv H; constructor; auto.
         destruct init_sp; try discriminate.
         unfold load_stack, Val.add, Mem.loadv in * |- * .
         erewrite Mem.load_free; eauto.

- (* Lbuiltin *)
  destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
    eauto. eauto. rewrite sep_swap in SEP; apply sep_proj2 in SEP; eexact SEP.
    eauto. rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
    exact BND2.
  intros [vargs' [P Q]].
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  exploit (external_call_parallel_rule); eauto.
  {
    repeat
    match goal with
        [ |- context [m_invar_weak (?U ** ?V)] ] =>
        replace (m_invar_weak (U ** V))
                with (m_invar_weak U || m_invar_weak V)
          by reflexivity
    end.
    rewrite frame_contents_invar_weak.
    rewrite stack_contents_invar_weak.
    reflexivity.
  }
  rename SEP into SEP_init; intros (j' & res' & m1' & EC & RES & SEP & INCR & ISEP).
  rewrite <- sep_assoc, sep_comm, sep_assoc in SEP.
  econstructor; split.
  + apply plus_one. econstructor; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  + constr_match_states.
    4: apply agree_regs_set_res; auto. 4: apply agree_regs_undef_regs; auto. 4: eapply agree_regs_inject_incr; eauto.
    4: eauto.
    4: apply agree_locs_set_res; auto. 4: apply agree_locs_undef_regs; auto.
    eapply match_stacks_change_meminj; eauto. all: eauto.
    * exists m, m'0; split; auto.
      intros. eapply Mem.valid_block_inject_2; eauto.
      apply sep_proj1 in SEP_init. simpl in SEP_init. eauto.
    * intros.
      destruct (j b0) eqn:?. destruct p.
      generalize (INCR _ _ _ Heqo). intros. rewrite H in H3; inv H3.
      eapply INJUNIQUE; eauto.
      generalize (ISEP _ _ _ Heqo H).
      intros (A & B).
      apply sep_proj1 in SEP_init. simpl in SEP_init.
      exploit Mem.valid_block_inject_2. apply INJSP. eauto. congruence.

  (* { (* inject_separated *) *)
  (*   red. intros b1 b2 delta H1 H2. *)
  (*   destruct (j b1) as [ [ ] | ] eqn:J . *)
  (*   + generalize J. intro J_. *)
  (*     apply INCR in J_. *)
  (*     rewrite H2 in J_. inv J_. *)
  (*     eauto. *)
  (*   + exploit ISEP; eauto. *)
  (*     generalize (INIT_M_VALID b1). *)
  (*     generalize (INIT_M'_VALID b2). *)
  (*     clear; tauto. *)
      (* } *)
    * eapply has_at_most_one_antecedent_incr; eauto.
    * eapply block_prop_impl; try eassumption.
      intro; eapply external_call_valid_block; eauto.
    * (* init_args_linear *) 
      revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.

      intros IAOOB.

      red. intros sl of ty IN rs2.
      specialize (INIT_ARGS _ _ _ IN rs2). inv INIT_ARGS.
      constructor; auto.
      destruct init_sp eqn:?; try discriminate.
      unfold load_stack, Val.add, Mem.loadv in * |- * .
      apply sep_proj1 in SEP_init; simpl in SEP_init.
      generalize (fun pf => init_args_out_of_bounds_external_call
                           _ _ _ _ _ _ _ pf
                           H5 _ _ _ _ _ _ STACKS
                           m_ext SEP_init IAOOB
                 ).
      intro IAOOB'.
      trim IAOOB'. intros. rewrite Heqv in H6. clear Heqv. inv H6.
      clearbody step. inv INJ_INIT_SP.
      rewrite Mem.valid_block_extends.
      eapply Mem.valid_block_inject_1; eauto. eauto.
      repeat red in IAOOB'. 
      admit.


      (* eapply *)
      (* apply INIT_ARGS in IN. *)
      (* specialize (IN rs1). *)
      (* inv IN; constructor; auto. *)
      (* destruct init_sp; try discriminate. *)
      (* unfold load_stack, Val.add, Mem.loadv in * |- * . *)
    * eauto with coqlib.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      eapply init_args_out_of_bounds_external_call; eauto.
      intros. subst. 
      clearbody step. clear H1 H6. inv INJ_INIT_SP.
      rewrite Mem.valid_block_extends.
      eapply Mem.valid_block_inject_1; eauto. apply sep_proj1 in SEP_init; simpl in SEP_init; eauto.
      eauto.
       apply sep_proj1 in SEP_init; simpl in SEP_init; eauto.
    * congruence.
    *
       revert Hsome_init_args Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      intros IAIB IAOOB. revert IAIB.
      eapply init_args_in_bounds_external_call. eexact H5. 
      apply sep_pick2 in SEP_init. eauto. all: eauto.
      -- intros; subst. clearbody step. specialize (SP_NOT_INIT _ _ eq_refl).
         revert H6. inv INJ_INIT_SP.
         rewrite H7 in H11. revert H12. inv H11.
         specialize (init_sp'_not_global _ _ eq_refl).
         intros.
         specialize (HAMOA _ _ eq_refl _ _ _ _ H7 H9). auto.
      -- apply sep_pick1 in SEP_init; simpl in SEP_init; eauto.
      --
        Lemma val_list_lessdef_inject_compose j l1 l2:
	        Val.lessdef_list l1 l2 ->
	        forall l3,
	          Val.inject_list j l2 l3 ->
	          Val.inject_list j l1 l3.
	      Proof.
	        induction 1; inversion 1; subst; auto.
	        constructor; auto.
	        inversion H; subst; auto.
	      Qed.


        Lemma eval_builtin_arg_lessdef':
          forall { A : Type } ge (rs1 rs2: A -> val) sp sp' m arg v v'
            (EBA: eval_builtin_arg ge rs1 sp m arg v) 
            (EBA': eval_builtin_arg ge rs2 sp' m arg v')
            (LDRS: forall a, Val.lessdef (rs1 a) (rs2 a))
            (LD: Val.lessdef sp sp'),
            Val.lessdef v v'.
        Proof.
          induction arg; intros; inv EBA; inv EBA'; subst; auto.
          - intros. exploit Mem.loadv_extends. apply Mem.extends_refl. apply H2.
            2: rewrite H3. simpl. apply Val.add_lessdef; auto. intros (v2 & B & C). inv B. auto.
          - intros; apply Val.add_lessdef; auto.
          - intros. exploit Mem.loadv_extends. apply Mem.extends_refl. apply H3.
            2: rewrite H4. auto. intros (v2 & B & C). inv B. auto.
          - apply Val.longofwords_lessdef. eauto. eauto.
        Qed.

        Lemma eval_builtin_args_lessdef':
          forall { A : Type } ge (rs1 rs2: A -> val) sp sp' m args vl vl'
            (EBA: eval_builtin_args ge rs1 sp m args vl) 
            (EBA': eval_builtin_args ge rs2 sp' m args vl')
            (LDRS: forall a, Val.lessdef (rs1 a) (rs2 a))
            (LD: Val.lessdef sp sp'),
            Val.lessdef_list vl vl'.
        Proof.
          induction args; simpl; intros. inv EBA; inv EBA'. constructor.
          inv EBA; inv EBA'. constructor; auto.
          eapply eval_builtin_arg_lessdef'; eauto.
        Qed.

        repeat match goal with
                 H : eval_builtin_args _ _ _ _ _ _ |- _ => revert H
               end.
        intros.
        eapply val_list_lessdef_inject_compose. 2: apply Q.
        exploit eval_builtin_args_lessdef. apply rs_lessdef. apply m_ext. eauto. intros (vl2 & EBA & LDL).
        eapply Val.lessdef_list_trans. eauto.
        eapply eval_builtin_args_lessdef'; eauto.

    * apply frame_set_res. apply frame_undef_regs. apply frame_contents_incr with j; auto.
      rewrite sep_swap2. apply stack_contents_change_meminj with j; auto. rewrite sep_swap2.
      exact SEP.

- (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  econstructor; eauto with coqlib.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  econstructor; eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lcond, true *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_true; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  eapply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto. eauto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  all: eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lcond, false *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_false; eauto.
  eapply eval_condition_inject with (m1 := m). eapply agree_reglist; eauto. apply sep_pick3 in SEP; exact SEP. auto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; eauto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_cond_caller_save.
  all: eauto.
  eauto with coqlib.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Ljumptable *)
  assert (rs0 arg = Vint n).
  { generalize (AGREGS arg). rewrite H1. intro IJ; inv IJ; auto. }
  econstructor; split.
  apply plus_one; eapply exec_Mjumptable; eauto.
  apply transl_find_label; eauto.
  econstructor. eauto. eauto. eauto.
  apply agree_regs_undef_regs; eauto.
  apply agree_locs_undef_locs. auto. apply destroyed_by_jumptable_caller_save.
  all: eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lreturn *)
  rewrite (sep_swap (stack_contents j s cs')) in SEP.
  exploit function_epilogue_correct; eauto.
  intros (rs' & m1' & A & B & C & D & E & F & G).
  econstructor; split.
  eapply plus_right. eexact D. econstructor; eauto. traceEq.
  inv Hinit_ls.
  constr_match_states. all: try subst; eauto.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
    intros; eapply init_args_out_of_bounds_free; eauto.
  + congruence.
  + eapply init_args_in_bounds_free; eauto.
    clearbody step. clear H1. intros; subst.
    revert H; inv INJ_INIT_SP.
    generalize (SP_NOT_INIT _ _ eq_refl).
    intros NEQ _ ->.
    apply NEQ. eapply INJUNIQUE; eauto. congruence.
  + eapply block_prop_impl; try eassumption.
    eauto with mem. 

  + (* init_args_linear *)
    clear H1.
    red.
    intros sl of ty H rs2.
    apply INIT_ARGS in H.
    specialize (H rs2).
    inv H; constructor; auto.
    destruct init_sp; try discriminate.
    unfold load_stack, Val.add, Mem.loadv in * |- * .
    erewrite Mem.load_free; eauto.
  + rewrite sep_swap; exact G.

- (* internal function *)
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
  intros EQ; inversion EQ; clear EQ; subst tf.
  rewrite sep_comm, sep_assoc in SEP. 
  exploit function_prologue_correct.
  eassumption.
  eassumption.
  eassumption.
  red; intros; eapply wt_callstate_wt_regs; eauto.
  reflexivity.
  reflexivity.
  eassumption.
  eapply match_stacks_type_sp; eauto.
  eapply match_stacks_type_retaddr; eauto.
  eassumption.
  rename SEP into SEP_init;
  intros (j' & rs' & m2' & sp' & m3' & m4' & m5' & A & B & C & D & E & F & SEP & J & K & KSEP & KV & KV' & PERMS).
  rewrite (sep_comm (globalenv_inject ge j')) in SEP.
  rewrite (sep_swap (minjection j' m')) in SEP.
  econstructor; split.
  + eapply plus_left. econstructor; eauto.
    rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
    eexact D. traceEq.
  + constr_match_states. 
    eapply match_stacks_change_meminj; eauto. all: eauto with coqlib.
    * exists m, m'0; split; eauto.
      intros.
      eapply Mem.valid_block_inject_2; eauto.
      apply sep_pick1 in SEP_init; simpl in SEP_init; eauto.
    * intros.
      destruct (j b) eqn:?. destruct p.
      exploit K. apply Heqo. rewrite H. intro Z; inv Z.
      eapply Mem.valid_block_inject_2 in Heqo.
      2: apply sep_pick1 in SEP_init; simpl in SEP_init; apply SEP_init.
      eapply Mem.fresh_block_alloc in A. congruence.
      generalize (KSEP _ _ _ Heqo H).
      intros (VB1 & VB2).
      eapply Mem.valid_block_inject_1 in H.
      2: apply sep_pick3 in SEP; simpl in SEP; apply SEP.
      clear - VB1 H H1 external_calls_prf.
      unfold Mem.valid_block in *.
      exploit Mem.nextblock_alloc; eauto.
      exploit Mem.alloc_result; eauto. intros; subst.
      rewrite H2 in H.
      apply Plt_succ_inv in H; destruct H; congruence.
    * eapply has_at_most_one_antecedent_incr; eauto.
    * eapply block_prop_impl; eauto.
    * (* init_args_linear *)
      red. intros sl of ty IN rs1.
      apply INIT_ARGS in IN.
      specialize (IN rs1).
      inv IN; constructor; auto.
      destruct init_sp; try discriminate.
      unfold load_stack, Val.add, Mem.loadv in * |- * .
      eapply Mem.load_alloc_other; eauto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.

Lemma init_args_out_of_bounds_alloc m_ lo hi m'_ b :
  Mem.alloc m_ lo hi = (m'_, b) ->
  block_prop (Mem.valid_block m_) init_sp ->
  forall sg_ j m m' sg ll lm,
    match_stacks j ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.inject j m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds, args_out_of_bounds, loc_out_of_bounds.
  intros H SPV sg_ j m m' sg ll lm H0 H1 H2 H3 b0 o H4 of ty H5 o0 H6.
  intro ABSURD.
  eapply Mem.perm_alloc_4 in ABSURD; eauto.
  { eapply H3; eauto. }
  apply Mem.fresh_block_alloc in H. red in SPV. rewrite H4 in SPV. congruence.
Qed.

eapply init_args_out_of_bounds_alloc. eauto.

{
  clear - m_ext ISP'VALID INJ_INIT_SP SEP_init external_calls_prf.
  destruct init_sp; simpl; auto. clearbody step. inv INJ_INIT_SP.
  simpl in *.
  rewrite Mem.valid_block_extends; eauto.
  eapply Mem.valid_block_inject_1; eauto.
  apply sep_pick1 in SEP_init; simpl in SEP_init; eauto.
}
eauto. eauto.
apply sep_pick1 in SEP_init; simpl in SEP_init; eauto.


    * congruence.
    * unfold store_stack in *.
      eapply init_args_in_bounds_perm.
      intros b o_ H o k p. apply PERMS. eauto.
    * clear - SEP_init INJ_INIT_SP H1.
      intros; subst. clearbody step. inversion INJ_INIT_SP. revert H3; subst.
      eapply Mem.fresh_block_alloc in H1. intros EQ NEQ; subst.
      apply H1. eapply Mem.valid_block_inject_1; eauto.
      apply sep_pick1 in SEP_init; simpl in SEP_init; eauto.
    * rewrite sep_swap in SEP. rewrite sep_swap. eapply stack_contents_change_meminj; eauto.

- (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  exploit transl_external_arguments; eauto. apply sep_proj1 in SEP; eauto.
  { (* init_args_mach *)
    eapply init_args_linear_to_mach; eauto.
    repeat
      match goal with
        | _ => assumption
        | K : ?m' |= _ ** _ |- ?m' |= _ =>
          generalize K;
            let  L := fresh in
            intro L;
              apply sep_proj1 in K;
              apply sep_proj2 in L
      end.
  }
  intros [vl [ARGS VINJ]].
  rewrite sep_comm, sep_assoc in SEP.
  exploit external_call_parallel_rule; eauto.
  {
    apply stack_contents_invar_weak.
  }
  intros (j' & res' & m1' & A & B & C & D & E).
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  {
    revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
	  rewrite Hs2.
	  inversion step_high; inversion 1; subst; try (simpl in * |- * ; now intuition congruence).

    intro Hno_init_args. 
	  (** BEGIN STACK *)
	  inversion f_eq; subst.

    inv STACKS.
    - simpl in *.
      destruct TP.
      +

        Lemma tailcall_possible_free_extcall_args:
          forall sg (TP: tailcall_possible sg)
            sp m,
            free_extcall_args sp m (regs_of_rpairs (loc_arguments sg)) = Some m.
        Proof.
          unfold tailcall_possible.
          intro sg; generalize (regs_of_rpairs (loc_arguments sg)).
          induction l; simpl; intros; eauto.
          generalize (TP _ (or_introl eq_refl)).
          destruct a; try easy. simpl. intros.
          apply IHl.  intros; apply TP; eauto.
        Qed.
        rewrite tailcall_possible_free_extcall_args. eexists; split; eauto.
        eexists; eexists; eexists; eauto.

        eapply external_call_symbols_preserved; eauto. apply senv_preserved. auto.
      + subst.

        exploit free_extcall_args_inject_right.
    econstructor. all: eauto.
    apply is_tail_refl.
    
	  exploit free_extcall_args_external_call; eauto.
	  eapply val_list_lessdef_inject_compose; eauto.
	  apply map_reg_lessdef; auto.
	  (** END STACK *)
	  intro STACK.
    
  }
  { (* sp valid *)
    eapply match_stacks_sp_valid; eauto.
    +
    intros b o H.
    generalize INJ_INIT_SP. rewrite H. intro INJ.
    inversion INJ; try congruence.
    eapply Mem.valid_block_inject_2; eauto.
    instantiate (1 := m).
    repeat
      match goal with
        | _ => assumption
        | K : ?m' |= _ ** _ |- Mem.inject _ _ ?m' =>
          generalize K;
            let  L := fresh in
            intro L;
              apply sep_proj1 in K;
              apply sep_proj2 in L
      end.
    +
    repeat
      match goal with
        | _ => assumption
        | K : ?m' |= _ ** _ |- ?m' |= _ =>
          generalize K;
            let  L := fresh in
            intro L;
              apply sep_proj1 in K;
              apply sep_proj2 in L
      end.
  }
  { (* sp not global *)
    eapply match_stacks_sp_not_global; eauto.
  }
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  eapply match_states_return with (j := j').
  eapply match_stacks_change_meminj; eauto.
  apply agree_regs_set_pair. apply agree_regs_inject_incr with j; auto. auto.
  apply agree_callee_save_set_result; auto.
  eauto.
  eapply inject_incr_trans; eauto.
  intros; eapply external_call_valid_block; eauto.
  intros; eapply external_call_valid_block; eauto.
  { (* inject_separated *)
    red. intros b1 b2 delta H1 H2.
    destruct (j b1) as [ [ ] | ] eqn:J .
    + generalize J. intro J_.
      apply D in J_.
      rewrite H2 in J_. inv J_.
      eauto.
    + exploit E; eauto.
      generalize (INIT_M_VALID b1).
      generalize (INIT_M'_VALID b2).
      clear; tauto.
  }
  {
    (* init_args_linear *)
    red. intros sl of ty H rs0.
    apply INIT_ARGS in H.
    specialize (H rs0).
    inv H; constructor; auto.
    destruct init_sp; try discriminate.
    unfold load_stack, Val.add, Mem.loadv in * |- * .
    (* erewrite external_call_not_writable; eauto. *)
    (* FIXME: PW: *) admit.
  }
  { (* init_sp_valid *)
    intros b0 o H1.
    eapply external_call_valid_block; eauto.
  }
  apply stack_contents_change_meminj with j; auto.
  rewrite sep_comm, sep_assoc; auto.

- (* return *)
  inv STACKS. simpl in AGLOCS. simpl in SEP. rewrite sep_assoc in SEP. 
  econstructor; split.
  apply plus_one. apply exec_return.
  econstructor; eauto.
  apply agree_locs_return with rs0; auto.
  apply frame_contents_exten with rs0 (parent_locset init_ls s); auto.
Admitted.

End WITHMEMINIT.

End WITHINITSP.

Let match_states s s' :=
  exists j init_m init_m',
    match_states Vzero Vzero (Locmap.init Vundef) (signature_main) Vzero init_m j init_m' s s' /\
    Ple (Genv.genv_next ge) (Mem.nextblock init_m) /\
    Ple (Genv.genv_next tge) (Mem.nextblock init_m').

Lemma transf_initial_states:
  forall st1, Linear.initial_state prog st1 ->
  exists st2, Mach.initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved. eauto.
  set (j := Mem.flat_inj (Mem.nextblock m0)).
  exists j. exists m0. exists m0.
  split.
{
  eapply match_states_call with (j := j); (try now (red; eauto)); eauto.
  constructor; (try now (red; eauto)); eauto. constructor.
  red; intros; congruence.
  intros sl of ty H rs. rewrite H3, loc_arguments_main in H. contradiction.
  simpl stack_contents. rewrite sep_pure. split; auto. split;[|split].
  eapply Genv.initmem_inject; eauto.
  simpl. exists (Mem.nextblock m0); split. apply Ple_refl.
  unfold j, Mem.flat_inj; constructor; intros.
    apply pred_dec_true; auto.
    destruct (plt b1 (Mem.nextblock m0)); congruence.
    change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
    change (Mem.valid_block m0 b0). eapply Genv.find_funct_ptr_not_fresh; eauto.
    change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
  red; simpl; tauto.
}
  rewrite genv_next_preserved.
  unfold ge. erewrite Genv.init_mem_genv_next by eauto.
  split; apply Ple_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> Linear.final_state st1 r -> Mach.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H0. inv H. inv H0. inv H. inv STACKS.
  assert (R: exists r, loc_result signature_main = One r) by (econstructor; reflexivity). 
  destruct R as [rres EQ]. rewrite EQ in H1. simpl in H1.
  generalize (AGREGS rres). rewrite H1. intros A; inv A.
  econstructor; eauto.
Qed.

Lemma wt_prog:
  forall i fd, In (i, Some (Gfun fd)) prog.(prog_defs) -> wt_fundef fd.
Proof.
  intros.
  exploit list_forall2_in_left. eexact (proj1 TRANSF). eauto.
  intros ([i' g] & P & Q & R). simpl in *. inv R.
  inv H1.
  destruct fd; simpl in *.
- monadInv H3. unfold transf_function in EQ.
  destruct (wt_function f). auto. discriminate.
- auto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog).
Proof.
  set (ms := fun s s' => wt_state (Locmap.init Vundef) s /\ match_states s s').
  eapply forward_simulation_plus with (match_states0 := ms).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; split; auto. split; auto.
  apply wt_initial_state with (prog0 := prog); auto. exact wt_prog.
- intros. destruct H. eapply transf_final_states; eauto.
- intros. destruct H0.
  destruct H1 as (j & im & im' & MS & GE & GE').
  exploit transf_step_correct; eauto.
  unfold Vzero; red; auto. unfold Vzero; red; auto.
  discriminate. discriminate. 
  eassumption. intros [s2' [A B]].
  exists s2'; split. exact A. split.
  eapply step_type_preservation; eauto. eexact wt_prog. eexact H.
  repeat eexists; eauto. 
Qed.

End PRESERVATION.
