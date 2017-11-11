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

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import Coqlib.
Require Import AST.
Require Import Locations.
Require Export Conventions1.

(** The processor-dependent and EABI-dependent definitions are in
    [arch/abi/Conventions1.v].  This file adds various processor-independent
    definitions and lemmas. *)

Lemma loc_arguments_acceptable_2:
  forall s l,
  In l (regs_of_rpairs (loc_arguments s)) -> loc_argument_acceptable l.
Proof.
  intros until l. generalize (loc_arguments_acceptable s). generalize (loc_arguments s).
  induction l0 as [ | p pl]; simpl; intros.
- contradiction.
- rewrite in_app_iff in H0. destruct H0.
  exploit H; eauto. destruct p; simpl in *; intuition congruence.
  apply IHpl; auto.
Qed.

(** ** Location of function parameters *)

(** A function finds the values of its parameter in the same locations
  where its caller stored them, except that the stack-allocated arguments,
  viewed as [Outgoing] slots by the caller, are accessed via [Incoming]
  slots (at the same offsets and types) in the callee. *)

Definition parameter_of_argument (l: loc) : loc :=
  match l with
  | S Outgoing n ty => S Incoming n ty
  | _ => l
  end.

Definition loc_parameters (s: signature) : list (rpair loc) :=
  List.map (map_rpair parameter_of_argument) (loc_arguments s).

Lemma incoming_slot_in_parameters:
  forall ofs ty sg,
  In (S Incoming ofs ty) (regs_of_rpairs (loc_parameters sg)) ->
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)).
Proof.
  intros.
  replace (regs_of_rpairs (loc_parameters sg)) with (List.map parameter_of_argument (regs_of_rpairs (loc_arguments sg))) in H.
  change (S Incoming ofs ty) with (parameter_of_argument (S Outgoing ofs ty)) in H.
  exploit list_in_map_inv. eexact H. intros [x [A B]]. simpl in A.
  exploit loc_arguments_acceptable_2; eauto. unfold loc_argument_acceptable; intros.
  destruct x; simpl in A; try discriminate.
  destruct sl; try contradiction.
  inv A. auto.
  unfold loc_parameters. generalize (loc_arguments sg). induction l as [ | p l]; simpl; intros.
  auto.
  rewrite map_app. f_equal; auto. destruct p; auto.
Qed.

(** * Tail calls *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

(** A tail-call is possible for a signature if the corresponding
    arguments are all passed in registers. *)

Definition tailcall_possible (s: signature) : Prop :=
  forall l, In l (regs_of_rpairs (loc_arguments s)) ->
  match l with R _ => True | S _ _ _ => False end.

(** Decide whether a tailcall is possible. *)

Definition tailcall_is_possible (sg: signature) : bool :=
  List.forallb
    (fun l => match l with R _ => true | S _ _ _ => false end)
    (regs_of_rpairs (loc_arguments sg)).

Lemma tailcall_is_possible_correct:
  forall s, tailcall_is_possible s = true -> tailcall_possible s.
Proof.
  unfold tailcall_is_possible; intros. rewrite forallb_forall in H.
  red; intros. apply H in H0. destruct l; [auto|discriminate].
Qed.

Lemma zero_size_arguments_tailcall_possible:
  forall sg, size_arguments sg = 0 -> tailcall_possible sg.
Proof.
  intros; red; intros. exploit loc_arguments_acceptable_2; eauto.
  unfold loc_argument_acceptable.
  destruct l; intros. auto. destruct sl; try contradiction. destruct H1.
  generalize (loc_arguments_bounded _ _ _ H0).
  generalize (typesize_pos ty). omega.
Qed.

(** * Calling convention *)

Require Import LanguageInterface.
Require Import String.
Require Import Values.
Require Import Memory.

(** Languages with [locset]s (currently LTL and Linear) use the
  following interface and calling convention. *)

Record locset_query :=
  lq {
    lq_id: string;
    lq_rs: Locmap.t;
    lq_mem: mem;
  }.

Canonical Structure li_locset: language_interface :=
  {|
    query := locset_query;
    reply := Locmap.t * mem;
    dummy_query := (lq EmptyString (Locmap.init Vundef) Mem.empty);
  |}.

(** We now define the calling convention between C and locset languages. *)

Definition callee_save_loc (l: loc) :=
  match l with
  | R r => is_callee_save r = true
  | S sl ofs ty => sl <> Outgoing
  end.

Definition agree_callee_save (ls1 ls2: Locmap.t) : Prop :=
  forall l, callee_save_loc l -> ls1 l = ls2 l.

Program Definition cc_locset: callconv li_c li_locset :=
  {|
    world_def := unit;
    dummy_world_def := tt;
    match_senv w := eq;
    match_query_def w :=
      fun '(cq id1 sg args m1) '(lq id2 rs m2) =>
        id1 = id2 /\
        args = map (fun p => Locmap.getpair p rs) (loc_arguments sg) /\
        m1 = m2;
    match_reply_def w :=
      fun '(cq _ sg _ _) '(lq _ rs _) '(res, m1) '(rs', m2) =>
        agree_callee_save rs rs' /\
        Locmap.getpair (map_rpair R (loc_result sg)) rs' = res /\
        m1 = m2;
  |}.

Notation ls_id w := (cq_id (world_q1 w)).
Notation ls_sg w := (cq_sg (world_q1 w)).
Notation ls_args w := (cq_args (world_q1 w)).
Notation ls_rs w := (lq_rs (world_q2 w)).
Notation ls_mem w := (cq_mem (world_q1 w)).

Lemma match_query_cc_locset (P: _->_->_->_->_->_->_-> Prop):
  (forall id sg args rs m,
   args = map (fun p => Locmap.getpair p rs) (loc_arguments sg) ->
   P id sg args rs m (cq id sg args m) (lq id rs m)) ->
  (forall w q1 q2, match_query cc_locset w q1 q2 ->
   P (ls_id w) (ls_sg w) (ls_args w) (ls_rs w) (ls_mem w) q1 q2).
Proof.
  intros H w q1 q2 Hq.
  destruct Hq as [w q1 q2 Hq].
  destruct q1 as [id1 sg args m1], q2 as [id2 rs m2].
  destruct Hq as (Hid & Hargs & Hm).
  simpl in *; subst.
  eauto.
Qed.

Lemma match_reply_cc_locset w vres rs' m':
  agree_callee_save (ls_rs w) rs' ->
  Locmap.getpair (map_rpair R (loc_result (ls_sg w))) rs' = vres ->
  match_reply cc_locset w (vres, m') (rs', m').
Proof.
  intros H.
  destruct w as [w q1 q2 Hq].
  destruct q1 as [id1 sg1 vargs m1], q2 as [id2 rs m2].
  destruct Hq as (Hid & Hargs & Hm).
  simpl in *.
  constructor. split; eauto.
Qed.

Ltac inv_locset_query :=
  let w := fresh "w" in
  let q1 := fresh "q1" in
  let q2 := fresh "q2" in
  let Hq := fresh "Hq" in
  intros w q1 q2 Hq;
  pattern (ls_id w), (ls_sg w), (ls_args w), (ls_rs w), (ls_mem w), q1, q2;
  revert w q1 q2 Hq;
  apply match_query_cc_locset.

(* XXX may be needed later
Lemma locmap_setpair_getpair p ls l:
  Val.lessdef
    (Locmap.get l (Locmap.setpair p (Locmap.getpair (map_rpair R p) ls) ls))
    (Locmap.get l ls).
Proof.
  unfold Locmap.setpair, Locmap.getpair.
  destruct p; simpl.
  - destruct (Loc.eq (R r) l); subst.
    + setoid_rewrite Locmap.gss; eauto.
    + setoid_rewrite Locmap.gso; eauto.
      simpl. destruct l; eauto; congruence.
  - destruct (Loc.eq (R rlo) l); subst.
    + setoid_rewrite Locmap.gss; eauto.
      apply val_loword_longofwords.
    + setoid_rewrite Locmap.gso; eauto.
      * destruct (Loc.eq (R rhi) l); subst.
        setoid_rewrite Locmap.gss. apply val_hiword_longofwords.
        setoid_rewrite Locmap.gso; eauto. destruct l; simpl; eauto; congruence.
      * destruct l; simpl; eauto; congruence.
Qed.
*)
