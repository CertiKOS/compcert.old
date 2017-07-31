(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                  Xavier Leroy, INRIA Paris                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86-64 generation: main proof. *)

Require Import Coqlib Errors.
Require Import Integers Floats AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Locations Mach Conventions Asm.
Require Import Asmgen Asmgenproof0 Asmgenproof1.

Definition match_prog (p: Mach.program) (tp: Asm.program) :=
  match_program (fun _ f tf => transf_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transf_program p = OK tp -> match_prog p tp.
Proof.
  intros. eapply match_transform_partial_program; eauto.
Qed.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls (injperm:= inject_perm_all)}.

Local Existing Instance mem_accessors_default.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

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
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf,
  Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = OK tf.
Proof (Genv.find_funct_ptr_transf_partial TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto.
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z (fn_code tf) <= Ptrofs.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); monadInv EQ0.
  omega.
Qed.

Lemma exec_straight_exec:
  forall fb f c ep tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
Qed.

Lemma exec_straight_at:
  forall fb f c ep tf tc c' ep' tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c ep tf tc ->
  transl_code f c' ep' = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' ep' tf tc'.
Proof.
  intros. inv H.
  exploit exec_straight_steps_2; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros.
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shrximm_label:
  forall n k c, mk_shrximm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_shrxlimm_label:
  forall n k c, mk_shrxlimm n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H. destruct (Int.eq n Int.zero); TailNoLabel.
Qed.
Hint Resolve mk_shrxlimm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c ->
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel.
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_storebyte_label:
  forall addr r k c, mk_storebyte addr r k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_storebyte; intros. TailNoLabel.
Qed.
Hint Resolve mk_storebyte_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty; try discriminate; destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty; try discriminate; destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_base_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc_base xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd RAX); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. unfold mk_setcc. destruct (Archi.ptr64 || low_ireg rd).
  apply mk_setcc_base_label.
  eapply tail_nolabel_trans. apply mk_setcc_base_label. TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec n Int.zero); TailNoLabel.
  destruct (Int64.eq_dec n Int64.zero); TailNoLabel.
  destruct (Float.eq_dec n Float.zero); TailNoLabel.
  destruct (Float32.eq_dec n Float32.zero); TailNoLabel.
  destruct (normalize_addrmode_64 x) as [am' [delta|]]; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i ep k c,
  transl_instr f i ep k = OK c ->
  match i with Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; eauto.
  eapply storeind_label; eauto.
  eapply loadind_label; eauto.
  eapply tail_nolabel_trans; eapply loadind_label; eauto.
  eapply transl_op_label; eauto.
  eapply transl_load_label; eauto.
  eapply transl_store_label; eauto.
  destruct s0; TailNoLabel.
  destruct s0; TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_jcc_label.
Qed.

Lemma transl_instr_label':
  forall lbl f i ep k c,
  transl_instr f i ep k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B).
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c ep tc,
  transl_code f c ep = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' false = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a).
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf.(fn_code) = None
  | Some c => exists tc, find_label lbl tf.(fn_code) = Some tc /\ transl_code f c false = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. simpl. eapply transl_code_label; eauto. rewrite transl_code'_transl_code in EQ0; eauto.
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tge tf lbl rs m = Next rs' m
  /\ transl_code_at_pc ge (rs' PC) b f c' false tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2.
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Ptrofs.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. erewrite functions_transl; eauto. 
  split. rewrite Pregmap.gss. constructor; auto.
  rewrite Ptrofs.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto.
- intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x))); inv EQ0.
  monadInv EQ. rewrite transl_code'_transl_code in EQ0.
  exists x; exists true; split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Section WITHINITSPRA.

  Variables init_sp init_ra: val.

  Definition match_stackframe_frame_adt s (f: option frame_adt * Z):=
    match s, f with
      Stackframe fn sp _ _, (Some (frame_with_info stk (Some fi)), n) =>
      stk = sp /\ n = frame_size fi /\
      forall f, Genv.find_funct_ptr ge fn = Some (Internal f) ->
           frame_size fi = Mach.fn_stacksize f /\
           seg_ofs (frame_link fi) = Ptrofs.unsigned (fn_link_ofs f) /\
           seg_ofs (frame_retaddr fi) = Ptrofs.unsigned (fn_retaddr_ofs f)
    | _, _ => False
    end.

  Definition ms_init (f: option frame_adt * Z) :=
    forall b o, init_sp = Vptr b o ->
           match f with
             (Some (frame_with_info stk _),n) =>
             b = stk
           | _ => False
           end.

  Definition ms_nil :=
    forall b o, init_sp = Vptr b o -> False.
  
  Inductive list_prefix {A B} (P: A -> B -> Prop) (Pinit : B -> Prop) (Pnil: Prop): list A -> list B -> Prop :=
  | lp_intro (PNIL: Pnil):
      list_prefix P Pinit Pnil nil nil
  | lp_intro_init_sp a r (PINIT: Pinit a):
      list_prefix P Pinit Pnil nil (a::r)
  | lp_cons a b l1 l2
            (LPrec: list_prefix P Pinit Pnil l1 l2)
            (PAB: P a b):
      list_prefix P Pinit Pnil (a::l1) (b::l2).
  
 Inductive match_states: Mach.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c ep ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c ep tf tc)
        (AG: agree ms (Vptr sp Ptrofs.zero) rs)
        (AXP: ep = true -> rs#RAX = parent_sp init_sp s)
        (MATCHFRAMES: list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb sp (Vptr sp Ptrofs.zero) c :: s) (Mem.stack_adt m)),
      match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp init_sp s) rs)
        (ATPC: rs PC = Vptr fb Ptrofs.zero)
        (ATLR: rs RA = parent_ra init_ra s)
        (MATCHFRAMES: list_prefix match_stackframe_frame_adt ms_init ms_nil s (Mem.stack_adt m)),
      match_states (Mach.Callstate s fb ms m)
                   (Asm.State rs m')
  | match_states_return:
      forall s ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms (parent_sp init_sp s) rs)
        (RA_VUNDEF: rs RA = Vundef)
        (ATPC: rs PC = parent_ra init_ra s)
        (MATCHFRAMES: list_prefix match_stackframe_frame_adt ms_init ms_nil s (Mem.stack_adt m)),
      match_states (Mach.Returnstate s ms m)
                   (Asm.State rs m').

Lemma exec_straight_steps:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 (Vptr sp Ptrofs.zero) rs2
    /\ (it1_is_parent ep i = true -> rs2#RAX = parent_sp init_sp s)) ->
  forall LF2: list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb sp (Vptr sp Ptrofs.zero) c :: s) (Mem.stack_adt m2),
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7.
  exploit H3; eauto. intros [rs2 [A [B C]]].
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto.
  econstructor; eauto. eapply exec_straight_at; eauto.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) ep tf tc ->
  it1_is_parent ep i = false ->
  (forall k c (TR: transl_instr f i ep k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 (Vptr sp Ptrofs.zero) rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tge tf lbl rs2 m2') ->
  forall LF2:   list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb sp (Vptr sp Ptrofs.zero) c' :: s) (Mem.stack_adt m2),
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach.State s fb (Vptr sp Ptrofs.zero) c' ms2 m2) st'.
Proof.
  intros s fb f rs1 i c ep tf tc m1' m2 m2' sp ms2 lbl c' H H0 H1 H2 H3 H4 H5.
  inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto.
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto.
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto.
  econstructor; eauto.
  eapply find_instr_tail. eauto.
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  congruence.
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach.state) : nat :=
  match s with
  | Mach.State _ _ _ _ _ _ => 0%nat
  | Mach.Callstate _ _ _ _ => 0%nat
  | Mach.Returnstate _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Hypothesis init_sp_not_vundef: init_sp <> Vundef.
Hypothesis init_ra_not_vundef: init_ra <> Vundef.

Hypothesis init_sp_type: Val.has_type init_sp Tptr.
Hypothesis init_ra_type: Val.has_type init_ra Tptr.

Hypothesis init_sp_ofs_zero:
  forall b o, init_sp = Vptr b o -> o = Ptrofs.zero.

Hypothesis frame_size_correct:
  forall fb f,
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    frame_size (Mach.fn_frame f) = fn_stacksize f /\
    Ptrofs.unsigned (fn_link_ofs f) = (seg_ofs (frame_link (Mach.fn_frame f))) /\
    Ptrofs.unsigned (fn_retaddr_ofs f) = (seg_ofs (frame_retaddr (Mach.fn_frame f))).

Lemma agree_undef_regs_parallel:
  forall l sp rs rs0,
    agree rs sp rs0 ->
    agree (Mach.undef_regs l rs) sp
    (undef_regs preg_of ## l rs0).
Proof.
  intros; eapply agree_undef_regs; eauto.
  intros. 
  rewrite undef_regs_other; auto.
  intros. intro; subst.
  rewrite preg_notin_charact  in H1.
  rewrite in_map_iff in H2.
  destruct H2 as (x & EQ & IN).
  apply H1 in IN.
  congruence.
Qed.


Lemma msfa_ext_code:
  forall fb sp ra c ra' c' s l,
    list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb sp ra c :: s) l ->
    list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb sp ra' c' :: s) l.
Proof.
  inversion 1; constructor; auto.
Qed.

Inductive asm_no_none: state -> Prop :=
| ann_intro:
    forall rs m
      (NONONE: Forall (fun x => match x with
                               (None,n) => False
                             |  _ => True
                             end) (Mem.stack_adt m)),
      asm_no_none (State rs m).

  Lemma exec_store_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2,
      exec_store ge k m1 a rs1 rs l = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1.
  Proof.
    intros.
    unfold exec_store in H; repeat destr_in H.
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite Mem.store_stack_blocks. 2: eauto.
    split; auto.
  Qed.

  Lemma exec_load_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2,
      exec_load ge k m1 a rs1 rs = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1.
  Proof.
    intros.
    unfold exec_load in H; destr_in H.
  Qed.

  Lemma goto_label_stack:
    forall F V (ge: _ F V) f l m1 rs1 rs2 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1.
  Proof.
    intros.
    unfold goto_label in H; repeat destr_in H.
  Qed.

  Lemma step_asm_no_none:
    forall s1 t s2,
      step tge s1 t s2 ->
      asm_no_none s1 ->
      asm_no_none s2.
  Proof.
    inversion 1.
    - subst. inversion 1; constructor.
      destruct i; simpl in H3; inv H3;
        first [ assumption
              | now (erewrite exec_load_stack; eauto)
              | now (erewrite exec_store_stack; eauto)
              | now (repeat destr_in H8; erewrite goto_label_stack; eauto)
              | now (repeat destr_in H8)
              | idtac ].
      + repeat destr_in H8.
        erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
        erewrite Mem.store_stack_blocks. 2: eauto.
        erewrite Mem.store_stack_blocks. 2: eauto.
        erewrite Mem.alloc_stack_blocks; eauto.
      + repeat destr_in H8.
        erewrite <- Mem.free_stack_blocks in NONONE. 2: eauto.
        destruct (Mem.unrecord_stack_adt _ _ Heqo2) as (bb & EQ).
        rewrite EQ in NONONE. inv NONONE; auto.
    - subst. inversion 1; subst; constructor.
      erewrite <- external_call_stack_blocks; eauto.
    - subst. inversion 1; subst; constructor.
      erewrite <- external_call_stack_blocks; eauto.
  Qed.

  Lemma if_zeq:
    forall {T} a P (A B : T),
      (if zeq a a && P then A else B) = if P then A else B.
  Proof.
    intros.
    destruct zeq; try congruence. simpl; reflexivity.
  Qed.

  Lemma if_zeq':
    forall {T} a (A B : T),
      (if proj_sumbool (zeq a a) then A else B) = A.
  Proof.
    intros.
    destruct zeq; simpl; try congruence. 
  Qed.

  Lemma if_peq:
    forall {T} a P (A B : T),
      (if peq a a && P then A else B) = if P then A else B.
  Proof.
    intros.
    destruct peq; try congruence. simpl; reflexivity.
  Qed.

  Lemma check_top_frame_ok:
    forall fb stk ra c s m m' f ,
      list_prefix match_stackframe_frame_adt ms_init ms_nil (Stackframe fb stk ra c :: s) (Mem.stack_adt m) ->
      Forall (fun x => match x with
                      (Some _, _) => True
                    | (None, _) => False
                    end) (Mem.stack_adt m') ->
      Mem.extends m m' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      (forall b o, init_sp = Vptr b o -> o = Ptrofs.zero) ->
      check_top_frame m' stk (fn_stacksize f) (parent_sp init_sp s) (f.(fn_link_ofs)) (f.(fn_retaddr_ofs)) = true.
  Proof.
    clear - memory_model_prf init_sp_not_vundef.
    unfold check_top_frame.
    intros fb stk ra c s m m' f MATCHFRAMES NONONE MEXT FIND PTRZERO.
    inv MATCHFRAMES.
    generalize (Mem.extends_stack_adt _ _ MEXT).
    rewrite <- H. intro A; inv A.
    rewrite <- H2 in NONONE. inv NONONE.
    destruct b1; simpl in *. destruct o; try easy.
    destruct b; simpl in *.
    destruct o; try easy. destruct f1; try easy. 
    destruct o; try easy.
    Ltac clean:=
      repeat match goal with
               H : _ /\ _ |- _ => destruct H; subst
             | H: True |- _ => clear H
             end.
    clean.
    inv H0.
    generalize (INJ _ _ eq_refl). intros; subst.
    specialize (H3 _ FIND).
    destruct H3 as (SEQ & LEQ & REQ).
    rewrite SEQ, LEQ, REQ.
    rewrite <- ! andb_assoc.
    rewrite if_peq, ! if_zeq, if_zeq'.
    inv H4; inv H6. inv LPrec. simpl. destruct (init_sp) eqn:?; auto.
    edestruct PNIL; eauto.
    destruct b1; simpl in *.
    destruct o; try easy.
    destruct a1; simpl in *.
    destruct o; try easy.
    clean.
    inv LPrec. simpl; auto. destruct init_sp eqn:?; auto.
    red in PINIT. rewrite Heqv in PINIT. 
    specialize (PINIT _ _ eq_refl).
    destruct f2; try easy. inv H0.
    specialize (PTRZERO _ _ eq_refl). subst.
    destruct (peq b0 b2). simpl. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); try discriminate. simpl. auto. congruence.
    exfalso; apply n. eapply FB0. reflexivity.
    specialize (PTRZERO _ _ eq_refl). subst.
    destruct (peq b0 b2). simpl. destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); try discriminate. simpl. auto. congruence.
    exfalso; apply n. eapply INJ0. reflexivity. auto.
    simpl.
    red in PAB.
    destruct a.
    destruct f2; try easy.
    destruct o; try easy.
    destruct PAB as (? & ? & PAB). subst.
    inv H0. simpl.
    erewrite <- INJ0. 2: reflexivity.
    rewrite if_peq.
    destruct (Ptrofs.eq_dec Ptrofs.zero Ptrofs.zero); try discriminate. simpl. auto. congruence.
  Qed.

  
Theorem step_simulation:
  forall S1 t S2, Mach.step init_sp init_ra return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1') (ANN: asm_no_none S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS; inv ANN.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros.
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto.
  split. apply agree_nextinstr; auto. simpl; congruence.
  eapply msfa_ext_code; eauto.

- (* Mgetstack *)
  unfold load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  split. eapply agree_set_mreg; eauto. congruence.
  simpl; congruence.
  eapply msfa_ext_code; eauto.
  
- (* Msetstack *)
  unfold store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]].
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto.

  intros [rs' [P Q]].
  exists rs'; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; intros. rewrite Q; auto with asmgen.
Local Transparent destroyed_by_setstack.
  destruct ty; simpl; intuition congruence.
  eapply msfa_ext_code; eauto.
  unfold Mem.storev in H; destr_in H. 
  erewrite Mem.store_no_abstract; eauto.
  
- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H0. auto.
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit (lessdef_parent_sp init_sp); eauto. clear B; intros B; subst parent'.
  exploit Mem.loadv_extends. eauto. eexact H1. auto.
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros.
  assert (DIFF: negb (mreg_eq dst AX) = true -> IR RAX <> preg_of dst).
    intros. change (IR RAX) with (preg_of AX). red; intros.
    unfold proj_sumbool in H1. destruct (mreg_eq dst AX); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR.
(* RAX contains parent *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). rewrite AXP; eauto.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite R; auto.
(* RAX does not contain parent *)
  monadInv TR.
  exploit loadind_correct. eexact EQ0. eauto. intros [rs1 [P [Q R]]]. simpl in Q.
  exploit loadind_correct. eexact EQ. instantiate (2 := rs1). rewrite Q. eauto.
  intros [rs2 [S [T U]]].
  exists rs2; split. eapply exec_straight_trans; eauto.
  split. eapply agree_set_mreg. eapply agree_set_mreg; eauto. congruence. auto.
  simpl; intros. rewrite U; auto.
  eapply msfa_ext_code; eauto.

- (* Mop *)
  assert (eval_operation tge (Vptr sp0 Ptrofs.zero) op rs##args m = Some v).
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]].
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto.
  simpl; congruence.
  eapply msfa_ext_code; eauto.

- (* Mload *)
  assert (eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]].
  exists rs2; split. eauto.
  split. eapply agree_set_undef_mreg; eauto. congruence.
  simpl; congruence.
  eapply msfa_ext_code; eauto.

- (* Mstore *)
  assert (eval_addressing tge (Vptr sp0 Ptrofs.zero) addr rs##args = Some a).
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR.
  exploit transl_store_correct; eauto. intros [rs2 [P Q]].
  exists rs2; split. eauto.
  split. eapply agree_undef_regs; eauto.
  simpl; congruence.
  eapply msfa_ext_code; eauto.
  unfold Mem.storev in H0; destr_in H0.
  erewrite Mem.store_no_abstract; eauto.

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H5.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H5; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.
  eapply msfa_ext_code; eauto.
(* simpl. rewrite FIND. auto. *)
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H6). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Ptrofs.add ofs Ptrofs.one)) fb f c false tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. eauto.
  econstructor; eauto.
  econstructor; eauto.
  simpl. eapply agree_exten; eauto. intros. Simplifs.
  Simplifs. rewrite <- H2. auto.
  eapply msfa_ext_code; eauto.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [parent' [A B]].
  exploit Mem.loadv_extends. eauto. eexact H2. auto. simpl. intros [ra' [C D]].
  exploit (lessdef_parent_sp init_sp); eauto. intros. subst parent'. clear B.
  exploit (lessdef_parent_ra init_ra); eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. constructor. intros (m2_ & E & F).
  exploit Mem.unrecord_stack_block_extends; eauto. intros (m2' & G & I).
  destruct ros as [rf|fid]; simpl in H; monadInv H8.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Ptrofs.zero).
    destruct (rs rf); try discriminate.
    revert H; predSpec Ptrofs.eq Ptrofs.eq_spec i Ptrofs.zero; intros; congruence.
  assert (rs0 x0 = Vptr f' Ptrofs.zero).
    exploit ireg_val; eauto. rewrite H8; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG).
  rewrite Ptrofs.unsigned_zero in E. simpl in E.

  (* Ltac rewrites H := *)
  (*   let H' := fresh in *)
  (*   generalize H; intro H'; *)
  (*   repeat match type of H' with *)
  (*          | @eq _ _ _ => rewrite H' *)
  (*          | ?a /\ ?b => *)
  (*            let H1 := fresh in *)
  (*            let H2 := fresh in *)
  (*            destruct H' as (H1 & H2); rewrites H1; rewrites H2 *)
  (*          | ?a : Type -> _ => *)
  (*            let x:=fresh "x" in *)
  (*            evar (x:a); specialize (H' x) *)
  (*          | ?a -> _ => *)
  (*            let x:=fresh "x" in *)
  (*            cut (a);[intro x; specialize (H' x); clear x| clear H'] *)
  (*          end. *)
  generalize (frame_size_correct _ _ FIND). intros (SEQ & LEQ & REQ).
  rewrite SEQ.
  rewrite E. rewrite G. 
  erewrite check_top_frame_ok; eauto.
  apply star_one. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H5. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  eapply parent_sp_type; eauto.
  Simplifs. rewrite Pregmap.gso; auto.
  generalize (preg_of_not_SP rf). rewrite (ireg_of_eq _ _ EQ1). congruence.
  edestruct Mem.unrecord_stack_adt as (b0 & EQ'). apply H4.
  erewrite Mem.free_stack_blocks in EQ'. 2: eauto.
  rewrite EQ' in MATCHFRAMES; inv MATCHFRAMES; auto.

+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H9). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG).
  rewrite Ptrofs.unsigned_zero in E. simpl in E.
  generalize (frame_size_correct _ _ FIND). intros (SEQ & LEQ & REQ).
  rewrite SEQ.
  rewrite E. rewrite G.
  erewrite check_top_frame_ok; eauto.
  apply star_one. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H5. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  econstructor; eauto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  eapply parent_sp_type; eauto.
  rewrite Pregmap.gss. unfold Genv.symbol_address. rewrite symbols_preserved. rewrite H. auto.
  edestruct Mem.unrecord_stack_adt as (b0 & EQ'). apply H4.
  erewrite Mem.free_stack_blocks in EQ'. 2: eauto.
  rewrite EQ' in MATCHFRAMES; inv MATCHFRAMES; auto.
  
- (* Mbuiltin *)
  inv AT. monadInv H4.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit builtin_args_match; eauto. intros [vargs' [P Q]].
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one.
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite <- sp_val by eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved. auto.
  clear. induction res; simpl; intros; eauto. intro; subst.
  eapply preg_of_not_SP in H. congruence.
  eauto.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  rewrite undef_regs_other. rewrite set_res_other. rewrite undef_regs_other_2.
  rewrite <- H1. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  rewrite preg_notin_charact. intros. auto with asmgen.
  auto with asmgen.
  simpl; intros. intuition congruence.
  apply agree_nextinstr_nf. eapply agree_set_res; auto.
  eapply agree_undef_regs; eauto. intros; apply undef_regs_other_2; auto.
  congruence.
  eapply msfa_ext_code; eauto.
  erewrite <- external_call_stack_blocks; eauto.
- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4.
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.
  congruence.
  eapply msfa_ext_code; eauto.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A.
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst.
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten; eauto.
  simpl. rewrite TC1; rewrite TC2; auto.
  eapply msfa_ext_code; eauto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]].
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl. rewrite B. eauto. auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A.
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  split. apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten; eauto.
  simpl; congruence.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A.
  apply exec_straight_one. simpl.
  rewrite TC1; rewrite TC2.
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  split. apply agree_nextinstr. eapply agree_exten; eauto.
  rewrite H1; congruence.
  eapply msfa_ext_code; eauto.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6.
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  set (rs1 := rs0 #RAX <- Vundef #RDX <- Vundef).
  exploit (find_label_goto_label f tf lbl rs1); eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  eapply find_instr_tail; eauto.
  simpl. rewrite <- H9.  unfold Mach.label in H0; unfold label; rewrite H0. eexact A.
  econstructor; eauto.
Transparent destroyed_by_jumptable.
  apply agree_undef_regs with rs0; auto. 
  simpl; intros. destruct H8. rewrite C by auto with asmgen. unfold rs1; Simplifs.
  congruence.
  eapply msfa_ext_code; eauto.
  
- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT.
  assert (NOOV: list_length_z tf.(fn_code) <= Ptrofs.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. unfold load_stack in *.
  replace (chunk_of_type Tptr) with Mptr in * by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  exploit Mem.loadv_extends. eauto. eexact H0. auto. simpl. intros [parent' [A B]].
  exploit (lessdef_parent_sp init_sp); eauto. intros. subst parent'. clear B.
  exploit Mem.loadv_extends. eauto. eexact H1. auto. simpl. intros [ra' [C D]].
  exploit (lessdef_parent_ra init_ra); eauto. intros. subst ra'. clear D.
  exploit Mem.free_parallel_extends; eauto. constructor. intros (m2' & E & F).
  exploit Mem.unrecord_stack_block_extends; eauto. intros (m2'' & G & I).
  monadInv H7.
  exploit code_tail_next_int; eauto. intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. rewrite C. rewrite A. rewrite <- (sp_val _ _ _ AG).
  rewrite Ptrofs.unsigned_zero in E; simpl in E.
  generalize (frame_size_correct _ _ FIND). intros (SEQ & LEQ & REQ).
  rewrite SEQ.
  rewrite  E, G; eauto.
  erewrite check_top_frame_ok; eauto.
  apply star_one. eapply exec_step_internal.
  transitivity (Val.offset_ptr rs0#PC Ptrofs.one). auto. rewrite <- H4. simpl. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. eauto. traceEq.
  constructor; auto.
  apply agree_set_other; auto.
  apply agree_set_other; auto. apply agree_nextinstr. apply agree_set_other; auto.
  eapply agree_change_sp; eauto. eapply parent_sp_def; eauto.
  eapply parent_sp_type; eauto.
  edestruct Mem.unrecord_stack_adt as (b0 & EQ'). apply H3.
  erewrite Mem.free_stack_blocks in EQ'. 2: eauto.
  rewrite EQ' in MATCHFRAMES; inv MATCHFRAMES; auto.
  
- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (fn_code x0))); inv EQ1.
  monadInv EQ0. rewrite transl_code'_transl_code in EQ1.
  unfold store_stack in *.
  exploit Mem.alloc_extends. eauto. eauto. apply Zle_refl. apply Zle_refl.
  intros [m1' [C D]].
  exploit Mem.storev_extends. eexact D. eexact H2. eauto. eauto.
  intros [m2' [F G]].
  exploit Mem.storev_extends. eexact G. eexact H3. eauto. eauto.
  intros [m3' [P Q]].
  exploit Mem.record_stack_blocks_extends.
  apply Q. eauto.
  {
    simpl. intros; subst.
    erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
    erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
    erewrite Mem.alloc_stack_blocks; eauto. intro INF. apply Mem.in_frames_valid in INF.
    eapply Mem.fresh_block_alloc in INF; eauto.
  }
  intros (m1'' & CC & DD).
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  simpl. rewrite Ptrofs.unsigned_zero. simpl. eauto.
  simpl.
  generalize (frame_size_correct _ _ H). intros (SEQ & LEQ & REQ).
  rewrite SEQ.
  rewrite C. simpl in F, P.
  replace (chunk_of_type Tptr) with Mptr in F, P by (unfold Tptr, Mptr; destruct Archi.ptr64; auto).
  rewrite (sp_val _ _ _ AG) in F. rewrite F.
  rewrite ATLR. rewrite P.
  assert (check_alloc_frame (Mach.fn_frame f) (fn_link_ofs f) (fn_retaddr_ofs f) = true).
  {
    unfold check_alloc_frame. simpl.
    revert H0.
    unfold Mach.check_alloc_frame. simpl. auto.
  }
  rewrite H5.
  rewrite CC.
  eauto.
  econstructor; eauto.
  unfold nextinstr. rewrite Pregmap.gss. repeat rewrite Pregmap.gso; auto with asmgen.
  rewrite ATPC. simpl. constructor; eauto.
  unfold fn_code. eapply code_tail_next_int. simpl in g. omega.
  constructor.
  apply agree_nextinstr. eapply agree_change_sp; eauto.
Transparent destroyed_at_function_entry.
  apply agree_undef_regs with rs0; eauto.
  simpl; intros. apply Pregmap.gso; auto with asmgen. tauto.
  congruence.
  constructor.
  intros. Simplifs. eapply agree_sp; eauto.
  unfold Mem.storev in H4, H3. destr_in H4. destr_in H3.
  erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
  constructor; auto.
  erewrite Mem.store_stack_blocks. 2: eauto.
  erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
  erewrite Mem.alloc_stack_blocks. 2: eauto.
  auto.
  generalize (frame_size_correct _ _ H). intros (SEQ & LEQ & REQ).
  constructor; auto.
  split; auto.
  rewrite H. inversion 1. subst. eauto.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match; eauto.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto.
  
  { (* rs SP Tint *)
    erewrite agree_sp by eauto.
    eapply parent_sp_type; eauto.
  }
  { (* rs RA Tint *)
    rewrite ATLR.
    eapply parent_ra_type; eauto.
  }
  { (* rs SP not Vundef *)
    erewrite agree_sp by eauto.
    eapply parent_sp_def; eauto.
  }
  { (* rs RA not Vundef *)
    rewrite ATLR.
    eapply parent_ra_def; eauto.
  }
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  unfold loc_external_result.
  clear. destruct (loc_result (ef_sig ef)); simpl; try split;
  apply preg_of_not_SP.
  auto.
  econstructor; eauto.
  unfold loc_external_result.
  apply agree_set_other; auto.
  apply agree_set_other; auto. apply agree_set_pair; auto.
  apply agree_undef_nondata_regs.
  apply agree_undef_regs_parallel; auto.
  simpl; intros; intuition subst; reflexivity.
  erewrite <- external_call_stack_blocks; eauto.
- (* return *)
  inv STACKS. simpl in *.
  right. split. omega. split. auto.
  econstructor; eauto. rewrite ATPC; eauto. congruence.
  eapply msfa_ext_code; eauto.
Qed.

End WITHINITSPRA.

Let match_states v1 v2 s1 s2 :=
  match_states v1 v2 s1 s2 /\ asm_no_none s2.

Lemma transf_initial_states:
  forall st1, Mach.initial_state prog st1 ->
  exists st2, Asm.initial_state tprog st2 /\ match_states Vnullptr Vnullptr st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  replace (Genv.symbol_address (Genv.globalenv tprog) (prog_main tprog) Ptrofs.zero)
    with (Vptr fb Ptrofs.zero).
  econstructor; eauto.
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  split. reflexivity. simpl. 
  unfold Vnullptr; destruct Archi.ptr64; congruence.
  eapply parent_sp_type. apply Val.Vnullptr_has_type. constructor.
  intros. rewrite Regmap.gi. auto.
  destruct (Mem.stack_adt m0). constructor.
  red; intros. inv H3.
  constructor. red; simpl; intros. inv H3.
  econstructor. erewrite Genv.init_mem_stack_adt; eauto. 
  unfold Genv.symbol_address.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved.
  unfold ge; rewrite H1. auto.
  Unshelve. eauto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states Vnullptr Vnullptr st1 st2 -> Mach.final_state st1 r -> Asm.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H0. constructor. auto.
  assert (r0 = AX).
  { unfold loc_result in H1; destruct Archi.ptr64; compute in H1; congruence. }
  subst r0.
  generalize (preg_val _ _ _ AX AG). rewrite H2. intros LD; inv LD. auto.
Qed.

Hypothesis frame_correct:
  forall (fb : block) (f : Mach.function),
    Genv.find_funct_ptr ge fb = Some (Internal f) ->
    frame_size (Mach.fn_frame f) = fn_stacksize f /\
    Ptrofs.unsigned (fn_link_ofs f) = (seg_ofs (frame_link (Mach.fn_frame f))) /\
    Ptrofs.unsigned (fn_retaddr_ofs f) = (seg_ofs (frame_retaddr (Mach.fn_frame f))).

Lemma star_preserves {G S} g (sstep: G -> S -> trace -> S -> Prop) (P: S -> Prop):
  (forall s t s', sstep g s t s' -> P s -> P s') ->
  forall s t s' , star sstep g s t s' -> P s -> P s'.
Proof.
  induction 2; simpl; intros; eauto.
Qed.

Lemma plus_preserves {G S} g (sstep: G -> S -> trace -> S -> Prop) (P: S -> Prop):
  (forall s t s', sstep g s t s' -> P s -> P s') ->
  forall s t s' , plus sstep g s t s' -> P s -> P s'.
Proof.
  inversion 2. subst. intros. eapply star_preserves; eauto.
Qed.

Theorem transf_program_correct:
  forward_simulation (Mach.semantics return_address_offset prog) (Asm.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  intros. inv H0.
  eapply step_simulation in H1; eauto.
  destruct H1 as [[s2' [PLUS MS]]|[MLT [ TE0  MS]]]; [left|right]; eauto.
  - eexists; split; eauto. constructor; auto.
    eapply plus_preserves.
    eapply step_asm_no_none; eauto. eauto.
    eauto.
  - split; auto. split; auto.
    constructor; auto.
  - unfold Vnullptr; destruct Archi.ptr64; congruence.
  - unfold Vnullptr; destruct Archi.ptr64; congruence.
  - apply Val.Vnullptr_has_type.
  - apply Val.Vnullptr_has_type.
  - inversion 1.
Qed.

End PRESERVATION.
