Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.
Require Asmgen.
Require Asmgenproof0.
Require Import Errors.

Section WITHMEMORYMODEL.

  Context {mem} `{memory_model: Mem.MemoryModel mem}.

  Existing Instance mem_accessors_default.

  Context `{external_calls_ops: !ExternalCallsOps mem}
          `{enable_builtins_instance: EnableBuiltins (memory_model_ops:=memory_model_ops) mem}.

  Definition is_unchanged (i: instruction) :=
    match i with
      Pallocframe _ _  
    | Pfreeframe _ _
    | Pload_parent_pointer _ _ => false
    | _ => true
    end.


  (** Instructions other than [Pallocframe] and [Pfreeframe] do not modify the
      content of the RSP register. We prove that Asm programs resulting from the
      Stacking pass satisfy this requirement. *)

  Definition asm_instr_no_rsp (i : Asm.instruction) : Prop :=
    is_unchanged i = true ->
    forall {F V} (ge: _ F V) rs1 m1 rs2 m2 f isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      rs2 # RSP = rs1 # RSP.

  Definition asm_code_no_rsp (c : Asm.code) : Prop :=
    forall i,
      In i c ->
      asm_instr_no_rsp i.

  Lemma asm_code_no_rsp_cons:
    forall a l,
      asm_instr_no_rsp a ->
      asm_code_no_rsp l ->
      asm_code_no_rsp (a::l).
  Proof.
    unfold asm_code_no_rsp.
    intros. simpl in H2. destruct H2; subst; auto.
  Qed.

  Lemma nextinstr_rsp:
    forall rs,
      nextinstr rs RSP = rs RSP.
  Proof.
    unfold nextinstr.
    intros; rewrite Pregmap.gso; congruence.
  Qed.

  Lemma nextinstr_nf_rsp:
    forall rs,
      nextinstr_nf rs RSP = rs RSP.
  Proof.
    unfold nextinstr_nf.
    intros. rewrite nextinstr_rsp.
    rewrite Asmgenproof0.undef_regs_other; auto.
    simpl; intuition subst; congruence. 
  Qed.

  Lemma preg_of_not_rsp:
    forall m x,
      preg_of m = x ->
      x <> RSP.
  Proof.
    unfold preg_of. intros; subst.
    destruct m; congruence.
  Qed.
  
  Lemma ireg_of_not_rsp:
    forall m x,
      Asmgen.ireg_of m = OK x ->
      IR x <> RSP.
  Proof.
    unfold Asmgen.ireg_of.
    intros m x A.
    destr_in A. inv A.
    eapply preg_of_not_rsp in Heqp.
    intro; subst. congruence.
  Qed.

  Lemma freg_of_not_rsp:
    forall m x,
      Asmgen.freg_of m = OK x ->
      FR x <> RSP.
  Proof.
    unfold Asmgen.freg_of.
    intros m x A. destr_in A. 
  Qed.


  Lemma compare_floats_rsp:
    forall a b rs1,
      compare_floats a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma compare_floats32_rsp:
    forall a b rs1,
      compare_floats32 a b rs1 RSP = rs1 RSP.
  Proof.
    unfold compare_floats32.
    intros.
    destruct a, b; rewrite ?Asmgenproof0.undef_regs_other by simpl; intuition congruence.
  Qed.


  Lemma exec_load_rsp:
    forall F V (ge: _ F V) K m1 am rs1 f0 rs2 m2,
      IR RSP <> f0->
      exec_load ge K m1 am rs1 f0 = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 DIFF LOAD.
    unfold exec_load in LOAD. destr_in LOAD. inv LOAD.
    rewrite nextinstr_nf_rsp. 
    rewrite Pregmap.gso. auto. auto. 
  Qed.

  Lemma exec_store_rsp:
    forall F V (ge: _ F V)  K m1 am rs1 f0 rs2 m2 (l: list preg) , (* preg_of m = f0 -> *)
      (forall r' : PregEq.t, In r' l -> r' <> RSP) ->
      exec_store ge K m1 am rs1 f0 l = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    intros F V ge' K m1 am rs1 f0 rs2 m2 l INL STORE.
    unfold exec_store in STORE. repeat destr_in STORE.
    rewrite nextinstr_nf_rsp. 
    rewrite Asmgenproof0.undef_regs_other.
    auto. intros; apply not_eq_sym. auto.
  Qed.

  Ltac solve_rs:=
    repeat match goal with
             H2 : Next _ _ = Next _ _ |- _ =>
             inv H2
           | |- _ :preg <> RSP => eapply preg_of_not_rsp; eauto
           | |- _ :preg<> RSP => eapply ireg_of_not_rsp; eauto
           | |- _ :preg <> RSP => eapply freg_of_not_rsp; eauto
           | |- RSP <> _  => apply not_eq_sym
           | |- _ => rewrite ?nextinstr_nf_rsp, ?nextinstr_rsp, ?compare_floats_rsp, ?compare_floats32_rsp;
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply ireg_of_not_rsp; eauto);
                   try rewrite Pregmap.gso by (apply not_eq_sym; eapply freg_of_not_rsp; eauto);
                   try reflexivity

           end.

  Lemma loadind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      Asmgen.loadind r i t m x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold Asmgen.loadind in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl; intros; eapply exec_load_rsp; eauto;
      apply not_eq_sym; solve_rs.
  Qed.

  Lemma storeind_no_change_rsp:
    forall i t m x0 x1 r,
      asm_code_no_rsp x0 ->
      Asmgen.storeind m r i t x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros i t m x0 x1 r IH EQ.
    unfold Asmgen.storeind in EQ.
    repeat destr_in EQ; apply asm_code_no_rsp_cons; auto; red; simpl; intros; eapply exec_store_rsp; eauto; simpl;
      intuition subst; congruence.
  Qed.

  Lemma mk_move_nochange_rsp:
    forall x0 x1 m m0,
      asm_code_no_rsp x0 ->
      Asmgen.mk_mov (preg_of m) (preg_of m0) x0 = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    intros x0 x1 m m0 A B.
    unfold Asmgen.mk_mov in B; repeat destr_in B; apply asm_code_no_rsp_cons; auto; red; simpl; intros;
      inv H1; rewrite nextinstr_rsp;
        rewrite Pregmap.gso; auto;
          apply not_eq_sym; eapply preg_of_not_rsp; eauto.
  Qed.  
  
  
  Ltac invasm :=
    repeat match goal with
             H: bind _ ?x = OK ?x1 |- _ =>
             monadInv H
           | |- _ => apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs
           end.

  Lemma mkset_cc_no_rsp:
    forall x0 m x2 i c,
      asm_code_no_rsp x0 ->
      In i (Asmgen.mk_setcc c x2 x0) ->
      Asmgen.ireg_of m = OK x2 ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 m x2 i c A B C.
    unfold Asmgen.mk_setcc in B. destr_in B. 
    - destruct c. simpl in *.
      destruct B; subst; auto; red; intros; simpl in H1; solve_rs.
      simpl in B. destr_in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      simpl in B. destr_in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      simpl in B. destr_in B.
      red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
    - destruct c.
      simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      simpl in B.
      destruct B; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
      destruct H0; subst; auto. red. intros IU F V ge rs1 m1 rs2 m2 f isp EI; simpl in EI; solve_rs.
  Qed.

  Lemma asmgen_transl_cond_rsp:
    forall x0 m x2 x1 cond l,
      asm_code_no_rsp x0 ->
      Asmgen.ireg_of m = OK x2 ->
      Asmgen.transl_cond cond l (Asmgen.mk_setcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold Asmgen.transl_cond; simpl.
    intros x0 m x2 x1 cond l ACNR IREG TRANSL.
    repeat destr_in TRANSL.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm. eapply mkset_cc_no_rsp; eauto. 
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm;  eapply mkset_cc_no_rsp; eauto.
    invasm. destruct c; simpl in *; solve_rs. eapply mkset_cc_no_rsp; eauto.
    invasm. destruct c; simpl in *; solve_rs. eapply mkset_cc_no_rsp; eauto.
    invasm. destruct c; simpl in *; solve_rs. eapply mkset_cc_no_rsp; eauto.
    invasm. destruct c; simpl in *; solve_rs. eapply mkset_cc_no_rsp; eauto.
    invasm.  eapply mkset_cc_no_rsp; eauto.
    invasm.  eapply mkset_cc_no_rsp; eauto.
  Qed.

  Lemma goto_label_rsp:
    forall F V (ge: _ F V) rs1 rs2 f l m1 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      rs2 RSP = rs1 RSP.
  Proof.
    unfold goto_label.
    intros F V ge rs1 rs2 f l m1 m2 A.
    repeat destr_in A. solve_rs.
  Qed.

  Lemma mkjcc_no_rsp:
    forall x0 x2 i c,
      asm_code_no_rsp x0 ->
      In i (Asmgen.mk_jcc c x2 x0) ->
      asm_instr_no_rsp i.
  Proof.
    intros x0 x2 i c A H1.
    unfold Asmgen.mk_jcc in H1. destr_in H1.
    - destruct H1. subst.  red; simpl; intros.
      repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      intros. eapply A; eauto.
    - destruct H1. subst. red; simpl; intros.
      repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      destruct H0. subst.  red; simpl; intros.
      repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs.
      intros. eapply A; eauto.
    - destruct H1. subst.  red; simpl; intros.
      repeat destr_in H1. eapply goto_label_rsp; eauto. solve_rs. solve_rs.
      intros. eapply A. eauto. 
  Qed.
  
  Lemma asmgen_transl_cond_rsp':
    forall x0 x2 x1 cond l,
      asm_code_no_rsp x0 ->
      Asmgen.transl_cond cond l (Asmgen.mk_jcc (Asmgen.testcond_for_condition cond) x2 x0) = OK x1 ->
      asm_code_no_rsp x1.
  Proof.
    unfold Asmgen.transl_cond; simpl.
    intros x0 x2 x1 cond l ACNR TRANSL.
    repeat destr_in TRANSL.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. destruct c; simpl in *; solve_rs. eapply mkjcc_no_rsp; eauto. 
    invasm. destruct c; simpl in *; solve_rs. eapply mkjcc_no_rsp; eauto. 
    invasm. destruct c; simpl in *; solve_rs. eapply mkjcc_no_rsp; eauto. 
    invasm. destruct c; simpl in *; solve_rs. eapply mkjcc_no_rsp; eauto. 
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
    invasm. intuition subst; eauto. red; simpl; intros. repeat destr_in H1.
    eapply goto_label_rsp; eauto. solve_rs.
  Qed.
  
  Lemma asmgen_no_change_rsp:
    forall f tf,
      Asmgen.transf_function f = OK tf ->
      asm_code_no_rsp (Asm.fn_code tf).
  Proof.
    intros f tf TR.
    unfold Asmgen.transf_function in TR.
    monadInv TR.
    destr_in EQ0. inv EQ0.
    unfold Asmgen.transl_function in EQ.
    monadInv EQ. simpl.
    apply asm_code_no_rsp_cons. red; simpl. congruence.
    unfold Asmgen.transl_code' in EQ0.
    revert EQ0.
    set (P := fun f => forall x y, f x = OK y -> asm_code_no_rsp x -> asm_code_no_rsp y).
    assert (P (fun c => OK c)).
    { unfold P; simpl. inversion 1; tauto. }
    revert H0.
    generalize (Mach.fn_code f) true (fun c : code => OK c).
    clear g Heqs.
    induction c; simpl; intros; eauto.
    eapply H0; eauto. red; easy.
    eapply IHc. 2: apply EQ0.
    unfold P. intros. monadInv H1.
    eapply H0; eauto.
    destruct a; simpl in EQ.
    - eapply loadind_no_change_rsp; eauto. 
    - eapply storeind_no_change_rsp; eauto.
    - destr_in EQ.
      eapply loadind_no_change_rsp; eauto.
      monadInv EQ.
      eapply loadind_no_change_rsp in EQ2. 2: eauto.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      repeat destr_in H3; solve_rs.
    - unfold Asmgen.transl_op in EQ.
      repeat destr_in EQ.
      eapply mk_move_nochange_rsp; eauto.
      invasm.
      invasm.
      invasm.
      invasm.
      invasm.
      invasm.
      invasm.
      invasm.
      invasm.

      monadInv H3.
      unfold Asmgen.mk_intconv in EQ4.
      destr_in EQ4. inv EQ4.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.
      inv EQ4.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.


      monadInv H3.
      unfold Asmgen.mk_intconv in EQ4.
      destr_in EQ4. inv EQ4.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.
      inv EQ4.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.
      apply asm_code_no_rsp_cons; auto.
      red; simpl; intros.
      solve_rs.

      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs. solve_rs. solve_rs.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat destr_in H3. solve_rs.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      destr_in EQ1.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      repeat destr_in EQ1.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      repeat apply asm_code_no_rsp_cons; auto; red; simpl; intros; solve_rs.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      progress invasm.
      eapply asmgen_transl_cond_rsp; eauto.
    - unfold Asmgen.transl_load in EQ.
      invasm.
      destruct m; invasm; try (eapply exec_load_rsp; eauto); try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto. inv EQ3. inv EQ3.
    -
      unfold Asmgen.transl_store in EQ.
      invasm.
      destruct m; invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      unfold Asmgen.mk_storebyte in EQ4. repeat destr_in EQ4.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      invasm. intuition subst;
                red; intros; simpl in *; solve_rs.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      eapply H2; eauto.
      invasm. intuition subst;
                red; intros; simpl in *; solve_rs.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      eapply H2; eauto.
      unfold Asmgen.mk_storebyte in EQ4. repeat destr_in EQ4.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      invasm. intuition subst;
                red; intros; simpl in *; solve_rs.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      eapply H2; eauto.
      invasm. intuition subst;
                red; intros; simpl in *; solve_rs.
      invasm; try eapply exec_store_rsp; eauto; try apply not_eq_sym; try eapply ireg_of_not_rsp; eauto;
        try eapply freg_of_not_rsp; eauto.
      eapply H2; eauto.
      inv EQ3.
      inv EQ3.
    - destr_in EQ; invasm. inv EQ. invasm.
    - destr_in EQ; invasm. repeat destr_in H3.
      intuition subst;
        red; intros; simpl in *; solve_rs.
      eapply H2; eauto.
      inv EQ. invasm.
      repeat destr_in H3.
      intuition subst;
        red; intros; simpl in *; solve_rs.
      eapply H2; eauto.
    - inv EQ. red; intros; simpl in *.
      intuition subst; red; intros; simpl in *; solve_rs. inv H3. eapply H2; eauto.
    - inv EQ. invasm.
    - inv EQ. invasm.
      eapply goto_label_rsp; eauto.
    - eapply asmgen_transl_cond_rsp'; eauto.
    - inv EQ. invasm. repeat destr_in H3.
      erewrite goto_label_rsp. 2: apply H5.
      solve_rs.
    - inv EQ. invasm.
      repeat destr_in H3.
      intuition subst;
        red; intros; simpl in *; solve_rs.
      eapply H2; eauto.
  Qed.

  Definition asm_instr_no_stack (i : Asm.instruction) : Prop :=
    is_unchanged i = true ->
    forall F V (ge: _ F V) rs1 m1 rs2 m2 f isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).


  Lemma exec_store_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2,
      exec_store ge k m1 a rs1 rs l = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs l rs2 m2 STORE.
    unfold exec_store in STORE; repeat destr_in STORE. 
    unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
    erewrite Mem.store_stack_blocks. 2: eauto.
    split; auto.
    split; intros.
    eapply Mem.perm_store_2; eauto.
    eapply Mem.perm_store_1; eauto.
  Qed.

  Lemma exec_load_stack:
    forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2,
      exec_load ge k m1 a rs1 rs = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge k m1 a rs1 rs rs2 m2 LOAD.
    unfold exec_load in LOAD; destr_in LOAD.
  Qed.

  Lemma goto_label_stack:
    forall F V (ge: _ F V) f l m1 rs1 rs2 m2,
      goto_label ge f l rs1 m1 = Next rs2 m2 ->
      Mem.stack_adt m2 = Mem.stack_adt m1 /\ (forall b o k p, Mem.perm m2 b o k p <-> Mem.perm m1 b o k p).
  Proof.
    intros F V ge f l m1 rs1 rs2 m2 GOTO.
    unfold goto_label in GOTO; repeat destr_in GOTO.
  Qed.

  Lemma asmgen_no_change_stack i:
    asm_instr_no_stack i.
  Proof.
    red; intros IU F V ge0 rs1 m1 rs2 m2 f isp EI.
    destruct i;
      simpl in IU; try discriminate; 
        simpl in EI; inv EI;
          first [ split;[reflexivity|tauto]
                | now (eapply exec_load_stack; eauto)
                | now (eapply exec_store_stack; eauto)
                | now (repeat destr_in H1; eapply goto_label_stack; eauto)
                | now (repeat destr_in H1)
                | idtac ].
  Qed.


  Definition asm_instr_nb_fw i:=
    forall F V (ge: _ F V) f rs1 m1 rs2 m2 isp,
      Asm.exec_instr isp ge f i rs1 m1 = Next rs2 m2 ->
      Ple (Mem.nextblock m1) (Mem.nextblock m2).

  Definition asm_code_nb_fw c :=
    forall i, In i c -> asm_instr_nb_fw i.


    Lemma exec_store_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs l rs2 m2,
        exec_store ge k m1 a rs1 rs l = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs l rs2 m2 STORE.
      unfold exec_store in STORE; repeat destr_in STORE. 
      unfold Mem.storev in Heqo; destr_in Heqo; inv Heqo.
      erewrite (Mem.nextblock_store _ _ _ _ _ _ H1); apply Ple_refl.
    Qed.

    Lemma exec_load_nb:
      forall F V (ge: _ F V) k m1 a rs1 rs rs2 m2,
        exec_load ge k m1 a rs1 rs = Next rs2 m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
    Proof.
      intros F V ge k m1 a rs1 rs rs2 m2 LOAD.
      unfold exec_load in LOAD; destr_in LOAD. inv LOAD.
      apply Ple_refl.
    Qed.


  Lemma asmgen_nextblock_forward i:
    asm_instr_nb_fw i.
  Proof.
    red. intros F V ge f rs1 m1 rs2 m2 isp EI.
    destruct i; simpl in EI; inv EI; try (apply Ple_refl);
      first [now eapply exec_load_nb; eauto
            | now (eapply exec_store_nb; eauto)
            | idtac ].
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
    - repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - unfold goto_label in H1. repeat destr_in H1; apply Ple_refl.
    - repeat destr_in H1.
      edestruct (Mem.push_frame_alloc_record) as (m3 & ALLOC & m4 & STORES & RSB). eauto.
      instantiate (1 :=
                     {| frame_adt_blocks := (b,frame)::nil;
                        frame_adt_size := frame_size frame;
                        frame_adt_blocks_norepet := norepet_1 _;
                     |}).
      reflexivity. reflexivity.
      edestruct Mem.record_stack_blocks_mem_unchanged; eauto. simpl. eauto.
      rewrite H0.
      apply Mem.do_stores_nextblock in STORES. rewrite STORES.
      rewrite (Mem.nextblock_alloc _ _ _ _ _ ALLOC).
      xomega.
    - repeat (destr_in H1; [idtac]). inv H1.
      edestruct Mem.unrecord_stack_block_mem_unchanged. simpl; eauto.
      rewrite H0.
      rewrite (Mem.nextblock_free _ _ _ _ _ Heqo0). apply Ple_refl.
    - repeat destr_in H1. apply Ple_refl.
  Qed.


  Lemma val_inject_set:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      v v' (VINJ: Val.inject j v v') r1 r,
      Val.inject j ((rs1 # r1 <- v) r) ((rs2 # r1 <- v') r).
  Proof.
    intros.
    destruct (PregEq.eq r1 r); subst; auto.
    rewrite ! Pregmap.gss; auto.
    rewrite ! Pregmap.gso by auto. auto.
  Qed.

  Lemma val_inject_undef_regs:
    forall l j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r))
      r,
      Val.inject j (undef_regs l rs1 r) (undef_regs l rs2 r).
  Proof.
    induction l; simpl; intros; eauto.
    apply IHl.
    intros; apply val_inject_set; auto.
  Qed.

  Lemma val_inject_nextinstr:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr rs1 r) (nextinstr rs2 r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto.
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma val_inject_nextinstr_nf:
    forall j rs1 rs2
      (RINJ: forall r, Val.inject j (rs1 r) (rs2 r)) r,
      Val.inject j (nextinstr_nf rs1 r) (nextinstr_nf rs2 r).
  Proof.
    unfold nextinstr_nf.
    intros.
    apply val_inject_nextinstr; auto.
    intros.
    apply val_inject_undef_regs; auto.
  Qed.


End WITHMEMORYMODEL.