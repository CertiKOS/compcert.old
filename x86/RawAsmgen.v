Require Import Smallstep.
Require Import Machregs.
Require Import Asm.
Require Import Integers.
Require Import List.
Require Import ZArith.
Require Memimpl.
Require Import Memtype.
Require Import Memory.
Require Import Archi.
Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Events.
Require Import Values.
Require Import Conventions1.

Section WITHMEMORYMODEL.

  Class MemoryModelSingleStack {mem} `{memory_model: Mem.MemoryModel mem} :=
    {
      size_stack_below:
        forall m: mem, Memimpl.Mem.size_stack (Memtype.Mem.stack_adt m) < Memimpl.Mem.stack_limit;
    }.
  
  Context `{memory_model: MemoryModelSingleStack}.

  Existing Instance mem_accessors_default.

  Context `{!ExternalCallsOps mem} `{!EnableBuiltins mem}.

  Definition exec_instr {F V} (ge: Genv.t F V) f i rs m :=
    match i with
    | Pallocframe fi ofs_ra ofs_link =>
      let sp := Val.offset_ptr (rs # RSP) (Ptrofs.repr (- align (Z.max 0 (frame_size fi)) 8)) in
      match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => Stuck
      | Some m2 =>
        match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
        | None => Stuck
        | Some m3 => Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m3
        end
      end
    | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
        match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
        | None => Stuck
        | Some sp => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m
        end
      end
    | _ => Asm.exec_instr ge f i rs m
    end.

  Inductive step (ge: Genv.t Asm.fundef unit) : state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs f i rs m rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) (fn_code f) = Some i ->
        exec_instr ge f i rs m = Next rs' m' ->
        step ge (State rs m) E0 (State rs' m')
  | exec_step_builtin:
      forall b ofs f ef args res rs m vargs t vres rs' m',
        rs PC = Vptr b ofs ->
        Genv.find_funct_ptr ge b = Some (Internal f) ->
        find_instr (Ptrofs.unsigned ofs) f.(fn_code) = Some (Pbuiltin ef args res) ->
        eval_builtin_args ge rs (rs RSP) m args vargs ->
        external_call ef ge vargs m t vres m' ->
        forall BUILTIN_ENABLED: builtin_enabled ef,
          rs' = nextinstr_nf
                  (set_res res vres
                           (undef_regs (map preg_of (destroyed_by_builtin ef)) rs)) ->
          step ge (State rs m) t (State rs' m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
        rs PC = Vptr b Ptrofs.zero ->
        Genv.find_funct_ptr ge b = Some (External ef) ->
        extcall_arguments rs m (ef_sig ef) args ->
        forall (SP_TYPE: Val.has_type (rs RSP) Tptr)
          (RA_TYPE: Val.has_type (rs RA) Tptr)
          (SP_NOT_VUNDEF: rs RSP <> Vundef)
          (RA_NOT_VUNDEF: rs RA <> Vundef), 
          external_call ef ge args m t res m' ->
          rs' = (set_pair (loc_external_result (ef_sig ef)) res (undef_regs (CR ZF :: CR CF :: CR PF :: CR SF :: CR OF :: nil) (undef_regs (map preg_of destroyed_at_call) rs))) #PC <- (rs RA) #RA <- Vundef ->
          step ge (State rs m) t (State rs' m').

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.

  Variable bstack: block.
  Variable id_stack: ident.
  Hypothesis find_bstack: Genv.find_symbol ge id_stack = Some bstack. 
  Hypothesis repr_stack_limit:
    Memimpl.Mem.stack_limit < Ptrofs.max_unsigned.



  Lemma size_stack_pos:
    forall l,
      0 <= Memimpl.Mem.size_stack l.
  Proof.
    induction l; simpl; intros; eauto. omega.
    destruct a.
    generalize (align_le (Z.max 0 z) 8) (Z.le_max_l 0 z); omega.
  Qed.
  
  Definition no_inject_below j m thr:=
    forall b delta o k p,
      j b = Some (bstack, delta) ->
      Mem.perm m b o k p ->
      thr <= o + delta.

  Definition agree_sp m1 rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      Ptrofs.unsigned ostack = Memimpl.Mem.stack_limit - Memimpl.Mem.size_stack (Mem.stack_adt m1).

  Definition perm_bstack m2:=
    forall (ofs : Z) (k : perm_kind) (p : permission),
       Mem.perm m2 bstack ofs k p -> 0 <= ofs < Ptrofs.max_unsigned.

  Definition perm_bstack_stack_limit m2:=
    forall (ofs : Z) (k : perm_kind) (p : permission),
      0 <= ofs < Memimpl.Mem.stack_limit ->
      Mem.perm m2 bstack ofs k p.

  Definition sp_aligned rs2:=
    forall ostack,
      rs2 # RSP = Vptr bstack ostack ->
      (8 | Ptrofs.unsigned ostack).

  Definition no_stack m2 :=
    Mem.stack_adt m2 = nil.
  

  

  
  Lemma alloc_inject:
    forall j m1 m2 (rs1 rs2: regset) fi m' b m1',
      Mem.inject j m1 m2 ->
      Mem.valid_block m2 bstack ->
      (forall r, Val.inject j (rs1#r) (rs2#r)) ->
      Mem.alloc m1 0 (frame_size fi) = (m', b) ->
      Mem.record_stack_blocks m' (inl (b, Some fi)) (frame_size fi) = Some m1' ->
      agree_sp m1 rs2 ->
      sp_aligned rs2 ->
      perm_bstack m2 ->
      perm_bstack_stack_limit m2 ->
      no_stack m2 ->
      forall ostack,
        rs2 # RSP = Vptr bstack ostack ->
        no_inject_below j m1 (Ptrofs.unsigned ostack) ->
      let newostack := Ptrofs.unsigned ostack - align (Z.max 0 (frame_size fi)) 8 in
      let rs2' := (rs2 # RSP <- (Vptr bstack (Ptrofs.repr newostack))) in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb) 
        /\ inject_incr j j'
      /\ no_inject_below j' m1' newostack
      /\ Mem.inject j' m1' m2
      /\ agree_sp m1' rs2'
      /\ sp_aligned rs2'.
  Proof.
    intros j m1 m2 rs1 rs2 fi m' b m1' MINJ VB RINJ ALLOC RSB AGSP SPAL PBS PBSL NOSTACK ostack EQRSP NIB.
    set (newostack := Ptrofs.unsigned ostack - align (Z.max 0 (frame_size fi)) 8).
    simpl; intros.
    assert (REPR: 0 <= newostack < Ptrofs.max_unsigned).
    {
      unfold newostack.
      generalize (size_stack_below m1').
      erewrite Mem.record_stack_block_stack_adt. 2: eauto.
      simpl.
      erewrite Mem.alloc_stack_blocks. 2: eauto.
      erewrite AGSP; eauto.
      split.  omega.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      omega.
    }
    generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB).
    intro A.
    trim A.
    {
      omega.
    }
    trim A.
    {
      intros; right; eapply PBS; eauto.
    }
    trim A.
    {
      intros; eapply PBSL; eauto.
      unfold newostack. rewrite AGSP; auto.
      generalize (size_stack_below m1').
      erewrite Mem.record_stack_block_stack_adt. 2: eauto.
      simpl.
      erewrite Mem.alloc_stack_blocks. 2: eauto.
      split.  omega.
      cut (ofs < Memimpl.Mem.size_stack (Mem.stack_adt m1) + align (Z.max 0 (frame_size fi)) 8). omega.
      eapply Z.lt_le_trans. apply H.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      rewrite Z.max_r by omega.
      omega. 
    }
    trim A.
    {
      red.
      intros.
      unfold newostack.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      apply SPAL; auto.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      unfold newostack in RNG.
      rewrite Z.max_r in RNG by omega. simpl in RNG.
      generalize (align_le (frame_size fi) 8).
      omega.
    }
    trim A.
    {
      rewrite NOSTACK. simpl. easy.
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split; [|split; [|split; [|split;[|split]]]].
    - intros. destruct peq; subst; auto.
    - red; intros.
      destruct (peq b0 b); auto.
    - red. intros b0 delta o k p JB PERM.
      eapply Mem.record_stack_block_perm in PERM.
      eapply Mem.perm_alloc_inv in PERM; eauto. 
      destruct peq.
      + subst. rewrite EQ1 in JB. inv JB. omega.
      + transitivity (Ptrofs.unsigned ostack).
        generalize (Z.le_max_l 0 (frame_size fi)); intro MAX.
        generalize (align_le (Z.max 0 (frame_size fi)) 8). unfold newostack. omega.
        eapply NIB; eauto. erewrite <- EQ2; eauto.
      + eauto.
    - admit.
    - red. rewrite Pregmap.gss. inversion 1. subst.
      erewrite Mem.record_stack_block_stack_adt. 2: eauto.
      simpl. erewrite Mem.alloc_stack_blocks. 2: eauto.
      rewrite Ptrofs.unsigned_repr.
      unfold newostack in *. rewrite (AGSP _ EQRSP).
      omega. omega.
    - red; intros. rewrite Pregmap.gss in H. inversion H. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r.
      apply SPAL; auto.
      apply align_divides. omega.
  Admitted.
  
  Inductive match_states: meminj -> state -> state -> Prop := 
  | match_states_intro:
      forall j (rs: regset) m (rs': regset) m' bnd
        (MINJ: Mem.inject j m m')
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (SPAL: sp_aligned rs')
        (PBS: perm_bstack m')
        (PBSL: perm_bstack_stack_limit m')
        (NS: no_stack m')
        ostack
        (RSPEQ: rs' RSP = Vptr bstack ostack)
        (NIB: no_inject_below j m (Ptrofs.unsigned ostack))
        (MPG: Separation.globalenv_preserved ge j bnd)
      ,
        match_states j (State rs m) (State rs' m').

  Axiom exec_instr_inject:
    forall j m1 m2 rs1 rs2 f i rs1' m1',
      match_states j (State rs1 m1) (State rs2 m2) ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' rs2' m2',
        Asm.exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'. 
  (* should be proved already somewhere *)

  Definition is_unchanged (i: instruction) :=
    match i with
      Pallocframe _ _ _ 
    | Pfreeframe _ _ _ => false
    | _ => true
    end.

  Lemma exec_instr_inject':
    forall j m1 m2 rs1 rs2 f i rs1' m1',
      match_states j (State rs1 m1) (State rs2 m2) ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros.
    destruct (is_unchanged i) eqn:?.
    - edestruct exec_instr_inject; eauto.
      destruct i; simpl in *; eauto; try congruence.
    - destruct i; simpl in *; try congruence.
      + (* allocframe *)
        repeat destr_in H0. inv H.
        edestruct alloc_inject as (j' & JSPEC & INCR & NIB' & MINJ' & AGSP' & SPAL') ; eauto.
        rewrite RSPEQ.  simpl.
        exploit Mem.store_mapped_inject. apply MINJ'. eauto. rewrite JSPEC. rewrite pred_dec_true. eauto. auto.
        eapply val_inject_incr; eauto. intros (n2 & STORE & MINJ2).
        rewrite Ptrofs.add_zero_l in STORE.
        unfold Ptrofs.add.
        rewrite Mem.address_inject.
        

        rewrite STORE.
  Qed.

  
  
  Theorem step_simulation:
    forall S1 t S2, Asm.step ge S1 t S2 ->
               forall S1' (MS: match_states S1 S1'),
                 (exists S2', step ge S1' t S2' /\ match_states S2 S2').
  Proof.
    destruct 1; intros; inv MS.
    -
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        destruct MPG.
        apply DOMAIN.
        eapply FUNCTIONS. eauto. 
      }
      rewrite JB in H7; inv H7. 
      generalize (exec_instr_inject _ _ _ _ _ _ _ _ _ MINJ RINJ H2).
      intros (j' & rs2' & m2' & EI & MINJ' & RINJ' & INCR).
      destruct (is_unchanged i) eqn:?.
      eexists; split.
      eapply exec_step_internal; eauto.
      rewrite Ptrofs.add_zero. eauto.
      instantiate (1 := m2'). instantiate (1:= rs2').
      rewrite <- EI. destruct i; simpl in *; try congruence.
      econstructor; eauto.
      admit.
      destruct i; simpl in Heqb; try congruence.
      + 
        eexists; split.
        eapply exec_step_internal; eauto.
        rewrite Ptrofs.add_zero. eauto.
        instantiate (1 := m2'). instantiate (1:= rs2').


        simpl in EI.
        eapply Ageneralize (Genv.find_funct_ptr_transf match_prog _ H0). intro FFP.
      generalize (find_instr_transl _ _ _ H1); intro FINSTR.

      assert (match i with
                Pallocframe _ _ _
              | Pfreeframe _ _ _ => False
              | _ => True
              end \/ (match i with
                Pallocframe _ _ _
              | Pfreeframe _ _ _ => True
              | _ => False
              end)) as DEC.
      {
        destruct i; simpl; auto.
      }
      destruct DEC.

  Qed.