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

Section WITHMEMORYMODEL.

  Context `{memory_model_ops: Mem.MemoryModelOps}.

  Existing Instance mem_accessors_default.

  Context `{!ExternalCallsOps mem} `{!EnableBuiltins mem}.

  Definition exec_instr {F V} (ge: Genv.t F V) f i rs m :=
    match i with
    | Pallocframe fi ofs_ra ofs_link =>
      let sp := Val.offset_ptr (rs # RSP) (Ptrofs.repr (- (frame_size fi))) in
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
        | Some sp =>
          match rs#RSP with
          | Vptr stk ofs => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m
          | _ => Stuck
          end
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

  Inductive match_states: state -> state -> Prop := 
  | match_states_intro:
      forall j rs m rs' m' bnd
        (MINJ: Mem.inject j m m')
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (MPG: Separation.globalenv_preserved ge j bnd)
      ,
        match_states (State rs m) (State rs' m').

  Axiom exec_instr_inject:
    forall j m1 m2 rs1 rs2 f i rs1' m1',
      Mem.inject j m1 m2 ->
      (forall r, Val.inject j (rs1#r) (rs2#r)) ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' rs2' m2',
        Asm.exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j' m1' m2'
        /\ (forall r, Val.inject j' (rs1'#r) (rs2'#r))
        /\ inject_incr j j'.
  (* should be proved already somewhere *)

  Definition is_unchanged (i: instruction) :=
    match i with
      Pallocframe _ _ _ 
    | Pfreeframe _ _ _ => false
    | _ => true
    end.

  Variable bstack: block.
  Variable id_stack: ident.
  Hypothesis find_bstack: Genv.find_symbol ge id_stack = Some bstack. 

  Lemma alloc_inject:
    forall j m1 m2 rs1 rs2 f i rs1' m1',
      Mem.inject j m1 m2 ->
      (forall r, Val.inject j (rs1#r) (rs2#r)) ->
      Mem.alloc m 0 (frame_size fi) = (m', b) ->
      Mem.record_stack_blocks m' (inl (b, Some fi)) (frame_size fi) = Some m'' ->
      rs2 # RSP = 
      exists j',
        j' b = 

  Lemma exec_instr_inject':
    forall j m1 m2 rs1 rs2 f i rs1' m1',
      Mem.inject j m1 m2 ->
      (forall r, Val.inject j (rs1#r) (rs2#r)) ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j' m1' m2'
        /\ (forall r, Val.inject j' (rs1'#r) (rs2'#r))
        /\ inject_incr j j'.
  Proof.
    intros. destruct (is_unchanged i) eqn:?.
    edestruct exec_instr_inject; eauto.
    destruct i; simpl in *; eauto; try congruence.
    destruct i; simpl in *; try congruence.
    -                           (* allocframe *)
      repeat destr_in H1.
      
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