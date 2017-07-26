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
Require Import AsmFacts.

Section WITHMEMORYMODEL.

  Class MemoryModelSingleStack {mem} `{memory_model: Mem.MemoryModel mem} :=
    {
      size_stack_below:
        forall m: mem, Memimpl.Mem.size_stack (Memtype.Mem.stack_adt m) < Memimpl.Mem.stack_limit;
    }.
  
  Context `{memory_model: MemoryModelSingleStack}.

  Inductive mono_initial_state {F V} (prog: program F V): state -> Prop :=
  |mis_intro:
     forall rs m m1 bstack,
       initial_state prog (State rs m) ->
       Mem.alloc m 0 (Memimpl.Mem.stack_limit) = (m1,bstack) ->
       mono_initial_state prog (State rs m1).

  Existing Instance mem_accessors_default.

  Context `{!ExternalCallsOps mem} `{!EnableBuiltins mem}.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.
  Definition bstack: block := Genv.genv_next ge.
  Section PRESERVATION.

  Definition current_offset (v: val) :=
    match v with
      Vptr stk ofs => Ptrofs.unsigned ofs
    | _ => Memimpl.Mem.stack_limit
    end.

  Definition offset_after_alloc (p: Z) fi :=
    (p - align (Z.max 0 (frame_size fi)) 8).

  Definition exec_instr {F V} (ge: Genv.t F V) f i rs m :=
    match i with
    | Pallocframe fi ofs_ra ofs_link =>
      let curofs := current_offset (rs RSP) in
      let sp := Vptr bstack (Ptrofs.repr (offset_after_alloc curofs fi)) in
      match Mem.storev Mptr m (Val.offset_ptr sp ofs_link) rs#RSP with
      | None => Stuck
      | Some m2 =>
        match Mem.storev Mptr m2 (Val.offset_ptr sp ofs_ra) rs#RA with
        | None => Stuck
        | Some m3 =>
          match Mem.record_stack_blocks m3 None (frame_size fi) with
            Some m4 =>
            Next (nextinstr (rs #RAX <- (rs#RSP) #RSP <- sp)) m4
          | _ => Stuck
          end
        end
      end
    | Pfreeframe sz ofs_ra ofs_link =>
      match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_ra) with
      | None => Stuck
      | Some ra =>
        match Mem.loadv Mptr m (Val.offset_ptr rs#RSP ofs_link) with
        | None => Stuck
        | Some sp =>
          match Mem.unrecord_stack_block m with
            Some m => Next (nextinstr (rs#RSP <- sp #RA <- ra)) m
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

  Hypothesis repr_stack_limit:
    0 <= Memimpl.Mem.stack_limit <= Ptrofs.max_unsigned.

  Lemma size_stack_pos:
    forall {A} (l: list (A*Z)),
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
      thr <= o + delta /\ in_frames (Mem.stack_adt m) b.

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
    Forall (fun x => fst x = None) (Mem.stack_adt m2).

  Inductive inject_stack: meminj -> list (option frame_adt * Z) -> Prop :=
  | inject_stack_nil j :
      inject_stack j nil
  | inject_stack_cons j l b fi:
      inject_stack j l ->
      j b = Some (bstack, Memimpl.Mem.stack_limit - Memimpl.Mem.size_stack l - align (Z.max 0 (frame_size fi)) 8) ->
      inject_stack j ((Some (frame_with_info b (Some fi)),frame_size fi)::l).

  Variable init_sp: val.
  
  Inductive load_rsp: list (option frame_adt * Z) -> mem -> Prop :=
  | load_rsp_nil m:
      load_rsp nil m
  | load_rsp_one m b fi sz:
      Mem.load Mptr m b (seg_ofs (frame_link fi)) = Some init_sp ->
      load_rsp ((Some (frame_with_info b (Some fi)),sz)::nil) m
  | load_rsp_cons m b fi sz b' fi' sz' l:
      Mem.load Mptr m b (seg_ofs (frame_link fi)) = Some (Vptr b' Ptrofs.zero) ->
      load_rsp ((Some (frame_with_info b' (Some fi')), sz')::l) m ->
      Plt b' b ->
      load_rsp ((Some (frame_with_info b (Some fi)),sz)::(Some (frame_with_info b' (Some fi')), sz')::l) m.

  Inductive perm_stack: list (option frame_adt * Z) -> mem -> Prop :=
  | ps_nil m:
      perm_stack nil m
  | ps_cons l m b fi sz:
      perm_stack l m ->
      (forall o k p, Mem.perm m b o k p <-> 0 <= o < frame_size fi) ->
      perm_stack ((Some (frame_with_info b (Some fi)), sz)::l) m.

  Definition inject_padding (j: meminj) (m: mem) : Prop :=
    forall b fi delta,
      Mem.get_frame_info m b = Some fi ->
      j b = Some (bstack, delta) ->
      forall b' o delta' k p,
        j b' = Some (bstack, delta') ->
        Mem.perm m b' o k p ->
        ~ ( delta + Z.max 0 (frame_size fi) <= o + delta' < delta + align (Z.max 0 (frame_size fi)) 8).
  
  Inductive match_states: meminj -> Z -> state -> state -> Prop :=
  | match_states_intro:
      forall j (rs: regset) m (rs': regset) m'
        (MINJ: Mem.inject j m m')
        (RSPzero: forall b o, rs # RSP = Vptr b o -> o = Ptrofs.zero )
        (RINJ: forall r, Val.inject j (rs # r) (rs' # r))
        (VB: Mem.valid_block m' bstack)
        (AGSP: agree_sp m rs')
        (AGSP1: match Mem.stack_adt m with
                  nil => rs # RSP = init_sp
                | (Some (frame_with_info b (Some fi)),n)::r => rs # RSP = Vptr b Ptrofs.zero
                | _ => False
                end)
        (SPAL: sp_aligned rs')
        (PBS: perm_bstack m')
        (PBSL: perm_bstack_stack_limit m')
        (NS: no_stack m')
        ostack
        (RSPEQ: forall b o, rs' RSP = Vptr b o -> b = bstack /\ o = ostack)
        (NIB: no_inject_below j m (Ptrofs.unsigned ostack))
        (IS: inject_stack j (Mem.stack_adt m))
        (IP: inject_padding j m)
        (PS: perm_stack (Mem.stack_adt m) m)
        (LRSP: load_rsp (Mem.stack_adt m) m)
        (GLOBFUN_INJ: forall b f, Genv.find_funct_ptr ge b = Some f -> j b = Some (b,0))
        (GLOBDEF_INJ: forall b f, Genv.find_def ge b = Some f -> j b = Some (b,0))
        (GLOBSYMB_INJ: meminj_preserves_globals' ge j)
        (GlobLe: (Genv.genv_next ge <= Mem.nextblock m)%positive)
        (GlobLeT: (Genv.genv_next ge <= Mem.nextblock m')%positive)
      ,
        match_states j (Ptrofs.unsigned ostack) (State rs m) (State rs' m').

  Lemma inject_stack_incr:
    forall j j' (INCR: inject_incr j j')
      l (IS: inject_stack j l),
      inject_stack j' l.
  Proof.
    induction 2; constructor; eauto.
  Qed.
  
  Definition is_ptr v :=
    match v with
      Vptr _ _ => True
    | _ => False
    end.

  Lemma is_ptr_dec v: {is_ptr v} + {~ is_ptr v}.
  Proof.
    destruct v; simpl; auto.
  Qed.


  Hypothesis stack_limit_divides:
    (8 | Memimpl.Mem.stack_limit).


  Lemma perm_stack_inv:
    forall l m (PS: perm_stack l m) m'
      (V: forall b, in_frames l b -> Mem.valid_block m b)
      (U: forall b o k p, in_frames l b -> Mem.perm m' b o k p <-> Mem.perm m b o k p),
      perm_stack l m'.
  Proof.
    induction 1; simpl; intros; constructor; auto.
    intros.
    split; intros.
    eapply U in H0; eauto.
    eapply H; eauto. simpl. eauto.
    eapply U; eauto; simpl; eauto.
    apply H. auto.
  Qed.

  Axiom exec_instr_inject:
    forall j m1 m2 rs1 rs2 f i rs1' m1'
      (MINJ: Mem.inject j m1 m2)
      (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
      (IU: is_unchanged i = true)
      (EXEC: Asm.exec_instr ge f i rs1 m1 = Next rs1' m1'),
      exists rs2' m2',
        Asm.exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j m1' m2'
        /\ (forall r, Val.inject j (rs1' # r) (rs2' # r))
        (* /\ (forall b b' delta, j b = None -> j' b = Some (b', delta) -> Ple (Genv.genv_next ge) b /\ b' <> bstack) *). 
  (* should be proved already somewhere *)

  Lemma free_inject:
    forall j m1 b lo hi m2 m3 m1',
      Mem.inject j m1 m1' ->
      Mem.free m1 b lo hi = Some m2 ->
      Mem.unrecord_stack_block m2 = Some m3 ->
    exists m2',
      Mem.unrecord_stack_block m1' = Some m2' /\
      Mem.inject j m3 m2'.
  Proof.
    intros.
    edestruct Mem.unrecord_stack_block_inject as (m2' & USB & INJ).
    auto. eapply Mem.free_left_inject. eauto. eauto. eauto.
    eauto.
  Qed.

  Hypothesis type_init_sp:
    Val.has_type init_sp Tptr.

  Lemma ZEQ: forall a b,
      proj_sumbool (zeq a b) = true -> a = b.
  Proof.
    intros; destruct zeq; auto. discriminate.
  Qed.

  Lemma ZLE: forall a b c d,
      zle a b || zle c d = true ->
      a <= b \/ c <= d.
  Proof.
    intros; destruct (zle a b), (zle c d); try congruence; try omega.
    simpl in H; congruence.
  Qed.

  Definition link_offsets l b o :=
    match get_assoc l b with
      Some fi => in_segment o (frame_link fi)
    | _ => False
    end.

  Lemma get_assoc_app:
    forall l2 l1 b,
      (forall b, in_frames l2 b -> in_frames l1 b -> False) ->
      in_frames l1 b ->
      get_assoc (l2 ++ l1) b = get_assoc l1 b.
  Proof.
    induction l2; simpl; intros; auto.
    destruct a.
    destruct o; eauto.
    destruct f; eauto.
    - destr. subst. eapply H in H0; eauto. easy. simpl; auto.
      eapply IHl2; eauto.
    - destr. eapply H in H0; eauto. easy.
      eapply IHl2; eauto.      
  Qed.

  Lemma in_frames_app:
    forall l1 l2 b,
      in_frames (l1 ++ l2) b <->
      in_frames l1 b \/ in_frames l2 b.
  Proof.
    clear.
    induction l1; simpl; intros; eauto. tauto.
    destruct a.
    split; intros; destruct H; auto.
    apply IHl1 in H. destruct H; auto. rewrite IHl1.
    destruct H; auto.
    rewrite IHl1. auto.
  Qed.

  Lemma load_rsp_plt:
    forall l a m,
      load_rsp (a :: l) m ->
      forall b b',
        in_frame (fst a) b ->
        in_frames l b' ->
        Plt b' b.
  Proof.
    clear.
    induction l; simpl; intros; eauto. easy.
    destruct a0. destruct a.
    simpl in *.
    inv H.
    simpl in *. subst.
    destruct H1. subst. auto.
    eapply IHl in H9. 2: simpl; eauto. 2: apply H. xomega.
  Qed.

  Lemma load_rsp_plt_app:
    forall l1 l2 m,
      load_rsp (l1 ++ l2) m ->
      forall b b',
        in_frames l1 b ->
        in_frames l2 b' ->
        Plt b' b.
  Proof.
    clear.
    induction l1; simpl; intros. easy.
    destruct a.
    destruct H0.
    eapply load_rsp_plt in H. 2: simpl; eauto. 2: rewrite in_frames_app. 2: right; eauto. auto.
    eapply IHl1; eauto. inv H; eauto.
    constructor.
  Qed.

  Lemma load_rsp_inv:
    forall l m ,
      load_rsp l m ->
      forall m' l1 l2,
        l1 = l2 ++ l ->
        (forall b, in_frames l2 b -> in_frames l b -> False) ->
        Mem.unchanged_on (link_offsets l1) m m' ->
        load_rsp l m'.
  Proof.
    induction 1; simpl; intros m' l1 l2 EQ DISJ UNCH.
    - constructor.
    - constructor.
      eapply Mem.load_unchanged_on. eauto. unfold link_offsets.
      intros. rewrite EQ. rewrite get_assoc_app; auto. simpl.
      rewrite pred_dec_true; eauto. unfold in_segment.
      rewrite frame_link_size; auto. simpl; auto. auto.
    - constructor.
      eapply Mem.load_unchanged_on; eauto.
      unfold link_offsets. erewrite EQ. rewrite get_assoc_app; auto. simpl. rewrite pred_dec_true; auto. unfold in_segment.
      intros. rewrite frame_link_size. auto.
      simpl; auto. 
      eapply IHload_rsp; auto. 
      + instantiate (1 := l2 ++ (Some (frame_with_info b (Some fi)),sz) :: nil). subst. simpl.
        intros. apply in_frames_app in H2. simpl in *.
        destruct H2.
        apply DISJ in H2. easy. auto.
        destruct H2; try congruence. subst.
        destruct H3. subst; xomega.
        eapply load_rsp_plt in H0. 2: simpl; eauto. 2: apply H2. xomega.
      + subst. rewrite app_ass. simpl. auto. 
      + auto.
  Qed.

  Lemma load_rsp_inv':
    forall l m m',
      load_rsp l m ->
      Mem.unchanged_on (link_offsets l) m m' ->
      load_rsp l m'.
  Proof.
    intros.
    eapply (load_rsp_inv l m H m' l nil). reflexivity. simpl; easy. auto.
  Qed.

  Lemma load_rsp_add:
    forall l m b frame,
      load_rsp l m ->
      Mem.load Mptr m b (seg_ofs (frame_link frame)) = Some (match l with
                                                         nil => init_sp
                                                       | (Some (frame_with_info b' _),_)::r => Vptr b' Ptrofs.zero
                                                       | _ => Vundef
                                                       end) ->
      (forall bs, in_frames l bs -> Plt bs b) ->
      load_rsp ((Some (frame_with_info b (Some frame)), frame_size frame) :: l) m.
  Proof.
    induction 1; simpl; intros; repeat constructor; auto.
  Qed.


  Lemma exec_load_unchanged_on:
    forall rs1 m1 rs1' m1' p am chunk P,
      exec_load ge chunk m1 am rs1 p = Next rs1' m1' ->
      Mem.unchanged_on P m1 m1'.
  Proof.
    unfold exec_load.
    intros. destr_in H. inv H.
    apply Mem.unchanged_on_refl.
  Qed.

  Lemma goto_label_unchanged_on:
    forall rs1 m1 rs1' m1' f l P,
      goto_label ge f l rs1 m1 = Next rs1' m1' ->
      Mem.unchanged_on P m1 m1'.
  Proof.
    unfold goto_label.
    intros. repeat destr_in H. 
    apply Mem.unchanged_on_refl.
  Qed.

  Lemma exec_store_unchanged_on:
    forall rs1 m1 rs1' m1' p am rl chunk,
      exec_store ge chunk m1 am rs1 p rl = Next rs1' m1' ->
      Mem.unchanged_on (link_offsets (Mem.stack_adt m1)) m1 m1'.
  Proof.
    unfold exec_store.
    intros rs1 m1 rs1' m1' p am rl chunk ES.
    destr_in ES. inv ES.
    unfold Mem.storev in Heqo. destr_in Heqo.
    eapply Mem.store_unchanged_on. eauto.
    eapply Mem.store_valid_access_3 in Heqo.
    destruct Heqo as (RP & AL & SA).
    trim SA. constructor.
    intros i0 RNG LO.
    red in LO. destr_in LO.
    destruct SA as [[IST NONLINK]|[NIST DATA]].
    apply NONLINK in RNG.
    red in RNG.
    unfold Mem.get_frame_info in RNG. rewrite Heqo in RNG.
    intuition congruence.
    red in DATA.
    unfold Mem.get_frame_info in DATA. rewrite Heqo in DATA.
    eapply frame_disjoints. eauto.
    right. right. right. right. left. apply DATA. auto.
  Qed.

  Lemma exec_instr_unchanged_on:
    forall f i rs1 m1 rs1' m1',
      is_unchanged i = true ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      Mem.unchanged_on (fun b o => match Mem.get_frame_info m1 b with
                                  Some fi => in_segment o (frame_link fi)
                                | _ => False
                                end) m1 m1'.
  Proof.
    intros f i.
    assert (forall P, (forall x, P x) -> P i). intros. auto.
    destruct i; simpl; intros rs1 m1 rs1' m1' IU EI;
      simpl in IU; try discriminate;
      repeat match goal with
               H: Next _ _ = Next _ _ |- _ => inv H
             | H: exec_load _ _ _ _ _ _ = _ |- _ => eapply exec_load_unchanged_on; eauto
             | H: exec_store _ _ _ _ _ _ _ = _ |- _ => eapply exec_store_unchanged_on; eauto
             | H: goto_label _ _ _ _ _ = _ |- _ => eapply goto_label_unchanged_on; eauto
             | |- Mem.unchanged_on _ ?m ?m => apply Mem.unchanged_on_refl
             | |- _ => repeat destr_in EI
             end.
  Qed.

  Lemma perm_stack_eq:
    forall l m b fi,
      perm_stack l m ->
      get_assoc l b = Some fi ->
      forall o k p,
        Mem.perm m b o k p <-> 0 <= o < frame_size fi.
  Proof.
    induction 1; simpl; intros; eauto. congruence.
    destr_in H1. inv H1.
    auto. eauto.
  Qed.

  Lemma in_stack_inj_below:
    forall j l,
      inject_stack j l ->
      forall b fi,
        get_assoc l b = Some fi ->
        exists l1 l2,
          l = l1 ++ l2 /\
          j b = Some (bstack, Memimpl.Mem.stack_limit - Memimpl.Mem.size_stack l2).
  Proof.
    induction 1; simpl; intros; eauto.
    congruence.
    destr_in H1; eauto.
    - subst.
      inv H1.
      rewrite H0.
      exists nil. 
      repeat eexists.
      f_equal. f_equal. simpl. omega. 
    - specialize (IHinject_stack _ _ H1).
      destruct IHinject_stack as (l1 & l2 & EQl & JB).
      subst.
      rewrite JB.
      repeat eexists.
      rewrite app_comm_cons. eauto.
  Qed.

  Lemma size_stack_app:
    forall {A} (l1 l2: list (A * Z)),
      Memimpl.Mem.size_stack (l1 ++ l2) = Memimpl.Mem.size_stack l1 + Memimpl.Mem.size_stack l2.
  Proof.
    induction l1; simpl; intros; eauto.
    destruct a.
    rewrite IHl1. omega.
  Qed.

  Ltac rewrite_perms_fw :=
    match goal with
    | H1: Mem.record_stack_blocks _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
      eapply (Mem.record_stack_block_perm' _ _ _ _ H1)
    | H1: Mem.alloc _ _ _ = (?m,_) |- Mem.perm ?m _ _ _ _ =>
      first [
          apply Mem.perm_implies; [apply (Mem.perm_alloc_2 _ _ _ _ _ H1) | try constructor]
        |  apply (Mem.perm_alloc_1 _ _ _ _ _ H1)
        ]
    | H1: Mem.store _ _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
      apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
    | H1: Mem.storev _ _ _ _ = Some ?m |- Mem.perm ?m _ _ _ _ =>
      apply (Mem.perm_store_1 _ _ _ _ _ _ H1)
    end.

  Ltac rewrite_stack_blocks :=
    match goal with
    | H: Mem.record_stack_blocks _ _ _ = Some ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.record_stack_blocks_stack_adt _ _ _ _ H)
    | H: Mem.alloc _ _ _ = (?m,_) |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.alloc_stack_blocks _ _ _ _ _ H)
    | H: Mem.store _ _ _ _ _ = Some ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.store_stack_blocks _ _ _ _ _ _ H)
    | H: Mem.storev _ _ _ _ = Some ?m |- context [Mem.stack_adt ?m] =>
      rewrite (Mem.store_stack_blocks _ _ _ _ _ _ H)
    end.

  Ltac rewrite_perms_bw H :=
    match type of H with
      Mem.perm ?m2 _ _ _ _ =>
      match goal with
      | H1: Mem.record_stack_blocks _ _ _ = Some ?m |- _ =>
        apply (Mem.record_stack_block_perm _ _ _ _ H1) in H
      | H1: Mem.alloc _ _ _ = (?m,_) |- _ =>
        apply (Mem.perm_alloc_inv _ _ _ _ _ H1) in H
      | H1: Mem.store _ _ _ _ _ = Some ?m |- _ =>
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
      | H1: Mem.storev _ _ _ _ = Some ?m |- _ =>
        apply (Mem.perm_store_2 _ _ _ _ _ _ H1) in H
      end
    end.

  Lemma val_inject_set:
    forall j rs1 rs2 r0 r1
      (RINJ: r0 <> r1 -> Val.inject j (rs1 r0) (rs2 r0))
      v v' (VINJ: Val.inject j v v'),
      Val.inject j ((rs1 # r1 <- v) r0) ((rs2 # r1 <- v') r0).
  Proof.
    intros.
    destruct (PregEq.eq r1 r0); subst; auto.
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
    forall j rs1 rs2 r
      (RINJ: forall r0, r0 = r \/ r0 = PC -> Val.inject j (rs1 r0) (rs2 r0)),
      Val.inject j (nextinstr rs1 r) (nextinstr rs2 r).
  Proof.
    unfold nextinstr.
    intros.
    apply val_inject_set; auto. 
    apply Val.offset_ptr_inject; auto.
  Qed.

  Lemma find_var_info_none_ge:
    forall b,
      (Genv.genv_next ge <= b)%positive ->
      Genv.find_var_info ge b = None.
  Proof.
    unfold Genv.find_var_info. intros.
    destr.
    apply Genv.genv_defs_range in Heqo. xomega.
  Qed.

  Lemma load_record_stack_blocks:
    forall m fi n m',
      Mem.record_stack_blocks m fi n = Some m' ->
      forall chunk b ofs,
        Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
  Proof.
    intros.
    destruct (plt b (Mem.nextblock m)).
    eapply Mem.load_unchanged_on_1.
    eapply Mem.strong_unchanged_on_weak.
    eapply Mem.record_stack_block_unchanged_on; eauto.
    apply p.
    instantiate (1 := fun _ _ => True); simpl; auto.
    destruct (Mem.load chunk m b ofs) eqn:LOAD.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n0.
    eapply Mem.perm_valid_block. apply H0.
    instantiate (1:= ofs). generalize (size_chunk_pos chunk); omega.
    clear LOAD.
    destruct (Mem.load chunk m' b ofs) eqn:LOAD; auto.
    apply Mem.load_valid_access in LOAD. destruct LOAD.
    exfalso; apply n0.
    eapply Mem.perm_valid_block.
    specialize (H0 ofs). trim H0. generalize (size_chunk_pos chunk); omega.
    rewrite_perms_bw H0.
    apply H0.
  Qed.


  Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m2 m3 m4 m5,
      match_states j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
      Mem.alloc m1 0 (frame_size fi) = (m2, b) ->
      Mem.store Mptr m2 b (seg_ofs (frame_link fi)) rs1#RSP = Some m3 ->
      Mem.store Mptr m3 b (seg_ofs (frame_retaddr fi)) rs1#RA = Some m4 ->
      Mem.record_stack_blocks m4 (Some (frame_with_info b (Some fi))) (frame_size fi) = Some m5 ->
      0 <= seg_ofs (frame_link fi) <= Ptrofs.max_unsigned ->
      0 <= seg_ofs (frame_retaddr fi) <= Ptrofs.max_unsigned ->
      let curofs := current_offset (rs1' # RSP) in
      let newostack := offset_after_alloc curofs fi in
      let rs2 := nextinstr ( rs1 #RAX <- (rs1#RSP)  #RSP <- (Vptr b Ptrofs.zero)) in
      let rs2' := nextinstr (rs1' #RAX <- (rs1'#RSP) #RSP <- (Vptr bstack (Ptrofs.repr newostack))) in
      exists j',
        (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb) 
        /\ inject_incr j j'
        /\ exists m3',
            Mem.storev Mptr m1' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr (seg_ofs (frame_link fi)))) rs1'#RSP = Some m3'
            /\
            exists m4',
              Mem.storev Mptr m3' (Val.offset_ptr (Vptr bstack (Ptrofs.repr newostack)) (Ptrofs.repr (seg_ofs (frame_retaddr fi)))) rs1'#RA = Some m4'
              /\ exists m5', Mem.record_stack_blocks m4' None (frame_size fi) = Some m5'
                       /\ match_states j' newostack (State rs2 m5) (State rs2' m5').
  Proof.
    intros j ostack m1 rs1 rs1' fi b m1' m2 m3 m4 m5 MS ALLOC STORE_PARENT STORE_RETADDR RSB REPRlink REPRretaddr curofs newostack rs2 rs2'.
    inv MS.
    assert (RSPDEC: (rs1' RSP = Vptr bstack ostack0 /\ curofs = Ptrofs.unsigned ostack0)
                    \/ (~ is_ptr (rs1' RSP) /\ curofs = Memimpl.Mem.stack_limit /\ Mem.stack_adt m1 = nil)).
    {
      destruct (is_ptr_dec (rs1' RSP)).
      left; destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      specialize (RSPEQ _ _ eq_refl).
      intuition subst. auto. reflexivity.
      right. split; auto.
      split; auto.
      destruct (rs1' RSP) eqn:?; simpl in *; try easy.
      generalize (RINJ RSP).
      repeat destr_in AGSP1.
      rewrite H0. inversion 1. rewrite <- H4 in n. simpl in n; easy.
    }
    assert (REPRcur: align (Z.max 0 (frame_size fi)) 8 <= curofs <= Ptrofs.max_unsigned).
    {
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      generalize (size_stack_below m5).
      erewrite Mem.record_stack_blocks_stack_adt. 2: eauto.
      simpl.
      erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
      erewrite Mem.store_stack_blocks. 2: simpl in *; eauto.
      erewrite Mem.alloc_stack_blocks. 2: eauto.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.
      unfold curofs, current_offset. rewrite EQRSP. erewrite AGSP; eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros.
      omega. 
      rewrite EQ, NIL. simpl. omega.
    }
    assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned).
    {
      unfold newostack.
      unfold offset_after_alloc.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      omega.
    }
    generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB).
    intro A.
    trim A. now omega.
    trim A. intros; right; eapply PBS; now eauto.
    trim A.
    {
      intros; eapply PBSL; eauto.
      split. omega.
      unfold newostack, offset_after_alloc.
      eapply Z.lt_le_trans with curofs.
      generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)).
      rewrite Z.max_r by omega. omega.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite H0. erewrite (AGSP _ EQRSP); eauto.
      generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega. omega. 
    }
    trim A.
    {
      red.
      intros.
      unfold newostack, offset_after_alloc.
      eapply Zdivides_trans with 8.
      destruct chunk; try (exists 8; reflexivity);
        try (exists 4; reflexivity);
        try (exists 2; reflexivity);
        try (exists 1; reflexivity).
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite H0. apply SPAL; auto.
      rewrite EQ. auto.
      apply align_divides. omega.
    }
    trim A.
    {
      intros b0 delta' ofs k p JB PERM RNG.
      generalize (NIB _ _ _ _ _ JB PERM).
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. 
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      generalize (align_le (frame_size fi) 8).
      unfold newostack, offset_after_alloc in RNG.
      rewrite Z.max_r in RNG by omega. simpl in RNG. omega.
      rewrite NIL in *. simpl. tauto. 
    }
    trim A.
    {
      revert NS. unfold no_stack.
      generalize (Mem.stack_adt m1').
      induction 1; simpl; intros; eauto.
      destruct x. simpl in *. rewrite H.
      simpl. intuition. 
    }
    destruct A as (f' & MINJ' & INCR & EQ1 & EQ2).
    exists f'.
    split.
    {
      intros.
      destruct peq; subst; eauto.
    }
    split; auto.
    (* store parent *)
    exploit Mem.store_mapped_inject. apply MINJ'. simpl in *; eauto. eauto.
    eapply val_inject_incr; eauto. intros (m3' & STORE & MINJ2).
    simpl.
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr (seg_ofs (frame_link fi)))) =
            seg_ofs (frame_link fi) + newostack) as EQ.
    2: rewrite EQ, STORE.
    rewrite Ptrofs.add_commut. erewrite Mem.address_inject; eauto. rewrite Ptrofs.unsigned_repr. omega. omega.
    exploit Mem.store_valid_access_3. exact STORE_PARENT. 
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    eexists; split; eauto.
    (* store return address *)
    exploit Mem.store_mapped_inject. apply MINJ2. simpl in *; eauto. eauto. 
    eapply val_inject_incr; eauto. intros (m4' & STORE' & MINJ3).
    assert (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr newostack) (Ptrofs.repr (seg_ofs (frame_retaddr fi)))) =
            seg_ofs (frame_retaddr fi) + newostack) as EQ'.
    2: rewrite EQ', STORE'.
    rewrite Ptrofs.add_commut.
    erewrite Mem.address_inject; eauto.
    rewrite Ptrofs.unsigned_repr; omega.
    exploit Mem.store_valid_access_3. exact STORE_RETADDR.
    intro VA; eapply Mem.store_valid_access_1 in VA; eauto. destruct VA.
    eapply H. 
    rewrite Ptrofs.unsigned_repr; generalize (size_chunk_pos Mptr); omega.
    eexists; split; eauto.
    (* record the stack block *)
    exploit Mem.record_stack_blocks_inject. apply MINJ3. 4: eauto.
    instantiate (1:= None). simpl. auto.
    simpl. intros. split; auto. intro; subst.
    revert H. repeat rewrite_stack_blocks. intro H.
    eapply Mem.in_frames_valid in H.
    eapply Mem.fresh_block_alloc in H; eauto.
    red; easy.
    intros (m5' & RSB' & MINJ'').
    rewrite RSB'.
    eexists; split; eauto.
    (* proving the final match_states *)
    rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
    econstructor; eauto.
    - intros b0 o A. unfold rs2 in A.
      rewrite nextinstr_rsp in A.
      rewrite Pregmap.gss in A. inv A; auto.
    - intros r.
      unfold rs2, rs2'.
      destruct (PregEq.eq r RSP).
      + subst. rewrite ! nextinstr_rsp. rewrite ! Pregmap.gss.
        econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
      + apply val_inject_nextinstr. intros.
        assert (r0 <> RSP) by intuition congruence.
        rewrite ! (Pregmap.gso _ _ H0) by auto.
        eapply val_inject_set; eauto.
    - eapply Mem.record_stack_block_valid; eauto.
      eapply Mem.store_valid_block_1. eauto.
      eapply Mem.store_valid_block_1. eauto.
      eauto.
    - red. unfold rs2'. rewrite nextinstr_rsp. rewrite Pregmap.gss. inversion 1. subst.
      repeat rewrite_stack_blocks.
      rewrite Ptrofs.unsigned_repr by auto.
      unfold newostack, offset_after_alloc in *.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
      rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ.
      rewrite H0. rewrite (AGSP _ EQRSP).
      simpl. omega.
      rewrite EQRSP, NIL in *. simpl. omega.
    - rewrite_stack_blocks. 
      unfold rs2. rewrite nextinstr_rsp. apply Pregmap.gss.
    - red. intros ostack1 A. unfold rs2' in A. rewrite nextinstr_rsp in A. rewrite Pregmap.gss in A.
      inversion A. subst.
      rewrite Ptrofs.unsigned_repr by omega.
      unfold newostack.
      apply Z.divide_sub_r.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
      rewrite H; apply SPAL; auto.
      rewrite EQRSP. auto.
      apply align_divides. omega.
    - red. intros ofs k p PERM.
      repeat rewrite_perms_bw PERM. eauto.
    - red; intros.
      repeat rewrite_perms_fw. eauto.
    - red; intros. repeat rewrite_stack_blocks. constructor; auto. 
    - unfold rs2'. rewrite nextinstr_rsp, Pregmap.gss. inversion 1. eauto.
    - rewrite Ptrofs.unsigned_repr by omega.
        red. intros b0 delta o k p JB PERM.
        repeat rewrite_perms_bw PERM.
        destruct peq.
        * subst. rewrite EQ1 in JB. inv JB. split. omega.
          rewrite_stack_blocks. simpl. auto.
        * split. unfold newostack, offset_after_alloc.
          transitivity curofs.
          -- generalize (Z.le_max_l 0 (frame_size fi)); intro MAX.
             generalize (align_le (Z.max 0 (frame_size fi)) 8). omega.
          -- 
             destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst. 
             rewrite H. 
             rewrite EQ2 in JB; auto. 
             exploit NIB; eauto. tauto.
             exploit NIB; eauto. rewrite <- EQ2. eauto. auto. 
             rewrite NIL. simpl; tauto.
          -- repeat rewrite_stack_blocks. simpl; auto.
             right.
             eapply NIB; eauto. rewrite <- EQ2; eauto.
    - repeat rewrite_stack_blocks.
      constructor; auto.
      eapply inject_stack_incr; eauto.
      rewrite EQ1. f_equal. f_equal.
      unfold newostack, offset_after_alloc.
      destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQRSP NIL]]]; subst.
      rewrite H.
      rewrite AGSP. omega. auto. rewrite EQRSP, NIL. simpl; omega.
    - intros b0 fi0 delta GFI FB0 b' o delta' k p FB1 P1.
      unfold Mem.get_frame_info in GFI.
      revert GFI. repeat rewrite_stack_blocks. intro GFI.
      simpl in GFI.
      repeat rewrite_perms_bw P1.
      destr_in GFI.
      + inv GFI. rewrite FB0 in EQ1; inv EQ1.
        destr_in P1.
        * subst. rewrite FB0 in FB1; inv FB1.
          rewrite Z.max_r by omega.  omega.
        * rewrite EQ2 in FB1 by auto.
          eapply NIB in P1; eauto.
          destruct P1 as (LE & IN).
          unfold newostack, offset_after_alloc.
          destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA.
          omega. rewrite NIL in IN; easy.
      + rewrite EQ2 in FB0 by auto.
        intro RNG.
        assert (0 < frame_size fi0).
        destruct (zlt 0 (frame_size fi0)); auto.
        rewrite Z.max_l in RNG by omega. change (align 0 8) with 0 in RNG. omega.
        rewrite Z.max_r in RNG by omega.
        destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA, ?NIL in *; try easy.
        generalize (perm_stack_eq _ _ _ _ PS GFI). intro PF0. 
        destr_in P1.
        * subst. rewrite EQ1 in FB1; inv FB1.
          cut (newostack + (frame_size fi)  <= delta). omega.
          unfold newostack. rewrite EQA.
          rewrite AGSP; auto.
          eapply in_stack_inj_below in GFI; eauto.
          destruct GFI as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0.
          rewrite Z.max_r in * by omega.
          unfold offset_after_alloc.
          rewrite Z.max_r by omega.
          cut (Memimpl.Mem.size_stack (Mem.stack_adt m1) 
               >= Memimpl.Mem.size_stack l2).
          generalize (align_le (frame_size fi) 8). omega.
          rewrite EQADT.
          rewrite size_stack_app.
          generalize (size_stack_pos l1); omega.
        * eapply IP.  apply GFI. eauto.
          rewrite <- EQ2. apply FB1. auto. eauto.
          rewrite Z.max_r by omega. omega.
    - repeat rewrite_stack_blocks. 
      constructor; auto.
      eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
      split; intros.
      repeat rewrite_perms_bw H0.
      destr_in H0.
      subst.
      eapply Mem.in_frames_valid in H.
      eapply Mem.fresh_block_alloc in H. easy.
      eauto.
      repeat rewrite_perms_fw. auto.
      split; intros.
      repeat rewrite_perms_bw H.
      rewrite pred_dec_true in H; auto.
      do 3 rewrite_perms_fw. eapply Mem.perm_implies. eapply Mem.perm_alloc_2. eauto. eauto. constructor.
    - repeat rewrite_stack_blocks.
      assert (Mem.unchanged_on (fun b o => in_frames (Mem.stack_adt m1) b) m1 m5).
      {
        eapply Mem.unchanged_on_trans.
        eapply Mem.alloc_unchanged_on. eauto.
        eapply Mem.unchanged_on_trans.
        eapply Mem.store_unchanged_on; simpl in *; eauto.
        intros. intro INF; eapply Mem.in_frames_valid in INF; eapply Mem.fresh_block_alloc; eauto.
        eapply Mem.unchanged_on_trans.
        eapply Mem.store_unchanged_on; simpl in *; eauto.
        intros. intro INF; eapply Mem.in_frames_valid in INF; eapply Mem.fresh_block_alloc; eauto.
        eapply Mem.strong_unchanged_on_weak.
        eapply Mem.record_stack_block_unchanged_on; eauto.
      }
      eapply load_rsp_inv' in LRSP.
      eapply load_rsp_add. eauto.



      erewrite load_record_stack_blocks. 2: eauto.
      erewrite Mem.load_store_other. 
      erewrite Mem.load_store_same. 
      2: rewrite <- STORE_PARENT. 2: simpl; f_equal.
      destr_in AGSP1.
      rewrite AGSP1.
      change (Mptr) with (chunk_of_type Tptr).
      rewrite Val.load_result_same. auto. auto.
      destr_in AGSP1.
      destr_in AGSP1.
      destr_in AGSP1.
      destr_in AGSP1.
      rewrite AGSP1.
      change (Mptr) with (chunk_of_type Tptr).
      rewrite Val.load_result_same. auto. simpl. unfold Tptr.
      destruct ptr64; auto. 
      eauto.
      right. 
      assert (DISJ: forall o, in_segment o (frame_link fi) -> in_segment o (frame_retaddr fi) -> False).
      generalize (frame_disjoints fi).
      intros (A & B).
      intros. eapply B in H0; eauto. apply H0; left; auto.
      unfold in_segment in DISJ. rewrite frame_retaddr_size, frame_link_size in DISJ.
      destruct (zle (seg_ofs (frame_link fi) + size_chunk Mptr) (seg_ofs (frame_retaddr fi))); auto.
      destruct (zle (seg_ofs (frame_retaddr fi) + size_chunk Mptr) (seg_ofs (frame_link fi))); auto.
      exfalso.
      specialize (DISJ (Z.max (seg_ofs (frame_link fi)) (seg_ofs (frame_retaddr fi)))).
      trim DISJ. split. apply Z.le_max_l.
      rewrite Zmax_spec. destr. omega. omega. 
      trim DISJ. split. apply Z.le_max_r.
      rewrite Zmax_spec. destr. omega. omega. auto.
      auto.
      intros bs INF. apply Mem.in_frames_valid in INF.
      eapply Plt_Ple_trans. apply INF.
      erewrite Mem.alloc_result. apply Ple_refl. eauto.
      eapply Mem.unchanged_on_implies. apply H.
      simpl; intros.
      red in H0.
      destr_in H0.
      destruct (in_frames_dec (Mem.stack_adt m1) b0); auto.
      rewrite not_in_frames_get_assoc in Heqo; eauto; congruence.
    - destruct GLOBSYMB_INJ; split.
      + intros. eapply INCR. eauto.
      + intros. destruct (peq b1 b).
        subst; rewrite EQ1 in H2. inv H2.
        simpl.
        unfold Genv.block_is_volatile.
        unfold Genv.find_var_info.
        replace (Genv.find_def ge bstack) with (None (A:=globdef Asm.fundef unit)).
        replace (Genv.find_def ge b) with (None (A:=globdef Asm.fundef unit)).
        auto.
        unfold Genv.find_def.
        destruct (Maps.PTree.get b (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        exploit Mem.fresh_block_alloc. eauto. red. xomega. easy.
        unfold Genv.find_def.
        destruct (Maps.PTree.get bstack (Genv.genv_defs ge)) eqn:EQdef; auto.
        apply Genv.genv_defs_range in EQdef.
        unfold bstack in EQdef. xomega.
        rewrite EQ2 in H2.
        eauto.
        auto.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_alloc. 2: eauto. xomega.
    - erewrite Mem.record_stack_block_nextblock. 2: eauto.
      erewrite Mem.nextblock_store. 2 : eauto.
      erewrite Mem.nextblock_store. 2 : eauto. xomega.
  Qed.

  Lemma size_stack_divides {A} (l: list (A*Z)):
    (8 | Memimpl.Mem.size_stack l).
  Proof.
    induction l; simpl; intros; eauto.
    exists 0; omega.
    destruct a.
    apply Z.divide_add_r. auto. apply align_divides. omega.
  Qed.

  Lemma inject_stack_all_below:
    forall l m,
      load_rsp l m ->
      forall b b',
        in_frame (fst (hd (None,0) l)) b ->
        in_frames (tl l) b' ->
        Plt b' b. 
  Proof.
    induction 1; simpl; intros. easy.
    easy.
    subst. 
    destruct H3. subst. auto.
    simpl in *.
    eapply Plt_trans.
    eapply IHload_rsp. eauto. eauto. eauto. 
  Qed.

  Lemma inject_stack_only_once:
    forall l m a b,
      load_rsp (a::l) m ->
      in_frame (fst a) b ->
      get_assoc l b = None.
  Proof.
    inversion 1; subst. simpl. auto.
    simpl. intro; subst.
    rewrite pred_dec_false.
    rewrite not_in_frames_get_assoc; auto.
    intro INF.
    cut (Plt b0 b'). xomega.
    eapply inject_stack_all_below; eauto.
    simpl. auto.
    intro; subst. xomega.             
  Qed.

  Lemma inject_stack_norepeat:
    forall l m a b,
      load_rsp (a::l) m ->
      in_frame (fst a) b ->
      ~ in_frames l b.
  Proof.
    inversion 1; subst. simpl. auto.
    simpl. intro; subst.
    destruct (peq b0 b').  subst. xomega. intros [A|A]; try congruence.
    cut (Plt b0 b'). xomega.
    eapply inject_stack_all_below; eauto.
    simpl. auto.
  Qed.

  Lemma exec_instr_inject':
    forall j ostack m1 m2 rs1 rs2 f i rs1' m1',
      match_states j ostack (State rs1 m1) (State rs2 m2) ->
      asm_instr_no_rsp i ->
      asm_instr_no_stack i ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' ostack' rs2' m2',
        exec_instr ge f i rs2 m2 = Next rs2' m2'
        /\ match_states j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros j ostack m1 m2 rs1 rs2 f i rs1' m1' MS AINR AINS EI.
    destruct (is_unchanged i) eqn:?.
    - edestruct exec_instr_inject as (rs2' & m2' & EXEC' & MINJ' & RINJ'); eauto.
      inv MS; eauto. inv MS; eauto.
      exists j, ostack, rs2', m2'; split; [|split]; eauto.
      destruct i; simpl in *; eauto; try congruence.
      inv MS; econstructor; eauto.
      + erewrite AINR; eauto.
      + eapply asmgen_nextblock_forward in EXEC'.
        red in VB |- *. xomega.
      + red. intros. erewrite AINR in H; eauto.
        edestruct AINS. eauto. apply EI. rewrite H0. auto.
      + edestruct AINS. eauto. apply EI. rewrite H.
        erewrite AINR; eauto.
      + red. intros.
        erewrite AINR in H; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'.
        rewrite H1 in H; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'.
        rewrite H1; eauto.
      + red; intros.
        edestruct AINS. eauto. apply EXEC'. rewrite H. auto.
      + erewrite AINR; eauto.
      + edestruct AINS. eauto. apply EI.
        red; intros.
        edestruct AINS. eauto. apply EI. rewrite H3.
        eapply NIB. auto. rewrite <- H4. eauto.
      + edestruct AINS. eauto. apply EI. rewrite H. eapply inject_stack_incr; eauto.
      + edestruct AINS. eauto. apply EI.
        red. unfold Mem.get_frame_info.
        rewrite H.
        intros b fi delta GFI JB b' o delta' k p JB' PERM RNG.
        eapply IP. eauto. eauto. eauto. rewrite <- H0; eauto.
        apply RNG.
      + edestruct AINS. eauto. apply EI. rewrite H.
        eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
        intros; apply H0.
      + edestruct AINS. eauto. apply EI. rewrite H.
        intros; eapply load_rsp_inv'. eauto.
        eapply exec_instr_unchanged_on; eauto.
      + etransitivity. apply GlobLe.
        eapply asmgen_nextblock_forward; eauto.
      + etransitivity. apply GlobLeT.
        eapply asmgen_nextblock_forward; eauto.

    - destruct i; simpl in *; try congruence.
      + (* allocframe *)
        repeat destr_in EI.
        unfold check_alloc_frame in Heqb0.
        repeat rewrite andb_true_iff in Heqb0.
        destruct Heqb0 as (EQ1 & EQ2).
        apply ZEQ in EQ1.
        apply ZEQ in EQ2.
        inversion MS; subst.
        rewrite Ptrofs.add_zero_l in *.
        rewrite EQ1, EQ2 in *.
        edestruct alloc_inject as (j' & JSPEC & INCR & m3' & STORE1 & m4' & STORE2 & m5' & RSB' & MS') ; eauto.
        rewrite <- EQ1. apply Ptrofs.unsigned_range_2.
        rewrite <- EQ2. apply Ptrofs.unsigned_range_2.
        simpl in *.
        set (newostack := offset_after_alloc (current_offset (rs2 RSP)) frame).
        fold newostack in STORE1, STORE2, JSPEC, MS'.
        rewrite <- EQ1 in STORE1. rewrite Ptrofs.repr_unsigned in STORE1.
        rewrite <- EQ2 in STORE2. rewrite Ptrofs.repr_unsigned in STORE2.
        rewrite STORE1, STORE2, RSB'.
        exists j',  newostack; eexists; eexists; split; eauto.

      + repeat destr_in EI.
        inv MS.
        specialize (RSPzero _ _ Heqv1). subst.
        exploit Mem.loadv_inject. eauto. apply Heqo.
        apply Val.offset_ptr_inject. rewrite <- Heqv1; auto. intros (v2 & LOAD2 & INJ2).
        exploit Mem.loadv_inject. eauto. apply Heqo0.
        apply Val.offset_ptr_inject. rewrite <- Heqv1; auto. intros (v3 & LOAD3 & INJ3).
        rewrite LOAD2, LOAD3.
        unfold check_top_frame in Heqb0.
        repeat (destr_in Heqb0; [idtac]).
        repeat rewrite andb_true_iff in Heqb1.
        destruct Heqb1 as ((((A & B) & C) & D) & E).
        destruct (peq b0 b); try congruence. subst.
        apply ZEQ in B. apply ZEQ in C. apply ZEQ in D. apply ZEQ in E. subst.
        set (newostack := Ptrofs.unsigned ostack0 + align (Z.max 0 (frame_size f1)) 8).
        edestruct free_inject as (m2' & USB & INJ); eauto. rewrite USB.
        exists j, newostack; eexists; eexists; split; [|split]; eauto.
        generalize (RINJ RSP). rewrite Heqv1. inversion 1; subst.
        symmetry in H2.
        rewrite Ptrofs.add_zero_l in *.
        exploit RSPEQ. eauto. intros (AA & B). subst.
        specialize (AGSP _ H2).
        assert (v0 = (match l with
                        nil => init_sp
                      | (Some (frame_with_info b' _),_)::r => Vptr b' Ptrofs.zero
                      | _ => Vundef
                      end)).
        {
          move Heqo0 at bottom.
          simpl in Heqo0. rewrite Ptrofs.add_zero_l in Heqo0.
          rewrite D in Heqo0.
          inv LRSP; congruence.
        }
        subst.
        specialize (SPAL _ H2).
        generalize (Mem.unrecord_stack_adt _ _ Heqo2).
        erewrite Mem.free_stack_blocks. 2: eauto. rewrite Heql. intros (bb0 & EQ).
        inv EQ.
        assert (0 <= Memimpl.Mem.stack_limit - Memimpl.Mem.size_stack (Mem.stack_adt m1') <= Ptrofs.max_unsigned) as RNGnewofs. 
        {
          generalize (size_stack_below m1').
          generalize (size_stack_pos (Mem.stack_adt m1')).
          omega.
        }
        assert (0 <= newostack <= Ptrofs.max_unsigned) as RNGnew.
        {
          unfold newostack.
          rewrite AGSP. rewrite Heql. simpl. omega.
        }
        rewrite <- (Ptrofs.unsigned_repr newostack) by omega.
        econstructor; eauto.
        * intros. rewrite nextinstr_rsp in H0. rewrite Pregmap.gso in H0 by congruence.
          rewrite Pregmap.gss in H0. subst.
          destr_in H0. destr_in Heqb0. destruct p.
          destruct o0; try discriminate.
          destruct f0; try discriminate.
          inv H0; auto. 
        * intros; apply val_inject_nextinstr.
          intros; apply val_inject_set; auto.
          intros; apply val_inject_set; auto.
        * red; edestruct Mem.unrecord_stack_block_mem_unchanged. simpl ; apply USB.
          rewrite H0; eauto.
        * red. rewrite nextinstr_rsp.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. intros; subst.
          inv INJ3.
          repeat destr_in H0. discriminate.
          rewrite Ptrofs.add_zero_l.
          inv IS. inv H6. rewrite H5 in H12; inv H12. simpl.
          rewrite Ptrofs.unsigned_repr. omega. simpl in RNGnewofs; omega.
          repeat destr_in H1. discriminate.
        * repeat destr_in INJ3.
          rewrite H2 in H. inv H. rewrite H3 in H6. inv H6.
          rewrite nextinstr_rsp. rewrite Pregmap.gso by congruence.
          rewrite Pregmap.gss.
          inv LRSP. auto.
        * red. rewrite nextinstr_rsp. 
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. intros; subst.
          inv LRSP. rewrite <- H6 in *. destr_in Heqb0; inv INJ3.
          rewrite <- H6 in *. inv INJ3.
          inv IS. inv H10. rewrite H5 in H16; inv H16.
          rewrite Ptrofs.add_zero_l.
          rewrite Ptrofs.unsigned_repr. rewrite Heql in AGSP. simpl in AGSP.
          apply Z.divide_sub_r.
          apply Z.divide_sub_r.
          auto.
          apply size_stack_divides.
          apply align_divides; omega.
          simpl in RNGnewofs. omega.
        * red.
          intros ofs k p PERM.
          eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto. eauto.
        * red.
          intros ofs k p RNG.
          eapply Mem.unrecord_stack_block_perm'. 2: eauto. eauto.                 
        * red.
          edestruct Mem.unrecord_stack_adt. apply USB. red in NS. rewrite H0 in NS.
          inv NS; auto.
        * unfold nextinstr.
          rewrite ! Pregmap.gso by congruence.
          rewrite Pregmap.gss. 
          intros. subst.
          inv LRSP. rewrite <- H6 in *. destr_in Heqb0; inv INJ3.
          rewrite <- H6 in *. inv INJ3.
          inv IS. inv H10. rewrite H5 in H16; inv H16.
          split; auto. rewrite Ptrofs.add_zero_l.
          unfold newostack. rewrite AGSP. rewrite Heql. simpl. f_equal. omega.
        * red. intros b0 delta0 o k p JB0 PERM.
          eapply Mem.unrecord_stack_block_perm in PERM. 2: eauto.
          erewrite Mem.perm_free in PERM. 2: eauto.
          destruct PERM as (NOTSAME & PERM).
          generalize (NIB b0 delta0 o k p JB0 PERM).
          destruct (peq b0 b).
          -- subst.
             inv PS. clear H7. rename H8 into PERM_in_range.
             apply PERM_in_range in PERM. intuition.
          -- clear NOTSAME.
             rewrite Heql. simpl. 
             intros (LE & OR). destruct OR; try congruence. split; auto.
             rewrite Ptrofs.unsigned_repr by omega.
             unfold newostack.
             destruct (zle (Ptrofs.unsigned (Ptrofs.repr delta) + align (Z.max 0 (frame_size f1)) 8) (o + delta0)); auto.
             exfalso.
             apply Z.gt_lt in g.
             assert (max_perm: forall m b o k p, Mem.perm m b o k p -> Mem.perm m b o Max Nonempty).
             {
               intros.
               eapply Mem.perm_implies.
               eapply Mem.perm_max. eauto. constructor.
             }
             generalize (Mem.free_range_perm _ _ _ _ _ Heqo1). intro FP.
             assert (0 < frame_size f1).
             destruct (zlt 0 (frame_size f1)); auto.
             apply Z.ge_le in g0.
             rewrite Z.max_l in g by omega.
             change (align 0 8) with 0 in g. omega.
             generalize (fun pf => Mem.address_inject _ _ _ b Ptrofs.zero _ _ Freeable MINJ (FP _ pf) H3).
             rewrite Ptrofs.unsigned_zero. rewrite Ptrofs.add_zero_l.  simpl.
             intro UR. trim UR. omega.
             destruct (zlt (o + delta0) (delta + frame_size f1)).
             ++ generalize (fun o2 RNG => Mem.mi_no_overlap _ _ _ MINJ b0 _ _ _ _ _ o o2 n JB0 H3 (max_perm _ _ _ _ _ PERM) (max_perm _ _ _ _ _ (FP _ RNG))).
                assert (exists o2, 0 <= o2 < frame_size f1 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                intro CONTRA; edestruct CONTRA; eauto.
             ++ assert (delta + frame_size f1 <= o + delta0 < delta + align (frame_size f1) 8).
                rewrite Z.max_r in g by omega. omega.
                assert (exists o2, frame_size f1 <= o2 < align (frame_size f1) 8 /\ o + delta0 = o2 + delta) as EX.
                {
                  exists (o + delta0 - delta).
                  omega.
                }
                destruct EX as (o2 & RNG & EQ').
                eapply IP. 4: apply PERM.  3: eauto. 2: apply H3.
                unfold Mem.get_frame_info; rewrite Heql.
                simpl. rewrite pred_dec_true; auto.
                rewrite Z.max_r. omega. omega.
        * 
          inv IS. auto.
        * red; intros.
          destruct (peq b' b).
          subst.
          eapply Mem.unrecord_stack_block_perm in H5. 2: eauto.
          eapply Mem.perm_free_2 in H5.
          easy. eauto.
          eapply perm_stack_eq. eauto. simpl. rewrite pred_dec_true. auto. reflexivity.
          eapply Mem.perm_free_3. eauto. eauto.
          eapply Mem.unrecord_stack_block_perm in H5. 2: eauto.
          eapply Mem.perm_free_3 in H5. 2: eauto.
          eapply IP; eauto.
          unfold Mem.get_frame_info. rewrite Heql.
          simpl.
          destruct peq; auto.
          subst.
          unfold Mem.get_frame_info in H0.
          erewrite inject_stack_only_once in H0.
          congruence.
          eauto. simpl; auto.
        * inv PS. eapply perm_stack_inv; eauto.
          intros; eapply Mem.in_frames_valid.
          rewrite Heql; simpl; auto.
          intros.
          cut (b0 <> b).
          intro DIFF.
          split; intros P.
          eapply Mem.unrecord_stack_block_perm in P. 2: eauto.
          eapply Mem.perm_free_3; eauto.
          eapply Mem.unrecord_stack_block_perm'. eauto.
          eapply Mem.perm_free_1; eauto.
          intro; subst.
          eapply inject_stack_norepeat in H0; eauto.
          simpl; auto.
        * inversion LRSP. constructor.
          rewrite <- H6 in *.
          eapply load_rsp_inv'. eauto.
          eapply Mem.unchanged_on_trans.
          eapply Mem.unchanged_on_implies.
          eapply Mem.free_unchanged_on. eauto.
          instantiate (1:= fun b0 o => b0 <> b). simpl. congruence.
          simpl.
          intros. 
          intro; subst.
          red in H10. destr_in H10. simpl in Heqo3. destr_in Heqo3. subst. xomega.
          exploit inject_stack_norepeat. apply LRSP. simpl. eauto.
          simpl.
          destruct (in_frames_dec l b); auto.
          erewrite not_in_frames_get_assoc in Heqo3; eauto; congruence. auto.
          eapply Mem.strong_unchanged_on_weak.
          eapply Mem.unrecord_stack_block_unchanged_on.
          eauto.
        * etransitivity. apply GlobLe.
          erewrite <- Mem.nextblock_free. 2: eauto.
          erewrite <- Mem.unrecord_stack_block_nextblock.
          2: eauto. xomega.
       * etransitivity. apply GlobLeT.
          erewrite <- Mem.unrecord_stack_block_nextblock.
          2: eauto. xomega.
  Qed.

  Definition asm_prog_no_rsp (ge: Genv.t Asm.fundef unit):=
    forall b f,
      Genv.find_funct_ptr ge b = Some (Internal f) ->
      asm_code_no_rsp (fn_code f).

  Hypothesis prog_no_rsp: asm_prog_no_rsp ge.

  Existing Instance symbols_inject_instance.
  Context `{ecprops: !ExternalCallsProps mem}.

  Axiom external_call_perm_frames:
    forall {F V} ef (ge: Genv.t F V) args m1 t res m2,
      external_call ef ge args m1 t res m2 ->
      forall b o k p,
        in_frames (Mem.stack_adt m1) b ->
        Mem.perm m2 b o k p <-> Mem.perm m1 b o k p.


  Axiom external_call_perm_bstack:
    forall {F V} ef (ge: Genv.t F V) args m1 t res m2,
      external_call ef ge args m1 t res m2 ->
      forall o k p,
        Mem.perm m2 bstack o k p <-> Mem.perm m1 bstack o k p.


  Lemma inj_incr_sep_same:
    forall j j' m1 m2 b1 b2 delta,
      inject_incr j j' ->
      inject_separated j j' m1 m2 ->
      j' b1 = Some (b2, delta) ->
      Mem.valid_block m2 b2 ->
      j b1 = Some (b2, delta).
  Proof.
    intros.
    destruct (j b1) eqn:JB.
    destruct p. eapply H in JB; eauto.
    congruence.
    exploit H0; eauto. intuition congruence.
  Qed.

  Lemma in_link_not_in_data:
    forall f o,
      in_segment o (frame_link f)
      -> ~ in_stack_data o (o + 1) f.
  Proof.
    clear. intros f o IS ISD.
    eapply frame_disjoints in IS.
    apply IS. do 4 right; left.
    apply ISD. omega.
  Qed.

  Lemma set_res_no_rsp:
    forall res vres rs,
      no_rsp_builtin_preg res ->
      set_res res vres rs RSP = rs RSP.
  Proof.
    induction res; simpl.
    - intros. eapply Pregmap.gso. auto.
    - auto.
    - intros vres rs (NR1 & NR2).
      rewrite IHres2; auto.
  Qed.

  Lemma val_inject_set_res:
    forall r rs1 rs2 v1 v2 j,
      Val.inject j v1 v2 ->
      (forall r0, Val.inject j (rs1 r0) (rs2 r0)) ->
      forall r0, Val.inject j (set_res r v1 rs1 r0) (set_res r v2 rs2 r0).
  Proof.
    induction r; simpl; intros; auto.
    apply val_inject_set; auto.
    eapply IHr2; eauto.
    apply Val.loword_inject. auto.
    intros; eapply IHr1; eauto.
    apply Val.hiword_inject. auto.
  Qed.

  Definition init_data_diff (id: init_data) (i: ident) :=
    match id with
      Init_addrof ii _ => ii <> i
    | _ => True
    end.

  Lemma store_init_data_eq:
    forall F V m (ge: _ F V) id gv b o i,
      init_data_diff i id ->
      Genv.store_init_data (Genv.add_global ge (id,gv)) m b o i =
      Genv.store_init_data ge m b o i.
  Proof.
    destruct i; simpl; intros; auto.
    unfold Genv.find_symbol; simpl. 
    rewrite Maps.PTree.gso; auto.
  Qed.

  Lemma store_init_data_list_eq:
    forall F V id i, 
      Forall (fun x => init_data_diff x id) i ->
      forall m (ge: _ F V) gv b o,
        Genv.store_init_data_list (Genv.add_global ge (id,gv)) m b o i =
        Genv.store_init_data_list ge m b o i.
  Proof.
    induction 1; simpl; intros; auto.
    rewrite store_init_data_eq; auto.
    destr. 
  Qed.

  Lemma alloc_global_eq:
    forall F V (l: (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall v, snd l = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_global (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_global ge m l .
  Proof.
    destruct l; simpl; intros.
    repeat (destr; [idtac]).
    rewrite store_init_data_list_eq. auto.
    apply H; auto.
  Qed.

  Lemma alloc_globals_eq:
    forall F V (l: list (ident * option (globdef F V))) m (ge: _ F V) id gv,
      (forall x v, In x l -> snd x = Some (Gvar v) -> Forall (fun x => init_data_diff x id) (gvar_init v)) ->
      Genv.alloc_globals (Genv.add_global ge (id,gv)) m l =
      Genv.alloc_globals ge m l .
  Proof.
    induction l; simpl; intros; eauto.
    rewrite alloc_global_eq. destr.
    apply IHl. intros; eauto.
    eauto.
  Qed.

  Lemma find_symbol_add_globals_other:
    forall F V l (ge: _ F V) s,
      ~ In s (map fst l) ->
      Genv.find_symbol (Genv.add_globals ge l) s =
      Genv.find_symbol ge s.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. intuition.
  Qed.


  Lemma find_symbol_add_global_other:
    forall F V l (ge: _ F V) s,
      s <> fst l ->
      Genv.find_symbol (Genv.add_global ge l) s =
      Genv.find_symbol ge s.
  Proof.
    destruct l; simpl; intros; eauto.
    unfold Genv.find_symbol; simpl.
    apply Maps.PTree.gso. intuition. 
  Qed.

  Lemma find_symbol_none_add_global:
    forall F V (ge: Genv.t F V) a i,
      Genv.find_symbol (Genv.add_global ge a) i = None ->
      i <> fst a /\ Genv.find_symbol ge i = None.
  Proof.
    unfold Genv.find_symbol; simpl.
    intros F V ge0 a i.
    rewrite Maps.PTree.gsspec.
    destr.
  Qed.

  Lemma find_symbol_none_add_globals:
    forall F V a (ge: Genv.t F V) i,
      Genv.find_symbol (Genv.add_globals ge a) i = None ->
      ~ In i (map fst a) /\ Genv.find_symbol ge i = None.
  Proof.
    induction a; simpl; intros; eauto.
    apply IHa in H.
    destruct H as (H1 & H).
    apply find_symbol_none_add_global in H; auto.
    intuition.
  Qed.

  Lemma find_symbol_none_not_in_defs:
    forall F V (p: program F V) i,
      Genv.find_symbol (Genv.globalenv p) i = None ->
      ~ In i (map fst (prog_defs p)).
  Proof.
    unfold Genv.globalenv.
    intros F V p.
    generalize (Genv.empty_genv F V (prog_public p)).
    generalize (prog_defs p).
    induction l; simpl; intros; eauto.
    apply find_symbol_none_add_globals in H.
    destruct H as (A & B).
    apply find_symbol_none_add_global in B.
    destruct B as (B & C).
    intuition.    
  Qed.

 


  Lemma extcall_arg_inject:
    forall j rs1 m1 arg1 loc rs2 m2,
      extcall_arg rs1 m1 loc arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j m1 m2 ->
      exists arg2,
        extcall_arg rs2 m2 loc arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eexists; split; try econstructor; eauto.
    exploit Mem.loadv_inject; eauto.
    apply Val.offset_ptr_inject; eauto.
    intros (v2 & LOAD & INJ).
    eexists; split; try econstructor; eauto.
  Qed.

  Lemma extcall_arg_pair_inject:
    forall j rs1 m1 arg1 ty rs2 m2,
      extcall_arg_pair rs1 m1 ty arg1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j m1 m2 ->
      exists arg2,
        extcall_arg_pair rs2 m2 ty arg2 /\
        Val.inject j arg1 arg2.
  Proof.
    destruct 1; simpl; intros.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ);
      eexists; split; try econstructor; eauto.
    eapply extcall_arg_inject in H; eauto.
    destruct H as (arg2 & EA & INJ).
    eapply extcall_arg_inject in H0; eauto.
    destruct H0 as (arg3 & EA1 & INJ1).
    eexists; split; try econstructor; eauto.
    apply Val.longofwords_inject; eauto.
  Qed.

  Lemma extcall_arguments_inject:
    forall j rs1 m1 args1 sg rs2 m2,
      extcall_arguments rs1 m1 sg args1 ->
      (forall r, Val.inject j (rs1 r) (rs2 r)) ->
      Mem.inject j m1 m2 ->
      exists args2,
        extcall_arguments rs2 m2 sg args2 /\
        Val.inject_list j args1 args2.
  Proof.
    unfold extcall_arguments.
    intros j rs1 m1 args1 sg rs2 m2.
    revert args1. generalize (loc_arguments sg).
    induction 1; simpl; intros; eauto.
    exists nil; split; try econstructor.
    eapply extcall_arg_pair_inject in H; eauto.
    decompose [ex and] H.
    edestruct IHlist_forall2 as (a2 & EA & INJ); eauto.
    eexists; split; econstructor; eauto.
  Qed.

  Theorem step_simulation:
    forall S1 t S2,
      Asm.step ge S1 t S2 ->
      forall j ostack S1' (MS: match_states j ostack S1 S1'),
      exists j' ostack' S2',
        step ge S1' t S2' /\
        match_states j' ostack' S2 S2'.
  Proof.
    destruct 1; intros; inversion MS; subst.
    - 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H7; inv H7. 
      assert (asm_instr_no_rsp i).
      {
        eapply prog_no_rsp. eauto.
        eapply Asmgenproof0.find_instr_in; eauto.
      }
      
      destruct (exec_instr_inject' _ _ _ _ _ _ _ _ _ _ MS H4 (asmgen_no_change_stack i) H2)
        as ( j' & ostack' & rs2' & m2' & EI' & MS' & INCR).
      do 3 eexists; split.
      eapply exec_step_internal; eauto.
      rewrite Ptrofs.add_zero. eauto.
      eauto.
    -
      edestruct (eval_builtin_args_inject) as (vargs' & Hargs & Hargsinj).
      6: eauto.
      eauto. eauto. eauto.
      eauto. 
      eapply GLOBSYMB_INJ.
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject.
      eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H9; inv H9. 
      
      do 3 eexists; split.
      eapply exec_step_builtin.
      eauto.
      eauto. 
      rewrite Ptrofs.add_zero; eauto.
      eauto.
      eauto.
      auto.
      reflexivity.
      econstructor.
      + eauto.
      + rewrite nextinstr_nf_rsp.
        intros b o.
        rewrite set_res_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        auto.
      + intros. apply val_inject_nextinstr_nf.
        apply val_inject_set_res; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
      + eapply external_call_valid_block; eauto.
      + red. rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. 
        rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red.
        intros.
        eapply Mem.perm_max in H6.
        eapply external_call_max_perm in H6.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply external_call_perm_bstack. eauto.
        eauto.
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + rewrite nextinstr_nf_rsp.
        rewrite set_res_no_rsp; auto.
        rewrite Asmgenproof0.undef_regs_other. eauto.
        intros; intro; subst.
        rewrite in_map_iff in H6.
        destruct H6 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      + 
        red.
        unfold Mem.get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.

        exploit inj_incr_sep_same. eauto. eauto. apply H7. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H9. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H10.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H11; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply external_call_perm_frames; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply load_rsp_inv'. eauto.
        eapply Mem.unchanged_on_implies.
        eapply external_call_unchanged_on. eauto.
        unfold Mem.strong_non_private_stack_access.
        unfold Mem.get_frame_info.
        intros b ofs0 ; generalize (Mem.stack_adt m). clear.
        induction l; simpl; intros; eauto.

        destruct a.
        simpl in *.
        red in H.
        simpl in H.
        destruct o.
        destruct f.
        destruct peq. subst.
        destruct o.
        eapply in_link_not_in_data; eauto.
        easy.
        destr_in H.
        eapply in_link_not_in_data; eauto.
        destruct in_dec. easy.
        destr_in H.
        eapply in_link_not_in_data; eauto.
        destr_in H.
        eapply in_link_not_in_data; eauto.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H9; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2. xomega.
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
      
    -

      edestruct (extcall_arguments_inject) as (vargs' & Hargs & Hargsinj).
      eauto.
      eauto. eauto. 
      edestruct (external_call_mem_inject_gen ef ge ge)
        as (j' & vres' & m2' & EC & RESinj & MemInj & Unch1 & Unch2 & INCR & SEP).
      apply meminj_preserves_globals'_symbols_inject. eauto.
      eauto.
      eauto.
      eauto. 
      generalize (RINJ PC); rewrite H. inversion 1; subst.
      assert (j b = Some (b,0)) as JB.
      {
        eapply GLOBFUN_INJ. eauto.
      }
      rewrite JB in H8; inv H8. 
      
      do 3 eexists; split.
      eapply exec_step_external.
      eauto.
      eauto.
      eauto.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      destruct Tptr; try easy.
      generalize (RINJ RSP). destruct (rs RSP); simpl in *; inversion 1; subst; try congruence.
      generalize (RINJ RA). destruct (rs RA); simpl in *; inversion 1; subst; try congruence.
      eauto.
      reflexivity.
      econstructor.
      + eauto.
      +

        Lemma set_pair_no_rsp:
          forall p res rs,
            no_rsp_pair p ->
            set_pair p res rs RSP = rs RSP.
        Proof.
          destruct p; simpl; intros; rewrite ! Pregmap.gso; intuition. 
        Qed.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + intros; apply val_inject_set.
        intros; apply val_inject_set.

        Lemma val_inject_set_pair:
          forall j p res1 res2 rs1 rs2,
            (forall r, Val.inject j (rs1 r) (rs2 r)) ->
            Val.inject j res1 res2 ->
            forall r,
              Val.inject j (set_pair p res1 rs1 r) (set_pair p res2 rs2 r).
        Proof.
          destruct p; simpl; intros; eauto.
          apply val_inject_set; auto.
          repeat (intros; apply val_inject_set; auto).
          apply Val.hiword_inject; auto.
          apply Val.loword_inject; auto.
        Qed.
        intros; apply val_inject_set_pair; auto.
        apply val_inject_undef_regs; auto.
        apply val_inject_undef_regs; auto.
        intros; eapply val_inject_incr; eauto.
        intros; eapply val_inject_incr; eauto.
        auto.
      + eapply external_call_valid_block; eauto.
      + red. repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        erewrite <- external_call_stack_blocks. eauto. eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto. 
      + red.
        repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto.
      + red.
        intros.
        eapply Mem.perm_max in H5.
        eapply external_call_max_perm in H5.
        2: eauto.
        eauto. eauto.
      + red.
        intros.
        eapply external_call_perm_bstack. eauto.
        eauto. 
      + red.
        erewrite <- external_call_stack_blocks. 2: eauto.
        eauto.
      + repeat rewrite Pregmap.gso by (congruence). 
        rewrite set_pair_no_rsp.
        rewrite Asmgenproof0.undef_regs_other.
        rewrite Asmgenproof0.undef_regs_other.
        eauto.
        intros; intro; subst. rewrite in_map_iff in H5.
        destruct H5 as (x & EQ & IN).
        apply preg_of_not_rsp in EQ. congruence.
        intros; intro; subst. clear - H5; simpl in *; intuition congruence.
        auto. 
      + red. intros b delta o k p JB1 PERM.
        erewrite <- external_call_stack_blocks. 2: eauto.
        destruct (j b) eqn:A. destruct p0.
        exploit INCR. eauto. eauto. intro JB2. rewrite JB1 in JB2; inv JB2.
        eapply NIB; eauto.
        eapply Mem.perm_max in PERM.
        eapply external_call_max_perm in PERM.
        2: eauto.
        eauto.
        eapply Mem.valid_block_inject_1; eauto.
        exploit SEP. eauto. eauto. intuition congruence.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply inject_stack_incr; eauto.
      + 
        red.
        unfold Mem.get_frame_info.
        erewrite <- external_call_stack_blocks. 2: eauto.
        intros.

        exploit inj_incr_sep_same. eauto. eauto. apply H6. auto.
        exploit inj_incr_sep_same. eauto. eauto. apply H8. auto.
        intros.
        eapply IP; eauto.
        eapply Mem.perm_max in H9.
        eapply external_call_max_perm; eauto.
        eapply Mem.valid_block_inject_1 in H10; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply perm_stack_inv. eauto.
        apply Mem.in_frames_valid.
        eapply external_call_perm_frames; eauto.
      + erewrite <- external_call_stack_blocks. 2: eauto.
        eapply load_rsp_inv'. eauto.
        eapply Mem.unchanged_on_implies.
        eapply external_call_unchanged_on. eauto.
        unfold Mem.strong_non_private_stack_access.
        unfold Mem.get_frame_info.
        intros b ofs0 ; generalize (Mem.stack_adt m). clear.
        induction l; simpl; intros; eauto.

        destruct a.
        simpl in *.
        red in H.
        simpl in H.
        destruct o.
        destruct f.
        destruct peq. subst.
        destruct o.
        eapply in_link_not_in_data; eauto.
        easy.
        destr_in H.
        eapply in_link_not_in_data; eauto.
        destruct in_dec. easy.
        destr_in H.
        eapply in_link_not_in_data; eauto.
        destr_in H.
        eapply in_link_not_in_data; eauto.
      + intros.
        eapply INCR; eauto.
      + intros.
        eapply INCR; eauto.
      + destruct GLOBSYMB_INJ.
        split. intros.
        eapply INCR; eauto.
        intros.
        destruct (j b1) eqn:JB1.
        destruct p.
        exploit INCR; eauto. rewrite H8; intro X; inv X.
        eauto.
        exploit SEP; eauto. intros (NV1 & NV2).
        simpl; unfold Genv.block_is_volatile.
        
        rewrite ! find_var_info_none_ge.
        auto.
        unfold Mem.valid_block in NV1. xomega.
        unfold Mem.valid_block in NV2.
        xomega. 
      + etransitivity. apply GlobLe. eapply external_call_nextblock; eauto.
      + etransitivity. apply GlobLeT. eapply external_call_nextblock; eauto.
  Qed.

End PRESERVATION.

  Hypothesis repr_stack_limit:
    0 <= Memimpl.Mem.stack_limit <= Ptrofs.max_unsigned.


  Lemma match_initial_states s:
    Asm.initial_state prog s ->
    exists s' j ostack, match_states Vnullptr j ostack s s' /\
                        mono_initial_state prog s'.
  Proof.
    inversion 1. subst.
    destruct (Mem.alloc m0 0 Memimpl.Mem.stack_limit) as [m1 bstack0] eqn:ALLOC.
    assert (bstack = bstack0).
    {
      unfold bstack.
      unfold ge.
      exploit Mem.alloc_result; eauto.
      erewrite <- Genv.init_mem_genv_next; eauto.
    }
    subst.
    assert (ge = ge0).
    {
      unfold ge, ge0. auto.
    }
    subst ge0. clear H1.
    assert (bstack = Mem.nextblock m0) as stackeq.
    {
      exploit Mem.alloc_result; eauto.
    }
    do 2 eexists; exists (Ptrofs.unsigned Ptrofs.zero); split.
    2: econstructor; eauto.
    exploit Genv.initmem_inject; eauto.
    intro FLATINJ.
    exploit Mem.alloc_right_inject. apply FLATINJ.
    eauto. intro STACKINJ.
    econstructor; eauto.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - unfold rs0.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      intros; apply val_inject_set; auto.
      + unfold Genv.symbol_address. destr; auto.
        econstructor. unfold Mem.flat_inj. rewrite pred_dec_true. eauto.
        erewrite <- Genv.init_mem_genv_next.
        eapply Genv.genv_symb_range; eauto. eauto. 
        reflexivity.
      + constructor.
      + constructor.
    - red.         
      rewrite stackeq. exploit Mem.nextblock_alloc; eauto. intro A; rewrite A; xomega.
    - red.
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - erewrite Genv.init_mem_stack_adt; eauto.
    - red. 
      unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - red. intros.
      eapply Mem.perm_alloc_3 in H1. 2: eauto.
      split. omega. eapply Z.lt_le_trans. apply H1. apply repr_stack_limit.
    - red; intros.
      eapply Mem.perm_implies. eapply Mem.perm_alloc_2; eauto. constructor.
    - red. erewrite Mem.alloc_stack_blocks; eauto.
      erewrite Genv.init_mem_stack_adt; eauto.
    - unfold rs0.
      rewrite Pregmap.gss. inversion 1.
    - red.
      unfold Mem.flat_inj.
      intros b delta o k p INJ PERM.
      destr_in INJ. inv INJ.
      exploit Mem.alloc_result; eauto. intro; subst. exfalso; clear - H1 p0. rewrite H1 in p0. xomega.
    -
      erewrite Genv.init_mem_stack_adt; eauto.
      constructor.
    - red. unfold Mem.get_frame_info.
      erewrite Genv.init_mem_stack_adt; eauto.
      simpl. congruence.
    - erewrite Genv.init_mem_stack_adt; eauto. constructor.
    - erewrite Genv.init_mem_stack_adt; eauto. constructor.
    - intros. unfold Mem.flat_inj. rewrite pred_dec_true; auto.
      eapply Genv.find_funct_ptr_not_fresh; eauto.
    - intros. unfold Mem.flat_inj. rewrite pred_dec_true; auto.
      eapply Genv.find_def_not_fresh; eauto.
    - split.
      simpl; intros; unfold Mem.flat_inj.
      rewrite pred_dec_true; auto.
      eapply Genv.find_symbol_not_fresh; eauto.
      simpl; intros b1 b2 delta; unfold Mem.flat_inj.
      intro A; destr_in A.
    - erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; apply Ple_refl.
    - erewrite Mem.nextblock_alloc.  erewrite <- Genv.init_mem_genv_next; eauto. unfold ge; xomega.
      eauto.
  Qed.

  Lemma transf_final_states:
    forall isp j o st1 st2 r,
      match_states isp j o st1 st2 -> Asm.final_state st1 r -> final_state st2 r.
  Proof.
    inversion 1; subst.
    inversion 1; subst.
    econstructor.
    generalize (RINJ PC). rewrite H3. unfold Vnullptr. destruct ptr64; inversion 1; auto.
    generalize (RINJ RAX). rewrite H5. unfold Vnullptr. destruct ptr64; inversion 1; auto.
  Qed.

End WITHMEMORYMODEL.


Print Assumptions step_simulation.