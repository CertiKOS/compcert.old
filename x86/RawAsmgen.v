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

  Existing Instance mem_accessors_default.

  Context `{!ExternalCallsOps mem} `{!EnableBuiltins mem}.

  Variable prog: Asm.program.
  Let ge := Genv.globalenv prog.

  Definition bstack: block := Genv.genv_next ge.
  Variable id_stack: ident.

  Variable tge: Genv.t Asm.fundef unit.
  Hypothesis tge_plus_stack:
    Genv.add_global ge (id_stack, Some (Gvar (mkglobvar tt nil false false))) = tge.

  Lemma find_bstack: Genv.find_symbol tge id_stack = Some bstack.
  Proof.
    simpl; intros. subst.
    unfold Genv.find_symbol. simpl.
    rewrite Maps.PTree.gss.
    reflexivity.
  Qed.

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
  
  Inductive match_states: bool -> meminj -> Z -> state -> state -> Prop := 
  | match_states_intro:
      forall j b (rs: regset) m (rs': regset) m' 
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
        (LRSP: b = true -> load_rsp (Mem.stack_adt m) m),
        match_states b j (Ptrofs.unsigned ostack) (State rs m) (State rs' m').

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

  (* Lemma alloc_inject: *)
  (*   forall j ostack m1 m2 (rs1 rs2: regset) fi m' b m1', *)
  (*     match_states true j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs2 m2) -> *)
  (*     Mem.alloc m1 0 (frame_size fi) = (m', b) -> *)
  (*     Mem.record_stack_blocks m' (Some (frame_with_info b (Some fi))) (frame_size fi) = Some m1' -> *)
  (*     let curofs := current_offset (rs2 # RSP) in *)
  (*     let newostack := offset_after_alloc curofs fi in *)
  (*     let rs1' := (rs1 # RSP <- (Vptr b Ptrofs.zero)) in *)
  (*     let rs2' := (rs2 # RSP <- (Vptr bstack (Ptrofs.repr newostack))) in *)
  (*     exists j' m2', *)
  (*       (forall bb, j' bb = if peq bb b then Some (bstack, newostack) else j bb)  *)
  (*       /\ inject_incr j j' *)
  (*       /\ Mem.record_stack_blocks m2 None (frame_size fi) = Some m2' *)
  (*       /\ match_states false j' newostack (State rs1' m1') (State rs2' m2'). *)
  (* Proof. *)
  (*   intros j ostack m1 m2 rs1 rs2 fi m' b m1' MS ALLOC RSB curofs newostack rs1' rs2'. *)
  (*   inv MS. *)
  (*   assert (RSPDEC: (rs2 RSP = Vptr bstack ostack0 /\ curofs = Ptrofs.unsigned ostack0) *)
  (*                   \/ (~ is_ptr (rs2 RSP) /\ curofs = Memimpl.Mem.stack_limit /\ Mem.stack_adt m1 = nil)). *)
  (*   { *)
  (*     destruct (is_ptr_dec (rs2 RSP)). *)
  (*     left; destruct (rs2 RSP) eqn:?; simpl in *; try easy. *)
  (*     specialize (RSPEQ _ _ eq_refl). *)
  (*     intuition subst. auto. reflexivity. *)
  (*     right. split; auto. *)
  (*     split; auto. *)
  (*     destruct (rs2 RSP) eqn:?; simpl in *; try easy. *)
  (*     generalize (RINJ RSP). *)
  (*     repeat destr_in AGSP1. *)
  (*     rewrite H0. inversion 1. rewrite <- H4 in n. simpl in n; easy. *)
  (*   } *)
  (*   assert (REPRcur: align (Z.max 0 (frame_size fi)) 8 <= curofs <= Ptrofs.max_unsigned). *)
  (*   { *)
  (*     generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)). *)
  (*     generalize (size_stack_below m1'). *)
  (*     erewrite Mem.record_stack_blocks_stack_adt. 2: eauto. *)
  (*     simpl. *)
  (*     erewrite Mem.alloc_stack_blocks. 2: eauto. *)
  (*     destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. *)
  (*     unfold curofs, current_offset. rewrite EQRSP. erewrite AGSP; eauto. *)
  (*     generalize (size_stack_pos (Mem.stack_adt m1)); intros. *)
  (*     omega.  *)
  (*     rewrite EQ, NIL. simpl. omega. *)
  (*   } *)
  (*   assert (REPR: 0 <= newostack <= Ptrofs.max_unsigned). *)
  (*   { *)
  (*     unfold newostack. *)
  (*     unfold offset_after_alloc. *)
  (*     generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)). *)
  (*     omega. *)
  (*   } *)
  (*   generalize (Mem.alloc_left_mapped_inject _ _ _ _ _ _ _ _ newostack MINJ ALLOC VB). *)
  (*   intro A. *)
  (*   trim A. *)
  (*   { *)
  (*     omega. *)
  (*   } *)
  (*   trim A. *)
  (*   { *)
  (*     intros; right; eapply PBS; eauto. *)
  (*   } *)
  (*   trim A. *)
  (*   { *)
  (*     intros; eapply PBSL; eauto. *)
  (*     split. omega. *)
  (*     unfold newostack, offset_after_alloc. *)
  (*     eapply Z.lt_le_trans with curofs. *)
  (*     generalize (align_le (Z.max 0 (frame_size fi)) 8) (Z.le_max_l 0 (frame_size fi)). *)
  (*     rewrite Z.max_r by omega. omega. *)
  (*     destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*     rewrite H0. erewrite (AGSP _ EQRSP); eauto. *)
  (*     generalize (size_stack_pos (Mem.stack_adt m1)); intros. omega. omega.  *)
  (*   } *)
  (*   trim A. *)
  (*   { *)
  (*     red. *)
  (*     intros. *)
  (*     unfold newostack, offset_after_alloc. *)
  (*     eapply Zdivides_trans with 8. *)
  (*     destruct chunk; try (exists 8; reflexivity); *)
  (*       try (exists 4; reflexivity); *)
  (*       try (exists 2; reflexivity); *)
  (*       try (exists 1; reflexivity). *)
  (*     apply Z.divide_sub_r. *)
  (*     destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*     rewrite H0. apply SPAL; auto. *)
  (*     rewrite EQ. auto. *)
  (*     apply align_divides. omega. *)
  (*   } *)
  (*   trim A. *)
  (*   { *)
  (*     intros b0 delta' ofs k p JB PERM RNG. *)
  (*     generalize (NIB _ _ _ _ _ JB PERM). *)
  (*     destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*     rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ. *)
  (*     generalize (align_le (frame_size fi) 8). *)
  (*     unfold newostack, offset_after_alloc in RNG. *)
  (*     rewrite Z.max_r in RNG by omega. simpl in RNG. omega. *)
  (*     rewrite NIL in *. simpl. tauto.  *)
  (*   } *)
  (*   trim A. *)
  (*   { *)
  (*     revert NS. unfold no_stack. *)
  (*     generalize (Mem.stack_adt m2). *)
  (*     induction 1; simpl; intros; eauto. *)
  (*     destruct x. simpl in *. rewrite H. *)
  (*     simpl. intuition.  *)
  (*   } *)
  (*   destruct A as (f' & MINJ' & INCR & EQ1 & EQ2). *)
  (*   exploit Mem.record_stack_blocks_inject. apply MINJ'. 4: eauto. *)
  (*   instantiate (1:= None). simpl. auto. *)
  (*   simpl. intros. split; auto. intro; subst. *)
  (*   erewrite Mem.alloc_stack_blocks in H; eauto. *)
  (*   eapply Mem.in_frames_valid in H. *)
  (*   eapply Mem.fresh_block_alloc in H; eauto. *)
  (*   red; easy. *)
  (*   intros (m2' & RSB' & MINJ''). *)
  (*   exists f', m2'. *)
  (*   split; [|split;[|split]]. *)
  (*   - intros. destruct peq; subst; auto. *)
  (*   - red; intros. *)
  (*     destruct (peq b0 b); auto. *)
  (*   - eauto. *)
  (*   - rewrite <- (Ptrofs.unsigned_repr newostack) by omega. *)
  (*     econstructor; eauto. *)
  (*     + intros b0 o A. unfold rs1' in A. rewrite Pregmap.gss in A. inv A; auto. *)
  (*     + intros r. *)
  (*       unfold rs1', rs2'. *)
  (*       destruct (PregEq.eq r RSP). *)
  (*       * subst. rewrite ! Pregmap.gss. *)
  (*         econstructor; eauto. rewrite Ptrofs.add_zero_l; auto. *)
  (*       * rewrite ! Pregmap.gso by auto. *)
  (*         eapply val_inject_incr; eauto. *)
  (*     + eapply Mem.record_stack_block_valid; eauto. *)
  (*     + red. unfold rs2'. rewrite Pregmap.gss. inversion 1. subst. *)
  (*       erewrite Mem.record_stack_blocks_stack_adt. 2: eauto. *)
  (*       simpl. erewrite Mem.alloc_stack_blocks. 2: eauto. *)
  (*       rewrite Ptrofs.unsigned_repr by auto. *)
  (*       unfold newostack, offset_after_alloc in *. *)
  (*       destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*       rewrite EQRSP in RSPEQ. specialize (RSPEQ _ _ eq_refl). inv RSPEQ. *)
  (*       rewrite H0. rewrite (AGSP _ EQRSP). *)
  (*       omega. *)
  (*       rewrite EQ, NIL in *. simpl. omega. *)
  (*     + erewrite Mem.record_stack_blocks_stack_adt. 2: eauto. simpl. *)
  (*       unfold rs1'. apply Pregmap.gss. *)
  (*     + red. intros ostack1 A. unfold rs2' in A; rewrite Pregmap.gss in A. *)
  (*       inversion A. subst. *)
  (*       rewrite Ptrofs.unsigned_repr by omega. *)
  (*       unfold newostack. *)
  (*       apply Z.divide_sub_r. *)
  (*       destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*       rewrite H; apply SPAL; auto. *)
  (*       rewrite EQ. auto. *)
  (*       apply align_divides. omega. *)
  (*     + red. intros ofs k p PERM. eapply Mem.record_stack_block_perm in PERM; eauto. *)
  (*     + red; intros. eapply Mem.record_stack_block_perm'; eauto. *)
  (*     + red; intros. erewrite Mem.record_stack_blocks_stack_adt. 2: eauto. constructor; auto. *)
  (*     + unfold rs2'. rewrite Pregmap.gss. inversion 1. eauto. *)
  (*     + rewrite Ptrofs.unsigned_repr by omega. *)
  (*       red. intros b0 delta o k p JB PERM. *)
  (*       eapply Mem.record_stack_block_perm in PERM. *)
  (*       eapply Mem.perm_alloc_inv in PERM; eauto. *)
  (*       2: eauto. *)
  (*       destruct peq. *)
  (*       * subst. rewrite EQ1 in JB. inv JB. split. omega. *)
  (*         erewrite Mem.record_stack_blocks_stack_adt. 2: eauto. constructor; auto. *)
  (*         simpl. auto. *)
  (*       * split. unfold newostack, offset_after_alloc. *)
  (*         transitivity curofs. *)
  (*         -- generalize (Z.le_max_l 0 (frame_size fi)); intro MAX. *)
  (*            generalize (align_le (Z.max 0 (frame_size fi)) 8). omega. *)
  (*         --  *)
  (*            destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst.  *)
  (*            rewrite H.  *)
  (*            rewrite EQ2 in JB; auto.  *)
  (*            exploit NIB; eauto. tauto. *)
  (*            exploit NIB; eauto. rewrite <- EQ2. eauto. auto.  *)
  (*            rewrite NIL. simpl; tauto. *)
  (*         -- erewrite Mem.record_stack_blocks_stack_adt; eauto. *)
  (*            erewrite Mem.alloc_stack_blocks; eauto. *)
  (*            simpl. right. *)
  (*            eapply NIB; eauto. rewrite <- EQ2; eauto. *)
  (*     + erewrite Mem.record_stack_blocks_stack_adt; eauto. *)
  (*       erewrite Mem.alloc_stack_blocks; eauto. *)
  (*       constructor; auto. *)
  (*       eapply inject_stack_incr; eauto. *)
  (*       rewrite EQ1. f_equal. f_equal. *)
  (*       unfold newostack, offset_after_alloc. *)
  (*       destruct (RSPDEC) as [[EQRSP ?]|[NOPTR [EQ NIL]]]; subst. *)
  (*       rewrite H. *)
  (*       rewrite AGSP. omega. auto. rewrite EQ, NIL. simpl; omega. *)
  (*     + intros b0 fi0 delta GFI FB0 b' o delta' k p FB1 P1. *)
  (*       unfold Mem.get_frame_info in GFI. *)
  (*       erewrite Mem.record_stack_blocks_stack_adt in GFI; eauto. *)
  (*       erewrite Mem.alloc_stack_blocks in GFI; eauto. *)
  (*       simpl in GFI. *)
  (*       eapply Mem.record_stack_block_perm in P1. 2: eauto. *)
  (*       eapply Mem.perm_alloc_inv in P1. 2: eauto.          *)
  (*       destr_in GFI. *)
  (*       * inv GFI. rewrite FB0 in EQ1; inv EQ1. *)
  (*         destr_in P1. *)
  (*         -- subst. rewrite FB0 in FB1; inv FB1. *)
  (*            rewrite Z.max_r by omega.  omega. *)
  (*         -- rewrite EQ2 in FB1 by auto. *)
  (*            eapply NIB in P1; eauto. *)
  (*            destruct P1 as (LE & IN). *)
  (*            unfold newostack, offset_after_alloc. *)
  (*            destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA. *)
  (*            omega. rewrite NIL in IN; easy. *)
  (*       *  *)
  (*         rewrite EQ2 in FB0 by auto. *)

  (*         Lemma perm_stack_eq: *)
  (*           forall l m b fi, *)
  (*             perm_stack l m -> *)
  (*             get_assoc l b = Some fi -> *)
  (*             forall o k p, *)
  (*               Mem.perm m b o k p <-> 0 <= o < frame_size fi. *)
  (*         Proof. *)
  (*           induction 1; simpl; intros; eauto. congruence. *)
  (*           destr_in H1. inv H1. *)
  (*           auto. eauto. *)
  (*         Qed. *)

  (*         intro RNG. *)
  (*         assert (0 < frame_size fi0). *)
  (*         destruct (zlt 0 (frame_size fi0)); auto. *)
  (*         rewrite Z.max_l in RNG by omega. change (align 0 8) with 0 in RNG. omega. *)
  (*         rewrite Z.max_r in RNG by omega. *)

  (*         destruct (RSPDEC) as [[EQRSP EQA]|[NOPTR [EQA NIL]]]; subst; rewrite EQA, ?NIL in *; try easy. *)
          
  (*         generalize (perm_stack_eq _ _ _ _ PS GFI). intro PF0.  *)

  (*         destr_in P1. *)
  (*         -- *)
  (*           subst. rewrite EQ1 in FB1; inv FB1. *)

  (*           cut (newostack + (frame_size fi)  <= delta). omega. *)
  (*           unfold newostack. rewrite EQA. *)
  (*           rewrite AGSP; auto. *)

  (*           Lemma in_stack_inj_below: *)
  (*             forall j l, *)
  (*               inject_stack j l -> *)
  (*               forall b fi, *)
  (*             get_assoc l b = Some fi -> *)
  (*             exists l1 l2, *)
  (*               l = l1 ++ l2 /\ *)
  (*               j b = Some (bstack, Memimpl.Mem.stack_limit - Memimpl.Mem.size_stack l2). *)
  (*           Proof. *)
  (*             induction 1; simpl; intros; eauto. *)
  (*             congruence. *)
  (*             destr_in H1; eauto. *)
  (*             - subst. *)
  (*               inv H1. *)
  (*               rewrite H0. *)
  (*               exists nil.  *)
  (*               repeat eexists. *)
  (*               f_equal. f_equal. simpl. omega.  *)
  (*             - specialize (IHinject_stack _ _ H1). *)
  (*               destruct IHinject_stack as (l1 & l2 & EQl & JB). *)
  (*               subst. *)
  (*               rewrite JB. *)
  (*               repeat eexists. *)
  (*               rewrite app_comm_cons. eauto. *)
  (*           Qed. *)

  (*           eapply in_stack_inj_below in GFI; eauto. *)
  (*           destruct GFI as (l1 & l2 & EQADT & JB0). rewrite FB0 in JB0. inv JB0. *)
  (*           rewrite Z.max_r in * by omega. *)

  (*           unfold offset_after_alloc. *)
  (*           rewrite Z.max_r by omega. *)

  (*           cut (Memimpl.Mem.size_stack (Mem.stack_adt m1)  *)
  (*                >= Memimpl.Mem.size_stack l2). *)
  (*           generalize (align_le (frame_size fi) 8). omega. *)
  (*           rewrite EQADT. *)

  (*           Lemma size_stack_app: *)
  (*             forall {A} (l1 l2: list (A * Z)), *)
  (*               Memimpl.Mem.size_stack (l1 ++ l2) = Memimpl.Mem.size_stack l1 + Memimpl.Mem.size_stack l2. *)
  (*           Proof. *)
  (*             induction l1; simpl; intros; eauto. *)
  (*             destruct a. *)
  (*             rewrite IHl1. omega. *)
  (*           Qed. *)
  (*           rewrite size_stack_app. *)
  (*           generalize (size_stack_pos l1); omega. *)

  (*         -- eapply IP.  apply GFI. eauto. *)
  (*            rewrite <- EQ2. apply FB1. auto. eauto. *)
  (*            rewrite Z.max_r by omega. omega. *)
                       
             
  (*     + erewrite Mem.record_stack_blocks_stack_adt; eauto. *)
  (*       erewrite Mem.alloc_stack_blocks; eauto. *)
  (*       constructor; auto. *)
  (*       eapply perm_stack_inv. eauto. apply Mem.in_frames_valid. *)
  (*       split; intros. *)
  (*       eapply Mem.record_stack_block_perm in H0. 2: eauto. *)
  (*       eapply Mem.perm_alloc_inv in H0; eauto. *)
  (*       destr_in H0. *)
  (*       subst. *)
  (*       eapply Mem.in_frames_valid in H. *)
  (*       eapply Mem.fresh_block_alloc in H. easy. *)
  (*       eauto. *)
  (*       eapply Mem.record_stack_block_perm'. eauto. *)
  (*       eapply Mem.perm_alloc_1 in H0; eauto. *)
  (*       split; intros. eapply Mem.record_stack_block_perm in H. 2: eauto. *)
  (*       eapply Mem.perm_alloc_inv in H; eauto. *)
  (*       rewrite pred_dec_true in H; auto. *)
  (*       eapply Mem.record_stack_block_perm'. eauto. *)
  (*       eapply Mem.perm_implies. *)
  (*       eapply Mem.perm_alloc_2. eauto. auto. constructor. *)
  (*     + congruence.         *)
  (* Qed.        *)


  Axiom exec_instr_inject:
    forall j m1 m2 rs1 rs2 f i rs1' m1'
      (MINJ: Mem.inject j m1 m2)
      (RINJ: forall r, Val.inject j (rs1 # r) (rs2 # r))
      (IU: is_unchanged i = true)
      (EXEC: Asm.exec_instr ge f i rs1 m1 = Next rs1' m1'),
      exists j' rs2' m2',
        Asm.exec_instr tge f i rs2 m2 = Next rs2' m2'
        /\ Mem.inject j' m1' m2'
        /\ (forall r, Val.inject j' (rs1' # r) (rs2' # r))
        /\ inject_incr j j'
        /\ (forall b b' delta, j b = None -> j' b = Some (b', delta) -> Ple (Genv.genv_next ge) b /\ b' <> bstack). 
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
  
  Lemma alloc_inject:
    forall j ostack m1 (rs1 rs1': regset) fi b m1' m2 m3 m4 m5,
      match_states true j (Ptrofs.unsigned ostack) (State rs1 m1) (State rs1' m1') ->
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
                       /\ match_states true j' newostack (State rs2 m5) (State rs2' m5').
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
      trim LRSP. auto. intros _.
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
      match_states true j ostack (State rs1 m1) (State rs2 m2) ->
      asm_instr_no_rsp i ->
      asm_instr_no_stack i ->
      Asm.exec_instr ge f i rs1 m1 = Next rs1' m1' ->
      exists j' ostack' rs2' m2',
        exec_instr tge f i rs2 m2 = Next rs2' m2'
        /\ match_states true j' ostack' (State rs1' m1') (State rs2' m2')
        /\ inject_incr j j'.
  Proof.
    intros j ostack m1 m2 rs1 rs2 f i rs1' m1' MS AINR AINS EI.
    destruct (is_unchanged i) eqn:?.
    - edestruct exec_instr_inject as (j' & rs2' & m2' & EXEC' & MINJ' & RINJ' & INCR & NOSTACK); eauto.
      inv MS; eauto. inv MS; eauto.
      exists j', ostack, rs2', m2'; split; [|split]; eauto.
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
        rewrite H0 in H2.
        destruct (j b) eqn:JB.
        destruct p0.
        rewrite H.
        eapply NIB. rewrite JB. erewrite INCR in H1.
        eauto.  eauto. eauto.
        eapply NOSTACK in H1. 2: auto. 
        intuition congruence.
      + edestruct AINS. eauto. apply EI. rewrite H. eapply inject_stack_incr; eauto.
      + edestruct AINS. eauto. apply EI.
        red. unfold Mem.get_frame_info.
        rewrite H.
        intros b fi delta GFI JB b' o delta' k p JB' PERM RNG.
        destruct (j b) eqn: JB0. destruct p0.
        exploit INCR. rewrite JB0. eauto. rewrite JB. inversion 1; subst.
        destruct (j b') eqn: JB'0. destruct p0.
        exploit INCR. rewrite JB'0. eauto. rewrite JB'. inversion 1; subst.
        eapply IP. eauto. eauto. eauto. rewrite <- H0; eauto.
        apply RNG.
        exploit NOSTACK. apply JB'0. apply JB'. intuition congruence.
        exploit NOSTACK. apply JB0. apply JB. intuition congruence.
      + edestruct AINS. eauto. apply EI. rewrite H.
        eapply perm_stack_inv. eauto. apply Mem.in_frames_valid.
        intros; apply H0.
      + edestruct AINS. eauto. apply EI. rewrite H.
        intros; eapply load_rsp_inv'. eauto.
        eapply exec_instr_unchanged_on; eauto.

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
        inv MS. trim LRSP; auto.
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
          intro.
          rewrite <- H6 in *.
          eapply load_rsp_inv'. eauto.
          eapply Mem.unchanged_on_trans.
          eapply Mem.unchanged_on_implies.
          eapply Mem.free_unchanged_on. eauto.
          instantiate (1:= fun b0 o => b0 <> b). simpl. congruence.
          simpl.
          intros. 
          intro; subst.
          red in H11. destr_in H11. simpl in Heqo3. destr_in Heqo3. subst. xomega.
          exploit inject_stack_norepeat. apply LRSP. simpl. eauto.
          simpl.
          destruct (in_frames_dec l b); auto.
          erewrite not_in_frames_get_assoc in Heqo3; eauto; congruence. auto.
          eapply Mem.strong_unchanged_on_weak.
          eapply Mem.unrecord_stack_block_unchanged_on.
          eauto.
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