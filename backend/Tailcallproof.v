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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Conventions Tailcall.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    omega.
    destruct (f!pc); try omega.
    destruct i; try omega.
    generalize (IHn n0). omega.
    generalize (IHn n0). omega.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  omega.
  destruct n2. omegaContradiction. assert (n1 <= n2)%nat by omega.
  simpl. destruct f!pc; try omega. destruct i; try omega.
  generalize (IHn1 n2 n H0). omega.
  generalize (IHn1 n2 n H0). omega.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. omegaContradiction. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. omega.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. omega.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. omega. omega.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. omega.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. omega. omega.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  caseEq (is_return niter f n r && tailcall_is_possible s &&
          opt_typ_eq (sig_res s) (sig_res (fn_sig f))); intros.
  destruct (andb_prop _ _ H0). destruct (andb_prop _ _ H1).
  eapply transf_instr_tailcall; eauto.
  eapply is_return_charact; eauto.
  constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0).
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Existing Instance inject_perm_all.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Definition regs_inject (j: meminj) (rs1 rs2: Regmap.t val) :=
  forall r,
    Val.inject j (rs1 # r) (rs2 # r).

Lemma meminj_preserves_globals_flat {F V} (g: Genv.t F V) m:
  Ple (Genv.genv_next g) (Mem.nextblock m) ->
  meminj_preserves_globals g (Mem.flat_inj (Mem.nextblock m)).
Proof.
  intros PLE.
  split; [|split].
  - intros id b FS.
    unfold Genv.find_symbol in FS.
    eapply Genv.genv_symb_range in FS.
    unfold Mem.flat_inj; rewrite pred_dec_true; auto. xomega.
  - intros id b FVI.
    unfold Genv.find_var_info in FVI.
    repeat destr_in FVI.
    eapply Genv.genv_defs_range in Heqo.
    unfold Mem.flat_inj; rewrite pred_dec_true; auto. xomega.
  - intros b1 b2 delta gv FVI FI.
    unfold Genv.find_var_info in FVI.
    repeat destr_in FVI.
    eapply Genv.genv_defs_range in Heqo.
    unfold Mem.flat_inj in FI; destr_in FI. 
Qed.


Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof (Genv.find_symbol_transf TRANSL).

Lemma functions_translated:
  forall (v: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof (Genv.find_funct_transf TRANSL).

Lemma funct_ptr_translated:
  forall (b: block) (f: RTL.fundef),
  Genv.find_funct_ptr ge b = Some f ->
  Genv.find_funct_ptr tge b = Some (transf_fundef f).
Proof (Genv.find_funct_ptr_transf TRANSL).

Lemma senv_preserved:
  Senv.equiv ge tge.
Proof (Genv.senv_transf TRANSL).

Lemma genv_next_preserved:
  Genv.genv_next tge = Genv.genv_next ge.
Proof.
  apply senv_preserved.
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0); auto.
Qed.

Lemma find_function_translated:
  forall ros rs rs' f m,
  find_function ge ros rs = Some f ->
  regs_inject (Mem.flat_inj (Mem.nextblock m)) rs rs' ->
  find_function tge ros rs' = Some (transf_fundef f).
Proof.
  intros until m; destruct ros; simpl.
  intros.
  assert (rs'#r = rs#r).
    exploit Genv.find_funct_inv; eauto. intros [b EQ].
    generalize (H0 r). rewrite EQ. intro LD. inv LD.
    unfold Mem.flat_inj in H4. repeat destr_in H4. reflexivity.
  rewrite H1. apply functions_translated; auto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge i); intros.
  apply funct_ptr_translated; auto.
  discriminate.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)


(* The list of boolean records whether the source frame has a corresponding
counterpart in the target stack ([true]) or not ([false]). This will later be used
to specify the shape of the stack injection function [g]. *)
Inductive match_stackframes: meminj -> list bool -> list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil j:
      match_stackframes j nil nil nil
  | match_stackframes_normal: forall j l stk stk' res sp pc rs rs' f,
      match_stackframes j l stk stk' ->
      regs_inject j rs rs' ->
      j sp = Some (sp,0) ->
      match_stackframes j (true::l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall j l stk stk' res sp pc rs f,
      match_stackframes j l stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      match_stackframes j (false::l)
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(* Specifying the shape of stack injection functions *)

Fixpoint compat_frameinj_rec (l: list bool) (g: frameinj) (ns nt: nat) :=
  match l with
    nil => forall i j (LE: (ns <= i)%nat) (Gi: g i = Some j), (nt <= j)%nat
  | true::l =>
    g ns = Some nt /\ compat_frameinj_rec l g (S ns) (S nt)
  | false::l =>
    g ns = None /\ compat_frameinj_rec l g (S ns) nt
  end.

Definition compat_frameinj l g := compat_frameinj_rec l g O O.

Lemma compat_frameinj_rec_above:
  forall l g ns nt (CFG: compat_frameinj_rec l g ns nt)
    i j (Gi: g i = Some j) (LE: (ns <= i)%nat),
    (nt <= j)%nat.
Proof.
  induction l; simpl; intros; eauto.
  destruct a; destruct CFG as (GNS & GABOVE).
  - destruct (Nat.eq_dec ns i); subst; auto.
    + rewrite GNS in Gi; inv Gi; auto.
    + eapply IHl in GABOVE. 2: apply Gi. 2: omega. omega.
  - destruct (Nat.eq_dec ns i); subst; auto. 
    + congruence.
    + eapply IHl in GABOVE. 2: apply Gi. 2: omega. omega.
Qed.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f g l
             (STACKS: match_stackframes (Mem.flat_inj (Mem.nextblock m)) l s s')
             (RLD: regs_inject (Mem.flat_inj (Mem.nextblock m)) rs rs')
             (MLD: Mem.inject (Mem.flat_inj (Mem.nextblock m)) g m m')
             (CFG: compat_frameinj (true::l) g),
      match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s f args m s' args' m' sz g l
        (MS: match_stackframes (Mem.flat_inj (Mem.nextblock m)) l s s')
        (LDargs: Val.inject_list (Mem.flat_inj (Mem.nextblock m)) args args')
        (MLD: Mem.inject (Mem.flat_inj (Mem.nextblock m)) g m m')
        (CFG: compat_frameinj l g),
      match_states (Callstate s f args m sz)
                   (Callstate s' (transf_fundef f) args' m' sz)
  | match_states_return:
      forall s v m s' v' m' g l
        (MS: match_stackframes (Mem.flat_inj (Mem.nextblock m)) l s s')
        (LDret: Val.inject (Mem.flat_inj (Mem.nextblock m)) v v')
        (MLD: Mem.inject (Mem.flat_inj (Mem.nextblock m)) g m m')
        (CFG: compat_frameinj (true::l) g),
        match_states (Returnstate s v m)
                     (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' g l
             (STACKS: match_stackframes (Mem.flat_inj (Mem.nextblock m)) l s s')
             (MLD: Mem.inject (Mem.flat_inj (Mem.nextblock m)) g m m')
             (RETspec: is_return_spec f pc r)
             (SZzero: f.(fn_stacksize) = 0)
             (LDret: Val.inject (Mem.flat_inj (Mem.nextblock m)) (rs#r) v')
             (CFG: compat_frameinj l g),
        match_states (State s f (Vptr sp Ptrofs.zero) pc rs m)
                     (Returnstate s' v' m').

Definition mem_state (s: state) : mem :=
  match s with
    State _ _ _ _ _ m
  | Callstate _ _ _ m _
  | Returnstate _ _ m => m
  end.

Definition match_state_ge {F V} (g: Genv.t F V) (s: state) :=
  Ple (Genv.genv_next g) (Mem.nextblock (mem_state s)).

Definition current_sp_state (s: state) : option (block * Z) :=
  match s with
    State _ f (Vptr sp _) _ _ _ => Some (sp, fn_stacksize f)
  | _ => None
  end.

Definition stackblocks_of_stackframe (sf: stackframe) : option (block * Z) :=
  match sf with
  | (Stackframe _ f (Vptr sp _) _ _) => Some (sp,fn_stacksize f)
  | _ => None
  end.


Definition stackframes_state (s: state) : list stackframe :=
  match s with
    State stk _ _ _ _ _
  | Callstate stk _ _ _ _
  | Returnstate stk _ _ => stk
  end.


Definition stack_blocks_of_state (s: state) : list (option (block * Z)) :=
  current_sp_state s :: map stackblocks_of_stackframe (stackframes_state s).

Definition sp_valid (s : state) : Prop :=
  Forall (fun bz => match bz with
                   Some (b,z) => Mem.valid_block (mem_state s) b
                 | None => False
                 end) (stack_blocks_of_state s).

Definition match_stack_adt (s: state) :=
  let stk := Mem.stack_adt (mem_state s) in
  let sbl := stack_blocks_of_state s in
  exists sprog sinit,
    stk = sprog ++ sinit /\
    list_forall2 (fun (f: frame_adt) obz =>
                    match obz with
                      Some (b,z) =>
                      map fst (frame_adt_blocks f) = b :: nil /\
                      forall o k p,
                        Mem.perm (mem_state s) b o k p ->
                        0 <= o < z
                    | None => False
                    end
                 ) sprog sbl.

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m sz => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)


Lemma regs_inject_regs:
  forall j rs1 rs2, regs_inject j rs1 rs2 ->
  forall rl, Val.inject_list j rs1##rl rs2##rl.
Proof.
  induction rl; constructor; auto.
Qed.

Lemma set_reg_inject:
  forall j r v1 v2 rs1 rs2,
  Val.inject j v1 v2 -> regs_inject j rs1 rs2 -> regs_inject j (rs1#r <- v1) (rs2#r <- v2).
Proof.
  intros; red; intros. repeat rewrite Regmap.gsspec.
  destruct (peq r0 r); auto.
Qed.

Lemma set_res_inject:
  forall j res v1 v2 rs1 rs2,
  Val.inject j v1 v2 -> regs_inject j rs1 rs2 ->
  regs_inject j (regmap_setres res v1 rs1) (regmap_setres res v2 rs2).
Proof.
  intros. destruct res; simpl; auto. apply set_reg_inject; auto.
Qed.





Variable fn_stack_requirements: ident -> Z.


Lemma ros_is_function_transf:
  forall j ros rs rs' id,
    meminj_preserves_globals ge j ->
    ros_is_function ge ros rs id ->
    regs_inject j rs rs' ->
    ros_is_function tge ros rs' id.
Proof.
  unfold ros_is_function. intros.
  destr_in H0. simpl.
  destruct H0 as (b & o & RS & FS).
  specialize (H1 r). rewrite RS in H1; inv H1.
  eexists; eexists; split; eauto.
  rewrite symbols_preserved. rewrite FS.
  f_equal.
  destruct H. apply H in FS. rewrite FS in H4; inv H4. auto.
Qed.

Lemma transf_step_correct:
  forall s1 t s2, step fn_stack_requirements ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1') (MSG: match_state_ge ge s1) (SPV: sp_valid s1) (MSA: match_stack_adt s1) (MSA': match_stack_adt s1'),
  (exists s2', step fn_stack_requirements tge s1' t s2' /\ match_states s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. econstructor; eauto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. omega. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.inject_list (Mem.flat_inj (Mem.nextblock m)) (rs##args) (rs'##args)). apply regs_inject_regs; auto.
  exploit eval_operation_inject; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  unfold Mem.flat_inj. rewrite pred_dec_true. reflexivity.
  inv SPV. eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.  rewrite <- EVAL'.
  rewrite eval_shift_stack_operation.
  apply eval_operation_preserved. exact symbols_preserved.
  econstructor; eauto. apply set_reg_inject; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. omega. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.inject_list (Mem.flat_inj (Mem.nextblock m)) (rs##args) (rs'##args)). apply regs_inject_regs; auto.
  exploit eval_addressing_inject; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  unfold Mem.flat_inj; rewrite pred_dec_true; auto.   inv SPV. eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_inject; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a0 := a'). eauto.  rewrite <- ADDR'.
  rewrite eval_shift_stack_addressing.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  econstructor; eauto. apply set_reg_inject; auto.

- (* store *)
  TransfInstr.
  assert (Val.inject_list (Mem.flat_inj (Mem.nextblock m)) (rs##args) (rs'##args)). apply regs_inject_regs; auto.
  exploit eval_addressing_inject; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  unfold Mem.flat_inj; rewrite pred_dec_true; auto. inv SPV. eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_mapped_inject. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a0 := a'). eauto.  rewrite <- ADDR'.
  rewrite eval_shift_stack_addressing.
  apply eval_addressing_preserved. exact symbols_preserved. eauto.
  destruct a; simpl in H1; try discriminate.
  econstructor; eauto.
  erewrite Mem.nextblock_store; eauto.
  erewrite Mem.nextblock_store; eauto.
  erewrite Mem.nextblock_store; eauto.

- (* call *)
  exploit find_function_translated; eauto. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert (X: { m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
  {
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
    red; intros; omegaContradiction.
  } 
  destruct X as [m'' FREE].
  generalize (Mem.free_right_inject _ _ _ _ _ _ _ _ MLD FREE). intro FINJ.
  trim FINJ.
  {
    unfold Mem.flat_inj.
    intros b1 delta ofs k p FI PERM RNG.
    repeat destr_in FI.
    rewrite stacksize_preserved in RNG. rewrite H7 in RNG. omega.
  }
  destruct MSA as (sprog & sinit & EQstk & LF2).
  inv LF2. simpl in EQstk.
  destruct MSA' as (sprog' & sinit' & EQstk' & LF2').
  inv LF2'. simpl in EQstk'.
  edestruct (Mem.unrecord_stack_block_succeeds m'') as (m2' & USB & EQ).
  erewrite Mem.free_stack_blocks; eauto.
  generalize (Mem.unrecord_stack_block_inject_right _ _ _ _ m2' FINJ). intro UINJ.
  trim UINJ.
  {
    rewrite EQstk. unfold is_stack_top. simpl.
    destruct H4 as (frame_blocks & perm_stack).
    rewrite frame_blocks. intros b [A|[]]; inv A.
    intros (o & k & p & PERM).
    apply perm_stack in PERM. rewrite H7 in PERM. omega.
  }
  trim UINJ.
  {
    red in CFG. simpl in CFG.
    intros i j Gi LT.
    eapply compat_frameinj_rec_above in Gi. 2: apply CFG. omega. omega.
  }
  trim UINJ. apply CFG.
  trim UINJ. eauto.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m2' (fn_stack_requirements id)); split.
  eapply exec_Itailcall; eauto.
  {
    eapply ros_is_function_transf; eauto.
    eapply meminj_preserves_globals_flat; eauto.
  }
  apply sig_preserved.
  econstructor. eapply match_stackframes_tail; eauto. apply regs_inject_regs; auto.
  eauto.
  {
    revert CFG.

    Lemma compat_frameinj_pop_right_rec:
      forall g l ns nt
        (CFR: compat_frameinj_rec l g ns (S nt))
        g' (G'spec: forall i, (ns <= i)%nat -> g' i = option_map pred (g i)),
        compat_frameinj_rec l g' ns nt.
    Proof.
      induction l; simpl; intros; eauto.
      - rewrite G'spec in Gi; auto.
        unfold option_map in Gi; repeat destr_in Gi.
        eapply CFR in Heqo. omega. auto.
      - destr; destruct CFR as (Gn & CFR).
        + split.
          * rewrite G'spec; auto.
            unfold option_map. rewrite Gn. reflexivity.
          * eapply IHl; eauto.
            intros; apply G'spec. omega.
        + split.
          * rewrite G'spec; auto.
            unfold option_map. rewrite Gn. reflexivity.
          * eapply IHl; eauto.
            intros; apply G'spec. omega.
    Qed.

    Lemma compat_frameinj_pop_right:
      forall g l,
        compat_frameinj (true :: l) g ->
        compat_frameinj (false :: l) (fun n : nat => if Nat.eq_dec n 0 then None else option_map Init.Nat.pred (g n)).
    Proof.
      intros g l (A & B); split; simpl; auto.
      eapply compat_frameinj_pop_right_rec; eauto.
      intros. destr. omega.
    Qed.
    eapply compat_frameinj_pop_right; eauto.

  }

+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
                          (transf_fundef fd) (rs'##args) m' (fn_stack_requirements id)); split.
  eapply exec_Icall; eauto.
  eapply ros_is_function_transf; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  apply sig_preserved.
  econstructor. constructor; eauto.
  unfold Mem.flat_inj; rewrite pred_dec_true. auto. inv SPV; auto.
  apply regs_inject_regs; auto. eauto.
  auto.

- (* tailcall *)
  exploit find_function_translated; eauto. intro FIND'.
  exploit Mem.free_parallel_inject; eauto.
  unfold Mem.flat_inj; rewrite pred_dec_true; auto. inv SPV; auto. constructor.
  intros [m'1 [FREE EXT]].
  exploit Mem.unrecord_stack_block_inject_parallel. apply EXT. eauto.
  {
    red in CFG. simpl in CFG.
    intros i j Gi LT.
    eapply compat_frameinj_rec_above in Gi. 2: apply CFG. omega. omega.
  }
  {
    apply CFG.
  }
  intros (m2' & USB' & UINJ).
  TransfInstr.
  left. exists (Callstate s' (transf_fundef fd) (rs'##args) m2' (fn_stack_requirements id)); split.
  eapply exec_Itailcall; eauto.
  eapply ros_is_function_transf; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  apply sig_preserved.
  eauto. rewrite stacksize_preserved; auto. rewrite ! Z.add_0_r in FREE. eauto.
  econstructor.
  erewrite Mem.unrecord_stack_block_nextblock by eauto.
  erewrite Mem.nextblock_free by eauto. eauto.
  eauto.  apply regs_inject_regs; auto.
  erewrite Mem.unrecord_stack_block_nextblock by eauto.
  erewrite Mem.nextblock_free by eauto. eauto.
  erewrite Mem.unrecord_stack_block_nextblock by eauto.
  erewrite Mem.nextblock_free by eauto. eauto.
  {
    destruct CFG as (G0 & CFG).

    Lemma compat_frameinj_rec_pop_parallel:
      forall g l ns nt
        (CFR: compat_frameinj_rec l g (S ns) (S nt)),
        compat_frameinj_rec l (fun n : nat => option_map Init.Nat.pred (g (S n))) ns nt.
    Proof.
      induction l; simpl; intros; eauto.
      - unfold option_map in Gi; repeat destr_in Gi.
        eapply CFR in Heqo. omega. omega.
      - destr; destruct CFR as (Gn & CFR).
        + split.
          * unfold option_map. rewrite Gn. reflexivity.
          * eapply IHl; eauto.
        + split.
          * unfold option_map. rewrite Gn. reflexivity.
          * eapply IHl; eauto.
    Qed.
    eapply compat_frameinj_rec_pop_parallel; eauto.

  }

- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_inject _ _ _ _ ge tge (fun r => rs#r) (fun r => rs'#r) (Vptr sp0 Ptrofs.zero)); eauto.
  {
    econstructor. unfold Mem.flat_inj. rewrite pred_dec_true; eauto. inv SPV; auto. reflexivity.
  }
  {
    simpl. intros; rewrite symbols_preserved; auto.
  }
  {
    simpl; intros.
    generalize (meminj_preserves_globals_flat ge m). intro MPG. trim MPG; eauto.
    destruct MPG; eauto.
  }
  intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto.
  eapply meminj_preserves_globals_flat; eauto.
  intros [f' [v' [m'1 [A [B [C [D [E [F G]]]]]]]]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'1); split.
  eapply exec_Ibuiltin; eauto.
  edestruct eval_builtin_args_inject with (e1:= fun r => rs # r) (e2:= fun r => rs' # r) (sp1:=Vptr sp0 Ptrofs.zero) as
      (args' & EVALargs' & INJargs); eauto.
  {
    econstructor. unfold Mem.flat_inj.  rewrite pred_dec_true; eauto. inv SPV; auto. reflexivity.
  }
  {
    simpl; intros.
    generalize (meminj_preserves_globals_flat ge m). intro MPG. trim MPG; eauto.
    destruct MPG; eauto.
  }
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  econstructor; eauto.
  
  apply set_res_inject; auto.

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_inject with (rs##args) m; auto. apply regs_inject_regs; auto.
  constructor; auto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  constructor; auto.

- (* return *)
  exploit Mem.free_parallel_inject; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  constructor. auto.
  destruct or; simpl. apply RLD. constructor.
  auto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. constructor.
  eapply Mem.free_left_inject; eauto.

- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. omega. split. auto.
  constructor. auto.
  simpl. auto.
  eapply Mem.free_left_inject; eauto.

- (* internal call *)
  exploit Mem.alloc_inject; eauto.
    instantiate (1 := 0). omega.
    instantiate (1 := fn_stacksize f). omega.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0); auto.
  destruct H0 as [EQ1 [EQ2 EQ3]].
  left. econstructor; split.
  simpl. eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. constructor; auto.
  apply regs_inject_init_regs. auto.

- (* external call *)
  exploit external_call_mem_inject; eauto.
  intros [res' [m2' [A [B [C D]]]]].
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.

- (* returnstate *)
  inv H2.
+ (* synchronous return in both programs *)
  left. econstructor; split.
  apply exec_return.
  constructor; auto. apply set_reg_inject; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). omega.
  split. auto.
  econstructor; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall st1, initial_state prog st1 ->
  exists st2, initial_state tprog st2 /\ match_states st1 st2.
Proof.
  intros. inv H.
  exploit funct_ptr_translated; eauto. intro FIND.
  exists (Callstate nil (transf_fundef f) nil m0); split.
  econstructor; eauto. apply (Genv.init_mem_transf TRANSL). auto.
  replace (prog_main tprog) with (prog_main prog).
  rewrite symbols_preserved. eauto.
  symmetry; eapply match_program_main; eauto. 
  rewrite <- H3. apply sig_preserved.
  constructor. constructor. constructor. apply Mem.inject_refl.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states st1 st2 -> final_state st1 r -> final_state st2 r.
Proof.
  intros. inv H0. inv H. inv H5. inv H3. constructor.
Qed.


(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_opt with (measure := measure); eauto.
  apply senv_preserved. 
  eexact transf_initial_states.
  eexact transf_final_states.
  exact transf_step_correct.
Qed.

End PRESERVATION.

