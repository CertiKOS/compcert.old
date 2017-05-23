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
Require Import Values Memory SeparationSingleStack Events Globalenvs Smallstep.
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

Lemma load_result_lessdef:
  forall ty v v',
  Val.lessdef v v' -> Val.has_type v ty -> Val.lessdef v (Val.load_result (chunk_of_type ty) v').
Proof.
  intros until v'; unfold Val.has_type, Val.load_result; destruct Archi.ptr64;
  destruct 1; intros; auto; destruct ty; simpl;
  try contradiction; try discriminate; try destruct v; auto; try intuition congruence.
Qed.

(* Frame inequalities *)

Lemma fe_ofs_local_pos:
  forall b,
    0 <= fe_ofs_local (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  etransitivity. 2: apply align_le ; try omega.
  etransitivity. 2: apply size_callee_save_area_incr.
  Local Transparent Z.mul.
  apply Z.add_nonneg_nonneg.
  - etransitivity. 2: apply align_le; try omega. omega. destruct Archi.ptr64; omega.
  - destruct Archi.ptr64; omega.
Qed.

Lemma fe_ofs_arg_pos:
  0 <= fe_ofs_arg.
Proof.
  reflexivity.
Qed.

Lemma fe_ofs_link_pos:
  forall b,
    0 <= fe_ofs_link (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  etransitivity. 2: apply align_le.
  Local Transparent Z.mul.
  - omega.
  - destruct Archi.ptr64; omega.
Qed.


Lemma fe_ofs_retaddr_pos:
  forall b,
    0 <= fe_ofs_retaddr (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  apply Z.add_nonneg_nonneg; try omega.
  etransitivity. 2: apply align_le; try omega.
  apply Z.add_nonneg_nonneg; try omega.
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply size_callee_save_area_incr.
  apply Z.add_nonneg_nonneg; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  omega.
Qed.


Lemma fe_size_pos:
  forall b,
    0 <= fe_size (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  apply Z.add_nonneg_nonneg; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  apply Z.add_nonneg_nonneg; try omega.
  etransitivity. 2: apply align_le; try omega.
  apply Z.add_nonneg_nonneg; try omega.
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply size_callee_save_area_incr.
  apply Z.add_nonneg_nonneg; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  omega.
Qed.


Lemma fe_ofs_callee_save_pos:
  forall b,
    0 <= fe_ofs_callee_save (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  apply Z.add_nonneg_nonneg; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  omega.
Qed.

Lemma fe_stack_data_pos:
  forall b,
    0 <= fe_stack_data (make_env b).
Proof.
  destruct b.
  Local Opaque Z.mul.
  simpl.
  etransitivity. 2: apply align_le; omega. 
  apply Z.add_nonneg_nonneg; try omega. 
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply size_callee_save_area_incr.
  apply Z.add_nonneg_nonneg; try now (destruct Archi.ptr64; omega).
  etransitivity. 2: apply align_le; try now (destruct Archi.ptr64; omega).
  omega.
Qed.

Definition shift_offset spofs ofs :=
  Ptrofs.unsigned spofs + ofs.

Lemma shift_offset_assoc:
  forall spofs ofs z,
    shift_offset spofs ofs + z =
    shift_offset spofs (ofs + z).
Proof.
  unfold shift_offset; intros; omega.
Qed.

Lemma le_add_pos:
  forall a b,
    0 <= b ->
    a <= a + b.
Proof.
  intros; omega.
Qed.

Lemma fe_ofs_link_fe_size:
  forall b,
    fe_ofs_link (make_env b) <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity.
  2: apply le_add_pos. 2: destruct Archi.ptr64; omega.
  etransitivity. 2: apply align_le.
  2: destruct Archi.ptr64; omega.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 2: omega. 
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 2: omega. 
  etransitivity. 2: apply size_callee_save_area_incr.
  destruct Archi.ptr64; omega.
  omega.  omega.
Qed.

Lemma fe_ofs_arg_fe_size:
  forall b,
    fe_ofs_arg <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply le_add_pos. 2: destruct Archi.ptr64; omega.
  etransitivity. 2: apply align_le. 2: destruct Archi.ptr64; omega.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 2: omega. 
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 2: omega. 
  etransitivity. 2: apply size_callee_save_area_incr.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le.
  unfold fe_ofs_arg. omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
  omega.  omega.
Qed.


Lemma fe_ofs_retaddr_fe_size:
  forall b,
    fe_ofs_retaddr (make_env b) <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  apply le_add_pos. 
  destruct Archi.ptr64; omega.
Qed.

Lemma fe_ofs_local_fe_size:
  forall b,
    fe_ofs_local (make_env b) <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le.
  apply le_add_pos. omega. omega.
  omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
Qed.


Lemma fe_ofs_local_fe_size':
  forall b,
    fe_ofs_local (make_env b) + 4 * bound_local b <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 
  etransitivity. 2: apply le_add_pos.
  apply align_le.
  omega. omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
Qed.

Lemma fe_ofs_callee_save_fe_size:
  forall b,
    fe_ofs_callee_save (make_env b) <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le.
  etransitivity. 2: apply size_callee_save_area_incr. 
  omega. omega. omega. omega. omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
Qed.

Lemma fe_stack_data_fe_size:
  forall b,
    fe_stack_data (make_env b) <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply le_add_pos.
  etransitivity. 2: apply align_le. 
  apply le_add_pos.
  omega. 
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
Qed.

Lemma fe_ofs_callee_save_fe_stack_data:
  forall b,
    size_callee_save_area b (fe_ofs_callee_save (make_env b)) <= fe_stack_data (make_env b).
Proof.
  destruct b. simpl.
  etransitivity. 2: apply align_le. 
  etransitivity. 2: apply le_add_pos.
  apply align_le.
  omega.  omega. omega.
Qed.


Lemma bound_outgoing_fe_size:
  forall b,
    4 * bound_outgoing b <= fe_size (make_env b).
Proof.
  destruct b. simpl.
  repeat (etransitivity; [| (apply le_add_pos || apply align_le || apply size_callee_save_area_incr)]); try omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
  destruct Archi.ptr64; omega.
Qed.

Section PRESERVATION.
Context `{external_calls_prf: ExternalCalls}.

Variable return_address_offset: Mach.function -> Mach.code -> ptrofs -> Prop.

Variable frame_layout: block -> frame.

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

Variables init_sp: Mem.stackblock.
Variable init_ra: val.
Let step := Mach.step init_sp init_ra return_address_offset frame_layout.

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
         (Ptrofs.repr fe.(fe_ofs_link))
         (Ptrofs.repr fe.(fe_ofs_retaddr)).
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
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

Lemma size_no_overflow: fe.(fe_size) <= Ptrofs.max_unsigned.
Proof.
  generalize TRANSF_F. unfold transf_function.
  destruct (wt_function f); simpl negb.
  destruct (zlt Ptrofs.max_unsigned (fe_size (make_env (function_bounds f)))).
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

(* Inspired from Mem.load_unchanged_on *)
Axiom get_stack_unchanged_on:
  forall (P : abs_block -> Z -> Prop) (m m' : mem) ty sp (ofs : Z) (v : val),
    Mem.unchanged_on P m m' ->
    (forall i : Z, ofs <= i < ofs + size_chunk (chunk_of_type ty) -> P (StackBlock sp) i) ->
    Mem.get_stack sp m ty ofs = Some v ->
    Mem.get_stack sp m' ty ofs = Some v.


(** Accessing the stack frame using [load_stack] and [store_stack]. *)

Program Definition stack_contains ty (* (chunk: memory_chunk) *) sp (ofs: Z) (spec: val -> Prop) : massert :=
  {|
    m_pred :=
      fun m =>
        0 <= ofs <= Ptrofs.max_unsigned
        /\ Mem.valid_access m (chunk_of_type ty) (StackBlock sp) ofs Freeable
        /\ exists v, Mem.get_stack sp m ty ofs = Some v /\ spec v;
    m_footprint :=
      fun b' ofs' => StackBlock sp = b' /\ ofs <= ofs' < ofs + size_chunk (chunk_of_type ty);
    m_invar_weak := false
  |}.
Next Obligation.
  rename H2 into v. split;[|split].
- auto.
- red; intros. split; auto. red; intros.
  eapply Mem.perm_unchanged_on; simpl; eauto.
  simpl.  intuition. apply H1; auto.
  destruct H1; auto.
- exists v. split; auto. eapply get_stack_unchanged_on; eauto. simpl; auto.
Qed.
Next Obligation.
  eauto with mem.
Qed. 

Lemma type_of_chunk_of_type ty:
  type_of_chunk (chunk_of_type ty) = ty.
Proof.
  destruct ty; reflexivity.
Qed.

Lemma get_stack_rule:           (* cf. Separation.load_rule *)
  forall spec m n ty ofs,
  m |= stack_contains ty n ofs spec ->
  exists v, Mem.get_stack n m ty ofs = Some v /\ spec v.
Proof.
  intros. destruct H as (D & E & v & F & G). exists v; split; auto.
Qed.

Lemma contains_get_stack:
  forall spec m ty ofs sp,
  m |= stack_contains ty sp ofs spec ->
  exists v, Mem.get_stack sp m ty ofs = Some v /\ spec v.
Proof.
  intros. unfold load_stack.
  eapply get_stack_rule; eauto.
Qed.

Definition stack_hasvalue ty sp (ofs : Z) (v : val) :=
  stack_contains ty sp ofs (fun v' : val => v' = v).

Lemma hasvalue_get_stack:
  forall ty m sp ofs v,
  m |= stack_hasvalue ty sp ofs v ->
  Mem.get_stack sp m ty ofs = Some v.
Proof.
  intros. exploit contains_get_stack; eauto. intros (v' & A & B). subst. eauto.
Qed.

Axiom stack_valid_access_set_stack:
  forall (m1 : mem) (chunk : memory_chunk) sp (ofs : Z) (v : val),
    Mem.valid_access m1 chunk (StackBlock sp) ofs Writable -> {m2 : mem | Mem.set_stack sp m1 (type_of_chunk chunk) ofs v = Some m2}.

Axiom set_stack_stack_valid_access_1:
  forall ty (m1 : mem) sp (ofs : Z) (v : val) (m2 : mem),
    Mem.set_stack sp m1 ty ofs v = Some m2 ->
    forall (chunk' : memory_chunk) sp' (ofs' : Z) (p : permission),
      Mem.valid_access m1 chunk' sp' ofs' p -> Mem.valid_access m2 chunk' sp' ofs' p.

Axiom get_stack_set_stack_same:
  forall ty (m1 : mem) sp (ofs : Z) (v : val) (m2 : mem),
    Mem.set_stack sp m1 ty ofs v = Some m2 ->
    Mem.get_stack sp m2 ty ofs = Some (Val.load_result (chunk_of_type ty) v).

Axiom set_stack_strong_unchanged_on:
  forall (P : abs_block -> Z -> Prop) ty (m : mem) sp (ofs : Z) (v : val) (m' : mem),
    Mem.set_stack sp m ty ofs v = Some m' ->
    (forall i : Z, ofs <= i < ofs + size_chunk (chunk_of_type ty) -> ~ P (StackBlock sp) i) ->
    Mem.strong_unchanged_on P m m'.

Axiom set_stack_unchanged_on:
  forall (P : abs_block -> Z -> Prop) ty (m : mem) sp (ofs : Z) (v : val) (m' : mem),
    Mem.set_stack sp m ty ofs v = Some m' ->
    (forall i : Z, ofs <= i < ofs + size_chunk (chunk_of_type ty) -> ~ P (StackBlock sp) i) ->
    Mem.unchanged_on P m m'.

Lemma set_stack_rule:
  forall ty (m : mem) sp (ofs : Z) (v : val) (spec1 spec : val -> Prop) (P : massert),
    m |= stack_contains ty sp ofs spec1 ** P ->
    spec (Val.load_result (chunk_of_type ty) v) ->
    exists m' : mem, Mem.set_stack sp m ty ofs v = Some m' /\
                m' |= stack_contains ty sp ofs spec ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & v0 & F & G).
  assert (H: Mem.valid_access m (chunk_of_type ty) (StackBlock sp) ofs Writable) by (eauto with mem).
  destruct (stack_valid_access_set_stack _ _ _ _ v H) as [m' STORE].
  rewrite type_of_chunk_of_type in STORE; auto.
  exists m'; split; auto. simpl. intuition auto.
  - eapply set_stack_stack_valid_access_1; eauto.
  - exists (Val.load_result (chunk_of_type ty) v); split; auto. eapply get_stack_set_stack_same; eauto.
  - apply (m_invar P) with m; auto. 
    destruct (m_invar_weak P).
    + eapply set_stack_strong_unchanged_on; eauto.
      intros; red; intros. apply (C (StackBlock sp) i); simpl; auto.
    + eapply set_stack_unchanged_on; eauto.
      intros; red; intros. apply (C (StackBlock sp) i); simpl; auto.
Qed.

Lemma contains_set_stack:
  forall (spec: val -> Prop) v spec1 m ty sp ofs P,
  m |= stack_contains ty sp ofs spec1 ** P ->
  spec (Val.load_result (chunk_of_type ty) v) ->
  exists m',
      store_stack m sp ty (Ptrofs.repr ofs) v = Some m'
  /\ m' |= stack_contains ty sp ofs spec ** P.
Proof.
  intros. unfold store_stack.
  rewrite Ptrofs.unsigned_repr.
  eapply set_stack_rule; eauto.
  destruct H. destruct H. auto.
Qed.

Lemma typesize_size_chunk ty:
  typesize ty * 4 = size_chunk (chunk_of_type ty).
Proof.
  destruct ty; simpl; reflexivity.
Qed.

(** [contains_locations j sp pos bound sl ls] is a separation logic assertion
  that holds if the memory area at block [sp], offset [pos], size [4 * bound],
  reflects the values of the stack locations of kind [sl] given by the
  location map [ls], up to the memory lessdefion [j].

  Two such [contains_locations] assertions will be used later, one to
  reason about the values of [Local] slots, the other about the values of
  [Outgoing] slots. *)

Program Definition contains_locations sp (pos bound: Z) (sl: slot) (ls: locset) : massert := {|
  m_pred := fun m =>
    (8 | pos) /\ 0 <= pos /\ pos + 4 * bound <= Ptrofs.modulus /\
    Mem.range_perm m (StackBlock sp) pos (pos + 4 * bound) Cur Freeable /\
    forall ofs ty, 0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
    exists v, Mem.get_stack sp m ty (pos + 4 * ofs) = Some v
         /\ Val.lessdef (ls (S sl ofs ty)) v;
  m_footprint := fun b' ofs => b' = StackBlock sp /\ pos <= ofs < pos + 4 * bound;
  m_invar_weak := false
|}.
Next Obligation.
  intuition auto. 
  - red; intros. eapply Mem.perm_unchanged_on; eauto. simpl; auto.
  - exploit H4; eauto. intros (v & A & B). exists v; split; auto.
    generalize (type_of_chunk_of_type ty). intro EQty.
    rewrite <- EQty in A |- *.
    eapply get_stack_unchanged_on; eauto.
    simpl; intros. 
    split; auto.
    rewrite type_of_chunk_of_type in *.
    rewrite <- typesize_size_chunk in H8. omega.
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

Remark stack_valid_access_location:
  forall m sp pos bound ofs ty p,
  (8 | pos) ->
  Mem.range_perm m (StackBlock sp) pos (pos + 4 * bound) Cur Freeable ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Mem.valid_access m (chunk_of_type ty) (StackBlock sp) (pos + 4 * ofs) p.
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
  forall m sp pos bound sl ls ofs ty,
  m |= contains_locations sp pos bound sl ls ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  exists v,
    Mem.get_stack sp m ty (pos + 4 * ofs) = Some v
  /\ Val.lessdef (ls (S sl ofs ty)) v.
Proof.
  intros. destruct H as (D & E & F & G & H).
  exploit H; eauto. 
Qed.

Axiom stack_perm_set_stack_1:
  forall ty (m1 : mem) sp (ofs : Z) (v : val) (m2 : mem),
  Mem.set_stack sp m1 ty ofs v = Some m2 ->
  forall b (ofs' : Z) (k : perm_kind) (p : permission), Mem.perm m1 b ofs' k p -> Mem.perm m2 b ofs' k p.

Axiom get_stack_set_stack_other
     : forall ty (m1 : mem) sp (ofs : Z) (v : val) (m2 : mem),
       Mem.set_stack sp m1 ty ofs v = Some m2 ->
       forall (ty' : typ) sp' (ofs' : Z),
         sp' <> sp \/ ofs' + AST.typesize ty' <= ofs \/ ofs + AST.typesize ty <= ofs' ->
         Mem.get_stack sp' m2 ty' ofs' = Mem.get_stack sp' m1 ty' ofs'.

Axiom stack_valid_access_get_stack
     : forall (m : mem) ty sp (ofs : Z),
    Mem.valid_access m (chunk_of_type ty) (StackBlock sp) ofs Readable ->
    exists v : val, Mem.get_stack sp m ty ofs = Some v.

Lemma set_location:
  forall m sp pos bound sl ls P ofs ty v v',
  m |= contains_locations sp pos bound sl ls ** P ->
  0 <= ofs -> ofs + typesize ty <= bound -> (typealign ty | ofs) ->
  Val.lessdef v v' ->
  exists m',
    Mem.set_stack sp m ty (pos + 4 * ofs) v' = Some m'
  /\ m' |= contains_locations sp pos bound sl (Locmap.set (S sl ofs ty) v ls) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F & G & H).
  edestruct stack_valid_access_set_stack as [m' SETSTACK].
  eapply stack_valid_access_location; eauto. 
  assert (PERM: Mem.range_perm m' (StackBlock sp) pos (pos + 4 * bound) Cur Freeable).
  { red; intros; eauto using stack_perm_set_stack_1 with mem. }
  exists m'; split.
- rewrite type_of_chunk_of_type in SETSTACK; eauto. 
- simpl. intuition auto.
+ unfold Locmap.set. 
  destruct (Loc.eq (S sl ofs ty) (S sl ofs0 ty0)); [|destruct (Loc.diff_dec (S sl ofs ty) (S sl ofs0 ty0))].
* (* same location *)
  inv e. rename ofs0 into ofs. rename ty0 into ty.
  exists (Val.load_result (chunk_of_type ty) v'); split.
  exploit get_stack_set_stack_same. eauto.
  rewrite type_of_chunk_of_type. tauto.
  apply Val.load_result_lessdef; auto.
* (* different locations *)
  exploit H; eauto. intros (v0 & X & Y). exists v0; split; auto.
  rewrite <- X. eapply get_stack_set_stack_other; eauto.
  destruct d. congruence. right. rewrite ! typesize_typesize. rewrite type_of_chunk_of_type. omega.
* (* overlapping locations *)
  destruct (stack_valid_access_get_stack m' ty0 sp (pos + 4 * ofs0)) as [v'' LOAD].
  apply Mem.valid_access_implies with Writable; auto with mem. 
  eapply stack_valid_access_location; eauto.
  exists v''; auto.
+ apply (m_invar P) with m; auto. 
  cut (Mem.strong_unchanged_on (m_footprint P) m m').
  {
    destruct (m_invar_weak P); auto using Mem.strong_unchanged_on_weak.
  }
  eapply set_stack_strong_unchanged_on; eauto.
  intros i; rewrite size_type_chunk, typesize_typesize. intros; red; intros.
  eelim C; eauto. simpl. split; auto. rewrite type_of_chunk_of_type in *; omega.
Qed.

Lemma initial_locations:
  forall sp pos bound P sl ls m,
  m |= range (StackBlock sp) pos (pos + 4 * bound) ** P ->
  (8 | pos) ->
  (forall ofs ty, ls (S sl ofs ty) = Vundef) ->
  m |= contains_locations sp pos bound sl ls ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F). split.
- simpl; intuition auto. red; intros; eauto with mem. 
  destruct (stack_valid_access_get_stack m ty sp (pos + 4 * ofs)) as [v LOAD].
  eapply stack_valid_access_location; eauto.
  red; intros; eauto with mem.
  exists v; split; auto. rewrite H1; auto.
- split; assumption.
Qed.

Lemma contains_locations_exten:
  forall ls ls' sp pos bound sl,
  (forall ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  massert_imp (contains_locations sp pos bound sl ls)
              (contains_locations sp pos bound sl ls').
Proof.
  intros; split; simpl; intros; auto.
  intuition auto. rewrite H. eauto.
Qed.

(** [contains_callee_saves j sp pos rl ls] is a memory assertion that holds
  if block [sp], starting at offset [pos], contains the values of the
  callee-save registers [rl] as given by the location map [ls],
  up to the memory lessdefion [j].  The memory layout of the registers in [rl]
  is the same as that implemented by [save_callee_save_rec]. *)

Fixpoint contains_callee_saves sp (pos: Z) (rl: list mreg) (ls: locset) : massert :=
  match rl with
  | nil => pure True
  | r :: rl =>
      let ty := mreg_type r in
      let sz := AST.typesize ty in
      let pos1 := align pos sz in
      stack_contains ty sp pos1 (fun v => Val.lessdef (ls (R r)) v)
      ** contains_callee_saves sp (pos1 + sz) rl ls
  end.

Lemma contains_callee_saves_invar_weak rl :
  forall sp pos ls,
    m_invar_weak (contains_callee_saves sp pos rl ls) = false.
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

Lemma stack_contains_imp:
  forall (spec1 spec2: val -> Prop) chunk b ofs,
  (forall v, spec1 v -> spec2 v) ->
  massert_imp (stack_contains chunk b ofs spec1) (stack_contains chunk b ofs spec2).
Proof.
  intros; split; [| split] ; simpl; intros.
- assumption.
- intuition auto. destruct H4 as (v & A & B). exists v; auto.
- auto.
Qed.

Lemma contains_callee_saves_exten:
  forall sp ls ls' rl pos,
  (forall r, In r rl -> ls' (R r) = ls (R r)) ->
  massert_eqv (contains_callee_saves sp pos rl ls)
              (contains_callee_saves sp pos rl ls').
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

Definition F_frame_layout : frame :=
  frame_of_frame_env b.

Axiom check_link_correct_unchanged:
  forall m sp frame parent
    (CLP: Mem.check_link_correct m sp frame parent)
    m'
    (UNCH: Mem.unchanged_on (fun b' ofs' => StackBlock sp = b' /\ frame_ofs_link frame <= ofs' < frame_ofs_link frame + size_chunk Mptr) m m'),
    Mem.check_link_correct m' sp frame parent.

Local Opaque fe_ofs_link.
Program Definition stack_check_parent sp parent : massert :=
  {|
    m_pred :=
      fun m =>
        Mem.valid_access m Mptr (StackBlock sp) fe.(fe_ofs_link) Freeable
        /\ Mem.check_link_correct m sp F_frame_layout parent;
    m_footprint :=
      fun b' ofs' => StackBlock sp = b' /\ fe.(fe_ofs_link) <= ofs' < fe.(fe_ofs_link) + size_chunk Mptr;
    m_invar_weak := false
  |}.
Next Obligation.
  split.
- red; intros. split; auto. red; intros.
  eapply Mem.perm_unchanged_on; simpl; eauto.
  simpl.  intuition. apply H; auto.
  apply H; auto.
- eapply check_link_correct_unchanged; eauto. 
Qed.
Next Obligation.
  eauto with mem.
Qed. 
Local Transparent fe_ofs_link.

Definition frame_contents_1 sp (ls ls0: locset) (parent: Mem.stackblock) (retaddr: val) :=
    contains_locations sp fe.(fe_ofs_local) b.(bound_local) Local ls
 ** contains_locations sp fe_ofs_arg b.(bound_outgoing) Outgoing ls
 ** stack_check_parent sp parent
 ** stack_hasvalue Tptr sp fe.(fe_ofs_retaddr) retaddr
 ** contains_callee_saves sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0.

Definition frame_contents sp (ls ls0: locset) (parent: Mem.stackblock) (retaddr: val) :=
  mconj (frame_contents_1 sp ls ls0 parent retaddr)
        (range (StackBlock sp) 0 fe.(fe_stack_data) **
         range (StackBlock sp) (fe.(fe_stack_data) + b.(bound_stack_data)) fe.(fe_size)).

Lemma frame_contents_invar_weak sp ls ls0 parent retaddr:
  m_invar_weak (frame_contents sp ls ls0 parent retaddr) = false.
Proof.
  simpl.
  rewrite contains_callee_saves_invar_weak.
  reflexivity.
Qed.

(** Accessing components of the frame. *)

Lemma frame_get_local:
  forall ofs ty sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  exists v,
    load_stack m sp ty (Ptrofs.repr (offset_local fe ofs)) = Some v
  /\ Val.lessdef (ls (S Local ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_proj1 in H.
  unfold load_stack.
  rewrite Ptrofs.unsigned_repr.
  eapply get_location; eauto.
  unfold offset_local.
  destruct H. destruct H3. split.
  omega.
  etransitivity.
  2: apply Z.sub_le_mono_r.
  2: apply H4.
  cut (ofs < bound_local b). omega.
  clear - H0. simpl in *. generalize (typesize_pos ty); omega.
Qed.

Lemma frame_get_outgoing:
  forall ofs ty sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  exists v,
    load_stack m sp ty (Ptrofs.repr (offset_arg ofs)) = Some v
  /\ Val.lessdef (ls (S Outgoing ofs ty)) v.
Proof.
  unfold frame_contents, frame_contents_1; intros. unfold slot_valid in H1; InvBooleans.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick2 in H.
  unfold load_stack.
  rewrite Ptrofs.unsigned_repr.
  eapply get_location; eauto.
  unfold offset_arg. simpl.
  destruct H. destruct H3. split.
  omega.
  etransitivity.
  2: apply Z.sub_le_mono_r.
  2: apply H4.
  cut (ofs < bound_outgoing b). omega.
  clear - H0. simpl in *. generalize (typesize_pos ty); omega.
Qed.

Lemma frame_get_parent:
  forall sp ls ls0 parent retaddr m P,
    m |= frame_contents sp ls ls0 parent retaddr ** P ->
    Mem.check_link_correct m sp F_frame_layout parent. 
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick3 in H.
  apply H.
Qed.

Lemma frame_get_retaddr:
  forall sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  load_stack m sp Tptr (Ptrofs.repr fe.(fe_ofs_retaddr)) = Some retaddr.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  apply mconj_proj1 in H. apply sep_proj1 in H. apply sep_pick4 in H.
  unfold load_stack.
  rewrite Ptrofs.unsigned_repr.
  eapply hasvalue_get_stack; eauto.
  split. apply fe_ofs_retaddr_pos.
  etransitivity. apply fe_ofs_retaddr_fe_size. apply size_no_overflow.
Qed.

(** Assigning a [Local] or [Outgoing] stack slot. *)

Lemma frame_set_local:
  forall ofs ty v v' sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Local ofs ty -> slot_valid f Local ofs ty = true ->
  Val.lessdef v v' ->
  exists m',
    store_stack m sp ty (Ptrofs.repr (offset_local fe ofs)) v' = Some m'
  /\ m' |= frame_contents sp (Locmap.set (S Local ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1. 
  rewrite ! sep_assoc; intros SEP.
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  unfold store_stack.
  rewrite Ptrofs.unsigned_repr; auto.
  {
    unfold offset_local. 
    destruct SEP. destruct H4. split.
    omega.
    etransitivity.
    2: apply Z.sub_le_mono_r.
    2: apply H6.
    cut (ofs < bound_local b). omega.
    clear - H0. simpl in *. generalize (typesize_pos ty); omega.
  }
  assert (forall i k p, Mem.perm m (StackBlock sp) i k p -> Mem.perm m' (StackBlock sp) i k p).
  {  intros. eapply stack_perm_set_stack_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc; exact B.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

Lemma frame_set_outgoing:
  forall ofs ty v v' sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  slot_within_bounds b Outgoing ofs ty -> slot_valid f Outgoing ofs ty = true ->
  Val.lessdef v v' ->
  exists m',
    store_stack m sp ty (Ptrofs.repr (offset_arg ofs)) v' = Some m'
  /\ m' |= frame_contents sp (Locmap.set (S Outgoing ofs ty) v ls) ls0 parent retaddr ** P.
Proof.
  intros. unfold frame_contents in H.
  exploit mconj_proj1; eauto. unfold frame_contents_1.
  rewrite ! sep_assoc, sep_swap. intros SEP. 
  unfold slot_valid in H1; InvBooleans. simpl in H0. 
  exploit set_location; eauto. intros (m' & A & B).
  exists m'; split; auto.
  {
    unfold store_stack; rewrite Ptrofs.unsigned_repr; auto.
    unfold offset_arg. 
    destruct SEP. destruct H4. split.
    omega.
    etransitivity.
    2: apply Z.sub_le_mono_r.
    2: apply H6.
    cut (ofs < bound_outgoing b). omega.
    clear - H0. simpl in *. generalize (typesize_pos ty); omega.
  }
  assert (forall i k p, Mem.perm m (StackBlock sp) i k p -> Mem.perm m' (StackBlock sp) i k p).
  {  intros. eapply stack_perm_set_stack_1; eauto. }
  eapply frame_mconj. eauto.
  unfold frame_contents_1; rewrite ! sep_assoc, sep_swap; eauto.
  eapply sep_preserved.
  eapply sep_proj1. eapply mconj_proj2. eassumption.
  intros; eapply range_preserved; eauto.
  intros; eapply range_preserved; eauto.
Qed.

(** Invariance by change of location maps. *)

Lemma frame_contents_exten:
  forall ls ls0 ls' ls0' sp parent retaddr P m,
  (forall sl ofs ty, ls' (S sl ofs ty) = ls (S sl ofs ty)) ->
  (forall r, In r b.(used_callee_save) -> ls0' (R r) = ls0 (R r)) ->
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  m |= frame_contents sp ls' ls0' parent retaddr ** P.
Proof.
  unfold frame_contents, frame_contents_1; intros.
  rewrite <- ! (contains_locations_exten ls ls') by auto.
  erewrite  <- contains_callee_saves_exten by eauto.
  assumption.
Qed.

(** Invariance by assignment to registers. *)

Corollary frame_set_reg:
  forall r v sp ls ls0 parent retaddr m P,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  m |= frame_contents sp (Locmap.set (R r) v ls) ls0 parent retaddr ** P.
Proof.
  intros. apply frame_contents_exten with ls ls0; auto.
Qed.

Corollary frame_undef_regs:
  forall sp ls ls0 parent retaddr m P rl,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  m |= frame_contents sp (LTL.undef_regs rl ls) ls0 parent retaddr ** P.
Proof.
Local Opaque sepconj.
  induction rl; simpl; intros.
- auto.
- apply frame_set_reg; auto. 
Qed.

Corollary frame_set_regpair:
  forall sp ls0 parent retaddr m P p v ls,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  m |= frame_contents sp (Locmap.setpair p v ls) ls0 parent retaddr ** P.
Proof.
  intros. destruct p; simpl.
  apply frame_set_reg; auto.
  apply frame_set_reg; apply frame_set_reg; auto.
Qed.

Corollary frame_set_res:
  forall sp ls0 parent retaddr m P res v ls,
  m |= frame_contents sp ls ls0 parent retaddr ** P ->
  m |= frame_contents sp (Locmap.setres res v ls) ls0 parent retaddr ** P.
Proof.
  induction res; simpl; intros.
- apply frame_set_reg; auto.
- auto.
- eauto.
Qed.


(** * Agreement between location sets and Mach states *)

(** Agreement with Mach register states *)

Definition agree_regs (ls: locset) (rs: regset) : Prop :=
  forall r, Val.lessdef (ls (R r)) (rs r).

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
  forall ls rs r,
  agree_regs ls rs -> Val.lessdef (ls (R r)) (rs r).
Proof.
  intros. auto.
Qed.

Lemma agree_reglist:
  forall ls rs rl,
  agree_regs ls rs -> Val.lessdef_list (reglist ls rl) (rs##rl).
Proof.
  induction rl; simpl; intros.
  auto. constructor; auto using agree_reg.
Qed.

Hint Resolve agree_reg agree_reglist: stacking.

(** Preservation under assignments of machine registers. *)

Lemma agree_regs_set_reg:
  forall ls rs r v v',
  agree_regs ls rs ->
  Val.lessdef v v' ->
  agree_regs (Locmap.set (R r) v ls) (Regmap.set r v' rs).
Proof.
  intros; red; intros.
  unfold Regmap.set. destruct (RegEq.eq r0 r). subst r0.
  rewrite Locmap.gss; auto.
  rewrite Locmap.gso; auto. red. auto.
Qed.

Lemma agree_regs_set_pair:
  forall p v v' ls rs,
  agree_regs ls rs ->
  Val.lessdef v v' ->
  agree_regs (Locmap.setpair p v ls) (set_pair p v' rs).
Proof.
  intros. destruct p; simpl.
- apply agree_regs_set_reg; auto.
- apply agree_regs_set_reg. apply agree_regs_set_reg; auto. 
  apply Val.hiword_lessdef; auto. apply Val.loword_lessdef; auto.
Qed.

Lemma agree_regs_set_res:
  forall res v v' ls rs,
  agree_regs ls rs ->
  Val.lessdef v v' ->
  agree_regs (Locmap.setres res v ls) (set_res res v' rs).
Proof.
  induction res; simpl; intros.
- apply agree_regs_set_reg; auto.
- auto.
- apply IHres2. apply IHres1. auto.
  apply Val.hiword_lessdef; auto.
  apply Val.loword_lessdef; auto.
Qed.

Lemma agree_regs_exten:
  forall ls rs ls' rs',
  agree_regs ls rs ->
  (forall r, ls' (R r) = Vundef \/ ls' (R r) = ls (R r) /\ rs' r = rs r) ->
  agree_regs ls' rs'.
Proof.
  intros; red; intros.
  destruct (H0 r) as [A | [A B]].
  rewrite A. constructor.
  rewrite A; rewrite B; auto.
Qed.

Lemma agree_regs_undef_regs:
  forall rl ls rs,
  agree_regs ls rs ->
  agree_regs (LTL.undef_regs rl ls) (Mach.undef_regs rl rs).
Proof.
  induction rl; simpl; intros.
  auto.
  apply agree_regs_set_reg; auto.
Qed.

(** Preservation under assignment of stack slot *)

Lemma agree_regs_set_slot:
  forall ls rs sl ofs ty v,
  agree_regs ls rs ->
  agree_regs (Locmap.set (S sl ofs ty) v ls) rs.
Proof.
  intros; red; intros. rewrite Locmap.gso; auto. red. auto.
Qed.

(** Preservation at function entry. *)

Lemma agree_regs_call_regs:
  forall ls rs,
  agree_regs ls rs ->
  agree_regs (call_regs ls) rs.
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
Local Transparent destroyed_by_store.
  unfold no_callee_saves, destroyed_by_store; intros; destruct chunk; try reflexivity; destruct Archi.ptr64; reflexivity.
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

Variable cs: list stackframe.
Variable fb: block.
Variable sp: Mem.stackblock.
Variable ls: locset.

Hypothesis ls_temp_undef:
  forall ty r, In r (destroyed_by_setstack ty) -> ls (R r) = Vundef.

Hypothesis wt_ls: forall r, Val.has_type (ls (R r)) (mreg_type r).

Lemma stack_range_contains:
  forall ty (ofs : Z) (P : massert) (m : mem),
    m |= range (StackBlock sp) ofs (ofs + size_chunk (chunk_of_type ty)) ** P ->
    (align_chunk (chunk_of_type ty) | ofs) ->
    m |= stack_contains ty sp ofs (fun _ : val => True) ** P.
Proof.
  intros. destruct H as (A & B & C). destruct A as (D & E & F).
  split; [|split].
  - assert (Mem.valid_access m (chunk_of_type ty) (StackBlock sp) ofs Freeable).
    { split; auto. red; auto. }
    split. generalize (size_chunk_pos (chunk_of_type ty)). unfold Ptrofs.max_unsigned. omega.
    split. auto.
    destruct (stack_valid_access_get_stack m ty sp ofs) as [v LOAD].
    eauto with mem.
    exists v; auto.
  - auto.
  - red. simpl. destruct al; simpl; try easy. intros.
    exploit C. 2: apply H1. 2: auto.
    simpl. intuition congruence.
Qed.

Axiom perm_set_stack_1:
  forall n m ty o v m' b ofs k p,
    Mem.set_stack n m ty o v = Some m' ->
    Mem.perm m b ofs k p ->
    Mem.perm m' b ofs k p.

Axiom valid_block_set_stack_1:
  forall n m ty o v m' b,
    Mem.set_stack n m ty o v = Some m' ->
    Mem.valid_block m b ->
    Mem.valid_block m' b.


Axiom set_stack_outside_extends:
  forall ty m1 m2 b o v m2',
    Mem.extends m1 m2 ->
    Mem.set_stack b m2 ty o v = Some m2' ->
    (forall ofs, Mem.perm m1 (StackBlock b) ofs Cur Readable ->
            o <= ofs < o + size_chunk (chunk_of_type ty) -> False) ->
    Mem.extends m1 m2'.

Lemma save_callee_save_rec_correct:
  forall k l pos rs m P,
    (forall r, In r l -> is_callee_save r = true) ->
    m |= range (StackBlock sp) pos (size_callee_save_area_rec l pos) ** P ->
    agree_regs ls rs ->
    forall m0,
      Mem.extends m0 m ->
      (forall ofs k,
          pos <= ofs < size_callee_save_area_rec l pos ->
          ~ Mem.perm m0 (StackBlock sp) ofs k Readable) ->
  exists rs', exists m',
     star step tge
        (State cs fb sp (save_callee_save_rec l pos k) rs m)
     E0 (State cs fb sp k rs' m')
  /\ m' |= contains_callee_saves sp pos l ls ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs ls rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b)
  /\ Mem.unchanged_on (fun b o => b <> StackBlock sp) m m'
  /\ Mem.extends m0 m'.
Proof.
Local Opaque mreg_type.
  induction l as [ | r l]; simpl; intros until P; intros CS SEP AG m0 EXT NOPERM.
- exists rs, m. 
  split. apply star_refl.
  split. rewrite sep_pure; split; auto. eapply sep_drop; eauto.
  split. auto. 
  split. auto.
  split. auto.
  split. apply Mem.unchanged_on_refl.
  auto.
- set (ty := mreg_type r) in *.
  set (sz := AST.typesize ty) in *.
  set (pos1 := align pos sz) in *.
  assert (POSpos: 0 <= pos).
  {
    destruct SEP. destruct H. auto.
  }
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
  apply stack_range_contains in SEP; auto.
  exploit (contains_set_stack (fun v' => Val.lessdef (ls (R r)) v') (rs r)).
  eexact SEP.
  apply load_result_lessdef; auto. apply wt_ls. 
  clear SEP; intros (m1 & STORE & SEP).
  set (rs1 := undef_regs (destroyed_by_setstack ty) rs).
  assert (AG1: agree_regs ls rs1).
  { red; intros. unfold rs1. destruct (In_dec mreg_eq r0 (destroyed_by_setstack ty)).
    erewrite ls_temp_undef by eauto. auto.
    rewrite undef_regs_other by auto. apply AG. }
  rewrite sep_swap in SEP.
  exploit set_stack_outside_extends. eauto. eauto.
  {
    intros.
    rewrite Ptrofs.unsigned_repr in H0.
    eapply NOPERM. 2: apply H.
    split. etransitivity. apply POS1. omega. 
    eapply Z.lt_le_trans. apply H0. unfold sz.
    etransitivity.
    2: apply size_callee_save_area_rec_incr.
    destruct ty; simpl; reflexivity.
    split.
    omega.
    destruct SEP. destruct H1. destruct H3. 
    unfold Ptrofs.max_unsigned. 
    etransitivity.
    2: apply Z.sub_le_mono_r.
    2: apply H3. omega.
  }
  intro EXT'.
  exploit (IHl (pos1 + sz) rs1 m1); eauto.
  {
    intros ofs k0 RNG.
    eapply NOPERM. omega.
  }
  intros (rs2 & m2 & A & B & C & D & VALID & UNCH & EXT'').
  exists rs2, m2. 
  split. eapply star_left; eauto. constructor. exact STORE. auto. traceEq.
  split. rewrite sep_assoc, sep_swap. exact B.
  split. intros. apply C. eapply perm_set_stack_1; eauto.
  split. auto.
  split. unfold store_stack, Val.offset_ptr, Mem.storev in STORE.
  eauto using valid_block_set_stack_1.
  split. unfold store_stack in STORE.
  eapply Mem.unchanged_on_trans. 2: apply UNCH.
  eapply set_stack_unchanged_on; eauto.
  auto.
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
  forall sp ls ls0 rs cs fb k m P,
  m |= range (StackBlock sp) fe.(fe_ofs_callee_save) (size_callee_save_area b fe.(fe_ofs_callee_save)) ** P ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  agree_callee_save ls ls0 ->
  agree_regs ls rs ->
  let ls1 := LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) in
  let rs1 := undef_regs destroyed_at_function_entry rs in
  forall m0,
    Mem.extends m0 m ->
    (forall ofs k,
        fe.(fe_ofs_callee_save) <= ofs < size_callee_save_area b fe.(fe_ofs_callee_save) ->
        ~ Mem.perm m0 (StackBlock sp) ofs k Readable) ->
  exists rs', exists m',
     star step tge
        (State cs fb sp (save_callee_save fe k) rs1 m)
     E0 (State cs fb sp k rs' m')
  /\ m' |= contains_callee_saves sp fe.(fe_ofs_callee_save) b.(used_callee_save) ls0 ** P
  /\ (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p)
  /\ agree_regs ls1 rs'
  /\ (forall b, Mem.valid_block m b -> Mem.valid_block m' b )
  /\ Mem.unchanged_on (fun b o => b <> StackBlock sp) m m'
  /\ Mem.extends m0 m'.
Proof.
  intros until P; intros SEP TY AGCS AG; intros ls1 rs1 m0 EXT NOPERM.
  exploit (save_callee_save_rec_correct cs fb sp ls1).
- intros. unfold ls1. apply LTL_undef_regs_same. eapply destroyed_by_setstack_function_entry; eauto.
- intros. unfold ls1. apply undef_regs_type. apply TY. 
- exact b.(used_callee_save_prop).
- eexact SEP.
- instantiate (1 := rs1). apply agree_regs_undef_regs. apply agree_regs_call_regs. auto.
- eexact EXT.
- eexact NOPERM.
- clear SEP. intros (rs' & m' & EXEC & SEP & PERMS & AG' & VALID & UNCH & EXT').
  exists rs', m'. 
  split. eexact EXEC.
  split. rewrite (contains_callee_saves_exten sp ls0 ls1). exact SEP.
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
  split. exact VALID.
  split. exact UNCH.
  exact EXT'.
Qed.

(** As a corollary of the previous lemmas, we obtain the following
  correctness theorem for the execution of a function prologue
  (allocation of the frame + saving of the link and return address +
  saving of the used callee-save registers). *)


Definition msegment sp (s: segment) : massert :=
  range sp (seg_ofs s) (seg_ofs s + seg_size s).

Definition frame_permission_nocs :=
  {|
    frame_ofs_link_perm := Freeable;
    frame_ofs_retaddr_perm := Freeable;
    frame_locals_perm := Nonempty;
    frame_outgoings_perm := Nonempty;
    frame_callee_saves_perm := Nonempty;
  |}.

Definition frame_permission_full :=
  {|
    frame_ofs_link_perm := Freeable;
    frame_ofs_retaddr_perm := Freeable;
    frame_locals_perm := Freeable;
    frame_outgoings_perm := Freeable;
    frame_callee_saves_perm := Freeable;
  |}.

Axiom push_frame_extends:
  forall m1 f m1' ra sp m2 ra' parent P,
    Mem.push_frame m1 f ra frame_permission_nocs = Some (m1', sp) ->
    Mem.extends m1 m2 ->
    Val.lessdef ra ra' ->
    m2 |= P ->
    Mem.get_sp m2 = Some parent ->
    exists m2',
      Mem.push_frame m2 f ra' frame_permission_full = Some (m2', sp) /\
      Mem.extends m1' m2' /\
      m2' |= msegment (StackBlock sp) (frame_outgoings f)
          ** msegment (StackBlock sp) (frame_locals f)
          ** msegment (StackBlock sp) (frame_callee_saves f)
          ** stack_check_parent sp parent
          ** stack_hasvalue Tptr sp (frame_ofs_retaddr f) ra'
          ** P /\
      m2' |=
          range (StackBlock sp) 0 (seg_ofs (frame_data f)) **
          range (StackBlock sp) (seg_ofs (frame_data f) + seg_size (frame_data f)) (frame_size f) ** P.

Lemma divide_align_refl:
  forall x y, 0 < y ->
    (y | x) -> align x y = x.
Proof.
  clear. intros.
  destruct H0. subst.
  unfold align.
  replace (x0 * y + y - 1) with (x0 * y + (y - 1)) by omega.
  rewrite Z_div_plus_full_l by omega.
  rewrite Z.div_small. rewrite Z.add_0_r. auto.
  omega.
Qed.


Lemma align_distr:
  forall al (AlPos: al > 0) z z1,
    align z al + align z1 al = align (align z al + z1) al.
Proof.
  intros.
  generalize (align_divides z al AlPos).
  generalize (align z al).
  unfold align.  intros z0 [x EQ]. subst.
  rewrite <- Z.mul_add_distr_r.
  f_equal. replace (x*al + z1 + al - 1) with ((x*al) + (z1 + al - 1)) by omega.
  rewrite Z.div_add_l. auto. omega.
Qed.



Ltac elim_div :=
  unfold Zdiv, Zmod in *;
  repeat
    match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
    end; unfold Remainder.

Lemma align_plus:
  forall al z,
    al = 4 \/ al = 8 ->
    align (align z 8) al = align z 8.
Proof.
  intros al z.
  unfold align. intros.
  elim_div. assert (al <> 0) by omega.
  intuition subst; omega.
Qed.



Lemma size_callee_save_area_rec_rew:
  forall l y x
    (DIV: (if Archi.ptr64 then 8 else 4| y)),
    size_callee_save_area_rec l (y + x) =
    y + size_callee_save_area_rec l x.
Proof.
  induction l; simpl; intros; eauto.
  etransitivity. 2: apply IHl; auto.
  f_equal.
  rewrite Z.add_assoc. f_equal.
  rewrite <- (fun pf => divide_align_refl _ _ pf DIV) by omega.
  erewrite <- align_plus.
  rewrite <- align_distr. reflexivity. destruct a; reflexivity.
  destruct a; simpl; destruct Archi.ptr64; simpl; auto.
Qed.

Lemma size_callee_save_area_is_add ofs:
  forall (DIV: (if Archi.ptr64 then 8 else 4| ofs)),
  size_callee_save_area b ofs = ofs + size_callee_save_area b 0.
Proof.
  unfold size_callee_save_area.
  intros.
  replace ofs with (ofs + 0).
  rewrite size_callee_save_area_rec_rew. omega. auto. omega.  
Qed.

Lemma fe_ocs_div:
  (if Archi.ptr64 then 8 else 4 | fe_ofs_callee_save fe).
Proof.
  simpl.
  apply Z.divide_add_r.
  apply align_divides. destruct Archi.ptr64; omega.
  reflexivity.
Qed.

Axiom push_frame_valid_block:
  forall (m1 m2: mem) f ra sp fperm,
    Mem.push_frame m1 f ra fperm = Some (m2, sp) ->
    forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b.

Axiom push_frame_perm:
  forall (m1 m2: mem) f ra sp fperm,
    Mem.push_frame m1 f ra fperm = Some (m2, sp) ->
    forall b o k p, Mem.perm m1 b o k p -> Mem.perm m2 b o k p.


Axiom push_frame_unchanged_on:
  forall (m1 m2: mem) f ra sp fperm,
    Mem.push_frame m1 f ra  fperm= Some (m2, sp) ->
    forall P, Mem.unchanged_on P m1 m2.

Axiom push_frame_perm_cs:
  forall (m1 m2: mem) f ra sp fperm,
    Mem.push_frame m1 f ra fperm = Some (m2, sp) ->
    forall o k p,
      Mem.perm m2 (StackBlock sp) o k p ->
      seg_ofs (frame_callee_saves f) <= o < seg_ofs (frame_callee_saves f) + seg_size (frame_callee_saves f) ->
      perm_order (frame_callee_saves_perm fperm) p.

Lemma function_prologue_correct:
  forall ls ls0 ls1 rs rs1 m1 m1' m2 sp parent ra cs fb k P,
  agree_regs ls rs ->
  agree_callee_save ls ls0 ->
  (forall r, Val.has_type (ls (R r)) (mreg_type r)) ->
  ls1 = LTL.undef_regs destroyed_at_function_entry (LTL.call_regs ls) ->
  rs1 = undef_regs destroyed_at_function_entry rs ->
  Mem.push_frame m1 (frame_of_frame_env b) Vundef frame_permission_nocs = Some (m2, sp) ->
  (* Val.has_type parent Tptr -> *)
  Val.has_type ra Tptr ->
  Mem.extends m1 m1' ->
  m1' |= P ->
  Mem.get_sp m1' = Some parent ->
  exists (* j' *) rs' m2' sp' m5',
    Mem.push_frame m1' (frame_of_frame_env b) ra frame_permission_full = Some (m2', sp')
    (* /\ store_stack m2' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_link_ofs) parent = Some m3' *)
    (* /\ store_stack m3' (Vptr sp' Ptrofs.zero) Tptr tf.(fn_retaddr_ofs) ra = Some m4' *)
  /\ star step tge
         (State cs fb sp' (save_callee_save fe k) rs1 m2')
      E0 (State cs fb sp' k rs' m5')
  /\ agree_regs ls1 rs'
  /\ agree_locs ls1 ls0
  /\ m5' |= frame_contents sp' ls1 ls0 parent ra ** P (* ** minjection m2 ** globalenv_inject ge ** P *)
  /\ Mem.extends m2 m5'
  (* /\ j' sp = Some(sp', fe.(fe_stack_data)) *)
  (* /\ lessdef_incr j' *)
  (* /\ lessdef_separated j' m1 m1' *)
  /\ (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)
  /\ (forall b, Mem.valid_block m1' b -> Mem.valid_block m5' b)
  /\ (forall b o k p, Mem.perm m1' b o k p -> Mem.perm m5' b o k p)
  /\ Mem.unchanged_on (fun b o => b <> StackBlock sp') m1' m5'.
Proof.
  intros until P; intros AGREGS AGCS WTREGS LS1 RS1 ALLOC TYRA EXT SEP PARENT.
  (* Stack layout info *)
Local Opaque b fe.
  generalize (frame_env_range b) (frame_env_aligned b). replace (make_env b) with fe by auto. simpl. 
  intros LAYOUT1 LAYOUT2.
  (* Allocation step *)
  edestruct (push_frame_extends) as (m2' & PF' & EXT' & SEP' & SEPCONJ1); eauto.
  (* Remember the freeable permissions using a mconj *)
  assert (SEPCONJ:
            m2' |= mconj (range (StackBlock sp) 0 (fe_stack_data fe) **
                                range (StackBlock sp) (fe_stack_data fe + bound_stack_data b) (fe_size fe))
                (range (StackBlock sp) 0 (fe_stack_data fe) **
                       range (StackBlock sp) (fe_stack_data fe + bound_stack_data b) (fe_size fe)) ** P).
  { apply mconj_intro; rewrite sep_assoc; assumption. }
  (* Dividing up the frame *)
  unfold msegment in SEP'.
  Opaque fe_ofs_callee_save fe_size fe_ofs_link fe_ofs_retaddr fe_ofs_local fe_ofs_arg.
  simpl in SEP'. replace (make_env b) with fe in SEP' by auto.

  (* Saving callee-save registers *)
  rewrite sep_swap3 in SEP'.
  exploit (save_callee_save_correct sp ls ls0 rs); eauto.
  rewrite size_callee_save_area_is_add. eauto. apply fe_ocs_div.
  {
    intros. intro PERM.
    eapply push_frame_perm_cs in PERM; eauto. simpl in PERM. inv PERM.
    simpl.
    rewrite <- size_callee_save_area_is_add. apply H.
    apply fe_ocs_div.
  }
  replace (LTL.undef_regs destroyed_at_function_entry (call_regs ls)) with ls1 by auto.
  replace (undef_regs destroyed_at_function_entry rs) with rs1 by auto.
  clear SEP; intros (rs2 & m5' & SAVE_CS & SEP & PERMS & AGREGS' & VALID & UNCH & EXT2).
  rewrite sep_swap2 in SEP.
  (* Materializing the Local and Outgoing locations *)
  exploit (initial_locations). eexact SEP. tauto. 
  instantiate (1 := Local). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap3 in SEP.
  exploit (initial_locations). eexact SEP. tauto. 
  instantiate (1 := Outgoing). instantiate (1 := ls1). 
  intros; rewrite LS1. rewrite LTL_undef_regs_slot. reflexivity.
  clear SEP; intros SEP.
  rewrite sep_swap3 in SEP.
  rewrite sep_swap23 in SEP.
  rewrite sep_swap34 in SEP.
  rewrite sep_swap45 in SEP.
  (* Now we frame this *)
  assert (SEPFINAL: m5' |= frame_contents sp ls1 ls0 parent ra ** P).
  { eapply frame_mconj. eexact SEPCONJ.
    unfold frame_contents_1; rewrite ! sep_assoc. exact SEP.
    
    (* assert (forall ofs k p, Mem.perm m2' (StackBlock sp) ofs k p -> Mem.perm m5' (StackBlock sp) ofs k p). *)
    (* { intros. apply PERMS; auto. *)
    (*   unfold store_stack in STORE_PARENT, STORE_RETADDR. *)
    (*   simpl in STORE_PARENT, STORE_RETADDR. *)
    (*   eauto using Mem.perm_store_1. } *)
    eapply sep_preserved. eapply sep_proj1. eapply mconj_proj2. eexact SEPCONJ.
    intros; apply range_preserved with m2'; auto.
    intros; apply range_preserved with m2'; auto.
  }
  clear SEP SEPCONJ.
(* Conclusions *)
  exists rs2, m2', sp, m5'.
  repeat (match goal with |- _ /\ _ => refine (conj _ _) end); auto.
  - eexact SAVE_CS.
  - rewrite LS1. apply agree_locs_undef_locs; [|reflexivity].
    constructor; intros. unfold call_regs. apply AGCS. 
    unfold mreg_within_bounds in H; tauto.
    unfold call_regs. apply AGCS. auto.
  - intros.
    eapply push_frame_valid_block; eauto.
  - intros. apply VALID. revert H. eapply push_frame_valid_block; eauto. 
  - intros. apply PERMS. eapply push_frame_perm; eauto.
  - eapply Mem.unchanged_on_trans. 2: apply UNCH. eapply push_frame_unchanged_on; eauto.
Qed.

(** The following lemmas show the correctness of the register reloading
  code generated by [reload_callee_save]: after this code has executed,
  all callee-save registers contain the same values they had at
  function entry. *)

Section RESTORE_CALLEE_SAVE.

Variable j: meminj.
Variable cs: list stackframe.
Variable fb: block.
Variable sp: Mem.stackblock.
Variable ls0: locset.
Variable m: mem.

Definition agree_unused (ls0: locset) (rs: regset) : Prop :=
  forall r, ~(mreg_within_bounds b r) -> Val.lessdef (ls0 (R r)) (rs r).

Lemma restore_callee_save_rec_correct:
  forall l ofs rs k,
  m |= contains_callee_saves sp ofs l ls0 ->
  agree_unused ls0 rs ->
  (forall r, In r l -> mreg_within_bounds b r) ->
  exists rs',
    star step tge
      (State cs fb sp (restore_callee_save_rec l ofs k) rs m)
   E0 (State cs fb sp k rs' m)
  /\ (forall r, In r l -> Val.lessdef (ls0 (R r)) (rs' r))
  /\ (forall r, ~(In r l) -> rs' r = rs r)
  /\ agree_unused ls0 rs'.
Proof.
Local Opaque mreg_type.
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
  split.
  + eapply star_step; eauto. 
    * econstructor. unfold load_stack. rewrite Ptrofs.unsigned_repr. exact LOAD.
      destruct H. destruct H. apply H.
    * traceEq.
  + split. intros.
    destruct (In_dec mreg_eq r0 l). auto. 
    assert (r = r0) by tauto. subst r0.
    rewrite C by auto. rewrite Regmap.gss. exact SPEC.
    split. intros. 
    rewrite C by tauto. apply Regmap.gso. intuition auto.
    exact D.
Qed.

End RESTORE_CALLEE_SAVE.

Lemma restore_callee_save_correct:
  forall m sp ls ls0 pa ra P rs k cs fb,
  m |= frame_contents sp ls ls0 pa ra ** P ->
  agree_unused ls0 rs ->
  exists rs',
    star step tge
       (State cs fb sp (restore_callee_save fe k) rs m)
    E0 (State cs fb sp k rs' m)
  /\ (forall r,
        is_callee_save r = true -> Val.lessdef (ls0 (R r)) (rs' r))
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


Axiom pop_frame_rule:
  forall m1 b m1' m2 lo hi P,
    m2 |= range (StackBlock b) lo hi ** P ->
    Mem.extends m1 m2 ->
    Mem.get_sp m2 = Some b ->
    Mem.pop_frame m1 = Some m1' ->
    exists m2',
      Mem.pop_frame m2 = Some m2' /\
      m2' |= P /\
      Mem.extends m1' m2'.

Lemma function_epilogue_correct:
  forall m' sp' ls ls0 pa ra P m rs m1 k cs fb,
    Mem.extends m m' ->
    m' |= frame_contents sp' ls ls0 pa ra ** P ->
    agree_regs ls rs ->
    agree_locs ls ls0 ->
    Mem.pop_frame m = Some m1 ->
    Mem.get_sp m' = Some sp' ->
    exists rs1 m1',
      Mem.check_link_correct m' sp' F_frame_layout pa
      /\ load_stack m' sp' Tptr (Ptrofs.repr (frame_ofs_retaddr F_frame_layout)) = Some ra
      /\ Mem.pop_frame m' = Some m1'
      /\ star step tge
             (State cs fb sp' (restore_callee_save fe k) rs m')
             E0 (State cs fb sp' k rs1 m')
      /\ agree_regs (return_regs ls0 ls) rs1
      /\ agree_callee_save (return_regs ls0 ls) ls0
      /\ Mem.extends m1 m1'
      /\ m1' |= P.
Proof.
  intros until fb; intros EXT SEP AGR AGL POP GSP.
  (* Can free *)
  exploit pop_frame_rule.
  rewrite <- sep_assoc. eapply mconj_proj2. eexact SEP.
  eexact EXT.
  eexact GSP.
  eexact POP.
  intros (m2' & POP' & SEP' & EXT').
  (* Reloading the callee-save registers *)
  exploit restore_callee_save_correct.
  eexact SEP.
  instantiate (1 := rs). 
  red; intros. destruct AGL. rewrite <- agree_unused_reg0 by auto. apply AGR.
  intros (rs' & LOAD_CS & CS & NCS).
  (* Reloading the back link and return address *)
  unfold frame_contents in SEP; apply mconj_proj1 in SEP.
  unfold frame_contents_1 in SEP; rewrite ! sep_assoc in SEP.
  assert (LOAD_LINK: Mem.check_link_correct m' sp' F_frame_layout pa).
  {
    eapply sep_pick3 in SEP. simpl in SEP. apply SEP.
  }
  exploit (hasvalue_get_stack Tptr). eapply sep_pick4; eexact SEP. intros LOAD_RETADDR.
  clear SEP.
  (* Conclusions *)
  exists rs', m2'.
  split. assumption.
  split. unfold load_stack. rewrite Ptrofs.unsigned_repr. assumption.
  simpl. split. apply fe_ofs_retaddr_pos. etransitivity. apply fe_ofs_retaddr_fe_size. apply size_no_overflow.
  split. assumption.
  split. eassumption.
  split. red; unfold return_regs; intros. 
  destruct (is_callee_save r) eqn:C.
  apply CS; auto.
  rewrite NCS by auto. apply AGR.
  split. red; unfold return_regs; intros.
  destruct l; auto. rewrite H; auto.
  split. assumption.
  apply SEP'.
Qed.

End FRAME_PROPERTIES.

(** * Call stack invariants *)

(** This is the memory assertion that captures the contents of the stack frames
  mentioned in the call stacks. *)

Variable init_ls: locset.

Fixpoint stack_contents (cs: list Linear.stackframe) (cs': list Mach.stackframe) : massert :=
  match cs, cs' with
  | nil, nil => pure True
  | Linear.Stackframe f _ ls c :: cs, Mach.Stackframe fb sp' ra c' :: cs' =>
      frame_contents f sp' ls (parent_locset init_ls cs) (parent_sp init_sp cs') (parent_ra init_ra cs')
      ** stack_contents cs cs'
  | _, _ => pure False
  end.

Lemma stack_contents_invar_weak cs :
  forall cs' , m_invar_weak (stack_contents cs cs') = false.
Proof.
  induction cs; destruct cs' ; simpl; auto.
  + destruct a; auto.
  + destruct a; auto.
    destruct s; auto.
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

(* [init_sg] is the signature of the outermost calling function. In the
whole-program, this is the signature of the [main] function (see the
match_states' definition at the very end of this file) *)

Variable init_sg: signature.

(** [match_stacks] captures additional properties (not related to memory)
  of the Linear and Mach call stacks. *)


Inductive match_stacks :
  list Linear.stackframe -> list stackframe -> signature -> signature -> Prop :=
| match_stacks_empty:
    forall sg
      (TP: tailcall_possible sg \/ sg = init_sg)
      (BND: 4 * size_arguments sg <= Ptrofs.max_unsigned),
      match_stacks nil nil sg sg
| match_stacks_cons:
    forall f sp ls c cs fb ra c' cs' sg trf
      isg
      (TAIL: is_tail c (Linear.fn_code f))
      (FINDF: Genv.find_funct_ptr tge fb = Some (Internal trf))
      (TRF: transf_function f = OK trf)
      (TRC: transl_code (make_env (function_bounds f)) c = c')
      (TY_RA: Val.has_type ra Tptr)
      (AGL: agree_locs f ls (parent_locset init_ls cs))
      (ARGS: forall ofs ty,
          In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments sg)) ->
          slot_within_bounds (function_bounds f) Outgoing ofs ty)
      (BND: 4 * size_arguments sg <= Ptrofs.max_unsigned)
      (NOT_INIT: init_sp <> sp)
      (STK: match_stacks cs cs' (Linear.fn_sig f) isg),
      match_stacks (Linear.Stackframe f sp ls c :: cs)
                   (Stackframe fb sp ra c' :: cs')
                   sg isg.

(* [args_out_of_bounds] states that the locations in [l] have no permission and
can therefore not be overwritten by the callee. This is exclusively applied to
the locations of the arguments of the outermost caller ([main] in the
whole-program setting). *)

Definition init_args_out_of_bounds sg m :=
  forall of ty,
    List.In (Locations.S Outgoing of ty) (regs_of_rpairs (loc_arguments sg)) ->
    let ofs := Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * of)) in
    forall o,
      ofs <= o < (ofs + size_chunk (chunk_of_type ty)) ->
      loc_out_of_bounds m (StackBlock init_sp) o.

Lemma init_args_out_of_bounds_store sg chunk m b o v m':
  Mem.store chunk m b o v = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m'.
Proof.
  unfold init_args_out_of_bounds.
  intros H H0 of ty H2 o1 H3.
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
  unfold init_args_out_of_bounds.
  intros H H0 of ty H2 o0 H3.
  intro ABSURD.
  eapply Mem.perm_free_3 in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Axiom pop_frame_valid_block:
  forall m m' b,
    Mem.pop_frame m = Some m' ->
    Mem.valid_block m b ->
    Mem.valid_block m' b.

Axiom pop_frame_perm:
  forall m m',
    Mem.pop_frame m = Some m' ->
    forall b o k p,
      Mem.perm m' b o k p ->
      Mem.perm m b o k p.


Lemma init_args_out_of_bounds_pop_frame sg m m' :
  Mem.pop_frame m = Some m' ->
  init_args_out_of_bounds sg m ->
  init_args_out_of_bounds sg m' .
Proof.
  unfold init_args_out_of_bounds.
  intros H H0 of ty H2 o0 H3.
  intro ABSURD.
  eapply pop_frame_perm in ABSURD; eauto.
  eapply H0; eauto.
Qed.

Lemma init_args_out_of_bounds_external_call sg_ ef args m_ t vl m'_ :
  Mem.valid_block m_ (StackBlock init_sp) ->
  external_call ef ge args m_ t vl m'_ ->
  forall m m' sg ll lm ,
    match_stacks ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.extends m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds.
  intros VB H m m' sg ll lm H0 H1 H2 H3 of ty H5 o0 H6.
  intro ABSURD.
  eapply H3; eauto.
  eapply external_call_max_perm; eauto.
Qed.

Definition block_prop P v :=
  match v with
    Vptr b o => P b
  | _ => True
  end.

Lemma init_args_out_of_bounds_alloc m_ lo hi m'_ b :
  Mem.alloc m_ lo hi = (m'_, b) ->
  Mem.valid_block m_ (StackBlock init_sp) ->
  forall sg_ m m' sg ll lm,
    match_stacks ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.extends m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds, loc_out_of_bounds.
  intros H SPV sg_ m m' sg ll lm H0 H1 H2 H3 of ty H5 o0 H6.
  intro ABSURD.
  eapply Mem.perm_alloc_4 in ABSURD; eauto.
  { eapply H3; eauto. }
  congruence.
Qed.


Axiom push_frame_perm_diff_block
     : forall m1 fr ra frp m2 sp,
       Mem.push_frame m1 fr ra frp = Some (m2, sp) ->
       forall b' ofs k p,
       Mem.perm m2 b' ofs k p -> b' <> StackBlock sp -> Mem.perm m1 b' ofs k p.

Axiom push_frame_fresh_block
     : forall m1 fr ra frp m2 sp,
       Mem.push_frame m1 fr ra frp = Some (m2, sp) ->
       ~ Mem.valid_block m1 (StackBlock sp).

Lemma init_args_out_of_bounds_push_frame m_ fr frp ra m'_ b :
  Mem.push_frame m_ fr ra frp = Some (m'_, b) ->
  Mem.valid_block m_ (StackBlock init_sp) ->
  forall sg_ m m' sg ll lm,
    match_stacks ll lm sg sg_ ->
    Mem.extends m_ m ->
    Mem.extends m m' ->
    init_args_out_of_bounds sg_ m_ ->
    init_args_out_of_bounds sg_ m'_ .
Proof.
  unfold init_args_out_of_bounds, loc_out_of_bounds.
  intros PUSH SPV sg_ m m' sg ll lm H0 H1 H2 H3 of ty H5 o0 H6.
  intro ABSURD.
  eapply push_frame_perm_diff_block in ABSURD; eauto.
  { eapply H3; eauto. }
  eapply push_frame_fresh_block in PUSH. congruence.
Qed.

Lemma match_stacks_size_args:
  forall ll lm sg sg_
    (MS: match_stacks ll lm sg sg_),
    4 * size_arguments sg <= Ptrofs.max_unsigned.
Proof.
  inversion 1; auto.
Qed.

(* (* [args_in_bounds] states that the locations of arguments in [l] are freeable *)
(* in [m]. This is instantiated with the locations of the arguments of the *)
(* outermost caller ([main] in the whole-program setting). In practice, the memory *)
(* [m] is that of the Mach memory state. *) *)

(* Definition args_in_bounds sp l m := *)
(*   exists m_, free_extcall_args sp m l = Some m_. *)

(* Definition init_args_in_bounds sg := *)
(*   args_in_bounds init_sp (regs_of_rpairs (loc_arguments sg)). *)

(* Lemma init_args_in_bounds_perm sg m m': *)
(*   (forall b o_, init_sp = Vptr b o_ -> forall o k p, Mem.perm m b o k p -> Mem.perm m' b o k p) -> *)
(*   init_args_in_bounds sg m -> *)
(*   init_args_in_bounds sg m'. *)
(* Proof. *)
(*   unfold init_args_in_bounds, args_in_bounds. *)
(*   generalize init_sp. *)
(*   intros sp H H0. *)
(*   destruct H0 as (m_ & H0). *)
(*   revert m m' H m_ H0. *)
(*   induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto. *)
(*   intros m m' H m_. *)
(*   unfold free_extcall_arg. *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   destruct sp; try discriminate. *)
(*   set (o := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (fe_ofs_arg + 4 * pos)))). *)
(*   destruct ( *)
(*       Mem.free m b o (o + size_chunk (chunk_of_type ty)) *)
(*     ) eqn:FREE; try discriminate. *)
(*   intros H0. *)
(*   generalize FREE. intro FREE1. *)
(*   apply Mem.free_range_perm in FREE1. *)
(*   unfold Mem.range_perm in FREE1. *)
(*   generalize (fun ofs => H _ _ (eq_refl _) _ _ _ (FREE1 ofs J)). *)
(*   clear FREE1. intro FREE2. *)
(*   apply Mem.range_perm_free in FREE2. *)
(*   destruct FREE2 as (m2 & FREE2). *)
(*   rewrite FREE2. *)
(*   eapply IHl; try eassumption. *)
(*   inversion 1; subst b0 o_. *)
(*   intros o0 k p. *)
(*   erewrite Mem.perm_free by eassumption. *)
(*   intros H2. *)
(*   erewrite Mem.perm_free by eassumption. *)
(*   specialize (H _ _ (eq_refl _) o0 k p). *)
(*   tauto. *)
(* Qed. *)

(* Lemma init_args_in_bounds_store sg chunk m b o v m': *)
(*   Mem.store chunk m b o v = Some m' -> *)
(*   init_args_in_bounds sg m -> *)
(*   init_args_in_bounds sg m'. *)
(* Proof. *)
(*   intro K. *)
(*   apply init_args_in_bounds_perm. *)
(*   intros b0 o_ H o0 k p. *)
(*   eauto using Mem.perm_store_1. *)
(* Qed. *)

(* Lemma init_args_in_bounds_storev sg chunk m bo v m': *)
(*   Mem.storev chunk m bo v = Some m' -> *)
(*   init_args_in_bounds sg m -> *)
(*   init_args_in_bounds sg m'. *)
(* Proof. *)
(*   destruct bo; try discriminate. *)
(*   apply init_args_in_bounds_store. *)
(* Qed. *)


(* Lemma init_args_in_bounds_free m b lo hi m' sg: *)
(*   Mem.free m b lo hi = Some m' -> *)
(*   (forall b' o', init_sp = Vptr b' o' -> b' <> b) -> *)
(*   init_args_in_bounds sg m -> *)
(*   init_args_in_bounds sg m'. *)
(* Proof. *)
(*   intros H H0. *)
(*   apply init_args_in_bounds_perm. *)
(*   intros b0 o_ H1 o k p. *)
(*   specialize (H0 _ _ H1). *)
(*   clear H1. *)
(*   intros H1. *)
(*   erewrite Mem.perm_free by eassumption. *)
(*   tauto. *)
(* Qed. *)

(* Lemma init_args_in_bounds_alloc m lo hi b m' sg: *)
(*   Mem.alloc m lo hi = (m', b) -> *)
(*   init_args_in_bounds sg m -> *)
(*   init_args_in_bounds sg m'. *)
(* Proof. *)
(*   intros H. *)
(*   apply init_args_in_bounds_perm. *)
(*   intros b0 o_ H0 o k p. *)
(*   eapply Mem.perm_alloc_1; eauto. *)
(* Qed. *)

(* Lemma free_extcall_args_change_mem sp: *)
(*   forall (l : list loc) (m' m'_ : mem) *)
(*     (PERM: *)
(*        forall b o (EQsp: sp = Vptr b o) *)
(*          of ty (IN: In (S Outgoing of ty) l) *)
(*          o' *)
(*          (RNG: Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (fe_ofs_arg + 4 * of))) <= o' < *)
(*                Ptrofs.unsigned (Ptrofs.add o (Ptrofs.repr (fe_ofs_arg + 4 * of))) + *)
(*                size_chunk (chunk_of_type ty)) *)
(*          k p (PERM: Mem.perm m' b o' k p), Mem.perm m'_ b o' k p) *)
(*     m_ (FEA: free_extcall_args sp m' l = Some m_), *)
(*   exists m_0, free_extcall_args sp m'_ l = Some m_0. *)
(* Proof. *)
(*   induction l. simpl; eauto. *)
(*   intros until m_. *)
(*   simpl. *)
(*   unfold free_extcall_arg. *)
(*   simpl In in PERM. *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   destruct sp; try discriminate. *)
(*   set (ofs := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (fe_ofs_arg + 4 * pos)))). *)
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
(*   intros b0 o EQ of ty0 IN o' RNG k p PERM'. *)
(*   inv EQ. *)
(*   erewrite Mem.perm_free by eassumption. *)
(*   erewrite Mem.perm_free in PERM' by eassumption. *)
(*   destruct PERM'; split; eauto. *)
(* Qed. *)


(* Lemma init_args_in_bounds_external_call sg_ ef args m_ t vl m'1 : *)
(*   forall (EC: external_call ef ge args m_ t vl m'1) *)
(*     m m' *)
(*     (MPG: meminj_preserves_globals ge j) *)
(*     (K: forall b o, init_sp = Vptr b o -> b = Some (b, 0)) *)
(*     (IMAGE: forall b o, init_sp = Vptr b o -> forall b' delta, b' = Some (b, delta) -> b' = b /\ delta = 0) *)
(*     (MEXT: Mem.extends m_ m) *)
(*     (MINJ: Mem.lessdef m m') *)
(*     (IAOOB: init_args_out_of_bounds sg_ m_) *)
(*     ll lm sg *)
(*     (MS: match_stacks ll lm sg sg_) *)
(*     args' *)
(*     (INJARGS: Val.lessdef_list args args') *)
(*     vl' m'2 *)
(*     (EC2: external_call ef ge args' m' t vl' m'2) *)
(*     (IAIB: init_args_in_bounds sg_ m'), *)
(*     init_args_in_bounds sg_ m'2. *)
(* Proof. *)
(*   intros EC m m' MPG K IMAGE MEXT MINJ IAOOB ll lm sg MS args' INJARGS vl' m'2 EC2 IAIB. *)
(*   generalize (Mem.extends_lessdef_compose _ _ _ _ MEXT MINJ). *)
(*   intros MINJ'. *)
(*   revert EC2. *)
(*   exploit external_call_mem_lessdef ; eauto. *)
(*   destruct 1 as (_ & res'_ & m'2_ & EC2 & _ & _ & _ & UNCHANGED & _ & _). *)
(*   intros EC2'. *)
(*   exploit external_call_determ . *)
(*   eexact EC2. *)
(*   eexact EC2'. *)
(*   destruct 1 as (_ & INJ). *)
(*   specialize (INJ (eq_refl _)). *)
(*   destruct INJ; subst. *)
(*   destruct IAIB. *)
(*   eapply free_extcall_args_change_mem. 2: eauto. *)
(*   intros b o EQsp of ty IN o' RNG k p PERM. *)
(*   specialize (K _ _ EQsp). *)
(*   eapply Mem.perm_unchanged_on; eauto. *)
(*   unfold init_args_out_of_bounds in IAOOB. *)
(*   unfold loc_out_of_reach. *)
(*   intros b0 delta JB. *)
(*   generalize JB. intro JB'. *)
(*   eapply IMAGE in JB'. *)
(*   destruct JB'; subst. *)
(*   rewrite Zminus_0_r. *)
(*   eapply IAOOB; eauto. eauto. *)
(* Qed. *)

Opaque Z.mul.


(* Lemma args_always_in_bounds m' sg_ ll lm sg  : *)
(*   forall (MS: match_stacks ll lm sg sg_) *)
(*     (IAIB: init_args_in_bounds sg_ m') *)
(*     (SEP: m' |= stack_contents ll lm), *)
(*     args_in_bounds (parent_sp init_sp lm) (regs_of_rpairs (loc_arguments sg)) m'. *)
(* Proof. *)
(*   inversion 1; subst; auto. *)
(*   simpl. intros _ SEP. *)
(*   clear - external_calls_prf ARGS SEP TRF BND. *)
(*   cut (forall l2 l1, *)
(*           regs_of_rpairs (loc_arguments sg) = l1 ++ l2 -> *)
(*           forall m', *)
(*             (forall o ty, *)
(*                 In (S Outgoing o ty) l2 -> *)
(*                 let of := Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (fe_ofs_arg + 4 * o))) *)
(*                 in *)
(*                 forall ofs, *)
(*                   of <= ofs < of + size_chunk (chunk_of_type ty) -> *)
(*                   0 <= ofs < fe_size (make_env (function_bounds f)) -> *)
(*                   ofs < fe_stack_data (make_env (function_bounds f)) \/ *)
(*                   fe_stack_data (make_env (function_bounds f)) + *)
(*                   bound_stack_data (function_bounds f) <= ofs -> *)
(*                   Mem.perm m' sp' ofs Cur Freeable) -> *)
(*             args_in_bounds (Vptr sp' Ptrofs.zero) l2 m'). *)
(*   { *)
(*     intros H. *)
(*     apply (H _ nil (eq_refl _)). *)
(*     intros. *)
(*     apply sep_proj1 in SEP. *)
(*     destruct SEP. *)
(*     destruct H3. *)
(*     apply sep_proj1 in H5. *)
(*     destruct H5. destruct H6. *)
(*     apply H7. omega. *)
(*     apply sep_proj2 in H5. destruct H5. destruct H6. apply H7. omega. *)
(*   } *)
(*   intro l2. *)
(*   unfold args_in_bounds. *)
(*   Opaque fe_stack_data fe_size. *)
(*   induction l2; simpl; eauto. *)
(*   intros l1 H m'0 H0. *)

(*   simpl In in H0. *)
(*   assert (regs_of_rpairs (loc_arguments sg) = (l1 ++ a :: nil) ++ l2) as EQ. *)
(*   { *)
(*     rewrite H. *)
(*     rewrite app_ass. *)
(*     reflexivity. *)
(*   } *)
(*   specialize (IHl2 _ EQ). *)
(*   clear EQ. *)
(*   unfold free_extcall_arg. *)
(*   destruct a; eauto. *)
(*   destruct sl; eauto. *)
(*   assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN. *)
(*   { *)
(*     rewrite H. *)
(*     apply in_or_app. *)
(*     simpl. *)
(*     auto. *)
(*   } *)
(*   generalize (ARGS _ _ IN). intro ARGS_. *)
(*   generalize (H0 _ _ (or_introl _ (eq_refl _))). *)
(*   set (of := Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr (fe_ofs_arg + 4 * pos)))). *)
(*   intros H1. *)
(*   generalize (eq_refl of). *)
(*   unfold of at 2. *)
(*   revert H1. *)
(*   generalize of. clear of. intro of. *)
(*   intros H1 H2. *)
(*   rewrite Ptrofs.add_commut in H2. *)
(*   rewrite Ptrofs.add_zero in H2. *)
(*   assert (EQ: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * pos)) = fe_ofs_arg + 4 * pos). *)
(*   { *)
(*     apply Ptrofs.unsigned_repr. *)
(*     generalize (loc_arguments_bounded _ _ _ IN); eauto. *)
(*     simpl. intro. *)
(*     exploit loc_arguments_acceptable_2; eauto. intros [A B]. *)
(*     split. omega. *)
(*     transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega. *)
(*     generalize (typesize_pos ty); omega. auto. *)
(*   } *)

(*   rewrite EQ in H2. *)
(*   exploit (Mem.range_perm_free' m'0 sp' of (of + size_chunk (chunk_of_type ty))). *)
(*   { *)
(*     red. *)
(*     intros ofs H3. *)
(*     eapply H1; eauto; try omega. *)
(*     - subst. rewrite Ptrofs.add_zero_l in *. *)
(*       simpl in EQ. rewrite EQ in *. simpl in H3. omega. *)
(*     - red in ARGS_. *)
(*       generalize (frame_env_separated' (function_bounds f)). *)
(*       intros. *)
(*       exploit loc_arguments_acceptable_2; eauto. intros [A B]. *)
(*       split. simpl in H2. omega. simpl in H2. *)
(*       eapply Zlt_le_trans. apply H3. *)
(*       etransitivity. *)
(*       2: apply frame_env_range. rewrite size_type_chunk, typesize_typesize. *)
(*       etransitivity. *)
(*       subst. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega. *)
(*       apply ARGS_. *)
(*       etransitivity. *)
(*       eapply align_le. *)
(*       2: etransitivity. 2: apply H4. destruct (Archi.ptr64); omega. *)
(*       generalize (bound_stack_data_pos (function_bounds f)); omega. *)
(*     - left. *)
(*       eapply Zlt_le_trans. apply H3. *)
(*       rewrite size_type_chunk, typesize_typesize. *)
(*       etransitivity. *)
(*       subst. simpl. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega. *)
(*       apply ARGS_. *)
(*       generalize (frame_env_separated' (function_bounds f)). *)
(*       intros. *)
(*       etransitivity. eapply align_le. *)
(*       2: etransitivity. 2: apply H4. destruct (Archi.ptr64); omega. *)
(*       omega. *)
(*   } *)
(*   destruct 1 as (m2 & Hm2). *)
(*   rewrite Hm2. *)
(*   eapply IHl2; clear IHl2. *)
(*   intros o ty0 H3 ofs H4 H5 H6. *)
(*   eapply Mem.perm_free_1; eauto. *)
(*   clear H0. *)
(*   right. *)
(*   generalize (loc_arguments_norepet sg). *)
(*   rewrite H. *)
(*   intros H0. *)
(*   apply Loc.norepet_app_inv in H0. *)
(*   destruct H0 as (_ & H0 & _). *)
(*   inversion H0; subst. *)
(*   rewrite Loc.notin_iff in H9. *)
(*   specialize (H9 _ H3). *)
(*   simpl in H9. *)
(*   destruct H9; try congruence. *)
(*   rewrite size_type_chunk in *. *)
(*   rewrite typesize_typesize in *. *)
(*   rewrite Ptrofs.add_commut in H4. *)
(*   rewrite Ptrofs.add_zero in H4. *)
(*   clear IN. *)
(*   assert (In (S Outgoing o ty0) (regs_of_rpairs (loc_arguments sg))) as IN. *)
(*   { *)
(*     rewrite H. *)
(*     apply in_or_app. *)
(*     simpl; auto. *)
(*   } *)
(*   generalize (ARGS _ _ IN). intro ARGS_IN. *)

(*   simpl. *)
(*   assert (EQ4: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * o)) = fe_ofs_arg + 4 * o). *)
(*   { *)
(*     apply Ptrofs.unsigned_repr. *)
(*     generalize (loc_arguments_bounded _ _ _ IN); eauto. *)
(*     simpl. intro. *)
(*     exploit loc_arguments_acceptable_2; eauto. intros [A B]. *)
(*     split. omega. *)
(*     transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega. *)
(*     generalize (typesize_pos ty); omega. auto. *)
(*   } *)
(*   rewrite EQ4 in H4. simpl in H4. omega. *)
(* Qed. *)

(* Lemma tailcall_possible_in_bounds: *)
(*   forall sg, *)
(*     tailcall_possible sg -> *)
(*     forall m, *)
(*       init_args_in_bounds sg m. *)
(* Proof. *)
(*   intros sg H m. *)
(*   unfold init_args_in_bounds, args_in_bounds. *)
(*   red in H. *)
(*   revert H. *)
(*   induction (regs_of_rpairs (loc_arguments sg)); simpl; eauto. *)
(*   intros H. *)
(*   unfold free_extcall_arg. *)
(*   destruct a. *)
(*   { *)
(*     eapply IHl; eauto. *)
(*     intros l0 H1. *)
(*     eapply H; eauto. *)
(*   } *)
(*   destruct sl; try (eapply IHl; eauto; intros; eapply H; eauto). *)
(*   exfalso. specialize (H _ (or_introl _ (eq_refl _))). *)
(*   contradiction. *)
(* Qed. *)

Lemma match_stacks_change_sig:
  forall sg1 cs cs' sg isg,
  match_stacks cs cs' sg isg ->
  tailcall_possible sg1 ->
  4 * size_arguments sg1 <= Ptrofs.max_unsigned ->
  match_stacks cs cs' sg1
               match cs with
                   nil => sg1
                 | _ => isg
               end.
Proof.
  induction 1; intros.
  econstructor; eauto.
  econstructor; eauto. intros. elim (H0 _ H2).
Qed.

(** Typing properties of [match_stacks]. *)

(** [CompCertX:test-compcert-protect-stack-arg] In whole-program settings, [init_sp = Vzero], so the following hypotheses are trivially true. 
    In non-whole-program settings, the following two hypotheses are provided by the caller's assembly semantics, which maintains the well-typedness of the assembly register set as an invariant. *)
(* Hypothesis init_sp_int: Val.has_type init_sp Tptr. *)
Hypothesis init_ra_int: Val.has_type init_ra Tptr.

(* Lemma match_stacks_type_sp: *)
(*   forall cs cs' sg isg, *)
(*   match_stacks cs cs' sg isg -> *)
(*   Val.has_type (parent_sp init_sp cs') Tptr. *)
(* Proof. *)
(*   induction 1; unfold parent_sp. auto. apply Val.Vptr_has_type. *)
(* Qed.  *)

Lemma match_stacks_type_retaddr:
  forall cs cs' sg isg,
  match_stacks cs cs' sg isg ->
  Val.has_type (parent_ra init_ra cs') Tptr.
Proof.
  induction 1; unfold parent_ra. auto. auto. 
Qed.

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
  forall ls rs ros f,
  agree_regs ls rs ->
  Linear.find_function ge ros ls = Some f ->
  exists bf, exists tf,
     find_function_ptr tge ros rs = Some bf
  /\ Genv.find_funct_ptr tge bf = Some tf
  /\ transf_fundef f = OK tf.
Proof.
  intros until f; intros AG FF.
  destruct ros; simpl in FF.
- exploit Genv.find_funct_inv; eauto. intros [b EQ]. rewrite EQ in FF.
  rewrite Genv.find_funct_find_funct_ptr in FF.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  generalize (AG m). rewrite EQ. intro INJ. inv INJ.
  rewrite Ptrofs.eq_true. auto.
- destruct (Genv.find_symbol ge i) as [b|] eqn:?; try discriminate.
  exploit function_ptr_translated; eauto. intros [tf [A B]].
  exists b; exists tf; split; auto. simpl.
  rewrite symbols_preserved. auto.
Qed.

(** Preservation of the arguments to an external call. *)


(* [init_args_mach] states that the locations of the arguments of function with
signature [sg] can be retrieved in [m'] (a Mach memory state) and agree with the
locset [init_ls].*)

Definition init_args_mach sg m' :=
  forall sl of ty,
    List.In (Locations.S sl of ty) (regs_of_rpairs (loc_arguments sg)) ->
    forall rs,
    exists v,
      extcall_arg rs m' init_sp (S sl of ty) v /\
      Val.lessdef (init_ls (S sl of ty)) v.

(** General case *)

Section EXTERNAL_ARGUMENTS.

Variable cs: list Linear.stackframe.
Variable cs': list stackframe.
Variable sg: signature.
Variables bound bound': block.
Variable isg: signature.
Hypothesis MS: match_stacks cs cs' sg isg.
Variable ls: locset.
Variable rs: regset.
Hypothesis AGR: agree_regs ls rs.
Hypothesis AGCS: agree_callee_save ls (parent_locset init_ls cs).
Variable m': mem.
Hypothesis SEP: m' |= stack_contents cs cs'.

Hypothesis init_args: init_args_mach isg m'.

Lemma transl_external_argument:
  forall l,
  In l (regs_of_rpairs (loc_arguments sg)) ->
  exists v, extcall_arg rs m' (parent_sp init_sp cs') l v /\ Val.lessdef (ls l) v.
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
  + Opaque frame_contents. simpl in SEP. simpl.
    assert (slot_valid f Outgoing pos ty = true).
    { destruct H0. unfold slot_valid, proj_sumbool.
      rewrite zle_true by omega. rewrite pred_dec_true by auto. reflexivity. }
    assert (slot_within_bounds (function_bounds f) Outgoing pos ty) by eauto.
    exploit frame_get_outgoing; eauto. apply SEP. intros (v & A & B).
    exists v; split.
    constructor. exact A.
    red in AGCS. rewrite AGCS; auto.
Qed.

Lemma transl_external_argument_2:
  forall p,
  In p (loc_arguments sg) ->
  exists v, extcall_arg_pair rs m' (parent_sp init_sp cs') p v /\ Val.lessdef (Locmap.getpair p ls) v.
Proof.
  intros. destruct p as [l | l1 l2].
- destruct (transl_external_argument l) as (v & A & B). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists v; split; auto. constructor; auto. 
- destruct (transl_external_argument l1) as (v1 & A1 & B1). eapply in_regs_of_rpairs; eauto; simpl; auto.
  destruct (transl_external_argument l2) as (v2 & A2 & B2). eapply in_regs_of_rpairs; eauto; simpl; auto.
  exists (Val.longofwords v1 v2); split. 
  constructor; auto.
  apply Val.longofwords_lessdef; auto.
Qed.

Lemma transl_external_arguments_rec:
  forall locs,
  incl locs (loc_arguments sg) ->
  exists vl,
      list_forall2 (extcall_arg_pair rs m' (parent_sp init_sp cs')) locs vl
   /\ Val.lessdef_list (map (fun p => Locmap.getpair p ls) locs) vl.
Proof.
  induction locs; simpl; intros.
  exists (@nil val); split. constructor. constructor.
  exploit transl_external_argument_2; eauto with coqlib. intros [v [A B]].
  exploit IHlocs; eauto with coqlib. intros [vl [C D]].
  exists (v :: vl); split; constructor; auto.
Qed.

Lemma transl_external_arguments:
  exists vl,
      extcall_arguments rs m' (parent_sp init_sp cs') sg vl
   /\ Val.lessdef_list (map (fun p => Locmap.getpair p ls) (loc_arguments sg)) vl.
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
Variables m m': mem.
Variables ls ls0: locset.
Variable rs: regset. 
Variables sp : Mem.stackblock.
Variables parent: Mem.stackblock.
Variable retaddr: val.
Hypothesis AGR: agree_regs ls rs.
Hypothesis SEP: m' |= frame_contents f sp ls ls0 parent retaddr.
Hypothesis EXT: Mem.extends m m'.

Lemma transl_builtin_arg_correct:
  forall vsp a v,
  eval_builtin_arg ge ls vsp m a v ->
  (forall l, In l (params_of_builtin_arg a) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_arg a) -> slot_within_bounds b sl ofs ty) ->
  exists v',
     eval_builtin_arg ge rs vsp m' (transl_builtin_arg fe a) v'
  /\ Val.lessdef v v'.
Proof.
  assert (SYMB: forall id ofs, Val.lessdef (Senv.symbol_address ge id ofs) (Senv.symbol_address ge id ofs)) by auto.
Local Opaque fe.
induction 1; simpl; intros VALID BOUNDS.
- assert (loc_valid f x = true) by auto.
  destruct x as [r | [] ofs ty]; try discriminate.
  + exists (rs r); auto with barg.
  + exploit frame_get_local; eauto. rewrite sep_comm, sep_pure. split. exact I. apply SEP. intros (v & A & B). 
    exists v; split; auto. constructor; auto.
    admit.                      (* pointer to stack *)
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_extends. eauto. eauto. auto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto. 
- econstructor; split; eauto with barg.
- exploit Mem.loadv_extends. eauto. eauto. auto.
  intros (v' & A & B). exists v'; split; auto. constructor; auto. 
- econstructor; split; eauto with barg. 
- destruct IHeval_builtin_arg1 as (v1 & A1 & B1); auto using in_or_app.
  destruct IHeval_builtin_arg2 as (v2 & A2 & B2); auto using in_or_app.
  exists (Val.longofwords v1 v2); split; auto with barg.
  apply Val.longofwords_lessdef; auto.
Admitted.

Lemma transl_builtin_args_correct:
  forall vsp al vl,
  eval_builtin_args ge ls vsp m al vl ->
  (forall l, In l (params_of_builtin_args al) -> loc_valid f l = true) ->
  (forall sl ofs ty, In (S sl ofs ty) (params_of_builtin_args al) -> slot_within_bounds b sl ofs ty) ->
  exists vl',
     eval_builtin_args ge rs vsp m' (List.map (transl_builtin_arg fe) al) vl'
  /\ Val.lessdef_list vl vl'.
Proof.
  induction 1; simpl; intros VALID BOUNDS.
- exists (@nil val); split; constructor.
- exploit transl_builtin_arg_correct; eauto using in_or_app. intros (v1' & A & B).
  exploit IHlist_forall2; eauto using in_or_app. intros (vl' & C & D).
  exists (v1'::vl'); split; constructor; auto.
Qed.

End BUILTIN_ARGUMENTS.

(** [CompCertX:test-compcert-protect-stack-arg] We have to prove that
the memory lessdefion introduced by the compilation pass is independent
of the initial memory i.e. it does not lessdef new blocks into blocks
already existing in the initial memory. This is stronger than
[meminj_preserves_globals], which only preserves blocks associated to
the global environment. *)

Section WITHMEMINIT.

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
-- the lessdefion from the Linear memory state into the Mach memory state
-- the preservation of the global environment.
- Agreement between, on the Linear side, the location sets [ls]
  and [parent_locset s] of the current function and its caller,
  and on the Mach side the register set [rs].
- The Linear code [c] is a suffix of the code of the
  function [f] being executed.
- Well-typedness of [f].
*)

Require Linear2.

Definition state_mem (s: Linear.state) :=
  match s with
  | Linear.State stack f sp c rs m => m
  | Linear.Callstate stack f rs m => m
  | Linear.Returnstate stack rs m => m
  end.


Opaque Z.mul.

Axiom get_stack_valid_access:
  forall (m : mem) ty sp (ofs : Z) (v : val),
    Mem.get_stack sp m ty ofs = Some v ->
    Mem.valid_access m (chunk_of_type ty) (StackBlock sp) ofs Readable.

Program Definition minit_args_mach sg_ : massert :=
  {|
    m_pred := init_args_mach sg_;
    m_footprint := fun b o =>
                     b = StackBlock init_sp /\
                     exists sl ofs ty,
                       In (S sl ofs ty) (regs_of_rpairs (loc_arguments sg_)) /\
                       let lo := Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * ofs)) in
                       lo <= o < lo + size_chunk (chunk_of_type ty);
    m_invar_weak := false
  |}.
Next Obligation.
  red; intros.
  exploit H. eauto. intros (v & EA & INJ).
  inv EA.
  eexists; split; eauto. econstructor; eauto.
  unfold load_stack in *.
  eapply get_stack_unchanged_on; eauto.

  simpl; intros; split; auto.
  exists Outgoing, of, ty; split; auto.
  Unshelve. eauto.
Defined.
Next Obligation.
  exploit H. eauto.
  intros (v & EA & INJ). inv EA.
  unfold load_stack in *.
  edestruct get_stack_valid_access as [RP AL]; eauto.
  eapply Mem.perm_valid_block. eapply RP.
  split; eauto.
  Unshelve. constructor.
Defined.

Definition in_segment (s: segment) (o: Z) :=
  seg_ofs s <= o < seg_ofs s + seg_size s.

Fixpoint bounds_stack m ll (* hi *) :=
  match ll with
  | Linear.Stackframe f sp ls c :: ll =>
    (forall ofs p,
        Mem.perm m (StackBlock sp) ofs Max p ->
        let fr := F_frame_layout f in
        in_segment (frame_callee_saves fr) ofs \/ in_segment (frame_locals fr) ofs \/ in_segment (frame_outgoings fr) ofs ->
        perm_order Nonempty p)
    /\ bounds_stack m ll
  | _ => True
  end.

Lemma bounds_stack_store:
  forall s m (BS: bounds_stack m s)
    chunk b o v m'
    (STORE: Mem.store chunk m b o v = Some m'),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; auto. destruct a; auto.
  split; auto.
  intros. destruct BS. eapply H1; eauto with mem.
  eapply IHs; eauto. apply BS.
Qed.

Lemma bounds_stack_free:
  forall s m (* b *) (BS: bounds_stack m s)
    b lo hi m'
    (FREE: Mem.free m b lo hi = Some m'),
    bounds_stack m' s.
Proof.
  Opaque bound_local bound_outgoing fe_ofs_callee_save fe_ofs_local.
  induction s; simpl; intros; auto. destruct a; auto.
  destruct BS.
  repeat (refine (conj _ _)).
  - intros. eapply H. rewrite Mem.perm_free in H1. 2: eauto. 2: eauto. destruct H1; eauto.
  - eapply IHs; eauto.
Qed.

Lemma bounds_stack_pop_frame:
  forall s m (* b *) (BS: bounds_stack m s)
    m'
    (FREE: Mem.pop_frame m = Some m'),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; auto. destruct a; auto.
  destruct BS.
  repeat (refine (conj _ _)).
  - intros. eapply H. eapply pop_frame_perm in H1. 2: eauto. 2: eauto. auto. 
  - eapply IHs; eauto.
Qed.

Fixpoint valid_stack m s :=
  match s with
  | Linear.Stackframe f sp ls c :: cs =>
    Mem.valid_block m (StackBlock sp) /\ valid_stack m cs
  | _ => True
  end.

Lemma bounds_stack_perm:
  forall s m (BS: bounds_stack m s)
    (VS: valid_stack m s)
    m'
    (PERM: forall b ofs p, Mem.valid_block m b -> Mem.perm m' b ofs Max p -> Mem.perm m b ofs Max p),
    bounds_stack m' s.
Proof.
  induction s; simpl; intros; eauto.
  destruct a; auto. destruct BS.
  split. intros; eauto. eapply H. eapply PERM; eauto. destruct VS; auto.
  auto. eapply IHs; auto. apply H0. destruct VS; auto.
Qed.

Variables init_m : mem.

Inductive match_states: Linear2.state -> Mach.state -> Prop :=
| match_states_intro:
    forall sg_ cs f sp c ls m cs' fb rs m' tf
        (STACKS: match_stacks cs cs' f.(Linear.fn_sig) sg_)
        (TRANSL: transf_function f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some (Internal tf))
        (AGREGS: agree_regs ls rs)
        (AGLOCS: agree_locs f ls (parent_locset init_ls cs))
        (* (INJSP: sp = Some(sp', fe_stack_data (make_env (function_bounds f)))) *)
        (* (INJUNIQUE: forall b delta, b = Some (sp', delta) -> b = sp) *)
        (* (INJ_INIT_SP: block_prop (fun b => b = Some (b,0)) init_sp) *)
        (* (HAMOA: has_at_most_one_antecedent init_sp) *)
        (ISP'VALID: Mem.valid_block m' (StackBlock init_sp))
        (* (INCR_init: lessdef_incr (Mem.flat_inj (Mem.nextblock init_m)) j) *)
        (* (INCR_sep: lessdef_separated (Mem.flat_inj (Mem.nextblock init_m)) init_m init_m) *)
        (INIT_VB: forall b, Mem.valid_block init_m b -> Mem.valid_block m b)
        (INIT_VB': forall b, Mem.valid_block init_m b -> Mem.valid_block m' b)
        (TAIL: is_tail c (Linear.fn_code f))
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.State cs f sp c ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (* (Hsome_init_args: init_args_in_bounds sg_ m') *)
        (SP_NOT_INIT: init_sp <> sp)
        (SEP: m' |= frame_contents f sp ls (parent_locset init_ls cs) (parent_sp init_sp cs') (parent_ra init_ra cs')
                 ** stack_contents cs cs'
                 ** (minit_args_mach sg_))
        (EXT: Mem.extends m m')
        (* (PERM_stack: forall (ofs : Z) (p : permission), Mem.perm m (StackBlock sp) ofs Max p -> 0 <= ofs < Linear.fn_stacksize f) *)
        (PERM_stack: forall ofs p,
            Mem.perm m (StackBlock sp) ofs Max p ->
            let fr := F_frame_layout f in
            in_segment (frame_callee_saves fr) ofs \/ in_segment (frame_locals fr) ofs \/ in_segment (frame_outgoings fr) ofs ->
            perm_order Nonempty p)
        (BS: bounds_stack m cs),
      match_states s2_
                   (Mach.State cs' fb sp (transl_code (make_env (function_bounds f)) c) rs m')
  | match_states_call:

      forall sg_ cs f ls m cs' fb rs m' tf
        (STACKS: match_stacks cs cs' (Linear.funsig f) sg_)
        (TRANSL: transf_fundef f = OK tf)
        (FIND: Genv.find_funct_ptr tge fb = Some tf)
        (AGREGS: agree_regs ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        (* (INCR_init: lessdef_incr (Mem.flat_inj (Mem.nextblock init_m)) j) *)
        (* (INCR_sep: lessdef_separated (Mem.flat_inj (Mem.nextblock init_m)) init_m init_m) *)
        (INIT_VB: forall b, Mem.valid_block init_m b -> Mem.valid_block m b)
        (INIT_VB': forall b, Mem.valid_block init_m b -> Mem.valid_block m' b)
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Callstate cs f ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (* (Hsome_init_args: init_args_in_bounds sg_ m') *)
        (* (INJ_INIT_SP: block_prop (fun b => b = Some (b,0)) init_sp) *)
        (* (HAMOA: has_at_most_one_antecedent init_sp) *)
        (ISP'VALID: Mem.valid_block m' (StackBlock init_sp))
        (SEP: m' |= stack_contents cs cs' ** minit_args_mach sg_)
        (EXT: Mem.extends m m')
        (BS: bounds_stack m cs),
      match_states s2_ (Mach.Callstate cs' fb rs m')
  | match_states_return:
      forall sg_ cs ls m cs' rs m' sg
        (STACKS: match_stacks cs cs' sg sg_)
        (AGREGS: agree_regs ls rs)
        (AGLOCS: agree_callee_save ls (parent_locset init_ls cs))
        (* (INCR_init: lessdef_incr (Mem.flat_inj (Mem.nextblock init_m)) j) *)
        (* (INCR_sep: lessdef_separated (Mem.flat_inj (Mem.nextblock init_m)) init_m init_m) *)
        (INIT_VB: forall b, Mem.valid_block init_m b -> Mem.valid_block m b)
        (INIT_VB': forall b, Mem.valid_block init_m b -> Mem.valid_block m' b)
        s2_
        (Hs2: Linear2.state_lower s2_ = Linear.Returnstate cs ls m)
        (Hno_init_args: init_args_out_of_bounds sg_ (state_mem (Linear2.state_higher s2_)))
        (Hinit_ls: Some (Linear2.state_init_ls s2_) = Some init_ls)
        (* (Hsome_init_args: init_args_in_bounds sg_ m') *)
        (* (INJ_INIT_SP: block_prop (fun b => b = Some (b,0)) init_sp) *)
        (* (HAMOA: has_at_most_one_antecedent init_sp) *)
        (ISP'VALID: Mem.valid_block m' (StackBlock init_sp))
        (SEP: m' |= stack_contents cs cs'
                 ** minit_args_mach sg_)
        (EXT: Mem.extends m m')
        (BS: bounds_stack m cs),
      match_states s2_ (Mach.Returnstate cs' rs m').

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

Lemma sep_rot:
  forall P Q R S,
    massert_eqv (P ** Q ** R ** S) (S ** P ** Q ** R).
Proof.
  intros.
  rewrite <- (sep_assoc  Q R), <- (sep_assoc P).
  rewrite (sep_comm _ S). auto.
Qed.

Lemma Ple_Plt:
  forall a b,
    (forall c, Plt c a -> Plt c b) ->
    Ple a b.
Proof.
  apply Events.Ple_Plt.
Qed.

Lemma eval_addressing_lessdef_strong:
  forall sp1 sp2 addr vl1 vl2 v1,
    Val.lessdef_list vl1 vl2 ->
    Val.lessdef sp1 sp2 ->
    eval_addressing ge addr vl1 = Some v1 ->
    exists v2, eval_addressing ge addr vl2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros.
  eapply eval_addressing_lessdef; eauto.
Qed.

Lemma reglist_lessdef rs1 rs2
      (LESSDEF: forall r, Val.lessdef (rs1 r) (rs2 r))
      l:
  Val.lessdef_list (reglist rs1 l) (reglist rs2 l).
Proof.
  induction l; simpl; auto.
Qed.

Lemma block_prop_impl (P Q: block -> Prop) v:
  (forall b, P b -> Q b) ->
  block_prop P v -> block_prop Q v.
Proof.
  destruct v; auto. simpl. intuition.
Qed.

(* Lemma free_extcall_args_lessdef_right m m' sg_ ll lm sg m_ m'_ : *)
(*   forall (MS: match_stacks ll lm sg sg_) *)
(*     (IAOOB: init_args_out_of_bounds sg_ m_) *)
(*     (MEXT: Mem.extends m_ m) *)
(*     (MINJ: Mem.lessdef m m') *)
(*     (FEA: free_extcall_args (parent_sp init_sp lm) m' (regs_of_rpairs (loc_arguments sg)) = Some m'_) *)
(*     (INJ_FLAT: block_prop (fun b => b = Some (b, 0)) init_sp) *)
(*     (INJ_UNIQUE: has_at_most_one_antecedent init_sp) *)
(*     (BS: bounds_stack m ll), *)
(*     Mem.lessdef m_ m'_. *)
(* Proof. *)
(*   intros MS IAOOB MEXT MINJ FEA INJ_FLAT INJ_UNIQUE BS. *)
(*   generalize (Mem.extends_lessdef_compose _ _ _ _ MEXT MINJ). *)
(*   revert FEA. *)
(*   cut (forall l2 l1, *)
(*           regs_of_rpairs(loc_arguments sg) = l1 ++ l2 -> *)
(*           free_extcall_args (parent_sp init_sp lm) m' l2 = Some m'_ -> *)
(*           Mem.lessdef m_ m' -> *)
(*           Mem.lessdef m_ m'_). *)
(*   { *)
(*     clear MEXT MINJ. *)
(*     intros HYP FEA MINJ. *)
(*     eapply HYP with (l1 := nil); eauto. *)
(*     reflexivity. *)
(*   } *)
(*   clear MINJ. *)
(*   intro l2. revert m' m'_; induction l2; simpl; intros m' m'_ l1 EQ FEA MINJ. congruence. *)
(*   generalize (IHl2 m' m'_ (l1 ++ a :: nil)). intro IHl2'. *)
(*   rewrite app_ass in IHl2'; simpl in IHl2'. *)
(*   specialize (IHl2' EQ). *)
(*   destruct a; simpl in *; auto. *)
(*   destruct sl; eauto. *)
(*   destruct (parent_sp init_sp lm) eqn:?; try discriminate. *)
(*   clear IHl2'. *)
(*   set (o := Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (4 * pos)))). *)
(*   fold o in FEA. *)
(*   destruct (Mem.free m' b o (o + size_chunk (chunk_of_type ty))) eqn:FREE; try discriminate. *)
(*   exploit Mem.free_right_lessdef; eauto. *)
(*   - intros b1 delta ofs k p JB PERM RNG. *)
(*     inv MS. *)
(*     + simpl in *.  subst. simpl in INJ_FLAT; red in INJ_UNIQUE. *)
(*       specialize (INJ_UNIQUE _ _ eq_refl _ _ _ _ INJ_FLAT JB). subst b1. *)
(*       assert (delta = 0) by congruence. subst delta. *)
(*       replace (ofs + 0) with ofs in * by omega. *)
(*       eapply IAOOB. eauto. *)
(*       rewrite EQ, in_app; simpl; eauto. *)
(*       unfold o in *; eauto. *)
(*       eapply Mem.perm_max. *)
(*       eapply Mem.perm_implies; eauto. *)
(*       constructor. *)
(*     + Opaque fe_stack_data. *)
(*       simpl in *. inv Heqv. *)
(*       specialize (INJ_UNIQUE0 _ _ JB). *)
(*       destruct INJ_UNIQUE0. *)
(*       subst. *)
(*       apply Mem.perm_max in PERM. *)
(*       assert (forall ofs p, *)
(*                  Mem.perm m_ b1 ofs Max p -> *)
(*                  0 <= ofs < Linear.fn_stacksize f) as BOUND. *)
(*       { *)
(*         intros ofss pp H3. *)
(*         eapply BS. *)
(*         eapply Mem.perm_extends; eauto. *)
(*       } *)
(*       specialize (BOUND _ _ PERM). *)
(*       rewrite INJ in JB; inv JB. *)
(*       revert RNG BOUND. *)
(*       rewrite size_type_chunk. *)
(*       generalize (bound_stack_data_stacksize f). *)
(*       unfold o in *. *)
(*       clear o. *)
(*       simpl. intros. *)
(*       generalize (frame_env_separated' (function_bounds f)). *)
(*       assert (In (S Outgoing pos ty) (regs_of_rpairs (loc_arguments sg))) as IN. *)
(*       { *)
(*         rewrite EQ, ! in_app; simpl; auto. *)
(*       } *)
(*       generalize (loc_arguments_bounded _ _ _ IN); eauto. *)
(*       intros. *)
(*       assert (EQ4: Ptrofs.unsigned (Ptrofs.repr (fe_ofs_arg + 4 * pos)) = fe_ofs_arg + 4 * pos). *)
(*       { *)
(*         apply Ptrofs.unsigned_repr. *)
(*         generalize (loc_arguments_bounded _ _ _ IN); eauto. *)
(*         simpl. intro. *)
(*         exploit loc_arguments_acceptable_2; eauto. intros [A B]. *)
(*         split. omega. *)
(*         transitivity (4 * size_arguments sg). apply Z.mul_le_mono_nonneg_l. omega. *)
(*         generalize (typesize_pos ty); omega. auto. *)
(*       } *)
(*       simpl in EQ4. rewrite Ptrofs.add_zero_l, EQ4 in *. *)
(*       cut (4 * pos + AST.typesize ty <= fe_stack_data (make_env (function_bounds f))). omega. *)
(*       rewrite typesize_typesize. *)
(*       etransitivity. *)
(*       subst. simpl. rewrite <- Z.mul_add_distr_l. apply Z.mul_le_mono_nonneg_l. omega. *)
(*       apply ARGS. eauto. *)
(*       etransitivity. *)
(*       2: apply H1. apply align_le. destruct Archi.ptr64; omega. *)
(*   - intros. *)
(*     eapply (IHl2 m0 m'_ (l1 ++ S Outgoing pos ty :: nil)). *)
(*     rewrite EQ , app_ass; simpl; auto. *)
(*     eauto. auto. *)
(* Qed. *)

(* Lemma free_extcall_args_external_call sg_ ef args m_ t vl m'_ : *)
(*   forall (EC: external_call ef ge args m_ t vl m'_) *)
(*     m m' *)
(*     (MEXT: Mem.extends m_ m) *)
(*     (MINJ: Mem.lessdef m m') *)
(*     (IAOOB: init_args_out_of_bounds sg_ m_) *)
(*     ll lm *)
(*     (MS: match_stacks ll lm (ef_sig ef) sg_) *)
(*     (SEP: m' |= stack_contents ll lm ** globalenv_lessdef ge j) *)
(*     args' *)
(*     (ARGSINJ: Val.lessdef_list args args') *)
(*     (IAIB: init_args_in_bounds sg_ m') *)
(*     (FLATINJ: block_prop (fun b : block => b = Some (b, 0)) init_sp) *)
(*     (INJUNIQUE: has_at_most_one_antecedent init_sp) *)
(*     (BS: bounds_stack m ll), *)
(*     exists m'_, free_extcall_args *)
(*              (parent_sp init_sp lm) *)
(*              m' *)
(*              (regs_of_rpairs (loc_arguments (ef_sig ef))) = Some m'_ /\ *)
(*            exists t2 res2 m2, *)
(*              external_call ef ge args' m'_ t2 res2 m2. *)
(* Proof. *)
(*   intros EC m m' MEXT MINJ IAOOB ll lm MS SEP args' ARGSINJ IAIB FLATINJ INJUNIQUE BS. *)
(*   exploit args_always_in_bounds; eauto. *)
(*   apply sep_proj1 in SEP; eauto. *)
(*   destruct 1. *)
(*   esplit. *)
(*   split; eauto. *)
(*   exploit free_extcall_args_lessdef_right; eauto. *)
(*   intros MINJ'. *)
(*   exploit external_call_mem_lessdef ; eauto. *)
(*   eapply globalenv_lessdef_preserves_globals. *)
(*   eapply sep_proj2 in SEP; eauto. *)
(*   destruct 1 as (? & ? & ? & ? & _). *)
(*   eauto. *)
(* Qed. *)

Lemma map_reg_lessdef rs1 rs2
      (LESSDEF: forall r: loc, Val.lessdef (rs1 r) (rs2 r))
      args:
  Val.lessdef_list (fun p => Locmap.getpair p rs1) ## args (fun p => Locmap.getpair p rs2) ## args.
Proof.
  induction args; simpl; auto.
  constructor; auto.
  destruct a; simpl; auto.
  apply Val.longofwords_lessdef; auto.
Qed.

Ltac constr_match_states :=
  econstructor;
  match goal with
    |- Linear2.state_lower _ = _ =>
    symmetry; eassumption
  | |- _ => idtac
  end.

Lemma intv_dec:
  forall a b c,
    { a <= b < c } + { b < a \/ b >= c }.
Proof.
  clear.
  intros.
  destruct (zle a b); destruct (zlt b c); try (right; omega); try (left; omega).
Qed.

Section EVAL_BUILTIN_ARG_LESSDEF.

  Variable A : Type.
  Variable ge' : Senv.t.
  Variables rs1 rs2 : A -> val.
  Hypothesis rs_lessdef: forall a, Val.lessdef (rs1 a) (rs2 a).
  Variables sp sp' : val.
  Hypothesis sp_lessdef: Val.lessdef sp sp'.
  Variable m m' : mem.
  Hypothesis m_ext: Mem.extends m m'.


  Lemma eval_builtin_arg_lessdef':
  forall arg v v'
    (EBA: eval_builtin_arg ge' rs1 sp m arg v)
    (EBA': eval_builtin_arg ge' rs2 sp' m' arg v'),
    Val.lessdef v v'.
  Proof.
    induction arg; intros; inv EBA; inv EBA'; subst; auto.
    - intros. exploit Mem.loadv_extends. eauto. apply H2.
      2: rewrite H3. simpl. apply Val.offset_ptr_lessdef; auto. intros (v2 & B & C). inv B. auto.
    - intros; apply Val.offset_ptr_lessdef; auto.
    - intros. exploit Mem.loadv_extends. eauto.  apply H3.
      2: rewrite H4. auto. intros (v2 & B & C). inv B. auto.
    - apply Val.longofwords_lessdef. eauto. eauto.
  Qed.

  Lemma eval_builtin_args_lessdef':
    forall args vl vl'
      (EBA: eval_builtin_args ge' rs1 sp m args vl)
      (EBA': eval_builtin_args ge' rs2 sp' m' args vl'),
      Val.lessdef_list vl vl'.
  Proof.
    induction args; simpl; intros. inv EBA; inv EBA'. constructor.
    inv EBA; inv EBA'. constructor; auto.
    eapply eval_builtin_arg_lessdef'; eauto.
  Qed.

End EVAL_BUILTIN_ARG_LESSDEF.

Lemma footprint_impl:
  forall P Q Q' b o,
    (forall b o, m_footprint Q b o -> m_footprint Q' b o) ->
    m_footprint (P ** Q) b o ->
    m_footprint (P ** Q') b o.
Proof.
  intros.
  destruct H0.
  left; auto.
  right; eauto.
Qed.

Lemma init_args_mach_unch:
  forall sg m m' P,
    Mem.unchanged_on P m m' ->
    (forall i, P (StackBlock init_sp) i) ->
    init_args_mach sg m ->
    init_args_mach sg m'.
Proof.
  red. intros sg m m' P UNCH NSP IAM sl of ty IN rs.
  exploit IAM; eauto. instantiate (1 := rs).
  intros (v & ea & inj); eexists; split; eauto.
  inv ea; constructor; auto.
  unfold load_stack in *. simpl in *.
  
  erewrite get_stack_unchanged_on; eauto.
Qed.

Hypothesis frame_layout_correct:
  forall f tf fb,
    transf_function f = OK tf ->
    Genv.find_funct_ptr tge fb = Some (Internal tf) ->
    frame_layout fb = F_frame_layout f.


Lemma ofs_local_repr:
  forall f ofs ty tf,
    0 <= ofs ->
    transf_function f = OK tf ->
    slot_within_bounds (function_bounds f) Local ofs ty ->
    0 <= offset_local (make_env (function_bounds f)) ofs <= Ptrofs.max_unsigned.
Proof.
  clear.
  intros.
  unfold offset_local in *.
  simpl in *. split. generalize (fe_ofs_local_pos (function_bounds f)); omega.
  etransitivity.
  apply Z.add_le_mono_l.
  apply Z.mul_le_mono_nonneg_l. omega.
  etransitivity. 2: apply H1. apply le_add_pos. generalize (typesize_pos ty); omega.
  etransitivity. 2: eapply size_no_overflow; eauto.
  apply fe_ofs_local_fe_size'.
Qed.

Lemma swb_local:
  forall f ofs ty ofs0,
    0 <= ofs ->
    slot_within_bounds (function_bounds f) Local ofs ty ->
    offset_local (make_env (function_bounds f)) ofs <= ofs0 < offset_local (make_env (function_bounds f)) ofs + size_chunk (chunk_of_type ty) ->
    in_segment (frame_locals (F_frame_layout f)) ofs0.
Proof.
  clear.
  intros.
  unfold in_segment; simpl in *.
  unfold offset_local in *.
  rewrite <- typesize_size_chunk in H1.
  omega.
Qed.



Lemma ofs_outgoing_repr:
  forall f ofs ty tf,
    0 <= ofs ->
    transf_function f = OK tf ->
    slot_within_bounds (function_bounds f) Outgoing ofs ty ->
    0 <= offset_arg ofs <= Ptrofs.max_unsigned.
Proof.
  clear.
  intros.
  unfold offset_arg in *.
  simpl in *. split. omega.
  etransitivity.
  apply Z.mul_le_mono_nonneg_l. omega.
  etransitivity. 2: apply H1. apply le_add_pos. generalize (typesize_pos ty); omega.
  etransitivity. 2: eapply size_no_overflow; eauto.
  apply bound_outgoing_fe_size.
Qed.

Lemma swb_outgoing:
  forall f ofs ty ofs0,
    0 <= ofs ->
    slot_within_bounds (function_bounds f) Outgoing ofs ty ->
    offset_arg ofs <= ofs0 < offset_arg ofs + size_chunk (chunk_of_type ty) ->
    in_segment (frame_outgoings (F_frame_layout f)) ofs0.
Proof.
  clear.
  intros.
  unfold in_segment; simpl in *.
  unfold offset_arg in *.
  rewrite <- typesize_size_chunk in H1.
  unfold fe_ofs_arg in *. omega. 
Qed.

Ltac trim H :=
  match type of H with
    ?A -> ?B =>
    let F := fresh in
    assert A as F;[
      clear H
    | specialize (H F); clear F
    ]
  end.

Lemma store_footprint_preserves:
  forall m P,
    m |= P ->
    forall chunk b o v m',
      Mem.store chunk m b o v = Some m' ->
      (forall ofs, o <= ofs < o + size_chunk chunk -> ~ m_footprint P (MemBlock b) ofs) ->
      m' |= P.
Proof.
  intros.
  eapply m_invar. eauto.
  eapply Mem.store_strong_unchanged_on in H0.
  destruct (m_invar_weak P); eauto.
  eapply Mem.strong_unchanged_on_weak; eauto.
  intros. apply H1. auto.
Qed.


Lemma contains_callee_saves_stack_footprint:
  forall rl b o sp pos ls,
    ~ m_footprint (contains_callee_saves sp pos rl ls) (MemBlock b) o.
Proof.
  clear.
  induction rl; simpl; intros. auto. intuition try congruence.
  eapply IHrl; eauto.
Qed.

Lemma frame_contents_stack_footprint:
  forall b o f sp ls ls2 parent ra,
    ~ m_footprint (frame_contents f sp ls ls2 parent ra) (MemBlock b) o.
Proof.
  clear.
  intros.
  simpl. intuition try congruence.
  eapply contains_callee_saves_stack_footprint; eauto.
Qed.

Lemma stack_contents_stack_footprint:
  forall cs cs' b o ,
    ~ m_footprint (stack_contents cs cs') (MemBlock b) o.
Proof.
  clear.
  induction cs; destruct cs'; simpl; intros; eauto.
  destruct a; simpl; auto.
  destruct a; simpl; auto. Opaque frame_contents.
  destruct s; simpl; auto.
  intuition try congruence.
  eapply frame_contents_stack_footprint; eauto.
  eapply IHcs; eauto.
Qed.

Lemma minit_args_stack_footprint:
  forall sg b o ,
    ~ m_footprint (minit_args_mach sg) (MemBlock b) o.
Proof.
  clear.
  simpl. intros. 
  intuition try congruence.
Qed.

Lemma conj_stack_footprint:
  forall P Q b o ,
    (forall b o, ~ m_footprint P (MemBlock b) o) ->
    (forall b o, ~ m_footprint Q (MemBlock b) o) ->
    ~ m_footprint (P ** Q) (MemBlock b) o.
Proof.
  clear.
  simpl; intuition; eauto.
Qed.

Section External_Rule.


(* Context `{external_calls_ops: !ExternalCallsOps mem}. *)
(* Context `{symbols_inject'_instance: !SymbolsInject}. *)
(* Context `{external_calls_props: !ExternalCallsProps mem}. *)
(* Context `{enable_builtins_instance: !EnableBuiltins mem}. *)
(* Context `{external_calls_prf: !ExternalCalls mem}. *)

Axiom external_call_nostack:
  forall F V ef (ge: Genv.t F V) vargs m t vres m',
    external_call ef ge vargs m t vres m' ->
    Mem.unchanged_on (fun b o => exists b', b = StackBlock b') m m'.

Lemma external_call_parallel_rule:
  forall (F V: Type) ef (ge: Genv.t F V) vargs1 m1 t vres1 m1' m2 P vargs2,
    m_invar_weak P = false ->
    external_call ef ge vargs1 m1 t vres1 m1' ->
    m2 |= P ->
    (forall b o, ~ m_footprint P (MemBlock b) o) ->
    Mem.extends m1 m2 ->
    Val.lessdef_list vargs1 vargs2 ->
    exists vres2 m2',
      external_call ef ge vargs2 m2 t vres2 m2'
      /\ Val.lessdef vres1 vres2
      /\ m2' |= P
      /\ Mem.extends m1' m2'.
Proof.
  intros until vargs2; intros INV_STRONG CALL SEP FP EXT ARGS.
  exploit external_call_mem_extends; eauto.
  intros (vres2 & m2' & CALL' & RES & EXT' & UNCH).
  assert (MAXPERMS: forall b ofs p,
             Mem.valid_block m1 b -> Mem.perm m1' b ofs Max p -> Mem.perm m1 b ofs Max p).
  { intros. eapply external_call_max_perm; eauto. }
  exists vres2, m2'; intuition auto.
  apply m_invar with (m0 := m2). auto.
  rewrite INV_STRONG.
  eapply Mem.unchanged_on_implies.
  eapply external_call_nostack. eauto.
  intros; simpl.
  destruct b. eauto.
  apply FP in H. easy.
Qed.  

End External_Rule.

Lemma frame_contents_valid_block:
  forall m f sp rs ls psp ra,
    m |= frame_contents f sp rs ls psp ra ->
    Mem.valid_block m (StackBlock sp).
Proof.
  clear; intros.
  destruct H as (A & _).
  unfold frame_contents_1 in A.
  rewrite sep_swap4 in A. apply sep_proj1 in A.
  destruct A as ( _ & A & _).
  eapply Mem.valid_access_valid_block; eauto with mem.
Qed.

Lemma valid_stack_same_valid_block:
  forall s m m' (SP: forall b, Mem.valid_block m b -> Mem.valid_block m' b),
    valid_stack m s ->
    valid_stack m' s.
Proof.
  clear; induction s; simpl; intros; eauto.
  destruct a.
  intuition eauto.
Qed.


Lemma stack_contents_valid_stack:
  forall s s' sg sg' m,
    m |= stack_contents s s' ->
    match_stacks s s' sg sg' ->
    valid_stack m s.
Proof.
  clear; induction s; simpl; intros; eauto.
  destruct a. destruct s'. intuition.
  destruct s0.
  destruct H as (A & B & _).
  inv H0.
  split; intuition eauto. 
  eapply frame_contents_valid_block; eauto.
Qed.

Variable fl : Linear.function -> frame.

Theorem transf_step_correct:
  forall s1 t s2, Linear2.step F_frame_layout ge s1 t s2 ->
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
      apply plus_one. apply exec_Mgetstack. unfold load_stack. exact A.
      constr_match_states.
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
      subst. destruct TP as [TP | TP] .
      * elim (TP _ IN_ARGS).
      * assert (init_args_mach init_sg m') as INIT_ARGS_MACH.
        {
          apply sep_proj2 in SEP. apply sep_proj2 in SEP.
          simpl in SEP. subst; auto.
        }
        exploit frame_get_parent; eauto.
        intro PARST. Opaque Z.mul bound_outgoing.
        subst.
        exploit INIT_ARGS_MACH. eauto. intros (v & EA & EAinj).
        esplit.
        -- split.
           ++ eapply plus_one.
              econstructor; eauto.
              erewrite frame_layout_correct; eauto.
              simpl. inv EA. eauto.
           ++ constr_match_states.
              constructor; auto. all: eauto with mem.
              ** apply agree_regs_set_reg; auto.
                 change (rs0 # temp_for_parent_frame <- Vundef)
                 with (undef_regs (destroyed_by_getstack Incoming) rs0).
                 eapply agree_regs_undef_regs; eauto.
                 erewrite agree_incoming. eauto. eauto. eauto.
              ** apply agree_locs_set_reg; eauto.
                 apply agree_locs_set_reg; eauto.
                 apply caller_save_reg_within_bounds.
                 reflexivity.
              ** eapply is_tail_cons_left; eauto.
              ** revert Hno_init_args.
                 generalize (Linear2.state_invariant s1). rewrite Hs2.
                 inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
              ** congruence.

      * subst sg isg.
        subst s cs'.
        
        exploit frame_get_outgoing.
        Opaque frame_contents.
        apply sep_proj2 in SEP. simpl in SEP. apply SEP.
        apply ARGS; eauto.
        eapply slot_outgoing_argument_valid; eauto.
        intros (v & A & B).
        econstructor; split.
        -- apply plus_one. eapply exec_Mgetparam; eauto.
           simpl. erewrite frame_layout_correct. 3: eauto. 2: eauto.
           eapply frame_get_parent. apply SEP. 
        -- constr_match_states.
           now (econstructor; eauto).
           all: eauto.
           ++ apply agree_regs_set_reg; auto.
              change (rs0 # temp_for_parent_frame <- Vundef)
              with (undef_regs (destroyed_by_getstack Incoming) rs0).
              eapply agree_regs_undef_regs; eauto.
              erewrite agree_incoming. eauto. eauto. eauto.
           ++ apply agree_locs_set_reg; eauto.
              apply agree_locs_set_reg; eauto.
              apply caller_save_reg_within_bounds.
              reflexivity.
           ++ eapply is_tail_cons_left; eauto.
           ++ revert Hno_init_args.
              generalize (Linear2.state_invariant s1). rewrite Hs2.
              inversion step_high; inversion 1; subst; simpl in *; now intuition congruence.
           ++ congruence.

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
               store_stack m' sp ty (Ptrofs.repr ofs') (rs0 src) = Some m''
               /\ m'' |= frame_contents f sp (Locmap.set (S sl ofs ty) (rs (R src))
                                                           (LTL.undef_regs (destroyed_by_setstack ty) rs))
                     (parent_locset init_ls s) (parent_sp init_sp cs') (parent_ra init_ra cs')
                     ** stack_contents s cs' ** minit_args_mach sg_
           ).
    {
      unfold ofs'; destruct sl; try discriminate.
      eapply frame_set_local; eauto.
      eapply frame_set_outgoing; eauto.
    }
    clear SEP; destruct A as (m'' & STORE & SEP).
    econstructor; split.
    + apply plus_one. destruct sl; try discriminate.
      econstructor. eexact STORE. eauto.
      econstructor. eexact STORE. eauto.
    + constr_match_states. all: eauto with coqlib. 
      * apply agree_regs_set_slot. apply agree_regs_undef_regs. auto.
      * apply agree_locs_set_slot. apply agree_locs_undef_locs. auto. apply destroyed_by_setstack_caller_save. auto.
      * unfold store_stack in STORE. eapply valid_block_set_stack_1; eauto. 
      * unfold store_stack in STORE. intros. eapply valid_block_set_stack_1. eauto.
        apply INIT_VB'. auto.
      * revert Hno_init_args.
        generalize (Linear2.state_invariant s1).
        rewrite Hs2.
        inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
      * congruence.
      * unfold store_stack in STORE. eapply set_stack_outside_extends. eauto. eauto.
        intros.
        generalize (PERM_stack _ _ (Mem.perm_cur_max _ _ _ _ H)). 
        intro A.
        assert (0 <= ofs).
        {
          clear - SV SW.
          unfold slot_valid in SV; destruct sl ; simpl in *; destruct (zle 0 ofs); auto; try discriminate.
        }
        destruct sl.
        -- Opaque F_frame_layout. simpl in A.
           trim A.
           {
             right; left. eapply swb_local. 2: eauto. auto.
             unfold ofs' in H1. rewrite Ptrofs.unsigned_repr in H1. auto.
             eapply ofs_local_repr; eauto.
           }
           inv A.
        -- simpl in SW. congruence.
        -- simpl in A.
           trim A.
           {
             right; right. eapply swb_outgoing. 2: eauto. auto.
             unfold ofs' in H1. rewrite Ptrofs.unsigned_repr in H1. auto.
             eapply ofs_outgoing_repr; eauto.
           }
           inv A.

- (* Lop *)
  assert (OP_INJ:
            exists v',
              eval_operation ge 
                             (transl_op (make_env (function_bounds f)) op) rs0##args m' = Some v' /\
              Val.lessdef v v').
  {
    eapply eval_operation_lessdef; eauto.
    eapply agree_reglist; eauto.
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
              eval_addressing ge 
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.lessdef a a').
  {
    eapply eval_addressing_lessdef; eauto.
    eapply agree_reglist; eauto.
  }
  destruct ADDR_INJ as [a' [A B]].
  exploit Mem.loadv_extends. eauto. eauto. apply B.
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
              eval_addressing ge
                              (transl_addr (make_env (function_bounds f)) addr) rs0##args = Some a' /\
              Val.lessdef a a').
  {
    eapply eval_addressing_lessdef; eauto.
    eapply agree_reglist; eauto.
  }
  destruct STORE_INJ as [a' [A B]].
  exploit Mem.storev_extends. eauto. eauto. eauto. eauto.
  intros (m1' & C & EXT1).
  econstructor; split.
  + apply plus_one. econstructor.
    instantiate (1 := a'). rewrite <- A. apply eval_addressing_preserved. exact symbols_preserved.
    eexact C. eauto.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    Opaque sepconj.
    inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.
    exploit eval_addressing_lessdef_strong. apply reglist_lessdef.
    eauto. eauto. eauto. intros (v2 & EA & LD).
    rewrite EA in H1; inv H1.
    destruct a0; try discriminate. inv LD. inv B. simpl in *.
    intro OOB.
    constr_match_states. all: eauto with coqlib.
    * rewrite transl_destroyed_by_store. apply agree_regs_undef_regs; auto.
    * apply agree_locs_undef_locs. auto. apply destroyed_by_store_caller_save.
    * eapply Mem.store_valid_block_1. eauto. auto.
    * intros. eapply Mem.store_valid_block_1. eauto. apply INIT_VB. auto.
    * intros. eapply Mem.store_valid_block_1. eauto. apply INIT_VB'. auto.
    * rewrite <- H3. simpl.
      eapply init_args_out_of_bounds_store; eauto.
    * congruence.
    * eapply frame_undef_regs; eauto.
      eapply store_footprint_preserves; eauto.
      simpl; intros.
      apply conj_stack_footprint.
      intros; apply frame_contents_stack_footprint.
      intros; apply conj_stack_footprint.
      intros; apply stack_contents_stack_footprint.
      intros; apply minit_args_stack_footprint.
    * intros; eapply PERM_stack; eauto.
      eauto with mem.
    * eapply bounds_stack_store; eauto.

- (* Lcall *)
  exploit find_function_translated; eauto.
  intros [bf [tf' [A [B C]]]].
  exploit is_tail_transf_function; eauto. intros IST.
  rewrite transl_code_eq in IST. simpl in IST.
  exploit return_address_offset_exists. eexact IST. intros [ra D].
  econstructor; split.
  + apply plus_one. econstructor; eauto.
  + constr_match_states; eauto.
    * econstructor; eauto with coqlib.
      apply Val.Vptr_has_type.
      intros; red.
      apply Zle_trans with (size_arguments (Linear.funsig f')); auto.
      apply loc_arguments_bounded; auto.
      etransitivity. apply Z.mul_le_mono_nonneg_l. omega. apply BOUND.
      etransitivity. 2: eapply size_no_overflow; eauto.
      transitivity (fe_stack_data (make_env (function_bounds f))).
      generalize (frame_env_separated' (function_bounds f)). simpl. clear. intros. decompose [and] H.
      change (Z.max (max_over_instrs f outgoing_space) (max_over_slots_of_funct f outgoing_slot) ) with
      (bound_outgoing (function_bounds f)).
      etransitivity.
      2: apply H7. apply align_le. destruct Archi.ptr64; omega.
      generalize (frame_env_range (function_bounds f)).
      generalize (bound_stack_data_pos (function_bounds f)). simpl.
      omega. 
    * simpl; red; auto.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; subst; simpl in * |- * ; now intuition congruence.
    * congruence.
    * simpl. rewrite sep_assoc. exact SEP.
    * simpl. split; auto.

- (* Ltailcall *)
  exploit function_epilogue_correct; eauto.
  admit.
  rename SEP into SEP_init. intros (rs1 & m1' & P & Q & R & S & T & U & EXT' & SEP).
  inv Hinit_ls.
  exploit find_function_translated; eauto.
  intros [bf [tf' [A [B C]]]].
  econstructor; split.
  + eapply plus_right. eexact S. econstructor; eauto.
    erewrite frame_layout_correct; eauto.
    erewrite frame_layout_correct; eauto.    
    traceEq.
  + assert (TAILCALL: tailcall_possible (Linear.funsig f')).
    {
      apply zero_size_arguments_tailcall_possible. eapply wt_state_tailcall; eauto.
    }
    exploit match_stacks_change_sig. eauto. eauto.
    erewrite wt_state_tailcall. vm_compute. congruence. eauto.
    intros MS'.
    constr_match_states.  all: eauto. subst; eauto.
    * intros.

      eapply pop_frame_valid_block. eauto.
      eapply INIT_VB. auto.
    * intros. eapply pop_frame_valid_block. eauto.
      apply INIT_VB'. auto. 
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      destruct s eqn:?.
      -- clear H1. subst.
         intros _.
         clear - TAILCALL. red; red; intros.
         apply TAILCALL in H. easy.
      -- eapply init_args_out_of_bounds_pop_frame; eauto.
    * congruence.
    * eapply pop_frame_valid_block; eauto.
    * split. 2:split.
      -- apply SEP.
      -- destruct s. 
         ++ red.
            intros sl of ty H rs2.
            elim (TAILCALL _ H).
         ++ apply SEP. 
      -- destruct SEP as (A1 & A2 & A3). revert A3. destruct s; auto.
         red; intros.
         eapply A3; eauto.
         destruct H3. decompose [ex and] H4.
         exploit TAILCALL. apply H7. simpl. easy.
    * eapply bounds_stack_pop_frame; eauto.

- (* Lbuiltin *)
  destruct BOUND as [BND1 BND2].
  exploit transl_builtin_args_correct.
  eauto. eauto.
  apply SEP.
  eauto. eauto.
  rewrite <- forallb_forall. eapply wt_state_builtin; eauto.
  exact BND2.
  intros [vargs' [P Q]].
  exploit (external_call_parallel_rule).
  2: eassumption.
  2: eassumption.
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
  {
    simpl; intros.
    apply conj_stack_footprint.
    intros; apply frame_contents_stack_footprint.
    intros; apply conj_stack_footprint.
    intros; apply stack_contents_stack_footprint.
    intros; apply minit_args_stack_footprint.
  }
  all: eauto.
  rename SEP into SEP_init; intros (res' & m1' & EC & RES & SEP & EXT').
  econstructor; split.
  + apply plus_one. econstructor; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  + constr_match_states.
    4: apply agree_regs_set_res; auto. 4: apply agree_regs_undef_regs; auto. 
    4: apply agree_locs_set_res; auto. 4: apply agree_locs_undef_regs; auto.
    eauto. all: eauto.
    (* * exists m, m'0; split; auto. *)
    (*   intros. eapply Mem.valid_block_lessdef_2; eauto. *)
    (*   apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init. *)
    (*   apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init. *)
    (*   simpl in SEP_init. eauto. *)
    (* * intros. *)
    (*   destruct (j b0) eqn:?. destruct p. *)
    (*   generalize (INCR _ _ _ Heqo). intros. rewrite H4 in H3; inv H3. *)
    (*   eapply INJUNIQUE; eauto. *)
    (*   generalize (ISEP _ _ _ Heqo H3). *)
    (*   intros (A & B). *)
    (*   apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init. *)
    (*   apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init. *)
    (*   simpl in SEP_init. simpl in SEP_init. *)
    (*   exploit Mem.valid_block_lessdef_2. apply INJSP. eauto. congruence. *)
    (* * revert INJ_INIT_SP. revert INCR. clear. destruct init_sp; simpl; auto. *)
    (* * eapply has_at_most_one_antecedent_incr; eauto. *)
    * eapply external_call_valid_block; eauto.
    * intros. eapply external_call_valid_block; eauto. 
    * intros. eapply external_call_valid_block; eauto. 
    * eauto with coqlib.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      eapply init_args_out_of_bounds_external_call; eauto.
      rewrite Mem.valid_block_extends. 2: eauto.
      rewrite Mem.valid_block_extends. 2: eauto. auto.
    * congruence.
    (* * revert Hsome_init_args Hno_init_args. *)
    (*   generalize (Linear2.state_invariant s1). *)
    (*   rewrite Hs2. *)
    (*   inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence. *)
    (*   intros IAIB IAOOB. *)
    (*   eapply init_args_in_bounds_external_call. eexact H6. *)
    (*   eapply globalenv_lessdef_preserves_globals. *)
    (*   apply sep_pick2 in H. eauto. *)
    (*   all: eauto. *)
    (*   -- intros. *)
    (*      revert INJ_INIT_SP INCR H7. clear. intros. subst. simpl in *; auto. *)
    (*   -- revert HAMOA INJ_INIT_SP INCR ISEP ISP'VALID. clear. *)
    (*      intros; subst; simpl in *; auto. *)
    (*      specialize (HAMOA _ _ eq_refl _ _ _ _ INJ_INIT_SP H0). subst. *)
    (*      rewrite H0 in INJ_INIT_SP. inv INJ_INIT_SP. auto. *)
    (*   -- apply sep_proj2 in SEP_init. apply sep_proj2 in SEP_init. *)
    (*      apply mconj_proj1 in SEP_init. apply sep_proj1 in SEP_init. *)
    (*      simpl in SEP_init. eauto. *)
    (*   -- eapply val_list_lessdef_lessdef_compose. 2: apply Q. *)
    (*      exploit Events.eval_builtin_args_lessdef. apply rs_lessdef. apply m_ext. eauto. *)
    (*      intros (vl2 & EBA & LDL). *)
    (*      eapply Val.lessdef_list_trans. eauto. *)
    (*      eapply Events.eval_builtin_args_lessdef'. 3: eauto. 3: eauto. all: eauto. *)
    * apply frame_set_res. apply frame_undef_regs. auto.
    * intros.
      exploit external_call_max_perm. eexact H2. 2: apply H.

      eapply Mem.valid_block_extends.
      2: eapply frame_contents_valid_block; eauto.
      eauto. apply SEP_init.
      intros; eapply PERM_stack; eauto.
    * eapply bounds_stack_perm. eauto.

      eapply valid_stack_same_valid_block. 
      2: eapply stack_contents_valid_stack; eauto.
      2: apply SEP_init.
      intro; apply Mem.valid_block_extends; now auto.

      intros. eapply external_call_max_perm. 3: eauto. eauto. eauto.

- (* Llabel *)
  econstructor; split.
  apply plus_one; apply exec_Mlabel.
  constr_match_states.
  all: eauto with coqlib.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lgoto *)
  econstructor; split.
  apply plus_one; eapply exec_Mgoto; eauto.
  apply transl_find_label; eauto.
  constr_match_states; eauto.
  eapply find_label_tail; eauto.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
  congruence.

- (* Lcond, true *)
  econstructor; split.
  apply plus_one. eapply exec_Mcond_true; eauto.
  eapply eval_condition_lessdef with (m1 := m). eapply agree_reglist; eauto.
  auto. auto.
  eapply transl_find_label; eauto.
  constr_match_states. eauto. eauto. eauto.
  apply agree_regs_undef_regs; auto. 
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
  eapply eval_condition_lessdef with (m1 := m). eapply agree_reglist; eauto.
  auto. auto.
  constr_match_states. eauto. eauto. eauto.
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
  constr_match_states. eauto. eauto. eauto.
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
  exploit function_epilogue_correct; eauto. admit.
  intros (rs' & m1' & A & B & C & D & E & F & EXT' & G).
  econstructor; split.
  eapply plus_right. eexact D. econstructor; eauto.
  erewrite frame_layout_correct; eauto.
  erewrite frame_layout_correct; eauto.
  traceEq.
  inv Hinit_ls.
  constr_match_states. all: try subst; eauto.
  + intros. eapply pop_frame_valid_block. eauto. apply INIT_VB; auto.
  + intros. eapply pop_frame_valid_block. eauto. apply INIT_VB'; auto.
  + revert Hno_init_args.
    generalize (Linear2.state_invariant s1).
    rewrite Hs2.
    inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
    intros; eapply init_args_out_of_bounds_pop_frame; eauto.
  + congruence.
  + eapply pop_frame_valid_block; eauto.
  + eapply bounds_stack_pop_frame; eauto.

- (* internal function *)
  revert TRANSL. unfold transf_fundef, transf_partial_fundef.
  destruct (transf_function f) as [tfn|] eqn:TRANSL; simpl; try congruence.
  intros EQ; inversion EQ; clear EQ; subst tf.
  exploit function_prologue_correct.
  eassumption.
  eassumption.
  red; intros; eapply wt_callstate_wt_regs; eauto.
  reflexivity.
  reflexivity.
  Transparent F_frame_layout.
  unfold F_frame_layout in H1. eassumption.
  eapply match_stacks_type_retaddr. eauto.
  apply EXT. apply SEP. admit.
  rename SEP into SEP_init;
  intros (rs' & m2' & sp' & m5' & A & B & C & D & SEP & EXT' & KV & KV' & PERMS & UNCH).
  econstructor; split.
  + eapply plus_left.
    * econstructor; eauto.
      rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
      erewrite frame_layout_correct; eauto.
    * rewrite (unfold_transf_function _ _ TRANSL). unfold fn_code. unfold transl_body.
      eexact B.
    * traceEq.
  +

      Axiom push_frame_extends_new_block:
        forall m1 m2,
          Mem.extends m1 m2 ->
          forall fr1 ra1 frp1 m1' sp1 fr2 ra2 frp2 m2' sp2,
            Mem.push_frame m1 fr1 ra1 frp1 = Some (m1',  sp1) ->
            Mem.push_frame m2 fr2 ra2 frp2 = Some (m2',  sp2) ->
            sp1 = sp2.

      exploit push_frame_extends_new_block. eexact EXT. eauto. eauto. intro; subst.
    constr_match_states. all: eauto with coqlib.
    * revert Hno_init_args.
      generalize (Linear2.state_invariant s1).
      rewrite Hs2.
      inversion step_high; inversion 1; try subst; simpl in * |- * ; try now intuition congruence.
      eapply init_args_out_of_bounds_push_frame. eauto.
      {
        revert ISP'VALID.
        rewrite <- Mem.valid_block_extends. 2: eauto.
        eapply Mem.valid_block_extends. auto.
      }
      eauto. eauto. eauto.
    * congruence.
    * intro; subst sp'. exploit push_frame_fresh_block. apply A. congruence. auto.
    * intros.

    * apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; simpl in SEP_init ; eauto.
      revert SEP_init INJ_INIT_SP A . clear - memory_model_prf.
      intros; subst. inversion INJ_INIT_SP.
      eapply Mem.fresh_block_alloc in A. simpl in *.
      eapply Mem.valid_block_lessdef_2 in INJ_INIT_SP; eauto. congruence.
    *
      rewrite sep_rot in SEP. rewrite sep_swap12.
      eapply stack_contents_change_meminj; eauto.
      rewrite sep_swap23, sep_swap12.
      eapply mconj_intro.
      rewrite sep_swap12, sep_swap23. eexact SEP.
      split;[|split].
      -- simpl.
         apply mconj_proj2 in SEP_init. apply sep_proj1 in SEP_init.
         eapply init_args_mach_unch; eauto. simpl.
         revert ISP'VALID A. clear - external_calls_prf. destruct init_sp; simpl; try congruence.
         intros.
         eapply Mem.fresh_block_alloc in A. inv H. congruence.
         eapply init_args_incr; eauto.
      -- rewrite sep_swap23, sep_swap12 in SEP. apply sep_proj2 in SEP. assumption.
      --
        apply mconj_proj2 in SEP_init.
        destruct SEP_init as (A1 & A2 & A3). revert A3.
        red. simpl.
        intros.
        exploit A3. simpl. eauto.
        destruct H2. right; auto.
        destruct H2. 2: left; auto.
        simpl in H2.
        assert ( b = sp' ).
        clear - H2.
        repeat match goal with
                 H : m_footprint _ _ _ \/ m_footprint _ _ _ |- _ => destruct H; auto
               | H : m_footprint _ _ _ |- _ => destruct H; auto
               end.
        revert H.
        generalize (used_callee_save (function_bounds f))
                   (fe_ofs_callee_save (make_env (function_bounds f)))
                   (parent_locset init_ls s).
        induction l; simpl; intros. easy.
        destruct H; auto. destruct H. auto. eauto.
        clear - A ISP'VALID H H3.
        decompose [ex and] H.
        exfalso. subst. eapply Mem.fresh_block_alloc; eauto. tauto.
    * intros. eapply Mem.perm_alloc_3; eauto.
    * eapply bounds_stack_perm. eauto.
      eapply match_stacks_valid_stack.
      eauto.
      apply mconj_proj1 in SEP_init; apply sep_proj1 in SEP_init; eauto.
      intros.
      eapply Mem.perm_alloc_4; eauto.
      eapply Mem.fresh_block_alloc in H1. congruence.

- (* external function *)
  simpl in TRANSL. inversion TRANSL; subst tf.
  exploit transl_external_arguments; eauto. apply sep_proj1 in SEP; eauto.
  { (* init_args_mach *)
    eapply sep_drop in SEP.
    eapply mconj_proj2 in SEP.
    eapply sep_proj1 in SEP.
    simpl in SEP; eauto.
  }
  intros [vl [ARGS VINJ]].
  assert (SEP_init := SEP).
  rewrite <- sep_swap12 in SEP. apply mconj_proj1 in SEP.
  rewrite (sep_comm _ (globalenv_lessdef _ _)) in SEP.
  exploit external_call_parallel_rule; eauto.
  {
    rewrite stack_contents_invar_weak. reflexivity.
  }
  intros (j' & res' & m1' & A & B & C & D & E).
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
	rewrite Hs2.
	inversion step_high; inversion 1; subst; try (simpl in * |- * ; now intuition congruence).
  intro Hno_init_args.
  econstructor; split.
  apply plus_one. eapply exec_function_external; eauto.
  {
	  inversion f_eq; subst.
    exploit free_extcall_args_external_call. all: eauto.
    rewrite sep_swap12 in SEP_init. apply mconj_proj1 in SEP_init.
    apply sep_proj1 in SEP_init. simpl in SEP_init. eauto.
    rewrite sep_swap12 in SEP_init.
    apply sep_drop in SEP_init. eauto.
	  eapply val_list_lessdef_lessdef_compose; eauto.
    apply map_reg_lessdef; auto.
    intros (m'_ & FEA & t2 & res2 & m2 & EC2).
    exists m'_; split; eauto.
    eapply external_call_symbols_preserved in EC2; eauto. apply senv_preserved.
  }
  inv f_eq.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constr_match_states.
  eapply match_stacks_change_meminj. 3: eexact STACKS.
  all:eauto.
  exists m, m'0; split; eauto.
  intros; eapply Mem.valid_block_lessdef_2; eauto. apply sep_proj1 in SEP; simpl in SEP; eauto.
  apply agree_regs_set_pair. apply agree_regs_lessdef_incr with j; auto. auto.
  apply agree_callee_save_set_result; auto.
  * eapply lessdef_incr_trans; eauto.
  * eapply lessdef_incr_sep_trans; eauto.
  * etransitivity. apply INIT_VB.
    eapply external_call_nextblock; eauto.
  * etransitivity. apply INIT_VB'.
    eapply external_call_nextblock; eauto.
  * rewrite <- H1. simpl in *.
    eapply init_args_out_of_bounds_external_call; eauto.
    intros.
    rewrite H3 in INJ_INIT_SP; inversion INJ_INIT_SP.
    rewrite Mem.valid_block_extends.
    eapply Mem.valid_block_lessdef_1; eauto. apply sep_proj1 in SEP; simpl in SEP; eauto.
    eauto.
    apply sep_proj1 in SEP; simpl in SEP; eauto.
  * congruence.
  * revert Hsome_init_args Hno_init_args.
    simpl.
    intros IAIB IAOOB.
    eapply init_args_in_bounds_external_call. eexact H4.
    eapply globalenv_lessdef_preserves_globals.
    apply sep_pick2 in SEP. eauto. all: eauto.
    -- intros.
       revert INJ_INIT_SP D H3. clear. intros. subst. simpl in *; auto.
    -- revert HAMOA INJ_INIT_SP D E ISP'VALID. clear.
       intros; subst; simpl in *; auto.
       specialize (HAMOA _ _ eq_refl _ _ _ _ INJ_INIT_SP H0). subst.
       rewrite H0 in INJ_INIT_SP. inv INJ_INIT_SP. auto.
    -- apply sep_pick1 in SEP; simpl in SEP; eauto.
    -- eapply val_list_lessdef_lessdef_compose. 2: apply VINJ.
       inv f_eq. apply map_reg_lessdef. auto.
    -- inv f_eq. eauto.
  * revert INJ_INIT_SP D. clear.
    destruct init_sp; simpl; auto.
  * revert HAMOA D E ISP'VALID. clear.
    red; intros.
    destruct (j b1) eqn:?. destruct p.
    destruct (j b2) eqn:?. destruct p.
    exploit D. eexact Heqo.
    exploit D. eexact Heqo0.
    intros. assert (b0 = b' /\ b = b') by (split; congruence). destruct H1; subst.
    eapply HAMOA; eauto.
    exploit E; eauto. rewrite EQ in ISP'VALID; simpl in ISP'VALID. intuition congruence.
    exploit E; eauto. rewrite EQ in ISP'VALID; simpl in ISP'VALID. intuition congruence.
  * eapply block_prop_impl. 2: eauto. intros; eapply external_call_valid_block; eauto.
  * apply stack_contents_change_meminj with j; auto.
    rewrite sep_swap12.
    apply mconj_intro.
    rewrite (sep_comm (stack_contents _ _ _)). eauto.
    split.
    rewrite sep_swap12 in SEP_init. apply mconj_proj2 in SEP_init.
    apply sep_proj1 in SEP_init. revert SEP_init.
    -- simpl.
       intro IAM.
       inv f_eq.
       exploit external_call_mem_extends. apply H4. eauto.
       apply map_reg_lessdef. apply rs_lessdef.
       intros (vres' & m2' & EC2 & LDres & EXTres & UNCH).
       exploit external_call_determ. eexact EC2. eexact H2.
       intros (AA & BB). intuition subst. clear H2.
       exploit external_call_mem_lessdef.
       3: eapply Mem.extends_lessdef_compose. 3: apply m_ext.
       3: apply sep_proj1 in SEP; simpl in SEP; eauto.
       eapply globalenv_lessdef_preserves_globals.
       apply sep_pick2 in SEP; eauto.
       eauto.
       eapply val_list_lessdef_lessdef_compose.
       apply map_reg_lessdef. apply rs_lessdef.
       simpl in VINJ. apply VINJ.
       intros (f' & vres'0 & m2'0 & EC3 & INJres & MINJres & UNCH' & UNCH3 & INCR2 & SEP2).
       exploit external_call_determ.
       eexact A. eexact EC3. intuition subst.
       revert HAMOA INJ_INIT_SP UNCH3 IAM Hno_init_args D. clear - external_calls_prf.
       red; intros.
       exploit IAM. eauto. instantiate (1 := rs).
       intros (v & ea & inj); eexists; split; eauto.
       inv ea; constructor; eauto.
       destruct init_sp eqn:?; simpl in *; try discriminate.
       unfold load_stack in *; simpl in *.
       eapply Mem.load_unchanged_on. eexact UNCH3. 2: eauto.
       red; red; intros.
       exploit Hno_init_args; eauto.
       exploit HAMOA. eauto. apply INJ_INIT_SP. apply H1.
       intro. subst b0.
       assert (delta = 0) by congruence. subst delta.
       rewrite Zminus_0_r in H2; eauto.
    -- split. apply sep_proj2 in C. rewrite sep_comm in C. eauto.
       rewrite sep_swap12 in SEP_init.
       apply mconj_proj2 in SEP_init.
       destruct SEP_init as (A1 & A2 & A3).
       revert A3.
       clear - D. red; simpl.
       intros. decompose [ex and] H. clear H.
       exploit A3. simpl. repeat eexists; eauto.
       revert H0.
       eapply footprint_impl.
       simpl. auto. auto.
  * eapply bounds_stack_perm. eauto. eapply match_stacks_valid_stack; eauto.
    apply sep_proj1 in SEP; eauto.
    intros. eapply external_call_max_perm; eauto.

- (* return *)
  inv STACKS. simpl in AGLOCS. simpl in SEP. rewrite sep_assoc in SEP. 
  econstructor; split.
  apply plus_one. apply exec_return.
  revert Hno_init_args.
  generalize (Linear2.state_invariant s1).
  rewrite Hs2.
  inversion step_high; inversion 1; subst; simpl in * |- * ; try now intuition congruence.
  intro IAOOB.
  constr_match_states; eauto.
  apply agree_locs_return with rs0; auto.
  rewrite <- H0; simpl; eassumption.
  congruence.
  apply frame_contents_exten with rs0 (parent_locset init_ls s); auto.
  intros. eapply BS. eauto. eapply BS.
  Unshelve. eauto.
Qed.

End WITHMEMINIT.

End WITHINITSP.

Inductive match_states' (s : Linear2.state) (s': Mach.state): Prop :=
| match_states'_intro:
    match_states Vnullptr Vnullptr (Locmap.init Vundef) (signature_main) Val.Vnullptr_has_type Mem.empty s s' ->
    match_states' s s'.

Lemma transf_initial_states:
  forall st1, Linear2.initial_state prog st1 ->
  exists st2, Mach.initial_state tprog st2 /\ match_states' st1 st2.
Proof.
  intros. inv H.
  inv init_lower.
  exploit function_ptr_translated; eauto. intros [tf [FIND TR]].
  econstructor; split.
  econstructor.
  eapply (Genv.init_mem_transf_partial TRANSF); eauto.
  rewrite (match_program_main TRANSF).
  rewrite symbols_preserved. eauto.
  set (j := Mem.flat_inj (Mem.nextblock m0)).
  constructor.
  econstructor. instantiate (4 := j). all: eauto.
  - rewrite H3. constructor.
    left; red; simpl. easy.
    vm_compute. congruence.
  - unfold Locmap.init. red; intros; auto.
  - unfold Locmap.init. red; intros; auto.
  - unfold j, Mem.flat_inj.
    red. intros.
    destruct (plt b0 (Mem.nextblock Mem.empty)); try congruence.
    rewrite Mem.nextblock_empty in p; xomega.
  - red. unfold Mem.flat_inj. intros b1.
    unfold Mem.valid_block. simpl.
    rewrite Mem.nextblock_empty in *. intros. split; xomega.
  - rewrite Mem.nextblock_empty; xomega.
  - rewrite Mem.nextblock_empty; xomega.
  - red. red. discriminate.
  - congruence.
  - red.  red.
    rewrite loc_arguments_main. simpl; eauto.
  - unfold Vnullptr. destruct Archi.ptr64; simpl; auto.
  - red. discriminate.
  - unfold Vnullptr. destruct Archi.ptr64; simpl; auto.
  - simpl stack_contents. rewrite sep_pure. split; auto. split;[|split].
    + split.
      * simpl. eapply Genv.initmem_lessdef; eauto.
      * simpl. red. simpl. easy.
    +  simpl. exists (Mem.nextblock m0); split. apply Ple_refl.
       unfold j, Mem.flat_inj; constructor; intros.
       apply pred_dec_true; auto.
       destruct (plt b1 (Mem.nextblock m0)); congruence.
       change (Mem.valid_block m0 b0). eapply Genv.find_symbol_not_fresh; eauto.
       change (Mem.valid_block m0 b0). eapply Genv.find_funct_ptr_not_fresh; eauto.
       change (Mem.valid_block m0 b0). eapply Genv.find_var_info_not_fresh; eauto.
    + red; simpl; tauto.
  - red; simpl. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r,
  match_states' st1 st2 -> Linear2.final_state st1 r -> Mach.final_state st2 r.
Proof.
  intros. inv H0. inv H. inv fin_higher. inv fin_lower. inv H0; try congruence.
  inv STACKS; try congruence.
  assert (R: exists r, loc_result signature_main = One r).
  { destruct (loc_result signature_main) as [r1 | r1 r2] eqn:LR.
  - exists r1; auto.
  - generalize (loc_result_type signature_main). rewrite LR. discriminate.
  }
  destruct R as [rres EQ]. rewrite EQ in H1. simpl in H1.
  rewrite <- H2 in Hs2; inv Hs2.
  generalize (Linear2.state_invariant st1).
  rewrite <- H, <- H2. intro A; inv A.
  generalize (AGREGS rres).
  specialize (rs_lessdef (R rres)); rewrite H1 in rs_lessdef. inv rs_lessdef. intro A; inv A.
  econstructor; eauto.
  unfold Locmap.getpair in H3. simpl in H3.
  rewrite EQ in H3. simpl in H3.
  unfold signature_main in EQ. vm_compute in EQ. inv EQ.
  congruence.
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

Theorem transf_program_correct':
  forward_simulation (Linear2.semantics prog) (Mach.semantics return_address_offset tprog).
Proof.
  set (ms := fun s s' => wt_state (Locmap.init Vundef) (Linear2.state_lower s) /\ match_states' s s').
  eapply forward_simulation_plus with (match_states := ms).
- apply senv_preserved.
- intros. exploit transf_initial_states; eauto. intros [st2 [A B]].
  exists st2; split; auto. split; auto.
  apply wt_initial_state with (prog0 := prog); auto. exact wt_prog.
  inv H. congruence.
- intros. destruct H. eapply transf_final_states; eauto.
- intros.
  destruct H0. destruct H1.
  exploit transf_step_correct; eauto.
  apply Val.Vnullptr_has_type. 
  intros [s2' [A B]].
  exists s2'; split. exact A. split.
  inv H.
  eapply step_type_preservation; eauto. eexact wt_prog.
  assert (Linear2.state_init_ls s1 = Locmap.init Vundef) as INIT.
  {
    inversion H1; congruence.
  }
  rewrite <- INIT.
  eexact step_low.
  repeat eexists; eauto. 
Qed.

Theorem transf_program_correct:
  forward_simulation (Linear.semantics prog) (Mach.semantics return_address_offset tprog).
Proof.
  eapply compose_forward_simulations.
  eapply Linear2.whole_program_linear_to_linear2.
  apply transf_program_correct' .
Qed.

End PRESERVATION.
