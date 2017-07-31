(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*                 Xavier Leroy, INRIA Paris                           *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Machine- and ABI-dependent layout information for activation records. *)

Require Import Coqlib.
Require Import AST Memory Separation.
Require Import Bounds.

Local Open Scope sep_scope.

(** The general shape of activation records is as follows,
  from bottom (lowest offsets) to top:
- Space for outgoing arguments to function calls.
- Back link to parent frame
- Saved values of integer callee-save registers used by the function.
- Saved values of float callee-save registers used by the function.
- Local stack slots.
- Space for the stack-allocated data declared in Cminor
- Return address.
*)

Definition fe_ofs_arg := 0.

Definition make_env (b: bounds) : frame_env :=
  let w := if Archi.ptr64 then 8 else 4 in
  let olink := align (4 * b.(bound_outgoing)) w in  (* back link *)
  let ocs := olink + w in                           (* callee-saves *)
  let ol :=  align (size_callee_save_area b ocs) 8 in (* locals *)
  let ostkdata := align (ol + 4 * b.(bound_local)) 8 in (* stack data *)
  let oretaddr := align (ostkdata + b.(bound_stack_data)) w in (* return address *)
  let sz := oretaddr + w in (* total size *)
  {| fe_size := sz;
     fe_ofs_link := olink;
     fe_ofs_retaddr := oretaddr;
     fe_ofs_local := ol;
     fe_ofs_callee_save := ocs;
     fe_stack_data := ostkdata;
     fe_used_callee_save := b.(used_callee_save) |}.

Section WITHMEM.
  Context `{memory_model_prf: Mem.MemoryModel (injperm:=inject_perm_all)}.
  Lemma frame_env_separated:
    forall b sp (m: mem) P,
      let fe := make_env b in
      m |= range sp 0 (fe_stack_data fe) ** range sp (fe_stack_data fe + bound_stack_data b) (fe_size fe) ** P ->
      m |= range sp (fe_ofs_local fe) (fe_ofs_local fe + 4 * bound_local b)
        ** range sp fe_ofs_arg (fe_ofs_arg + 4 * bound_outgoing b)
        ** range sp (fe_ofs_link fe) (fe_ofs_link fe + size_chunk Mptr)
        ** range sp (fe_ofs_retaddr fe) (fe_ofs_retaddr fe + size_chunk Mptr)
        ** range sp (fe_ofs_callee_save fe) (size_callee_save_area b (fe_ofs_callee_save fe))
        ** P.
  Proof.
    Local Opaque Z.add Z.mul sepconj range.
    intros; simpl.
    set (w := if Archi.ptr64 then 8 else 4).
    set (olink := align (4 * b.(bound_outgoing)) w).
    set (ocs := olink + w).
    set (ol :=  align (size_callee_save_area b ocs) 8).
    set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
    set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
    replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
    assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
    generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
    assert (0 <= 4 * b.(bound_outgoing)) by omega.
    assert (4 * b.(bound_outgoing) <= olink) by (apply align_le; omega).
    assert (olink + w <= ocs) by (unfold ocs; omega).
    assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
    assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
    assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
    assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
    (* Reorder as:
     outgoing
     back link
     callee-save
     local
     retaddr *)
    rewrite sep_swap12.
    rewrite sep_swap23.
    rewrite sep_swap45.
    rewrite sep_swap34.
    (* Apply range_split and range_split2 repeatedly *)
    unfold fe_ofs_arg.
    apply range_split_2. fold olink. omega. omega. 
    apply range_split. omega.
    apply range_split_2. fold ol. omega. omega.
    apply range_drop_right with ostkdata. omega.
    rewrite sep_swap.
    apply range_drop_left with (ostkdata + bound_stack_data b). omega.
    rewrite sep_swap. 
    exact H.
  Qed.

Lemma frame_env_separated':
  (* forall `{memory_model_prf: Mem.MemoryModel} *)
  forall b ,
    let w := if Archi.ptr64 then 8 else 4 in
    let fe := make_env b in
     let olink := align (4 * bound_outgoing b) w in
     let ocs := olink + w in
     let ol := align (size_callee_save_area b ocs) 8 in
     let ostkdata := align (ol + 4 * bound_local b) 8 in
     let oretaddr := align (ostkdata + bound_stack_data b) w in
     0 <= olink
  /\ olink + w <= ocs
  /\ ocs <= size_callee_save_area b ocs
  /\ size_callee_save_area b ocs <= ol
  /\ ol + 4 * bound_local b <= ostkdata
  /\ ostkdata + bound_stack_data b <= oretaddr
  /\ olink <= fe_stack_data fe.
Proof.
Local Opaque Z.add Z.mul sepconj range fe_stack_data.
intros; simpl.
generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
replace (size_chunk Mptr) with w by (rewrite size_chunk_Mptr; auto).
assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
assert (0 <= 4 * b.(bound_outgoing)) by omega.
assert (4 * b.(bound_outgoing) <= olink) by (apply align_le; omega).
assert (olink + w <= ocs) by (unfold ocs; omega).
assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
repeat split; auto.
omega.
Local Transparent fe_stack_data.
simpl. fold w. fold olink. fold ocs. fold ol. fold ostkdata. omega.
Qed.

Lemma frame_env_range:
  forall b,
  let fe := make_env b in
  0 <= fe_stack_data fe /\ fe_stack_data fe + bound_stack_data b <= fe_size fe.
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  generalize b.(bound_local_pos) b.(bound_outgoing_pos) b.(bound_stack_data_pos); intros.
  assert (0 <= 4 * b.(bound_outgoing)) by omega.
  assert (4 * b.(bound_outgoing) <= olink) by (apply align_le; omega).
  assert (olink + w <= ocs) by (unfold ocs; omega).
  assert (ocs <= size_callee_save_area b ocs) by (apply size_callee_save_area_incr). 
  assert (size_callee_save_area b ocs <= ol) by (apply align_le; omega).
  assert (ol + 4 * b.(bound_local) <= ostkdata) by (apply align_le; omega).
  assert (ostkdata + bound_stack_data b <= oretaddr) by (apply align_le; omega).
  split. omega. omega. 
Qed.

Lemma frame_env_aligned:
  forall b,
  let fe := make_env b in
     (8 | fe_ofs_arg)
  /\ (8 | fe_ofs_local fe)
  /\ (8 | fe_stack_data fe)
  /\ (align_chunk Mptr | fe_ofs_link fe)
  /\ (align_chunk Mptr | fe_ofs_retaddr fe).
Proof.
  intros; simpl.
  set (w := if Archi.ptr64 then 8 else 4).
  set (olink := align (4 * b.(bound_outgoing)) w).
  set (ocs := olink + w).
  set (ol :=  align (size_callee_save_area b ocs) 8).
  set (ostkdata := align (ol + 4 * b.(bound_local)) 8).
  set (oretaddr := align (ostkdata + b.(bound_stack_data)) w).
  assert (0 < w) by (unfold w; destruct Archi.ptr64; omega).
  replace (align_chunk Mptr) with w by (rewrite align_chunk_Mptr; auto).
  split. apply Zdivide_0.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  split. apply align_divides; omega.
  apply align_divides; omega.
Qed.

Lemma le_add_pos:
  forall a b,
    0 <= b ->
    a <= a + b.
Proof.
  intros; omega.
Qed.

(* fe_ofs_link fe_ofs_retaddr fe_size fe_ofs_local  fe_ofs_arg *)
(*        fe_ofs_callee_save  fe_stack_data. *)
Opaque bound_local bound_outgoing  size_callee_save_area bound_stack_data.


Program Definition frame_of_frame_env (b: bounds) : frame_info :=
  let fe := make_env b in
  {|
    frame_size := fe_size fe;
    frame_link := {| seg_ofs := (fe_ofs_link fe); seg_size := size_chunk Mptr |};
    frame_retaddr := {| seg_ofs := (fe_ofs_retaddr fe); seg_size := size_chunk Mptr |};
    frame_locals := {| seg_ofs := (fe_ofs_local fe);
                      seg_size := 4 * bound_local b |};
    frame_outgoings := {| seg_ofs := fe_ofs_arg;
                        seg_size := 4 * bound_outgoing b |};
    frame_callee_saves := {| seg_ofs := (fe_ofs_callee_save fe);
                             seg_size := size_callee_save_area b (fe_ofs_callee_save fe) - fe_ofs_callee_save fe|};
    frame_data := {| seg_ofs := fe_stack_data fe;
                     seg_size := bound_stack_data b |};
  |}.
Next Obligation.
  generalize (frame_env_separated' b).
  simpl.
  intros A.
  repeat match goal with
           H : _ /\ _ |- _ => destruct H
         end.
  unfold in_segment; simpl.
  repeat split; try easy.
  - intros. intro A. destruct A; auto.
    cut (o < o). omega.
    eapply Z.lt_le_trans. apply H6.
    etransitivity. 2: apply H7.
    etransitivity. 2: apply align_le; omega.
    etransitivity. 2: apply le_add_pos.
    etransitivity. 2: apply align_le; omega.
    omega.
    generalize (bound_local_pos b); omega.
  - intros. intro A. destruct A; auto.
    + cut (o < o). omega. 
      eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7.
      change fe_ofs_arg with 0. rewrite Z.add_0_l.
      etransitivity. 2: apply le_add_pos.
      apply align_le. destruct Archi.ptr64; omega.
      destruct Archi.ptr64; omega.
    + destruct H7; auto.
      cut (o < o). omega.
      eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7.
      change fe_ofs_arg with 0. rewrite Z.add_0_l.
      etransitivity. 2: apply align_le; omega.
      etransitivity. 2: apply le_add_pos.
      etransitivity. 2: apply align_le; omega.
      etransitivity. 2: apply size_callee_save_area_incr.
      etransitivity. 2: apply le_add_pos.
      etransitivity. 2: apply align_le. omega.
      destruct Archi.ptr64; omega.
      destruct Archi.ptr64; omega.
      generalize (bound_local_pos b); omega.
  - intros. intro A. destruct A; auto.
    + cut (o < o). omega.
      eapply Z.lt_le_trans. apply H7.
      etransitivity. 2: apply H6.
      change fe_ofs_arg with 0. rewrite Z.add_0_l.
      etransitivity. 2: apply align_le; omega.
      etransitivity. 2: apply size_callee_save_area_incr.
      etransitivity. 2: apply le_add_pos.
      etransitivity. 2: apply align_le. omega.
      destruct Archi.ptr64; omega.
      destruct Archi.ptr64; omega.
    + destruct H7; auto.
      * cut (o < o). omega.
        eapply Z.lt_le_trans. apply H7.
        etransitivity. 2: apply H6. omega.
      * destruct H7; auto.
        cut (o < o). omega.
        eapply Z.lt_le_trans. apply H6.
        etransitivity. 2: apply H7. omega.
  - intros. intro A. destruct A; auto.
    + cut (o < o). omega.
      eapply Z.lt_le_trans. apply H7.
      etransitivity. 2: apply H6. 
      etransitivity. 2: apply align_le.
      etransitivity. 2: apply le_add_pos.
      apply align_le. omega.
      generalize (bound_stack_data_pos b); omega.
      destruct Archi.ptr64; omega.
    + destruct H7; auto.
      * cut (o < o). omega.
        eapply Z.lt_le_trans. apply H7.
        etransitivity. 2: apply H6.
        change fe_ofs_arg with 0. rewrite Z.add_0_l.
        etransitivity. 2: apply align_le.
        etransitivity. 2: apply le_add_pos.
        etransitivity. 2: apply align_le.
        etransitivity. 2: apply le_add_pos.
        etransitivity. 2: apply align_le.
        etransitivity. 2: apply size_callee_save_area_incr.
        etransitivity. 2: apply le_add_pos.
        apply align_le.
        destruct Archi.ptr64; omega.
        destruct Archi.ptr64; omega. omega.
        generalize (bound_local_pos b); omega.
        omega.
        generalize (bound_stack_data_pos b); omega.
        destruct Archi.ptr64; omega.
      * destruct H7; auto.
        -- cut (o < o). omega.
           eapply Z.lt_le_trans. apply H7.
           etransitivity. 2: apply H6.
           assert (forall x y, x + (y - x) = y) by (intros; omega).
           rewrite H8.
           etransitivity. 2: apply align_le.
           etransitivity. 2: apply le_add_pos.
           etransitivity. 2: apply align_le.
           etransitivity. 2: apply le_add_pos.
           apply align_le. omega.
           generalize (bound_local_pos b); omega.
           omega.
           generalize (bound_stack_data_pos b); omega.
           destruct Archi.ptr64; omega.
        -- destruct H7; auto. 
           cut (o < o). omega.
           eapply Z.lt_le_trans. apply H7.
           etransitivity. 2: apply H6.
           apply align_le.
           destruct Archi.ptr64; omega.
  - intros. intro A.
    cut (o < o). omega.
    repeat match goal with
             H: _ \/ _ |- _ => destruct H; auto
           end.
    + eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7.

      Ltac t := repeat match goal with
             | |- ?x <= ?y + ?z => etransitivity; [| apply le_add_pos]
             | |- ?x <= align ?x ?z => apply align_le
             | |- ?x <= align ?y ?z => etransitivity; [| apply align_le]
             | |- 8 > 0 => omega
             | |- 0 <= 4 * bound_local ?b => generalize (bound_local_pos b); omega
             | |- 0 <= bound_stack_data ?b => generalize (bound_stack_data_pos b); omega
             | |- (if ?x then _ else _) > 0 => destruct x; omega
             | |- context [if Archi.ptr64 then 8 else 4] => rewrite <- size_chunk_Mptr
             | |- ?x <= size_callee_save_area _ ?x => apply size_callee_save_area_incr
             end.
      t. 
    + eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7.
      t.
    + eapply Z.lt_le_trans. apply H7.
      etransitivity. 2: apply H6.
      change fe_ofs_arg with 0. rewrite Z.add_0_l.
      t.
    + eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7. rewrite <- size_chunk_Mptr; omega.
    + eapply Z.lt_le_trans. apply H6.
      etransitivity. 2: apply H7.
      t.
    + easy.
Qed.

End WITHMEM.