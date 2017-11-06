(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.
Require Export MemPerm.
Require Export StackADT.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Lemma zle_zlt:
  forall lo hi o,
    zle lo o && zlt o hi = true <-> lo <= o < hi.
Proof.
  intros.
  destruct (zle lo o), (zlt o hi); intuition; try congruence; try omega.
Qed.

Section FORALL.

  Variables P: Z -> Prop.
  Variable f: forall (x: Z), {P x} + {~ P x}.
  Variable lo: Z.

  Program Fixpoint forall_rec (hi: Z) {wf (Zwf lo) hi}:
    {forall x, lo <= x < hi -> P x}
    + {~ forall x, lo <= x < hi -> P x} :=
    if zlt lo hi then
      match f (hi - 1) with
      | left _ =>
        match forall_rec (hi - 1) with
        | left _ => left _ _
        | right _ => right _ _
        end
      | right _ => right _ _
      end
    else
      left _ _
  .
  Next Obligation.
    red. omega.
  Qed.
  Next Obligation.
    assert (x = hi - 1 \/ x < hi - 1) by omega.
    destruct H2. congruence. auto.
  Qed.
  Next Obligation.
    intro F. apply wildcard'. intros; apply F; eauto. omega.
  Qed.
  Next Obligation.
    intro F. apply wildcard'. apply F. omega.
  Qed.
  Next Obligation.
    omegaContradiction.
  Defined.

End FORALL.


Local Notation "a # b" := (PMap.get b a) (at level 1).

Module Mem.
Export Memtype.Mem.

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Definition stack_limit: Z := 4096.

Definition in_bounds (o: Z) (bnds: Z*Z) :=
  fst bnds <= o < snd bnds.

Record mem' : Type := mkmem {
  mem_contents: PMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef;
  stack_adt:
    list frame_adt;
  stack_valid:
    forall b, in_frames stack_adt b -> Plt b nextblock;
  stack_norepet:
    nodup stack_adt;
  stack_perms:
    Forall (frame_agree_perms (fun b o k p => perm_order' ((mem_access#b) o k) p)) stack_adt;
  stack_below_limit:
    size_stack stack_adt < stack_limit;
  mem_bounds: PMap.t (Z*Z);
  mem_bounds_perm: forall b o k p,
      perm_order' ((mem_access#b) o k) p ->
      in_bounds o (mem_bounds#b)
  }.

Definition mem := mem'.

Lemma mkmem_ext:
  forall cont1 cont2 acc1 acc2 next1 next2
    a1 a2 b1 b2 c1 c2 adt1 adt2 sv1 sv2 sssl1 sssl2 stk1 stk2 stkperm1 stkperm2 bnd1 bnd2 bndpf1 bndpf2,
  cont1=cont2 -> acc1=acc2 -> next1=next2 -> adt1 = adt2 -> bnd1 = bnd2 ->
  mkmem cont1 acc1 next1 a1 b1 c1 adt1 sv1 sssl1 stk1 stkperm1 bnd1 bndpf1 =
  mkmem cont2 acc2 next2 a2 b2 c2 adt2 sv2 sssl2 stk2 stkperm2 bnd2 bndpf2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (plt b m.(nextblock)).
  auto.
  assert (m.(mem_access)#b ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. omega.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. omega.
  right; red; intros. elim n. red; intros; apply H0; omega.
  right; red; intros. elim n. apply H0. omega.
  left; red; intros. omegaContradiction.
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs)
  /\ (perm_order p Writable -> stack_access (stack_adt m) b ofs (ofs + size_chunk chunk)).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. destruct H as (A & B & C).
  split; [|split]; eauto with mem.
  intros; apply C. eapply perm_order_trans; eauto.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). omega.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). omega.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  destruct H3. split. 
  - eapply Zdivide_trans; eauto. eapply align_le_divides; eauto.
  - rewrite <- H. auto.
Qed.

Lemma non_writable_private_stack_access_dec : forall p m b ofs chunk,
  {(perm_order p Writable -> stack_access m b ofs (ofs + size_chunk chunk))}
  + {~ (perm_order p Writable -> stack_access m b ofs (ofs + size_chunk chunk))}.
Proof.
  intros.
  destruct (perm_order_dec p Writable);
  destruct (stack_access_dec m b ofs (ofs + size_chunk chunk)); auto.
  left. intros. congruence.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p);
  destruct (Zdivide_dec (align_chunk chunk) ofs (align_chunk_pos chunk));
  destruct (non_writable_private_stack_access_dec p (stack_adt m) b ofs chunk);
  try now (right; red; intro V; inv V; destruct H0; contradiction).
  left; constructor; auto.
Qed.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by omega. auto.
  split. simpl. apply Zone_divide.
  intros. inversion H0.
  destruct H. apply H. simpl. omega.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

Lemma stack_perm m:
  Forall (frame_agree_perms (perm m)) (stack_adt m).
Proof.
  eapply Forall_impl.
  2: apply stack_perms.
  unfold frame_agree_perms. unfold perm. tauto.
Qed.

Hint Resolve stack_norepet stack_perm.

Program Definition empty: mem :=
  mkmem (PMap.init (ZMap.init Undef))
        (PMap.init (fun ofs k => None))
        1%positive _ _ _ nil _ _ _ _ (PMap.init (0,0)) _.
Next Obligation.
  repeat rewrite PMap.gi. red; auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  rewrite PMap.gi. auto.
Qed.
Next Obligation.
  easy.
Qed.
Next Obligation.
  constructor.
Qed.
Next Obligation.
  unfold stack_limit. omega.
Qed. 
Next Obligation.
  rewrite PMap.gi in H. inv H.
Qed.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)

Program Definition alloc (m: mem) (lo hi: Z) : (mem * block) :=
  (mkmem (PMap.set m.(nextblock)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (PMap.set m.(nextblock)
                   (fun ofs k => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                   m.(mem_access))
         (Psucc m.(nextblock))
         _ _ _ 
         (stack_adt m) _ _ _ _ (PMap.set m.(nextblock) (lo,hi) m.(mem_bounds)) _,
   m.(nextblock)).
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. destruct (zle lo ofs && zlt ofs hi); red; auto with mem.
  apply access_max.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)).
  subst b. elim H. apply Plt_succ.
  apply nextblock_noaccess. red; intros; elim H.
  apply Plt_trans_succ; auto.
Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b (nextblock m)). auto. apply contents_default.
Qed.
Next Obligation.
  apply stack_valid in H. xomega.
Qed.
Next Obligation.
  generalize (stack_perm m). rewrite ! Forall_forall.
  intros F x IN.
  red; intros.
  eapply F; eauto.
  rewrite PMap.gso in H0; eauto.
  intro; subst. 
  exploit in_frames_in_frame; eauto.
  intro INS. apply stack_valid in INS.
  xomega.
Qed.
Next Obligation.
  apply stack_below_limit.
Qed.
Next Obligation.
  rewrite PMap.gsspec in *.
  destr. destr_in H. apply zle_zlt in Heqb0. red. simpl. auto.
  inv H.
  eapply mem_bounds_perm; eauto.
Qed.

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (PMap.set b
                (fun ofs k => if zle lo ofs && zlt ofs hi then None else m.(mem_access)#b ofs k)
                m.(mem_access))
        m.(nextblock) _ _ _ (stack_adt m) _ _ _ _ m.(mem_bounds) _.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b).
  destruct (zle lo ofs && zlt ofs hi). red; auto. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst.
  destruct (zle lo ofs && zlt ofs hi). auto. apply nextblock_noaccess; auto.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply stack_valid; auto.
Qed.
Next Obligation.
  generalize (stack_perm m). rewrite ! Forall_forall.
  intros F x IN.
  red; intros.
  eapply F; eauto.
  rewrite PMap.gsspec in H0; eauto.
  destr_in H0; eauto. subst.
  destr_in H0; eauto. inv H0.
Qed.
Next Obligation.
  apply stack_below_limit.
Qed. 
Next Obligation.
  rewrite PMap.gsspec in *. repeat destr_in H. subst.
  eapply mem_bounds_perm; eauto.
  eapply mem_bounds_perm; eauto.
Qed.

Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN (n: nat) (p: Z) (c: ZMap.t memval) {struct n}: list memval :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (nat_of_Z n) ofs (m.(mem_contents)#b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN (vl: list memval) (p: Z) (c: ZMap.t memval) {struct vl}: ZMap.t memval :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall vl c p q,
  (forall r, p <= r < p + Z_of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite inj_S in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. omega.
  apply ZMap.gso. apply not_eq_sym. apply H. omega.
Qed.

Remark setN_outside:
  forall vl c p q,
  q < p \/ q >= p + Z_of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. omega.
Qed.

Remark getN_setN_same:
  forall vl p c,
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. omega.
  apply IHvl.
Qed.

Remark getN_exten:
  forall c1 c2 n p,
  (forall i, p <= i < p + Z_of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite inj_S in H. simpl. decEq.
  apply H. omega. apply IHn. intros. apply H. omega.
Qed.

Remark getN_setN_disjoint:
  forall vl q c n p,
  Intv.disjoint (p, p + Z_of_nat n) (q, q + Z_of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark getN_setN_outside:
  forall vl q c n p,
  p + Z_of_nat n <= q \/ q + Z_of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

Remark setN_default:
  forall vl q c, fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (PMap.set b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(nextblock)
                _ _ _ (stack_adt m) _ _ _ _ m.(mem_bounds) _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  destruct m; eauto.
Qed. 
Next Obligation.
  destruct m; auto. 
Qed.
Next Obligation.
  apply stack_below_limit.
Qed.
Next Obligation.
  eapply mem_bounds_perm; eauto.
Qed.


(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z_of_nat (length bytes)) Cur Writable then
    if stack_access_dec (stack_adt m) b ofs (ofs + Z_of_nat (length bytes)) then
    Some (mkmem
             (PMap.set b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(nextblock)
                 _ _ _ (stack_adt m) _ _ _ _ m.(mem_bounds) _)
    else None
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation.
  apply stack_valid; auto.
Qed.
Next Obligation.
  destruct m; auto. 
Qed.
Next Obligation.
  apply stack_below_limit.
Qed.
Next Obligation.
  eapply mem_bounds_perm; eauto.
Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (PMap.set b
                        (fun ofs k => if zle lo ofs && zlt ofs hi then Some p else m.(mem_access)#b ofs k)
                        m.(mem_access))
                m.(nextblock) _ _ _ (stack_adt m) _ _ _ _ m.(mem_bounds) _)
  else None.
Next Obligation.
  repeat rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs && zlt ofs hi). red; auto with mem. apply access_max.
  apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros.
  rewrite PMap.gsspec. destruct (peq b0 b). subst b0.
  destruct (zle lo ofs). destruct (zlt ofs hi).
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto.
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply stack_valid; auto.
Qed.
Next Obligation.
  generalize (stack_perm m). rewrite ! Forall_forall.
  intros F x IN.
  red; intros.
  rewrite PMap.gsspec in H1. destr_in H1; eauto.
  - subst. destr_in H1. eapply F; eauto. 
    apply H. apply zle_zlt; auto.
    eapply F; eauto.
  - eapply F; eauto.
Qed.
Next Obligation.
  apply stack_below_limit.
Qed.
Next Obligation.
  rewrite PMap.gsspec in H0.
  destr_in H0. destr_in H0. subst. eapply mem_bounds_perm; eauto. apply H.
  apply zle_zlt; auto.
  subst. eapply mem_bounds_perm; eauto.
  eapply mem_bounds_perm; eauto.
Qed.

Record mem_inj {injperm: InjectPerm} (f: meminj) (g: frameinj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      inject_perm_condition p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2);
    mi_stack_blocks:
      stack_inject f g (perm m1) (stack_adt m1) (stack_adt m2);
  }.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' {injperm: InjectPerm} (m1 m2: mem) : Prop :=
  mk_extends {
    mext_next: nextblock m1 = nextblock m2;
    mext_inj:  mem_inj inject_id (flat_frameinj (length (stack_adt m1))) m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty;
    mext_length_stack:
      length (stack_adt m2) = length (stack_adt m1);
  }.

Definition extends {injperm: InjectPerm} := extends'.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Record inject' {injperm: InjectPerm} (f: meminj) (g: frameinj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_inj:
      mem_inj f g m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta,
      f b = Some(b', delta) ->
      delta >= 0
      /\
      forall ofs,
        perm m1 b (Ptrofs.unsigned ofs) Max Nonempty
        \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
        0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
Definition inject {injperm: InjectPerm} := inject'.

Local Hint Resolve mi_mappedblocks: mem.


(** The [magree] predicate is a variant of [extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation. *)

Definition locset := block -> Z -> Prop.

Record magree' {injperm: InjectPerm} (m1 m2: mem) (P: locset) : Prop := mk_magree {
  ma_perm:
    forall b ofs k p,
      perm m1 b ofs k p -> inject_perm_condition p -> perm m2 b ofs k p;
  ma_perm_inv:
    forall b ofs k p,
      perm m2 b ofs k p -> perm m1 b ofs k p \/ ~ perm m1 b ofs Max Nonempty;
  ma_memval:
    forall b ofs,
    perm m1 b ofs Cur Readable ->
    P b ofs ->
    memval_lessdef (ZMap.get ofs (PMap.get b (mem_contents m1)))
                   (ZMap.get ofs (PMap.get b (mem_contents m2)));
  ma_nextblock:
    nextblock m2 = nextblock m1;
  ma_stack_adt:
    stack_inject inject_id (flat_frameinj (length (stack_adt m1))) (perm m1) (stack_adt m1) (stack_adt m2);
  ma_length_stack:
    length (stack_adt m2) = length (stack_adt m1);
}.

Definition magree {injperm: InjectPerm} := magree'.

(** Injecting a memory into itself. *)

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition inject_neutral {injperm: InjectPerm} (thr: block) (m: mem) :=
  mem_inj (flat_inj thr) (flat_frameinj (length (stack_adt m))) m m.

Record unchanged_on' (P: block -> Z -> Prop) (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_nextblock:
    Ple (nextblock m_before) (nextblock m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (PMap.get b m_after.(mem_contents)) =
    ZMap.get ofs (PMap.get b m_before.(mem_contents));
}.

Definition unchanged_on := unchanged_on'.

Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

Definition valid_block_dec m b: { valid_block m b } + { ~ valid_block m b }.
Proof.
  apply plt.
Qed.

Definition valid_block_dec_eq m b: { forall b0, b0 = b -> valid_block m b0 } + { ~ (forall b0, b0 = b -> valid_block m b0) }.
Proof.
  destruct (valid_block_dec m b); [left|right].
  intros; subst; auto.
  intro X; apply n. apply X; auto.
Qed.

Definition valid_block_list_dec m l:  { forall b, In b l -> valid_block m b } + { ~ (forall b, In b l -> valid_block m b) }.
Proof.
  induction l; simpl; intros.
  left; tauto.
  destruct IHl, (valid_block_dec m a); intuition.
  left; intros; intuition subst; auto.
Qed.

Definition valid_frame_dec f m: { valid_frame f m } + { ~ valid_frame f m }.
Proof.
  unfold valid_frame; simpl; auto.
  apply valid_block_list_dec.
Qed.

Definition sumbool_not {A} (x: {A} + {~A}): {~A} + {~ (~A)}.
Proof.
  destruct x. right; intro NA. apply NA. apply a.
  left; auto.
Defined.

Definition in_bounds_inside (orng: option (Z*Z)) (z1 z2: Z) : Prop :=
  match orng with
    Some (lo, hi) => lo <= z1 /\ z2 <= hi
  | None => True
  end.

Lemma in_bounds_inside_dec:
  forall (o: option Z) (p: Z * Z),
    { in_bounds_inside (option_map (fun x => (0,x)) o) (fst p) (snd p) } + { ~ in_bounds_inside (option_map (fun x => (0,x)) o) (fst p) (snd p) }.
Proof.
  intros.
  destruct p as (z1 & z2).
  unfold in_bounds_inside; destruct o; simpl; auto.
  destruct (zle 0 z1); [|right; intros (A & B); omega].
  destruct (zle z2 z); [left; omega |right; intros (A & B); omega].
Qed.

Definition eq_bounds (orng: option (Z*Z)) (z1 z2: Z) : Prop :=
  match orng with
    Some (lo, hi) => lo = z1 /\ z2 = hi
  | None => True
  end.

Lemma eq_bounds_dec:
  forall (o: option Z) (p: Z * Z),
    { eq_bounds (option_map (fun x => (0,x)) o) (fst p) (snd p) } + { ~ eq_bounds (option_map (fun x => (0,x)) o) (fst p) (snd p) }.
Proof.
  intros.
  destruct p as (z1 & z2).
  unfold eq_bounds; destruct o; simpl; auto.
  destruct (zeq 0 z1); [|right; intros (A & B); omega].
  destruct (zeq z2 z); [left; omega |right; intros (A & B); omega].
Qed.


Lemma nodup_add:
  forall s f,
    nodup s ->
    Forall (fun x => ~ in_frames s x) (frame_blocks f) ->
    nodup (f::s).
Proof.
  intros.
  constructor; auto. intros. rewrite Forall_forall in H0.
  intro INS. eapply H0; eauto.
Qed.

Lemma valid_frames_add:
  forall s f thr,
    (forall b, in_frames s b -> Plt b thr) ->
    (forall b, in_frame f b -> Plt b thr) ->
    forall b : block, in_frames (f :: s) b -> Plt b thr.
Proof.
  simpl; intros; intuition.
Qed.

Lemma frame_agree_perms_add:
  forall f s m,
    Forall
      (frame_agree_perms
         (fun (b : block) (o : Z) (k : perm_kind) (p : permission) => perm_order' ((mem_access m) # b o k) p))
      s ->
    Forall (fun b => forall o k p, Mem.perm m b o k p ->
                           forall fi, frame_adt_info f = Some fi ->
                                 0 <= o < frame_size fi)%Z (frame_blocks f) ->
    Forall
      (frame_agree_perms
         (fun (b : block) (o : Z) (k : perm_kind) (p : permission) => perm_order' ((mem_access m) # b o k) p))
      (f :: s).
Proof.
  intros.
  constructor; auto.
  red; intros.
  rewrite Forall_forall in H0. destr. eapply H0 in H1; eauto.
Qed.

Lemma size_stack_add:
  forall f s
    (SZ: (size_stack s + align (Z.max 0 (frame_adt_size f)) 8 < stack_limit)%Z),
    size_stack (f :: s) < stack_limit.
Proof.
  simpl. intros. destruct f, p. tauto.
Qed.

(* Lemma in_bounds_dec (o lo hi: Z): { lo <= o < hi } + { ~ (lo <= o < hi) }. *)
(* Proof. *)
(*   intros. *)
(*   destruct (zle lo o), (zlt o hi); try (right; omega); left; omega. *)
(* Qed. *)


(*   Lemma in_bounds_option_dec (o : Z) (bnds: option (Z*Z)): { forall lo hi, bnds = Some (lo, hi) -> lo <= o < hi } + { ~ forall lo hi, bnds = Some (lo, hi) -> lo <= o < hi  }. *)
(*   Proof. *)
(*     intros. *)
(*     destruct bnds. 2: left; intros; congruence. *)
(*     destruct p. *)
(*     destruct (zle z o), (zlt o z0); try (    right; intro A; specialize (A _ _ eq_refl); omega). *)
(*     left; inversion 1; subst; simpl in *; omega. *)
(*   Qed. *)

  (* Definition check_bound bl fi m := *)
  (*   Forall_dec *)
  (*     _ *)
  (*     (fun b => *)
  (*        forall_rec *)
  (*          _ *)
  (*          (fun o => *)
  (*             in_bounds_option_dec o *)
  (*                                  (option_map (fun x => (0,x)) (option_map frame_size (frame_adt_info fi)))) *)
  (*                              (fst (m.(mem_bounds) #b)) (snd (m.(mem_bounds) #b)) *)
  (*                ) *)
  (*                bl. *)
  
(* Program Definition record_stack_blocks_exec (m: mem) (f: frame_adt): option mem := *)
(*   if (valid_frame_dec f m) *)
(*   then if (Forall_dec _ (fun x => sumbool_not (in_frames_dec (stack_adt m) x)) (frame_blocks f)) *)
(*        then if  *)
(*             check_bound (frame_blocks f) f m *)
(*             then if (zlt (size_stack (stack_adt m) + align (Z.max 0 (frame_adt_size f)) 8) stack_limit) *)
(*                  then Some *)
(*                         (mkmem (mem_contents m) *)
(*                                (mem_access m) *)
(*                                (nextblock m) *)
(*                                (access_max m) *)
(*                                (nextblock_noaccess m) *)
(*                                (contents_default m) *)
(*                                (f :: stack_adt m) *)
(*                                (valid_frames_add _ _ _ (stack_valid m) _) *)
(*                                (nodup_add _ _ (stack_norepet m) _) *)
(*                                (frame_agree_perms_add _ _ _ (stack_perm m) _) *)
(*                                (size_stack_add _ _ _) *)
(*                                (mem_bounds m) *)
(*                                _) *)
(*                  else None *)
(*             else None *)
(*        else None *)
(*   else None. *)
(* Next Obligation. *)
(*   eapply H; eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   rewrite Forall_forall in H1 |- *. *)
(*   intros. *)
(*   eapply H1; eauto. eapply mem_bounds_perm in H4. auto. rewrite H5.  simpl. auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   eapply mem_bounds_perm; eauto. *)
(* Qed. *)

Inductive record_stack_blocks (m: mem) (f: frame_adt) : mem -> Prop :=
| rsb_intro:
    forall (VF:valid_frame f m)
      (NOTIN: Forall (fun x => ~ in_frames (stack_adt m) x) (frame_blocks f))
      (RNG: Forall (fun b => forall o k p, Mem.perm m b o k p ->
                                   forall fi, frame_adt_info f = Some fi ->
                                         0 <= o < frame_size fi)%Z (frame_blocks f))
      (SZ: (size_stack (stack_adt m) + align (Z.max 0 (frame_adt_size f)) 8 < stack_limit)%Z),
      record_stack_blocks m f (mkmem (mem_contents m)
                         (mem_access m)
                         (nextblock m)
                         (access_max m)
                         (nextblock_noaccess m)
                         (contents_default m)
                         (f :: stack_adt m)
                         (valid_frames_add _ _ _ (stack_valid m) VF)
                         (nodup_add _ _ (stack_norepet m) NOTIN)
                         (frame_agree_perms_add _ _ _ (stack_perm m) RNG)
                         (size_stack_add _ _ SZ)
                         (mem_bounds m)
                         (mem_bounds_perm m)).

Program Definition record_stack_blocks_none (m: mem) bl sz : option mem :=
  if (valid_frame_dec (bl,None,sz) m)
  then if (Forall_dec _ (fun x => sumbool_not (in_frames_dec (stack_adt m) x)) bl)
       then if (zlt (size_stack (stack_adt m) + align (Z.max 0 sz) 8) stack_limit)
            then Some
                   (mkmem (mem_contents m)
                          (mem_access m)
                          (nextblock m)
                          (access_max m)
                          (nextblock_noaccess m)
                          (contents_default m)
                          ((bl,None,sz) :: stack_adt m)
                          (valid_frames_add _ _ _ (stack_valid m) _)
                          (nodup_add _ _ (stack_norepet m) _)
                          (frame_agree_perms_add _ _ _ (stack_perm m) _)
                          (size_stack_add _ _ _)
                          (mem_bounds m)
                          _)
            else None
       else None
  else None.
Next Obligation.
  eapply H; eauto.
Qed.
Next Obligation.
  rewrite Forall_forall; congruence.
Qed.
Next Obligation.
  eapply mem_bounds_perm; eauto.
Qed.

Lemma record_stack_blocks_ext:
  forall m1 fi m2 m2',
    record_stack_blocks m1 fi m2 ->
    m2 = m2' ->
    record_stack_blocks m1 fi m2'.
Proof.
  intros; subst; congruence.
Qed.

Lemma record_stack_blocks_none_correct:
  forall m bl sz m',
    record_stack_blocks_none m bl sz = Some m' <->
    record_stack_blocks m (bl,None,sz) m'.
Proof.
  unfold record_stack_blocks_none.
  split; intros.
  - repeat destr_in H.
    eapply record_stack_blocks_ext. econstructor. apply mkmem_ext; auto.
    Unshelve.
    simpl; auto. rewrite Forall_forall; simpl; intros. congruence.
    simpl. auto. auto. 
  - inv H.
    repeat destr. f_equal. apply mkmem_ext; auto.
    simpl in *; omega.
    exfalso; apply n. auto.
Qed.

Fixpoint do_stores (m: mem) (l: list (memory_chunk * val * val)) : option mem :=
  match l with
    nil => Some m
  | (k,addr,v)::r =>
    match storev k m addr v with
      Some m1 => do_stores m1 r
    | None => None
    end
  end.

Lemma do_stores_nextblock :
  forall l m m',
    do_stores m l = Some m' ->
    nextblock m' = nextblock m.
Proof.
  induction l; simpl; intros.
  congruence. repeat destr_in H.
  destruct v0; simpl in *; try congruence.
  assert (nextblock m1 = nextblock m). unfold store in Heqo. repeat destr_in Heqo. reflexivity.
  rewrite <- H. eauto.
Qed.

Lemma do_stores_stack_adt :
  forall l m m',
    do_stores m l = Some m' ->
    stack_adt m' = stack_adt m.
Proof.
  induction l; simpl; intros.
  congruence. repeat destr_in H.
  destruct v0; simpl in *; try congruence.
  unfold store in Heqo. repeat destr_in Heqo.
  eapply IHl in H1; eauto.
Qed.

Lemma do_stores_perm_inv:
  forall l m m',
    do_stores m l = Some m' ->
    forall b o k p,
      perm m' b o k p ->
      perm m b o k p.
Proof.
  induction l; simpl; intros.
  congruence. repeat destr_in H.
  destruct v0; simpl in *; try congruence.
  unfold store in Heqo0. repeat destr_in Heqo0.
  eapply IHl in H0. 2: eauto.
  apply H0.
Qed.


Program Definition push_frame (m0: mem) (fi: frame_info) (l: list (memory_chunk * ptrofs * val))  : option (mem*block) :=
  match alloc m0 0 (frame_size fi) with
    (m,b) =>
    match do_stores m (store_spec_of_ofs_spec b l) with
      Some m =>
      if (zlt (size_stack (stack_adt m) + align (Z.max 0 (frame_size fi)) 8) stack_limit)
      then Some (mkmem (mem_contents m)
                       (mem_access m)
                       (nextblock m)
                       (access_max m)
                       (nextblock_noaccess m)
                       (contents_default m)
                       ((b::nil,Some fi,frame_size fi) :: stack_adt m)
                       (valid_frames_add _ _ _ (stack_valid m) _)
                       (nodup_add _ _ (stack_norepet m) _)
                       (frame_agree_perms_add _ _ _ (stack_perm m) _)
                       (size_stack_add _ _ _)
                       (mem_bounds m)
                       (mem_bounds_perm m),b)
      else None
    | None => None
    end
  end.
Next Obligation.
  simpl in *. red in H0. simpl in H0. destruct H0; try easy. subst.
  symmetry in Heq_anonymous. apply do_stores_nextblock in Heq_anonymous. simpl in *. rewrite Heq_anonymous. xomega.
Qed.
Next Obligation.
  simpl. constructor; auto.
  symmetry in Heq_anonymous. apply do_stores_stack_adt in Heq_anonymous. simpl in *. rewrite Heq_anonymous.
  intro INF. apply stack_valid in INF. xomega.
Qed.
Next Obligation.
  constructor; auto.
  intros. eapply do_stores_perm_inv in H0. 2: eauto. red in H0. simpl in H0. inv H1. 
  rewrite PMap.gss in H0. destr_in H0. 2: now inv H0.
  apply zle_zlt. auto.
Qed.


Lemma push_frame_alloc_record:
  forall m1 b fi l m4,
    push_frame m1 fi l = Some (m4,b) ->
    exists m2,
      alloc m1 0 (frame_size fi) = (m2, b) /\
      exists m3,
      do_stores m2 (store_spec_of_ofs_spec b l) = Some m3 /\
      record_stack_blocks m3 (b::nil,Some fi,frame_size fi) m4.
Proof.
  unfold push_frame. intros.
  simpl in *. 
  repeat destr_in H. simpl in *.
  unfold alloc. eexists;  split.
  eauto.
  (* intros. eexists; split. eauto.
  simpl in H1. setoid_rewrite H in H1.
  repeat destr_in H1.
  eapply record_stack_blocks_ext. econstructor.
  apply mkmem_ext; try reflexivity.
  Unshelve. simpl. auto.
  constructor; auto. unfold perm. simpl; intros. rewrite PMap.gss in H. destr_in H.
  inv H0. eapply zle_zlt; auto.
  inv H.
  constructor; auto. simpl.   intro INF. apply stack_valid in INF. xomega.
  red; unfold in_frame. intros ? [?|[]]; subst.
  red; simpl. xomega.*)
Admitted.

Lemma alloc_record_push_frame:
  forall m1 m2 b fi l m3 m4,
    alloc m1 0 (frame_size fi) = (m2, b) ->
    do_stores m2 (store_spec_of_ofs_spec b l) = Some m3 ->
    record_stack_blocks m3 (b::nil,Some fi,frame_size fi) m4 ->
    push_frame m1 fi l = Some (m4,b).
Proof.
  unfold push_frame. intros.
  unfold alloc in H. inv H. simpl. 
  (*destr.
  f_equal. apply mkmem_ext; auto.*)
Admitted.


Lemma record_stack_block_det:
  forall m f m1 m2,
    record_stack_blocks m f m1 ->
    record_stack_blocks m f m2 ->
    m1 = m2.
Proof.
  intros m f m1 m2 H H0. inv H; inv H0. 
  apply mkmem_ext; auto.
Qed.

(* Program Definition record_stack_blocks (m: mem) (f: frame_adt): option mem := *)
(*   if valid_frame_dec f m *)
(*   then *)
(*     if Forall_dec _ (fun x => sumbool_not (in_frames_dec (stack_adt m) x)) (frame_blocks f) *)
(*     then *)
(*       if Forall_dec _ (fun b => eq_bounds_dec (option_map frame_size (frame_adt_info f)) ((block_bounds m) # b)) *)
(*                    (frame_blocks f) *)
(*       then  *)
(*         if zlt (size_stack (stack_adt m) + align (Z.max 0 (frame_adt_size f)) 8) stack_limit *)
(*         then Some (mkmem (mem_contents m) *)
(*                          (mem_access m) *)
(*                          (nextblock m) *)
(*                          (access_max m) *)
(*                          (nextblock_noaccess m) *)
(*                          (contents_default m) *)
(*                          (block_bounds m) *)
(*                          _ *)
(*                          (f :: stack_adt m) *)
(*                          _ _ _ _) *)
(*         else None *)
(*       else None *)
(*     else None *)
(*   else None. *)
(* Next Obligation. *)
(*   eapply perm_bounds. eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   generalize stack_valid. intro.  *)
(*   destruct H3; eauto. apply H in H3; auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor. eapply stack_norepet. *)
(*   unfold in_frame. rewrite <- Forall_forall. *)
(*   auto. *)
(* Qed. *)
(* Next Obligation. *)
(*   constructor; auto. 2:destruct m; auto. *)
(*   red; intros. *)
(*   rewrite Forall_forall in H1. *)
(*   specialize (H1 _ H3). *)
(*   apply perm_bounds in H4. *)
(*   destr. simpl in H1. *)
(*   red in H4. omega.   *)
(* Qed. *)
(* Next Obligation. *)
(*   repeat destr. *)
(* Qed. *)

Lemma in_frames_tl:
  forall (l: list frame_adt)  b,
    in_frames ((tl l)) b ->
    in_frames (l) b.
Proof.
  destruct l; simpl; auto.
Qed.

Lemma size_stack_tl:
  forall l,
    size_stack (tl l) <= size_stack l.
Proof.
  induction l; simpl; intros. omega.
  destruct a,p.
  generalize (align_le (Z.max 0 z) 8) (Z.le_max_l 0 z); omega.
Qed.

Lemma Forall_tl:
  forall {A} P (l: list A),
    Forall P l ->
    Forall P (tl l).
Proof.
  induction 1; simpl; auto.
Qed.

Definition unrecord_stack_block (m: mem) : option mem :=
  match stack_adt m with
    nil => None
  | a::r => Some ((mkmem (mem_contents m)
                   (mem_access m)
                   (nextblock m)
                   (access_max m)
                   (nextblock_noaccess m)
                   (contents_default m)
                   (tl (stack_adt m))
                   (fun b pf => stack_valid m b (in_frames_tl _ _ pf))
                   (nodup_tl _ (stack_norepet m))
                   (Forall_tl _ _ (stack_perms m)) 
                   (Z.le_lt_trans _ _ _ (size_stack_tl _) (stack_below_limit m))
                   (mem_bounds m)
                   (mem_bounds_perm m)
                 ))
          end.

Ltac unfold_unrecord' H m :=
  unfold unrecord_stack_block in H;
  let A := fresh in
  case_eq (stack_adt m); [
    intro A
  | intros ? ? A
  ]; setoid_rewrite A in H; inv H.
Ltac unfold_unrecord :=
  match goal with
    H: unrecord_stack_block ?m = _ |- _ => unfold_unrecord' H m
  end.


Lemma and_dec: forall {A B: Prop},
    A ->
    {B} + {~B} ->
    { A /\ B } + { ~ (A /\ B) }.
Proof.
  intros. destruct H0; [left|right]; intuition.
Qed.

Lemma in_segments_dec:
  forall l x,
    {in_segments x l} + {~in_segments x l}.
Proof.
  induction l; simpl; intros; eauto.
  destruct (in_segment_dec x a).
  left; auto.
  edestruct (IHl x);[left|right]; intuition.
Qed.

Lemma disjoint_dec:
  forall l,
    {segments_disjoint l} + {~segments_disjoint l}.
Proof.
  induction l; simpl; intros; eauto.
  destruct IHl.
  apply and_dec; auto.
  apply forall_rec.
  intros.
  destruct (in_segments_dec l x); [right|left]; auto.
  right; intuition.
Qed.

Lemma in_segment_in_segments:
  forall l x i,
    In x l ->
    in_segment i x ->
    in_segments i l.
Proof.
  induction l; simpl; intros; eauto.
  destruct H; subst; eauto.
Qed.

(* returns f1 augmented with f2, at offset delta *)
Program Definition insert_frame_info delta (f1 f2: frame_info): option frame_info:=
  if zle 0 delta
  then if zlt (frame_size f2 + delta) (frame_size f1)
       then
         if disjoint_dec ({| seg_ofs := delta; seg_size := frame_size f2 |}::frame_link f1)
         then
           Some {|
               frame_size := frame_size f1;
               frame_link := frame_link f1 ++ (map (fun fl => {| seg_ofs := seg_ofs fl + delta; seg_size := seg_size fl |}) (frame_link f2));
               frame_perm := fun o => if zle delta o && zlt o (frame_size f2 + delta) then frame_perm f2 (o - delta) else frame_perm f1 o
             |}
         else None
       else None
  else None.
Next Obligation.
  rewrite Forall_forall. intros x IN. rewrite in_app in IN.
  destruct IN as [IN|IN].
  generalize (frame_link_size f1). rewrite Forall_forall. eauto.
  generalize (frame_link_size f2). rewrite Forall_forall. intros A.
  rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst. simpl. eauto.
Qed.
Next Obligation.
  rewrite Forall_forall. intros x IN. rewrite in_app in IN.
  destruct IN as [IN|IN]. generalize (frame_link_rng f1); eauto. rewrite Forall_forall; eauto.
  rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst. simpl in *. 
  generalize (frame_link_rng f2); eauto. rewrite Forall_forall; eauto.
  intros A o RNG.
  specialize (A _ IN (o - delta)). trim A. omega.
  omega.
Qed.
Next Obligation.
  rewrite Forall_forall. intros x IN. rewrite in_app in IN. 
  destruct IN as [IN|IN].
  - (* link of original frame *)
    intros i INS.
    destr.
    + apply zle_zlt in Heqb.
      specialize (H2 i). trim H2. red. simpl. omega. exfalso; apply H2.
      eapply in_segment_in_segments; eauto.
    + generalize (frame_link_readonly f1). rewrite Forall_forall. eauto.
  - (* link in new frame *)
    rewrite in_map_iff in IN. destruct IN as (x0 & EQ & IN). subst. 
    unfold in_segment. simpl.
    intros i INS.
    destr.
    + apply zle_zlt in Heqb.
      generalize (frame_link_readonly f2). rewrite Forall_forall. intros A.
      eapply A. eauto. red. omega.
    + generalize (frame_link_rng f2); rewrite Forall_forall; intro A.
      specialize (A _ IN (i - delta)). trim A. omega.
      assert ( ~ (delta <= i < frame_size f2 + delta)). rewrite <- zle_zlt. congruence. omega.
Qed.

Lemma insert_frame_info_size:
  forall delta f1 f2 f3,
    insert_frame_info delta f1 f2 = Some f3 ->
    frame_size f1 = frame_size f3.
Proof.
  unfold insert_frame_info. intros.
  repeat destr_in H. reflexivity.
Qed.

Program Definition update_top_stack_adt (m: mem) (newfi: frame_info) (delta : Z) : option mem :=
  match stack_adt m with
  | (bl, Some fi,sz)::r =>
    match insert_frame_info delta fi newfi with
      Some fi' =>
      Some (mkmem
              m.(mem_contents)
                  m.(mem_access)
                      m.(nextblock)
                          m.(access_max) m.(nextblock_noaccess) m.(contents_default) 
                          ((bl,Some fi',sz)::r) _ _ _ _ m.(mem_bounds) m.(mem_bounds_perm))
    | _ => None
    end
  | _ => None
  end.
Next Obligation.
  generalize (stack_valid m b). rewrite <- Heq_anonymous0. simpl. eauto.
Qed.
Next Obligation.
  generalize (stack_norepet m). rewrite <- Heq_anonymous0.
  inversion 1; constructor; auto.
Qed.
Next Obligation.
  generalize (stack_perms m). rewrite <- Heq_anonymous0.
  inversion 1; constructor; auto.
  red. simpl; intros.
  red in H2. simpl in H2. subst. eapply H2 in H5; eauto.
  erewrite insert_frame_info_size in H5; eauto.
Qed.
Next Obligation.
  generalize (stack_below_limit m). rewrite <- Heq_anonymous0.
  simpl. auto.
Qed.

Local Instance memory_model_ops :
  MemoryModelOps mem.
Proof.
  esplit.
  exact empty.
  exact alloc.
  exact free.
  exact load.
  exact store.
  exact loadbytes.
  exact storebytes.
  exact drop_perm.
  exact nextblock.
  exact perm.
  exact valid_pointer.
  exact @extends.
  exact @magree.
  exact @inject.
  exact @inject_neutral.
  exact unchanged_on.
  exact unchanged_on.
  exact stack_adt.
  exact record_stack_blocks.
  exact push_frame.
  exact record_stack_blocks_none.
  exact unrecord_stack_block.
  exact stack_limit.
  exact update_top_stack_adt.
Defined.

Section WITHINJPERM.
Context {injperm: InjectPerm}.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)

Theorem nextblock_empty: nextblock empty = 1%positive.
Proof. reflexivity. Qed.

Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. rewrite PMap.gi. simpl. tauto.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); omega.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; [|split]; auto.
  inversion 1.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.

Lemma getN_length:
  forall c n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite nat_of_Z_neg; auto.
  red; intros. omegaContradiction.
Qed.

Lemma getN_concat:
  forall c n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z_of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. omega.
  rewrite inj_S. simpl. decEq.
  replace (p + Zsucc (Z_of_nat n1)) with ((p + 1) + Z_of_nat n1) by omega.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite nat_of_Z_plus; auto.
  rewrite getN_concat. rewrite nat_of_Z_eq; auto.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by omega.
  destruct H4. apply r; omega. apply r0; omega.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite nat_of_Z_plus in H; auto. rewrite getN_concat in H.
  rewrite nat_of_Z_eq in H; auto.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; omega.
  red; intros; apply r; omega.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite inj_S in H.
  replace ofs with (ofs+0) by omega.
  apply H; omega.
  apply IHn.
  intros.
  rewrite <- Zplus_assoc.
  apply H.
  rewrite inj_S. omega.
Qed.

Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A [B C]]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. omega. omega.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Zdivides_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4. 
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  omega. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. omega.
Qed.

Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add. rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_valid_access. eexact H2. intros [P [Q R]]. auto. } 
  exists v1; exists v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store' :
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  exists m2: mem, store chunk m1 b ofs v = Some m2 .
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Qed.

Local Hint Resolve valid_access_store': mem.

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros m1 chunk b ofs v H.
  destruct (store _ _ _ _ _) eqn:STORE; eauto.
  exfalso.
  apply @valid_access_store' with (v := v) in H; auto.
  destruct H.
  congruence.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = PMap.set b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.
 
Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_stack_access_1: forall b lo hi,
  stack_access (stack_adt m1) b lo hi -> stack_access (stack_adt m2) b lo hi.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_stack_access_2: forall b lo hi,
  stack_access (stack_adt m2) b lo hi -> stack_access (stack_adt m1) b lo hi.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Local Hint Resolve store_stack_access_1 store_stack_access_2 : mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. destruct H as (A & B & C).
  split; [|split]; try solve [red; auto with mem].
  auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. destruct H as (A & B & C).
  split; [|split]; try solve [red; auto with mem].
  auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply inj_eq_rev; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. omega.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  rewrite PMap.gss.
  replace (nat_of_Z (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (nat_of_Z_neg _ z). auto.
  destruct H. omegaContradiction.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite nat_of_Z_eq. auto. omega.
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_in:
  forall vl p q c,
  p <= q < p + Z_of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. omegaContradiction.
  simpl length in H. rewrite inj_S in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. omega.
  right. apply IHvl. omega.
Qed.

Lemma getN_in:
  forall c q n p,
  p <= q < p + Z_of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; omegaContradiction.
  rewrite inj_S in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. omega.
Qed.

End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
             store_valid_access_3: mem.

Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  rewrite PMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by omega. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. omega. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite inj_S in H3. omega.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. omega. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Zsucc (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite inj_S; auto. }
  omega.
  unfold c'. simpl. rewrite setN_outside by omega. apply ZMap.gss.
Qed.

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (peq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
    try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); omega.
  generalize (size_chunk_pos chunk); omega.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try omegaContradiction.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. omega.
  elim n. apply valid_access_compat with chunk2; auto. omega.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; omega.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes':
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    stack_access (stack_adt m1) b ofs (ofs + Z_of_nat (length bytes)) ->
  exists m2, storebytes m1 b ofs bytes = Some m2.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable).
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z_of_nat (length bytes))).
  econstructor; reflexivity.
  contradiction. contradiction.
Qed.

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
  stack_access (stack_adt m1) b ofs (ofs + Z_of_nat (length bytes)) ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros m1 b ofs bytes H H0.
  destruct (storebytes _ _ _ _) eqn:STOREBYTES; eauto.
  exfalso.
  apply range_perm_storebytes' in H.
  destruct H.
  congruence. congruence.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable); inv H.
  destruct (valid_access_dec m1 chunk b ofs Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs 
              (ofs + Z.of_nat (length (encode_val chunk v)))).
  - f_equal. apply mkmem_ext; auto.
  - inversion H2.
  - elim n. clear H2. rewrite encode_val_length in r, s. constructor; try rewrite size_chunk_conv; auto.
  - auto.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length (encode_val chunk v))) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs
              (ofs + Z.of_nat (length (encode_val chunk v))));
  try now (destruct v0; destruct a; elim n;
           rewrite encode_val_length; rewrite <- size_chunk_conv; auto).
  - f_equal. apply mkmem_ext; auto.
  - destruct v0. destruct a. elim n.
    rewrite encode_val_length. rewrite <- size_chunk_conv. apply s. constructor.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = PMap.set b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_stack_access_1: forall b lo hi,
  stack_access (stack_adt m1) b lo hi -> stack_access (stack_adt m2) b lo hi.
Proof.
  intros.
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem storebytes_stack_access_2: forall b lo hi,
  stack_access (stack_adt m2) b lo hi -> stack_access (stack_adt m1) b lo hi.
Proof.
  intros.
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem storebytes_stack_access_3:
  stack_access (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)).
Proof.
  unfold storebytes in STORE. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Local Hint Resolve storebytes_stack_access_1
      storebytes_stack_access_2
      storebytes_stack_access_3: mem.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. inv H1. constructor; [|split];
  try now (try red; auto with mem).
  intros. auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. inv H1. constructor; [|split];
  try now (try red; auto with mem).
  intros. auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes. 
  destruct (range_perm_dec m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable);
  destruct (stack_access_dec (stack_adt m1) b ofs (ofs + Z.of_nat (length bytes)));
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. rewrite PMap.gss. rewrite nat_of_Z_of_nat.
  apply getN_setN_same.
  red; eauto with mem.
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  apply getN_setN_disjoint. rewrite nat_of_Z_eq; auto. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; destruct H1; split; [|split]; auto with mem. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0; destruct H1. split; [|split]; auto with mem. red; auto with mem.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall bytes1 bytes2 ofs c,
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z_of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. omega.
  simpl length. rewrite inj_S. simpl. rewrite IHbytes1. decEq. omega.
Qed.


(* Lemma in_segment_concat : forall ofs l1 l2 fd, *)
(*   in_segment ofs (ofs+l1) fd -> *)
(*   in_segment (ofs+l1) (ofs+l1+l2) fd -> *)
(*   in_segment (ofs) (ofs+l1+l2) fd. *)
(* Proof. *)
(*   intros. unfold in_segment. *)
(*   unfold in_segment in H,H0. *)
(*   omega. *)
(* Qed. *)

Lemma public_stack_range_concat : forall lo mid hi f,
  public_stack_range lo mid f ->
  public_stack_range mid hi f ->
  public_stack_range lo hi f.
Proof.
  intros. unfold public_stack_range.
  unfold public_stack_range in H,H0.
  intros.
  destruct (zlt ofs mid).
  apply H. omega.
  apply H0. omega.
Qed.

Lemma stack_access_concat : forall m b lo hi mid,
  stack_access m b lo mid ->
  stack_access m b mid hi ->
  stack_access m b lo hi.
Proof.
  intros. unfold stack_access, public_stack_access in *.
  destruct H, H0; try intuition congruence.
  left. intuition. red; intros.
  destruct (zlt o mid); eauto. apply H2. omega. apply H3. omega.
  destr. right; intuition.
  eapply public_stack_range_concat; eauto.
Qed.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z_of_nat(length bytes1)) (ofs + Z_of_nat(length bytes1) + Z_of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (stack_access_dec (stack_adt m) b ofs (ofs + Z.of_nat (length bytes1))); try congruence.
  destruct (stack_access_dec (stack_adt m1) b (ofs + Z.of_nat (length bytes1))
            (ofs + Z.of_nat (length bytes1) + Z.of_nat (length bytes2))); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z_of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  destruct (stack_access_dec (stack_adt m) b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2)))).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  rewrite PMap.gss.  rewrite setN_concat. symmetry. apply PMap.set2.
  (* Impossible case: stack_access *)
  elim n.
  rewrite app_length. rewrite inj_plus. rewrite Zplus_assoc.
  eapply stack_access_concat; eauto.
  apply storebytes_stack_access_2 with b ofs bytes1 m1; assumption.
  (* Impossible case: range_perm *)
  elim n.
  rewrite app_length. rewrite inj_plus. red; intros.
  destruct (zlt ofs0 (ofs + Z_of_nat(length bytes1))).
  apply r. omega.
  eapply perm_storebytes_2; eauto. apply r0. omega.
Qed.

Lemma storebytes_get_frame_info:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    forall b', get_frame_info (stack_adt m2) b' = get_frame_info (stack_adt m1) b'.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable),
  (stack_access_dec (stack_adt m1) b o (o + Z.of_nat (length v))); try discriminate. inv H.
  unfold get_frame_info. reflexivity. 
Qed.

Lemma storebytes_is_stack_top:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    forall b', is_stack_top (stack_adt m2) b' <-> is_stack_top (stack_adt m1) b'.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable),
  (stack_access_dec (stack_adt m1) b o (o + Z.of_nat (length v))); try discriminate. inv H.
  unfold is_stack_top, get_stack_top_blocks. simpl. tauto.
Qed.

Lemma storebytes_stack_adt:
  forall m1 b o v m2,
    storebytes m1 b o v = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof.
  unfold storebytes.
  intros.
  destruct (range_perm_dec m1 b o (o + Z.of_nat (length v)) Cur Writable),
  (stack_access_dec (stack_adt m1) b o (o + Z.of_nat (length v))); try discriminate. inv H.
  unfold is_stack_top, get_stack_top_blocks. simpl. tauto.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros.
  (* Prove (storebytes m b ofs bytes1 = Some m1) *)
  destruct (range_perm_storebytes' m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite inj_plus. omega.
  exploit storebytes_stack_access_3; eauto. rewrite app_length.
  rewrite inj_plus.
  intros.
  intros; exploit stack_access_inside. eauto. 3: apply id. omega. omega.
  (* Prove storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2 = Some m2 *)
  destruct (range_perm_storebytes' m1 b (ofs + Z_of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite inj_plus. omega. auto.
  eapply storebytes_stack_access_1. eauto.
  exploit stack_access_inside. 4: exact id.
  eapply storebytes_stack_access_3. apply H.
  omega.  rewrite app_length.
  rewrite inj_plus.
  omega.
  assert (Some m2 = Some m2').
  rewrite <- H.
  eapply storebytes_concat; eauto. inv H0.
  exists m1; split; auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A [B C]]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Zdivides_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Zdivide_plus_r. apply Zdivides_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

Theorem storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P [Q R]]. exact Q.
Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = Psucc (nextblock m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite nextblock_alloc.
  apply Plt_trans_succ; auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply Plt_strict.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite nextblock_alloc. apply Plt_succ.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite nextblock_alloc in H. rewrite alloc_result.
  exploit Plt_succ_inv; eauto. tauto.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gsspec. destruct (peq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply Plt_strict.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true.
  rewrite zlt_true. simpl. auto with mem. omega. omega.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite PMap.gsspec. unfold eq_block. destruct (peq b' (nextblock m1)); intros.
  destruct (zle lo ofs); try contradiction. destruct (zlt ofs hi); try contradiction.
  split; auto.
  auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Lemma alloc_get_frame_info:
  forall b,
    get_frame_info (stack_adt m2) b = get_frame_info (stack_adt m1) b.
Proof.
  unfold alloc in ALLOC. inv ALLOC. reflexivity.
Qed.

Lemma alloc_is_stack_top:
  forall b,
    is_stack_top (stack_adt m2) b <-> is_stack_top (stack_adt m1) b.
Proof.
  unfold alloc in ALLOC. inv ALLOC. reflexivity.
Qed.


Lemma alloc_stack_adt:
  stack_adt m2 = stack_adt m1.
Proof.
  unfold alloc in ALLOC; inv ALLOC. reflexivity.
Qed.

Lemma alloc_not_readonly_ofs:
  forall b o,
    not_readonly_ofs (stack_adt m1) b o <->
    not_readonly_ofs (stack_adt m2) b o.
Proof.
  unfold not_readonly_ofs.
  intros; rewrite alloc_get_frame_info.
  tauto.
Qed.

Lemma alloc_range_not_readonly_ofs:
  forall b lo hi,
    range_not_readonly_ofs (stack_adt m1) b lo hi <->
    range_not_readonly_ofs (stack_adt m2) b lo hi.
Proof.
  unfold range_not_readonly_ofs. intros.
  split; intros; eapply alloc_not_readonly_ofs; eauto.
Qed.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros chunk b' ofs p [A [B C]]; split; [|split]; try now (red; auto with mem).
  intro; trim C; auto.
  unfold stack_access, public_stack_access in *; intros.
  rewrite alloc_get_frame_info.
  rewrite alloc_is_stack_top.
  rewrite <- alloc_range_not_readonly_ofs; auto.
Qed.

Lemma alloc_get_frame_info_new:
  get_frame_info (stack_adt m2) b = None.
Proof.
  unfold get_frame_info.
  rewrite alloc_stack_adt.
  destruct (in_frames_dec ((stack_adt m1)) b).
  apply stack_valid in i.
  apply fresh_block_alloc in i. easy.
  apply not_in_frames_get_assoc; auto.
Qed.

Lemma stack_top_in_frames:
  forall m b,
    is_stack_top (stack_adt m) b -> in_frames (stack_adt m) b.
Proof.
  intros.
  destruct (stack_adt m).
  easy. red in H. simpl in H.
  left. eauto.
Qed.

Lemma stack_top_valid:
  forall m b, is_stack_top (stack_adt m) b -> valid_block m b.
Proof.
  intros.
  eapply stack_top_in_frames in H.
  eapply stack_valid. auto.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. omega.
  split; auto.
  red; intros.
  right; split; red.
  2: rewrite alloc_get_frame_info_new; auto.
  rewrite alloc_is_stack_top.
  intro IST; eapply stack_top_valid in IST. apply fresh_block_alloc; auto.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. destruct H as (A & B & C).
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply A. omega.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply A. omega.
  exploit perm_alloc_inv. eexact H0. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H1. rewrite dec_eq_true. intro.
  intuition omega.
  split; auto. red; intros. 
  exploit perm_alloc_inv. apply A. eauto. rewrite dec_eq_false; auto.
  split; auto.
  intros. specialize (C H0).
  unfold stack_access, public_stack_access in *; intros.
  rewrite <- alloc_get_frame_info.
  rewrite <- alloc_is_stack_top.
  rewrite alloc_range_not_readonly_ofs.
  auto. 
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. elimtype False. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  rewrite PMap.gso. auto. rewrite H1. apply sym_not_equal; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  rewrite PMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. omega. auto with mem.
    split; auto. inversion 1.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. rewrite PMap.gss.
  generalize (nat_of_Z n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H0. destruct H0; eauto.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

(** ** Properties related to [free]. *)

Theorem range_perm_free':
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  exists m2: mem, free m1 b lo hi = Some m2.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Qed.

Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros m1 b lo hi H.
  destruct (free _ _ _ _) eqn:FREE; eauto.
  exfalso.
  apply range_perm_free' in H.
  destruct H.
  congruence.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
  congruence. congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  elimtype False; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gss. unfold proj_sumbool. rewrite zle_true. rewrite zlt_true.
  simpl. tauto. omega. omega.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf); auto. subst b.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.


Lemma free_stack_adt: stack_adt m2 = stack_adt m1.
Proof.
  unfold free in FREE.
  unfold unchecked_free in FREE.
  destruct (range_perm_dec m1 bf lo hi Cur Freeable);
    inversion FREE.
  simpl. reflexivity.
Qed.
  
Lemma get_frame_info_free: forall b,
  get_frame_info (stack_adt m1) b = get_frame_info (stack_adt m2) b.
Proof.
  unfold get_frame_info. intros.
  rewrite free_stack_adt. reflexivity.
Qed.

Lemma get_stack_top_blocks_free: 
  (get_stack_top_blocks (stack_adt m1)) = (get_stack_top_blocks (stack_adt m2)).
Proof.
  unfold get_stack_top_blocks.
  rewrite free_stack_adt. reflexivity.
Qed.
  
Lemma free_is_stack_top: forall b,
  is_stack_top (stack_adt m1) b <-> is_stack_top (stack_adt m2) b.
Proof.
  unfold is_stack_top.
  rewrite get_stack_top_blocks_free. 
  tauto.
Qed.

Lemma free_public_stack_access: forall b lo hi,
  public_stack_access (stack_adt m1) b lo hi <->
  public_stack_access (stack_adt m2) b lo hi.
Proof.
  unfold public_stack_access.
  intros. rewrite <- get_frame_info_free.
  tauto.
Qed.

Lemma free_not_readonly_ofs: forall b o,
  not_readonly_ofs (stack_adt m1) b o <->
  not_readonly_ofs (stack_adt m2) b o.
Proof.
  unfold not_readonly_ofs.
  intros. rewrite <- get_frame_info_free.
  tauto.
Qed.

Lemma free_range_not_readonly_ofs: forall b lo hi,
  range_not_readonly_ofs (stack_adt m1) b lo hi <->
  range_not_readonly_ofs (stack_adt m2) b lo hi.
Proof.
  unfold range_not_readonly_ofs.
  intros.
  split; intros; apply free_not_readonly_ofs; eauto.
Qed.

Lemma free_stack_access: forall b lo hi,
  stack_access (stack_adt m1) b lo hi <->
  stack_access (stack_adt m2) b lo hi.
Proof.
  unfold stack_access.
  intros.
  rewrite free_is_stack_top.
  rewrite free_public_stack_access.
  rewrite free_range_not_readonly_ofs.
  tauto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. destruct H2. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto. 
  destruct (zlt lo hi). intuition. right. omega.
  split; auto.
  intros. 
  apply free_stack_access. auto.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  omega. apply H3. omega.
  elim (perm_free_2 ofs Cur p).
  omega. apply H3. omega.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite PMap.gsspec. destruct (peq b bf). subst b.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
  destruct H0. split; try assumption.
  intros. apply free_stack_access. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. omega.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; omega.
Qed.

Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1: mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2':
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> exists m', drop_perm m b lo hi p = Some m' .
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.
Proof.
  intros m b lo hi p H.
  destruct (drop_perm _ _ _ _ _) eqn:DROP; eauto.
  exfalso.
  apply @range_perm_drop_2' with (p := p) in H; auto.
  destruct H.
  congruence.
Defined.


Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite nextblock_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  omega. omega.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. rewrite PMap.gss. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  omega. omega.
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b). subst b'.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition omega.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite PMap.gsspec. destruct (peq b' b).
  subst b'. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma drop_stack_adt: stack_adt m' = stack_adt m.
Proof.
  unfold drop_perm in DROP.
  destruct (range_perm_dec m b lo hi Cur Freeable);
    inversion DROP.
  simpl. reflexivity.
Qed.
  
Lemma get_frame_info_drop: forall b,
  get_frame_info (stack_adt m) b = get_frame_info (stack_adt m') b.
Proof.
  unfold get_frame_info. intros.
  rewrite drop_stack_adt. reflexivity.
Qed.

Lemma get_stack_top_blocks_drop: 
  (get_stack_top_blocks (stack_adt m)) = (get_stack_top_blocks (stack_adt m')).
Proof.
  unfold get_stack_top_blocks.
  rewrite drop_stack_adt. reflexivity.
Qed.
  
Lemma drop_perm_is_stack_top: forall b,
  is_stack_top (stack_adt m) b <-> is_stack_top (stack_adt m') b.
Proof.
  unfold is_stack_top.
  rewrite get_stack_top_blocks_drop. 
  tauto.
Qed.

Lemma drop_perm_public_stack_access: forall b lo hi,
  public_stack_access (stack_adt m) b lo hi <->
  public_stack_access (stack_adt m') b lo hi.
Proof.
  unfold public_stack_access.
  intros. rewrite <- get_frame_info_drop.
  tauto. 
Qed.

Lemma drop_perm_not_readonly_ofs: forall b o,
  not_readonly_ofs (stack_adt m) b o <->
  not_readonly_ofs (stack_adt m') b o.
Proof.
  unfold not_readonly_ofs.
  intros. rewrite <- get_frame_info_drop.
  tauto. 
Qed.

Lemma drop_perm_range_not_readonly_ofs: forall b lo hi,
  range_not_readonly_ofs (stack_adt m) b lo hi <->
  range_not_readonly_ofs (stack_adt m') b lo hi.
Proof.
  unfold range_not_readonly_ofs.
  split; intros; apply drop_perm_not_readonly_ofs; eauto.
Qed.

Lemma drop_perm_stack_access: forall b lo hi,
  stack_access (stack_adt m) b lo hi <->
  stack_access (stack_adt m') b lo hi.
Proof.
  unfold stack_access.
  intros.
  rewrite drop_perm_is_stack_top,
  drop_perm_public_stack_access,
  drop_perm_range_not_readonly_ofs; tauto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
  destruct H1. split; try assumption.
  intros. apply drop_perm_stack_access. auto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
  destruct H0. split; try assumption.
  intros. apply drop_perm_stack_access. auto.
Qed.

Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. omega. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

(** Preservation of permissions *)

Lemma perm_inj:
  forall f g m1 m2 b1 ofs k p b2 delta,
  mem_inj f g m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  inject_perm_condition p ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f g m1 m2 b1 lo hi k p b2 delta,
  mem_inj f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  inject_perm_condition p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by omega.
  eapply perm_inj; eauto. apply H0. omega.
Qed.


Lemma is_stack_top_inj:
  forall f g m1 m2 b1 b2 delta
    (MINJ: mem_inj f g m1 m2)
    (FB: f b1 = Some (b2, delta))
    (IST: is_stack_top (stack_adt m1) b1)
    (G0: frameinj_pack_after O g),
    is_stack_top (stack_adt m2) b2.
Proof.
  intros. inv MINJ.
  eapply is_stack_top_inj_gen; eauto.
Qed.

Lemma is_stack_top_extends:
  forall m1 m2 b
    (MINJ: extends m1 m2)
    (IST: is_stack_top (stack_adt m1) b),
    is_stack_top (stack_adt m2) b.
Proof.
  intros.
  inv MINJ.
  eapply is_stack_top_inj; eauto. reflexivity.
  unfold flat_frameinj. red; intros. destr_in H0. inv H0; omega.
Qed.

Lemma is_stack_top_inject:
  forall f g m1 m2 b1 b2 delta
    (MINJ: inject f g m1 m2)
    (FB: f b1 = Some (b2, delta))
    (G0: frameinj_pack_after O g)
    (IST: is_stack_top (stack_adt m1) b1),
    is_stack_top (stack_adt m2) b2.
Proof.
  intros.
  eapply is_stack_top_inj; eauto. inv MINJ; eauto.
Qed.

Lemma get_frame_info_inj:
  forall f g m1 m2 b1 b2 delta
    (MINJ: mem_inj f g m1 m2)
    (FB : f b1 = Some (b2, delta)),
    option_le (fun fi => 
                 forall ofs k p,
                   perm m1 b1 ofs k p ->
                   inject_perm_condition p ->
                   frame_public fi (ofs + delta))
              (shift_frame delta)
              delta
              (get_frame_info (stack_adt m1) b1)
              (get_frame_info (stack_adt m2) b2).
Proof.
  intros; destruct MINJ.
  eapply get_frame_info_inj_gen; eauto.
Qed.

Lemma public_stack_range_not_ret_or_link:
  forall m b lo hi f,
    get_frame_info m b = Some f ->
    public_stack_range lo hi f ->
    range_not_readonly_ofs m b lo hi.
Proof.
  intros m b lo hi f GFI ISD.
  red in ISD.
  red; red. rewrite GFI.
  intros.
  apply ISD in H.
  congruence. 
Qed.

Lemma public_stack_range_shift:
  forall f1 f2 delta,
    shift_frame delta f1 f2 ->
    forall lo hi,
      0 <= lo -> hi <= frame_size f1 ->
      public_stack_range lo hi f1 ->
      public_stack_range (lo+delta) (hi+delta) f2.
Proof.
  unfold public_stack_range, frame_public. intros.
  replace ofs with (ofs-delta+delta) by omega.
  erewrite <- (H2 (ofs - delta)) by omega.
  symmetry; apply shift_perm; eauto.
  omega.
Qed.

Lemma stack_access_inj:
  forall f g m1 m2 b1 b2 delta lo hi p
    (MINJ : mem_inj f g m1 m2)
    (FB : f b1 = Some (b2, delta))
    (G0: frameinj_pack_after O g)
    (RP: range_perm m1 b1 lo hi Cur p)
    (IPC: inject_perm_condition p)
    (NPSA: stack_access (stack_adt m1) b1 lo hi),
    stack_access (stack_adt m2) b2 (lo + delta) (hi + delta).
Proof.
  intros; inv MINJ; eapply stack_access_inj_gen; eauto.
Qed.

Lemma valid_access_inj_gen:
  forall f g m1 m2 b1 b2 delta chunk ofs p
         (MINJ : stack_inject f g (perm m1) (stack_adt m1) (stack_adt m2))
         (PERMS: forall b1 b2 delta,
             f b1 = Some (b2, delta) ->
             forall o k p,
               perm m1 b1 o k p ->
               inject_perm_condition p ->
               perm m2 b2 (o+delta) k p)
         (ALIGN: forall b1 b2 delta chunk ofs p,
             f b1 = Some (b2, delta) ->
             range_perm m1 b1 ofs (ofs+size_chunk chunk) Max p ->
             (align_chunk chunk | delta)),
    f b1 = Some(b2, delta) ->
    (perm_order p Writable ->       frameinj_pack_after O g) ->
    valid_access m1 chunk b1 ofs p ->
    inject_perm_condition p ->
    valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as (A & B & C). split; [| split].
  - replace (ofs + delta + size_chunk chunk)
      with ((ofs + size_chunk chunk) + delta) by omega.
    red; intros.
    replace ofs0 with ((ofs0-delta)+delta) by omega.
    eapply PERMS; eauto.
    eapply A. omega.
  - apply Z.divide_add_r; auto. eapply ALIGN; eauto with mem.
  - intro O; specialize (C O).
    rewrite <- Z.add_assoc.
    rewrite (Z.add_comm delta).
    rewrite Z.add_assoc.
    eapply stack_access_inj_gen; eauto.
Qed.

Lemma valid_access_inj:
  forall f g m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  (perm_order p Writable -> frameinj_pack_after O g) ->
  valid_access m1 chunk b1 ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H.
  eapply valid_access_inj_gen; eauto.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f g m1 m2 b1 b2 delta,
  mem_inj f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z_of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite inj_S in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. omega.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by omega.
  apply IHn. red; intros; apply H1; omega.
Qed.

Lemma load_inj:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  inversion 1.
  eapply inject_perm_condition_writable; constructor.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. eapply getN_inj; eauto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f g m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (nat_of_Z len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by omega.
  eapply range_perm_inj; eauto with mem.
  eapply inject_perm_condition_writable; constructor.
  eapply getN_inj; eauto.
  destruct (zle 0 len). rewrite nat_of_Z_eq; auto. omega.
  rewrite nat_of_Z_neg. simpl. red; intros; omegaContradiction. omega.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by omega.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. omega.
Qed.


Lemma store_stack_adt:
  forall chunk m1 b1 ofs v1 n1,
    store chunk m1 b1 ofs v1 = Some n1 ->
    stack_adt n1 = stack_adt m1.
Proof.
  unfold store. intros.
  destruct (valid_access_dec m1 chunk b1 ofs Writable); try discriminate.
  inv H; auto.
Qed.

Lemma store_mapped_inj:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
    mem_inj f g m1 m2 ->
    store chunk m1 b1 ofs v1 = Some n1 ->
    meminj_no_overlap f m1 ->
    f b1 = Some (b2, delta) ->
    frameinj_pack_after O g ->
    Val.inject f v1 v2 ->
    exists n2,
      store chunk m2 b2 (ofs + delta) v2 = Some n2
      /\ mem_inj f g n1 n2.
Proof.
  intros. 
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
  {
    eapply valid_access_inj; eauto with mem.
    eapply inject_perm_condition_writable; constructor.
  }
  destruct (valid_access_store' _ _ _ _ v2 H5) as [n2 STORE].
  exists n2; split. auto.
  constructor.
  - (* perm *)
    intros. eapply perm_store_1; [eexact STORE|].
    eapply mi_perm; eauto.
    eapply perm_store_2; eauto.
  - (* align *)
    intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
    red; intros; eauto with mem.
  - (* mem_contents *)
    intros.
    rewrite (store_mem_contents _ _ _ _ _ _ H0).
    rewrite (store_mem_contents _ _ _ _ _ _ STORE).
    rewrite ! PMap.gsspec.
    destruct (peq b0 b1). subst b0.
    + (* block = b1, block = b2 *)
      assert (b3 = b2) by congruence. subst b3.
      assert (delta0 = delta) by congruence. subst delta0.
      rewrite peq_true.
      apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
      apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
    + destruct (peq b3 b2). subst b3.
      * (* block <> b1, block = b2 *)
        rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
        rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
        assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
        eapply H1; eauto. eauto 6 with mem.
        exploit store_valid_access_3. eexact H0. intros [A B].
        eapply perm_implies. apply perm_cur_max. apply A. omega. auto with mem.
        destruct H9. congruence. omega.
      * (* block <> b1, block <> b2 *)
        eapply mi_memval; eauto. eauto with mem.
  - rewrite (store_stack_adt _ _ _ _ _ _ STORE).
    rewrite (store_stack_adt _ _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong.
    2: apply mi_stack_blocks; auto.
    intros; eapply perm_store_2; eauto.
Qed.

Lemma store_unmapped_inj:
  forall f g chunk m1 b1 ofs v1 n1 m2,
    mem_inj f g m1 m2 ->
    store chunk m1 b1 ofs v1 = Some n1 ->
    f b1 = None ->
    mem_inj f g n1 m2.
Proof.
  intros. constructor.
  - (* perm *)
    intros. eapply mi_perm; eauto with mem.
  - (* align *)
    intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
    red; intros; eauto with mem.
  - (* mem_contents *)
    intros.
    rewrite (store_mem_contents _ _ _ _ _ _ H0).
    rewrite PMap.gso. eapply mi_memval; eauto with mem.
    congruence.
  - rewrite (store_stack_adt _ _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong.
    2 : apply mi_stack_blocks; auto.
    intros; eapply perm_store_2; eauto.
Qed.

Lemma store_outside_inj:
  forall f g m1 m2 chunk b ofs v m2',
    mem_inj f g m1 m2 ->
    (forall b' delta ofs',
        f b' = Some(b, delta) ->
        perm m1 b' ofs' Cur Readable ->
        ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
    store chunk m2 b ofs v = Some m2' ->
    mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
  - (* perm *)
    eauto with mem.
  - (* access *)
    intros; eapply mi_align0; eauto.
  - (* mem_contents *)
    intros.
    rewrite (store_mem_contents _ _ _ _ _ _ H1).
    rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
    rewrite setN_outside. auto.
    rewrite encode_val_length. rewrite <- size_chunk_conv.
    destruct (zlt (ofs0 + delta) ofs); auto.
    destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). omega.
    byContradiction. eapply H0; eauto. omega.
    eauto with mem.
  - rewrite (store_stack_adt _ _ _ _ _ _ H1).
    eapply stack_inject_invariant_strong.
    2: eauto. tauto.
Qed.

Lemma storebytes_mapped_inj:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
    mem_inj f g m1 m2 ->
    storebytes m1 b1 ofs bytes1 = Some n1 ->
    meminj_no_overlap f m1 ->
    f b1 = Some (b2, delta) ->
    frameinj_pack_after O g ->
    list_forall2 (memval_inject f) bytes1 bytes2 ->
    exists n2,
      storebytes m2 b2 (ofs + delta) bytes2 = Some n2
      /\ mem_inj f g n1 n2.
Proof.
  intros f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2 H H0 H1 H2 G0 H3.
  inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z_of_nat (length bytes2)) Cur Writable).
  {
    replace (ofs + delta + Z_of_nat (length bytes2))
      with ((ofs + Z_of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    eapply inject_perm_condition_writable; constructor.
    rewrite (list_forall2_length H3). omega.
  }
  assert (stack_access (stack_adt m2) b2 (ofs + delta) (ofs + delta + Z_of_nat (length bytes2))).
  {
    replace (ofs + delta + Z_of_nat (length bytes2))
      with ((ofs + Z_of_nat (length bytes1)) + delta).
    eapply stack_access_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    eapply inject_perm_condition_writable; constructor.
    eapply storebytes_stack_access_3; eauto.
    rewrite (list_forall2_length H3). omega.
  }
  destruct (range_perm_storebytes' _ _ _ _ H4 H5) as [n2 STORE]. 
  exists n2; split. eauto.
  constructor.
  - (* perm *)
    intros.
    eapply perm_storebytes_1; [apply STORE |].
    eapply mi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
  - (* align *)
    intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  - (* mem_contents *)
    intros.
    assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
    rewrite ! PMap.gsspec. destruct (peq b0 b1). subst b0.
    + (* block = b1, block = b2 *)
      assert (b3 = b2) by congruence. subst b3.
      assert (delta0 = delta) by congruence. subst delta0.
      rewrite peq_true.
      apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
    + destruct (peq b3 b2). subst b3.
      * (* block <> b1, block = b2 *)
        rewrite setN_other. auto.
        intros.
        assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
        {
          eapply H1; eauto 6 with mem.
          exploit storebytes_range_perm. eexact H0.
          instantiate (1 := r - delta).
          rewrite (list_forall2_length H3). omega.
          eauto 6 with mem.
        }
        destruct H10. congruence. omega.
      * (* block <> b1, block <> b2 *)
        eauto.
  - rewrite (storebytes_stack_adt _ _ _ _ _ STORE).
    rewrite (storebytes_stack_adt _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong.
    2: apply mi_stack_blocks; auto.
    intros; eapply perm_storebytes_2; eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f g m1 b1 ofs bytes1 n1 m2,
    mem_inj f g m1 m2 ->
    storebytes m1 b1 ofs bytes1 = Some n1 ->
    f b1 = None ->
    mem_inj f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
  - (* perm *)
    intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
  - (* align *)
    intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  - (* mem_contents *)
    intros.
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite PMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
    congruence.
  - rewrite (storebytes_stack_adt _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong.
    2: apply mi_stack_blocks; auto.
    intros; eapply perm_storebytes_2; eauto.
Qed.

Lemma storebytes_outside_inj:
  forall f g m1 m2 b ofs bytes2 m2',
    mem_inj f g m1 m2 ->
    (forall b' delta ofs',
        f b' = Some(b, delta) ->
        perm m1 b' ofs' Cur Readable ->
        ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
    storebytes m2 b ofs bytes2 = Some m2' ->
    mem_inj f g m1 m2'.
Proof.
  intros. inversion H. constructor.
  - (* perm *)
    intros. eapply perm_storebytes_1; eauto with mem.
  - (* align *)
    eauto.
  - (* mem_contents *)
    intros.
    rewrite (storebytes_mem_contents _ _ _ _ _ H1).
    rewrite PMap.gsspec. destruct (peq b2 b). subst b2.
    rewrite setN_outside. auto.
    destruct (zlt (ofs0 + delta) ofs); auto.
    destruct (zle (ofs + Z_of_nat (length bytes2)) (ofs0 + delta)). omega.
    byContradiction. eapply H0; eauto. omega.
    eauto with mem.
  - rewrite (storebytes_stack_adt _ _ _ _ _ H1).
    eapply stack_inject_invariant_strong.
    2: apply mi_stack_blocks; eauto. tauto.
Qed.

Lemma storebytes_empty_inj:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
    mem_inj f g m1 m2 ->
    storebytes m1 b1 ofs1 nil = Some m1' ->
    storebytes m2 b2 ofs2 nil = Some m2' ->
    mem_inj f g m1' m2'.
Proof.
  intros. destruct H. constructor.
  - (* perm *)
    intros.
    eapply perm_storebytes_1; eauto.
    eapply mi_perm0; eauto.
    eapply perm_storebytes_2; eauto.
  - (* align *)
    intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. eapply perm_storebytes_2; eauto.
  - (* mem_contents *)
    intros.
    assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
    rewrite (storebytes_mem_contents _ _ _ _ _ H0).
    rewrite (storebytes_mem_contents _ _ _ _ _ H1).
    simpl. rewrite ! PMap.gsspec.
    destruct (peq b0 b1); destruct (peq b3 b2); subst; eapply mi_memval0; eauto.
  - rewrite (storebytes_stack_adt _ _ _ _ _ H1).
    rewrite (storebytes_stack_adt _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong.
    2: apply mi_stack_blocks0; auto. 
    intros; eapply perm_storebytes_2; eauto.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f g m1 m2 lo hi b2 m2',
    mem_inj f g m1 m2 ->
    alloc m2 lo hi = (m2', b2) ->
    mem_inj f g m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
  - (* perm *)
    intros. eapply perm_alloc_1; eauto.
  - (* align *)
    eauto.
  - (* mem_contents *)
    intros.
    assert (perm m2 b0 (ofs + delta) Cur Readable).
    {
      eapply mi_perm0; eauto.
      eapply inject_perm_condition_writable; constructor.
    }
    assert (valid_block m2 b0) by eauto with mem.
    rewrite <- MEM; simpl. rewrite PMap.gso. eauto with mem.
    rewrite NEXT. eauto with mem.
  - subst. simpl; auto.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f g m1 m2 lo hi m1' b1,
    mem_inj f g m1 m2 ->
    alloc m1 lo hi = (m1', b1) ->
    f b1 = None ->
    mem_inj f g m1' m2.
Proof.
  intros. inversion H. constructor.
  - (* perm *)
    intros. exploit perm_alloc_inv; eauto. intros.
    destruct (eq_block b0 b1). congruence. eauto.
  - (* align *)
    intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. exploit perm_alloc_inv; eauto.
    destruct (eq_block b0 b1); auto. congruence.
  - (* mem_contents *)
    injection H0; intros NEXT MEM. intros.
    rewrite <- MEM; simpl. rewrite NEXT.
    exploit perm_alloc_inv; eauto. intros.
    rewrite PMap.gsspec. unfold eq_block in H4. destruct (peq b0 b1).
    rewrite ZMap.gi. constructor. eauto.
  - rewrite (alloc_stack_adt _ _ _ _ _ H0).
    eapply stack_inject_invariant_strong. 2: eauto.
    intros; eapply perm_alloc_4; eauto. congruence.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
    mem_inj f g m1 m2 ->
    alloc m1 lo hi = (m1', b1) ->
    valid_block m2 b2 ->
    inj_offset_aligned delta (hi-lo) ->
    (forall ofs k p, lo <= ofs < hi -> inject_perm_condition p -> perm m2 b2 (ofs + delta) k p) ->
    f b1 = Some(b2, delta) ->


    (~ Plt b1 (nextblock m1) ->
     forall f2 fi,
       In f2 (stack_adt m2) ->
       in_frame f2 b2 ->
       frame_adt_info f2 = Some fi ->
       forall o k pp,
         perm m1' b1 o k pp ->
         inject_perm_condition pp ->
         frame_public fi (o + delta)
    ) ->
    mem_inj f g m1' m2.
Proof.
  intros. rename H5 into PLT. inversion H. constructor.
  - (* perm *)
    intros.
    exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
    rewrite H4 in H5; inv H5. eauto. eauto.
  - (* align *)
    intros. destruct (eq_block b0 b1).
    subst b0. assert (delta0 = delta) by congruence. subst delta0.
    assert (lo <= ofs < hi).
    { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
    assert (lo <= ofs + size_chunk chunk - 1 < hi).
    { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); omega. }
    apply H2. omega.
    eapply mi_align0 with (ofs := ofs) (p := p); eauto.
    red; intros. eapply perm_alloc_4; eauto.
  - (* mem_contents *)
    injection H0; intros NEXT MEM.
    intros. rewrite <- MEM; simpl. rewrite NEXT.
    exploit perm_alloc_inv; eauto. intros.
    rewrite PMap.gsspec. unfold eq_block in H7.
    destruct (peq b0 b1). rewrite ZMap.gi. constructor. eauto.
  - rewrite (alloc_stack_adt _ _ _ _ _ H0).
    eapply stack_inject_invariant with (thr:=nextblock m1). 4: eauto.
    + intros.
      exploit perm_alloc_inv. eauto. eauto. destr.
      subst.
      apply alloc_result in H0. subst. xomega.
    + rewrite Forall_forall; intros. eapply stack_valid. eapply in_frames_in_frame; eauto.
    + intros.
      exploit perm_alloc_inv; eauto.
      destr.
      * subst. intros. rewrite H4 in H5; inv H5. eapply PLT; eauto.
      * inv mi_stack_blocks0. intros; eapply stack_inject_not_in_frames; eauto.
        intro INF; apply stack_valid in INF; congruence.
Qed.

Lemma free_left_inj:
  forall f g m1 m2 b lo hi m1',
  mem_inj f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f g m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
(* stack_adt *)
  rewrite (free_stack_adt _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_free_3; eauto.
Qed.

Lemma free_right_inj:
  forall f g m1 m2 b lo hi m2',
  mem_inj f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f g m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p ->
    inject_perm_condition p ->
    perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  omega.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
(* stack_adt *)
  rewrite (free_stack_adt _ _ _ _ _ H0). auto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_perm_stack_adt:
  forall m1 b lo hi p m1',
    drop_perm m1 b lo hi p = Some m1' ->
    stack_adt m1' = stack_adt m1.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m1 b lo hi Cur Freeable); try discriminate. inv H; reflexivity.
Qed.

Lemma drop_unmapped_inj:
  forall f g m1 m2 b lo hi p m1',
  mem_inj f g m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f g m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
(* stack_adt *)
  rewrite (drop_perm_stack_adt _ _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_drop_4; eauto.
Qed.

Lemma drop_mapped_inj:
  forall f g m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f g m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  range_perm m2 b2 (lo + delta) (hi + delta) Cur Freeable ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f g m1' m2'.
Proof.
  intros.
  assert (exists m2', drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' ) as X.
  apply range_perm_drop_2'. auto. 
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H3 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). omega. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. omega.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H2; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. omega. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
(* stack_adt *)
  rewrite (drop_perm_stack_adt _ _ _ _ _ _ H0).
  rewrite (drop_perm_stack_adt _ _ _ _ _ _ DROP).
  eapply stack_inject_invariant_strong. 2: eauto.
  intros. eapply perm_drop_4; eauto.
Qed.

Lemma drop_outside_inj: forall f g m1 m2 b lo hi p m2',
  mem_inj f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f g m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. omega.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
  (* stack_adt *)
  rewrite (drop_perm_stack_adt _ _ _ _ _ _ H0). auto.
Qed.

Lemma stack_inject_id:
  forall p s,
    stack_inject inject_id (flat_frameinj (length s)) p s s.
Proof.
  intros; unfold flat_frameinj; constructor.
  - red. intros i1 i2. repeat destr.
  - intros. destr_in H0; inv H0. 
    exists f1. intuition.
    apply inject_frame_id.
  - inversion 1; subst; intros; eauto.
    exists i1, f1; intuition.
    apply frame_at_pos_lt in H0. destr.
  - inversion 1; eauto. intros; exfalso; apply H0. eapply in_frames_in_frame; eauto.
  - intros i j H; destr_in H; inv H.
  - intros. exists i; destr.
  - intros i j H; destr_in H; inv H. omega.
  - intros i1 i2 f1 f2 FAP1 FAP2 H; repeat destr_in H.
    assert (f1 = f2) by (eapply frame_at_same_pos; eauto). subst. auto.
Qed.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by omega.
  apply memval_lessdef_refl.
  apply stack_inject_id. auto. auto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by omega. eapply loadbytes_inj; eauto.
Qed.

Lemma storev_stack_adt:
 forall chunk m1 addr v m2,
   storev chunk m1 addr v = Some m2 ->
   stack_adt m2 = stack_adt m1.
Proof.
  intros chunk m1 addr v m2 H; unfold storev in H; destr_in H.
  eapply store_stack_adt; eauto.
Qed.

Ltac rewrite_stack_backwards :=
  repeat match goal with
         | H: store _ ?m1 _ _ _ = Some ?m2 |- context [stack_adt ?m2] =>
           rewrite (store_stack_adt _ _ _ _ _ _ H)
         | H: storev _ ?m1 _ _ = Some ?m2 |- context [stack_adt ?m2] =>
           rewrite (storev_stack_adt _ _ _ _ _ H)
         | H: storebytes ?m1 _ _ _ = Some ?m2 |- context [stack_adt ?m2] =>
           rewrite (storebytes_stack_adt _ _ _ _ _ H)
         | H: alloc ?m1 _ _ = (?m2,_) |- context [stack_adt ?m2] =>
           rewrite (alloc_stack_adt _ _ _ _ _ H)
         | H: free ?m1 _ _ _ = Some ?m2 |- context [stack_adt ?m2] =>
           rewrite (free_stack_adt _ _ _ _ _ H)
         | H: drop_perm ?m1 _ _ _ _ = Some ?m2 |- context [stack_adt ?m2] =>
           rewrite (drop_perm_stack_adt _ _ _ _ _ _ H)
         end.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    unfold flat_frameinj. red; intros. destr_in H3. inv H3; omega.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  constructor; auto.
  rewrite (nextblock_store _ _ _ _ _ _ H0).
  rewrite (nextblock_store _ _ _ _ _ _ A).
  auto.
  erewrite store_stack_adt; eauto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
  rewrite_stack_backwards; auto.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega.
  intros. eauto using perm_store_2.
  rewrite_stack_backwards; auto.
Qed.

Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.

Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    unfold flat_frameinj; red; intros. repeat destr_in H3; omega.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by omega. auto.
  constructor; auto.
  rewrite (nextblock_storebytes _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ A).
  auto.
  erewrite storebytes_stack_adt; eauto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
  rewrite_stack_backwards; auto.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (nextblock_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. omega.
  intros. eauto using perm_storebytes_2. 
  rewrite_stack_backwards; auto.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
  {
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  }
  subst b'.
  exists m2'; split; auto.
  constructor.
  - rewrite (nextblock_alloc _ _ _ _ _ H0).
    rewrite (nextblock_alloc _ _ _ _ _ ALLOC).
    congruence.
  - eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
    + eapply alloc_right_inj; eauto.
      erewrite alloc_stack_adt; eauto.
    + eauto with mem.
    + red. intros. apply Zdivide_0.
    + intros.
      eapply perm_implies with Freeable; auto with mem.
      eapply perm_alloc_2; eauto.
      omega.
    + intros NPLT f2 fi INS INF FINFO o k p PERM IPC.
      erewrite alloc_stack_adt in INS. 2: eauto.
      exfalso; apply NPLT. rewrite mext_next0. apply stack_valid. eapply in_frames_in_frame; eauto.
  - intros. eapply perm_alloc_inv in H; eauto.
    generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
    destruct (eq_block b0 b).
    subst b0. 
    assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by omega.
    destruct EITHER.
    left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
    right; tauto.
    exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
  - rewrite_stack_backwards; auto.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  erewrite free_stack_adt; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A]. 
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
  rewrite_stack_backwards; auto.
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. omega.
  intros. eauto using perm_free_3. 
  rewrite_stack_backwards; auto.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  inject_perm_condition Freeable ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert (exists m2': mem, free m2 b lo hi = Some m2' ) as X.
    apply range_perm_free'. red; intros.
    replace ofs with (ofs + 0) by omega.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  inv H. constructor.
  rewrite (nextblock_free _ _ _ _ _ H1).
  rewrite (nextblock_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  erewrite free_stack_adt; eauto.
  unfold inject_id; intros. inv H.
  eapply perm_free_2. eexact H1. instantiate (1 := ofs); omega. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
  rewrite_stack_backwards; auto.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_next0. tauto.
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> inject_perm_condition p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Lemma flat_frameinj_pack:
  forall x n,
    frameinj_pack_after x (flat_frameinj n).
Proof.
  unfold flat_frameinj. red; intros.
  repeat destr_in H0; omega.
Qed.

Hint Resolve flat_frameinj_pack.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
    extends m1 m2 -> valid_access m1 chunk b ofs p -> inject_perm_condition p ->
    valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by omega.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
  eapply inject_perm_condition_writable; constructor.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

Lemma magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q.
Proof.
  intros. destruct H. constructor; auto.
Qed.

Lemma mextends_agree:
  forall m1 m2 P, extends m1 m2 -> magree m1 m2 P.
Proof.
  intros. destruct H. destruct mext_inj0. constructor; intros.
- replace ofs with (ofs + 0) by omega. eapply mi_perm0; eauto. auto.
- eauto.
- exploit mi_memval0; eauto. unfold inject_id; eauto.
  rewrite Zplus_0_r. auto.
- auto.
- auto.
- rewrite_stack_backwards; auto.
Qed.

Lemma magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> extends m1 m2.
Proof.
  intros. destruct H0. constructor; auto. constructor; unfold inject_id; intros.
- inv H0. rewrite Zplus_0_r. eauto.
- inv H0. apply Zdivide_0.
- inv H0. rewrite Zplus_0_r. eapply ma_memval0; eauto.
- auto.
Qed.

Lemma magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes'.
Proof.
  assert (GETN: forall c1 c2 n ofs,
    (forall i, ofs <= i < ofs + Z.of_nat n -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    list_forall2 memval_lessdef (getN n ofs c1) (getN n ofs c2)).
  {
    induction n; intros; simpl.
    constructor.
    rewrite inj_S in H. constructor.
    apply H. omega.
    apply IHn. intros; apply H; omega.
  }
  unfold loadbytes; intros. destruct H.
  destruct (range_perm_dec m1 b ofs (ofs + n) Cur Readable); inv H0.
  rewrite pred_dec_true. econstructor; split; eauto.
  apply GETN. intros. rewrite nat_of_Z_max in H.
  assert (ofs <= i < ofs + n) by xomega.
  apply ma_memval0; auto.
  red; intros; eauto.
  eapply ma_perm0; eauto.
  eapply inject_perm_condition_writable; constructor.
Qed.

Lemma magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', load chunk m2 b ofs = Some v' /\ Val.lessdef v v'.
Proof.
  intros. exploit load_valid_access; eauto. intros [A [B _]].
  exploit load_loadbytes; eauto. intros [bytes [C D]].
  exploit magree_loadbytes; eauto. intros [bytes' [E F]].
  exists (decode_val chunk bytes'); split.
  apply loadbytes_load; auto.
  apply val_inject_id. subst v. apply decode_val_inject; auto.
Qed.

Lemma is_stack_top_magree:
  forall P m1 m2 b
    (MINJ: magree m1 m2 P)
    (IST: is_stack_top (stack_adt m1) b),
    is_stack_top (stack_adt m2) b.
Proof.
  intros.
  apply ma_stack_adt in MINJ.
  eapply stack_inject_is_stack_top; eauto.
  reflexivity.
Qed.

Lemma get_frame_info_magree:
  forall P m1 m2 b
    (MINJ: magree m1 m2 P)
    (* (INFRAMES: in_frames (stack_adt m1) b) *),
    option_le (fun fi => 
                 forall ofs k p,
                   perm m1 b ofs k p ->
                   inject_perm_condition p ->
                   frame_public fi ofs)
              (shift_frame 0) 0
              (get_frame_info (stack_adt m1) b)
              (get_frame_info (stack_adt m2) b).
Proof.
  intros; destruct MINJ.
  exploit get_frame_info_inj_gen; eauto.
  - reflexivity.
  - instantiate (1:=b). inversion 1; subst; econstructor; auto.
    intros; rewrite <- Z.add_0_r; eauto.
Qed.

Lemma stack_access_magree:
  forall P m1 m2 b lo hi p
    (MINJ : magree m1 m2 P)
    (RP: range_perm m1 b lo hi Cur p)
    (IPC: inject_perm_condition p)
    (NPSA: stack_access (stack_adt m1) b lo hi),
    stack_access (stack_adt m2) b lo hi.
Proof.
  intros. inv MINJ.
  exploit stack_access_inj_gen; eauto.
  reflexivity.
  rewrite ! Z.add_0_r. tauto.
Qed.

Lemma magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q.
Proof.
  assert (SETN: forall (access: Z -> Prop) bytes1 bytes2,
    list_forall2 memval_lessdef bytes1 bytes2 ->
    forall p c1 c2,
    (forall i, access i -> i < p \/ p + Z.of_nat (length bytes1) <= i -> memval_lessdef (ZMap.get i c1) (ZMap.get i c2)) ->
    forall q, access q ->
    memval_lessdef (ZMap.get q (setN bytes1 p c1))
                   (ZMap.get q (setN bytes2 p c2))).
  {
    induction 1; intros; simpl.
  - apply H; auto. simpl. omega.
  - simpl length in H1; rewrite inj_S in H1.
    apply IHlist_forall2; auto.
    intros. rewrite ! ZMap.gsspec. destruct (ZIndexed.eq i p). auto.
    apply H1; auto. unfold ZIndexed.t in *; omega.
  }
  intros.
  destruct (range_perm_storebytes' m2 b ofs bytes2) as [m2' ST2].
  { erewrite <- list_forall2_length by eauto. red; intros.
    eapply ma_perm; eauto.
    eapply storebytes_range_perm; eauto.
    eapply inject_perm_condition_writable; constructor.
  }
  { erewrite <- list_forall2_length by eauto.
    eapply stack_access_magree. eauto.
    eapply storebytes_range_perm; eauto.
    apply inject_perm_condition_writable. constructor.
    eapply storebytes_stack_access_3; eauto.
  }
  exists m2'; split; auto.
  constructor; intros.
- eapply perm_storebytes_1; eauto. eapply ma_perm; eauto.
  eapply perm_storebytes_2; eauto.
- exploit ma_perm_inv; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
- rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ ST2).
  rewrite ! PMap.gsspec. destruct (peq b0 b).
+ subst b0. apply SETN with (access := fun ofs => perm m1' b ofs Cur Readable /\ Q b ofs); auto.
  intros. destruct H5. eapply ma_memval; eauto.
  eapply perm_storebytes_2; eauto.
+ eapply ma_memval; eauto. eapply perm_storebytes_2; eauto.
- rewrite (nextblock_storebytes _ _ _ _ _ H0).
  rewrite (nextblock_storebytes _ _ _ _ _ ST2).
  eapply ma_nextblock; eauto.
- rewrite (storebytes_stack_adt _ _ _ _ _ H0).
  rewrite (storebytes_stack_adt _ _ _ _ _ ST2).
  eapply stack_inject_invariant_strong.
  2: eapply ma_stack_adt; eauto.
  inversion 1.
  eapply perm_storebytes_2; eauto.
- rewrite_stack_backwards; inv H; auto.
Qed.

Lemma magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. constructor; intros.
- eapply ma_perm; eauto. eapply perm_storebytes_2; eauto.
- exploit ma_perm_inv; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
- rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite PMap.gsspec. destruct (peq b0 b).
+ subst b0. rewrite setN_outside. eapply ma_memval; eauto. eapply perm_storebytes_2; eauto.
  destruct (zlt ofs0 ofs); auto. destruct (zle (ofs + Z.of_nat (length bytes1)) ofs0); try omega.
  elim (H1 ofs0). omega. auto.
+ eapply ma_memval; eauto. eapply perm_storebytes_2; eauto.
- rewrite (nextblock_storebytes _ _ _ _ _ H0).
  eapply ma_nextblock; eauto.
- rewrite (storebytes_stack_adt _ _ _ _ _ H0).
  eapply stack_inject_invariant_strong.
  2: eapply ma_stack_adt; eauto.
  unfold inject_id. intros b0 ofs0 k p b' delta H3 H4. inv H3.
  eapply perm_storebytes_2; eauto.
- rewrite_stack_backwards; inv H; auto.
Qed.

Lemma magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P.
Proof.
  intros. eapply magree_storebytes_left; eauto.
  eapply store_storebytes; eauto.
  intros. rewrite encode_val_length in H2.
  rewrite <- size_chunk_conv in H2. apply H1; auto.
Qed.

Lemma magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
  magree m1 m2 P ->
  inject_perm_condition Freeable ->
  free m1 b lo hi = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ ~(lo <= i < hi) ->
                P b' i) ->
  exists m2', free m2 b lo hi = Some m2' /\ magree m1' m2' Q.
Proof.
  intros m1 m2 P Q b lo hi m1' MAGREE IPC FREE COND.
  destruct (range_perm_free' m2 b lo hi) as [m2' FREE'].
  red; intros. eapply ma_perm; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  constructor; intros.
- (* permissions *)
  assert (perm m2 b0 ofs k p). { eapply ma_perm; eauto. eapply perm_free_3; eauto. }
  exploit perm_free_inv; eauto. intros [[A B] | A]; auto.
  subst b0. eelim perm_free_2. eexact FREE. eauto. eauto.
- (* inverse permissions *)
  exploit ma_perm_inv; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B] | A]; auto.
  subst b0; right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
- (* contents *)
  rewrite (free_result _ _ _ _ _ FREE).
  rewrite (free_result _ _ _ _ _ FREE').
  simpl. eapply ma_memval; eauto. eapply perm_free_3; eauto.
  apply COND; auto. destruct (eq_block b0 b); auto.
  subst b0. right. red; intros. eelim perm_free_2. eexact FREE. eauto. eauto.
- (* nextblock *)
  rewrite (free_result _ _ _ _ _ FREE).
  rewrite (free_result _ _ _ _ _ FREE').
  simpl. eapply ma_nextblock; eauto.
- rewrite (free_stack_adt _ _ _ _ _ FREE').
  rewrite (free_stack_adt _ _ _ _ _ FREE).
  eapply stack_inject_invariant_strong.
  2: eapply ma_stack_adt; eauto.
  unfold inject_id. intros b0 ofs0 k p b' delta H3 H4. inv H3.
  eapply perm_free_3; eauto.
- rewrite_stack_backwards; inv MAGREE; auto.
Qed.

Lemma magree_valid_access:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  valid_access m1 chunk b ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. destruct H0 as (A & B & C); split; [|split]; auto.
  red; intros. eapply ma_perm; eauto.
  intros. specialize (C H0).
  eapply stack_access_magree; eauto.
Qed.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (plt b1 (nextblock m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f g m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f g m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  perm m1 b1 ofs k p ->
  inject_perm_condition p ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

Theorem perm_inject_inv:
  forall f g m1 m2 b1 ofs b2 delta k p,
  inject f g m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

Theorem range_perm_inject:
  forall f g m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  inject_perm_condition p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  (perm_order p Writable -> frameinj_pack_after O g) ->
  inject_perm_condition p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; eauto.
Qed.

Theorem valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto. inversion 1.
  eapply inject_perm_condition_writable; constructor.
Qed.

Theorem weak_valid_pointer_inject:
  forall f g m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f g m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by omega.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of g machine integer overflow
  during address computations. *)

Lemma delta_pos:
  forall f g m1 m2 b1 b2 delta,
  inject f g m1 m2 ->
  f b1 = Some (b2, delta) ->
  delta >= 0.
Proof.
  intros.
  exploit mi_representable; eauto. intuition. 
Qed.

Lemma address_inject:
  forall f g m1 m2 b1 ofs1 b2 delta p,
  inject f g m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  exploit B; eauto. clear B; intro B.
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). omega.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; omega.
Qed.

Lemma address_inject':
  forall f g m1 m2 chunk b1 ofs1 b2 delta,
  inject f g m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). omega.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. 
  intros [A B]. exploit B; eauto.
  destruct H0; eauto with mem.
  pose proof (Ptrofs.unsigned_range ofs). intro.
  rewrite Ptrofs.unsigned_repr. auto.
  omega.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f g m1 m2 b ofs b' delta,
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f g m1 m2 b ofs b' ofs',
  inject f g m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. 
  intros [A B]. exploit B; eauto.
  destruct H0; eauto with mem. intros.
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; omega.
Qed.

Theorem inject_no_overlap:
  forall f g m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f g m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

Theorem different_pointers_inject:
  forall f g m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f g m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). omega.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). omega.
Qed.

Theorem disjoint_or_equal_inject:
  forall f g m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f g m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. omega.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try omega.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. omega.
  instantiate (1 := x - delta2). apply H3. omega.
  intuition.
Qed.

Theorem aligned_area_inject:
  forall f g m m' b ofs al sz b' delta,
  inject f g m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by omega.
  assert (Q: Zabs al <= Zabs sz). apply Zdivide_bounds; auto. omega.
  rewrite Zabs_eq in Q; try omega. rewrite Zabs_eq in Q; try omega.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. omega. split. congruence.
    inversion 1.
    exploit valid_access_inject; eauto. inversion 1.
    eapply inject_perm_condition_writable; constructor.
    unfold valid_access. intros (C & D & E).
    congruence.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f g m1 m2 chunk b1 ofs b2 delta v1,
  inject f g m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

Theorem loadv_inject:
  forall f g m1 m2 chunk a1 a2 v1,
  inject f g m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f g m1 m2 b1 ofs len b2 delta bytes1,
  inject f g m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  frameinj_pack_after O g ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f g n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; eauto. intros ofs0 P. eapply B.
  destruct P; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_unmapped_inject:
  forall f g chunk m1 b1 ofs v1 n1 m2,
  inject f g m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. exploit mi_representable; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2. 
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_inject:
  forall f g m1 m2 chunk b ofs v m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

Theorem storev_mapped_inject:
  forall f g chunk m1 a1 v1 n1 m2 a2 v2,
  inject f g m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  frameinj_pack_after O g ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f g n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem storebytes_mapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  frameinj_pack_after O g ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f g n1 n2.
Proof.
  intros f g m1 b1 ofs bytes1 n1 m2 b2 delta bytes2 H H0 H1 FPA H2.
  inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2. 
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_unmapped_inject:
  forall f g m1 b1 ofs bytes1 n1 m2,
  inject f g m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f g n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_inject:
  forall f g m1 m2 b ofs bytes2 m2',
  inject f g m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
Qed.

Theorem storebytes_empty_inject:
  forall f g m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f g m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f g m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. exploit mi_representable0; eauto.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2. 
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f g m1 m2 lo hi b2 m2',
  inject f g m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f g m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto. 
  eapply mi_perm_inv0; eauto.
Qed.

Lemma in_frame_is_in_frames:
  forall l f b,
    In f l ->
    in_frame f b ->
    in_frames l b.
Proof.
  induction l; simpl; intros; eauto.
  destruct H; subst; auto.
  destruct a; eauto.
Qed.

(** The following shows how to transport a stack injection when more blocks get
injected. We have an hypothesis about those new blocks. Namely, they are not
part of the source stack, and if the block they're injected to is part of the
stack, then the corresponding locations have the public stack permission. The
typical case when a new block is not in the stack but the target block they
inject to is already in is Inlining, where the parent function clearly already
exists and is already on the stack when the block for the callee is allocated.
Another scenario is generation of single-stack-block Asm, where the unique stack
block is also present and part of the stack when the 'source' blocks get
allocated. *)

Lemma stack_inject_incr:
  forall f f' g (p: block -> Z -> perm_kind -> permission -> Prop)  s1 s2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_frames s1 b
        /\ forall f2 fi,
            In f2 s2 ->
            in_frame f2 b' ->
            frame_adt_info f2 = Some fi ->
            forall o k pp,
              p b o k pp ->
              inject_perm_condition pp ->
              frame_public fi (o + delta)) ->
    stack_inject f g p s1 s2 ->
    stack_inject f' g p s1 s2.
Proof.
  intros f f' g p s1 s2 INCR NEW SI.
  inv SI; constructor; eauto.
  - intros i1 f1 i2 FAP GI.
    exploit stack_inject_frames; eauto.
    intros (f2 & FP & FI).
    exists f2; intuition.
    eapply frame_inject_incr; eauto.
    intros b b' delta NONE SOME IFR.
    eapply NEW in SOME; eauto. destruct SOME as (NIN & _) ; eapply NIN. eapply in_frames_in_frame; eauto.
    eapply frame_at_pos_In; eauto.
  - intros b1 b2 delta SOME i1 f1 FAP IFR.
    destruct (f b1) as [[b2' delta']|] eqn:FB.
    exploit INCR. eauto. rewrite SOME. inversion 1; subst.
    eauto.
    generalize (NEW _ _ _ FB SOME). intros NIN; exfalso; apply NIN.
    eapply in_frames_in_frame; eauto. eapply frame_at_pos_In; eauto.
  - intros b1 b2 delta f2 fi SOME NIFR INS INF FINFO o k p0 P IPC.
    destruct (f b1) as [[b2' delta']|] eqn:FB.
    exploit INCR. eauto. rewrite SOME. inversion 1; subst.
    eauto.
    generalize (NEW _ _ _ FB SOME). intros (NIN1 & NIN2); eapply NIN2; eauto.
Qed.

Lemma stack_injection_incr:
  forall f f' g (p: block -> Z -> perm_kind -> permission -> Prop) s1 s2,
    inject_incr f f' ->
    (forall b b' delta,
        f b = None ->
        f' b = Some (b', delta) ->
        ~ in_frames s1 b
        /\ forall f2 fi,
            In f2 s2 ->
            in_frame f2 b' ->
            frame_adt_info f2 = Some fi ->
            forall o k pp,
              p b o k pp ->
              inject_perm_condition pp ->
              frame_public fi (o + delta)) ->
    stack_inject f g p s1 s2 ->
    stack_inject f' g p s1 s2.
Proof.
  intros f f' g p s1 s2 H H0 SI.
  eapply stack_inject_incr; eauto.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f g m1 m2 lo hi m1' b1,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
  {
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  }
  assert (mem_inj f' g m1 m2).
  {
    inversion mi_inj0; constructor; eauto with mem.
    - unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    - unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    - unfold f'; intros. destruct (eq_block b0 b1). congruence.
      apply memval_inject_incr with f; auto.
    - eapply stack_injection_incr; eauto.
      unfold f'; intros b b' delta NONE SOME.
      destr_in SOME.
  }
  exists f'; repeat refine (conj _ _).
  - constructor.
    + (* inj *)
      eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
    + (* freeblocks *)
      intros. unfold f'. destruct (eq_block b b1). auto.
      apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
    + (* mappedblocks *)
      unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    + (* no overlap *)
      unfold f'; red; intros.
      destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
      eapply mi_no_overlap0. eexact H3. eauto. eauto.
      exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
      exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
    + (* representable *)
      unfold f'; intros.
      destruct (eq_block b b1); try discriminate.
      exploit mi_representable0; try eassumption.
      intros [A B]; split; auto.
      intros; eapply B; eauto.
      destruct H4; eauto using perm_alloc_4.
    + (* perm inv *)
      intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
      exploit mi_perm_inv0; eauto. 
      intuition eauto using perm_alloc_1, perm_alloc_4.
  - (* incr *)
    auto.
  - (* image *)
    unfold f'; apply dec_eq_true.
  - (* incr *)
    intros; unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f g m1 m2 lo hi m1' b1 b2 delta,
  inject f g m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> inject_perm_condition p -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  (forall f2 fi,
      In f2 (stack_adt m2) ->
      in_frame f2 b2 ->
      frame_adt_info f2 = Some fi ->
      forall o k pp,
        perm m1' b1 o k pp ->
        inject_perm_condition pp ->
        frame_public fi (o + delta)) ->
  exists f',
     inject f' g m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros f g m1 m2 lo hi m1' b1 b2 delta H H0 H1 H2 H3 H4 H5 H6 NIF.
  inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
  {
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  }
  assert (mem_inj f' g m1 m2).
  {
    inversion mi_inj0; constructor; eauto with mem.
    - unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    - unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); omega.
      eauto.
    - unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
    - eapply stack_injection_incr; eauto.
      unfold f'. intros b b' delta0 NONE SOME. destr_in SOME. inv SOME.
      split; auto.
      intro IFR.
      apply fresh_block_alloc in H0.
      apply H0. eapply stack_valid. auto.
      intros; eapply NIF; eauto.
      eapply perm_alloc_1; eauto.
  }
  exists f'; repeat refine (conj _ _).
  - constructor.
    + (* inj *)
      eapply alloc_left_mapped_inj; eauto.
      unfold f'; apply dec_eq_true.
    + (* freeblocks *)
      unfold f'; intros. destruct (eq_block b b1). subst b.
      elim H9. eauto with mem.
      eauto with mem.
    + (* mappedblocks *)
      unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
    + (* overlap *)
      unfold f'; red; intros.
      exploit perm_alloc_inv. eauto. eexact H12. intros P1.
      exploit perm_alloc_inv. eauto. eexact H13. intros P2.
      destruct (eq_block b0 b1); destruct (eq_block b3 b1).
      congruence.
      inversion H10; subst b0 b1' delta1.
      destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
      eapply H6; eauto. omega.
      inversion H11; subst b3 b2' delta2.
      destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
      eapply H6; eauto. omega.
      eauto.
    + (* representable *)
      {
        unfold f'; intros.
        destruct (eq_block b b1).
        - subst. injection H9; intros; subst b' delta0.
          split. omega.
          intros.
          destruct H10.
          exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
          exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
          eapply inject_perm_condition_writable; constructor.
          generalize (Ptrofs.unsigned_range_2 ofs). omega.
          exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
          exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
          eapply inject_perm_condition_writable; constructor.
          generalize (Ptrofs.unsigned_range_2 ofs). omega.
        - exploit mi_representable0; try eassumption.
          intros [A B]; split; auto.
          intros; eapply B; eauto.
          destruct H10; eauto using perm_alloc_4.
      }
    + (* perm inv *)
      intros. unfold f' in H9; destruct (eq_block b0 b1).
      inversion H9; clear H9; subst b0 b3 delta0.
      assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by omega.
      destruct EITHER.
      left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
      right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
      exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
  - (* incr *)
    auto.
  - (* image of b1 *)
    unfold f'; apply dec_eq_true.
  - (* image of others *)
    intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_parallel_inject:
  forall f g m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f g m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' g m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  eapply alloc_right_inject; eauto.
  eauto.
  instantiate (1 := b2). eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; omega.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  red; intros. apply Zdivide_0.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  erewrite alloc_stack_adt. 2: eauto.
  intros f2 fi NIF NIF'. exploit in_frames_in_frame; eauto. intro A.
  apply stack_valid in A.
  eapply fresh_block_alloc in A; eauto. easy.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f g m1 m2 b lo hi m1',
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f g m1' m2.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros.   exploit mi_representable0; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto. 
Qed.

Lemma free_list_left_inject:
  forall f g m2 l m1 m1',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f g m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
Qed.

Lemma free_right_inject:
  forall f g m1 m2 b lo hi m2',
  inject f g m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.
Proof.
  intros. inversion H. constructor.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f g m1 l m1' m2 b lo hi m2',
  inject f g m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f g m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Theorem free_parallel_inject:
  forall f g m1 m2 b lo hi m1' b' delta,
  inject f g m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  inject_perm_condition Freeable ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f g m1' m2'.
Proof.
  intros f g m1 m2 b lo hi m1' b' delta INJ FREE FB IPC.
  destruct (range_perm_free' m2 b' (lo + delta) (hi + delta)) as [m2' FREE'].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite FREE; auto.
  intros b1 delta0 ofs k p FB1 PERM RNG.
  destruct (eq_block b1 b).
  subst b1. rewrite FB1 in FB; inv FB.
  exists lo, hi; split; auto with coqlib. omega.
  exploit mi_no_overlap. eexact INJ. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. omega.
  intros [A|A]. congruence. omega.
Qed.

Lemma drop_outside_inject: forall f g m1 m2 b lo hi p m2',
  inject f g m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f g m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite nextblock_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

(** The following property is needed by Unusedglobproof, to prove
    injection between the initial memory states. *)

Lemma zero_delta_inject f g m1 m2:
  (forall b1 b2 delta, f b1 = Some (b2, delta) -> delta = 0) ->
  (forall b1 b2, f b1 = Some (b2, 0) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2) ->
  (forall b1 p, f b1 = Some p -> forall b2, f b2 = Some p -> b1 = b2) ->
  (forall b1 b2,
     f b1 = Some (b2, 0) ->
     forall o k p,
       Mem.perm m1 b1 o k p ->
       inject_perm_condition p ->
       Mem.perm m2 b2 o k p) ->
  (forall b1 b2,
     f b1 = Some (b2, 0) ->
     forall o k p,
       Mem.perm m2 b2 o k p ->
       Mem.perm m1 b1 o k p \/ ~ Mem.perm m1 b1 o Max Nonempty) ->
  (forall b1 b2,
     f b1 = Some (b2, 0) ->
     forall o v1,
       loadbytes m1 b1 o 1 = Some (v1 :: nil) ->
       exists v2,
         loadbytes m2 b2 o 1 = Some (v2 :: nil) /\
         memval_inject f v1 v2) ->
  stack_inject f g (perm m1) (stack_adt m1) (stack_adt m2) ->
  Mem.inject f g m1 m2.
Proof.
  intros Delta0 VB NODUP PERM PERMINV LOADBYTES STACK.
  constructor.
  {
    constructor.
    - intros b1 b2 delta ofs k p FB1 PERM' IPC.
      specialize (Delta0 _ _ _ FB1).
      subst.
      rewrite Z.add_0_r.
      eapply PERM; eauto.
    - intros b1 b2 delta chunk ofs p FB1 RP.
      specialize (Delta0 _ _ _ FB1).
      subst.
      exists 0. omega.
    - intros b1 ofs b2 delta H3 H4.
      specialize (Delta0 _ _ _ H3).
      subst.
      rewrite Z.add_0_r.
      specialize (LOADBYTES _ _ H3 ofs).
      revert LOADBYTES.
      unfold loadbytes.
      destruct (range_perm_dec m1 b1 ofs (ofs + 1) Cur Readable) as [ | n1].
      + simpl.
        destruct (range_perm_dec m2 b2 ofs (ofs + 1) Cur Readable) as [ | n2].
        {
          intro H2.
          specialize (H2 _ (eq_refl _)).
          destruct H2 as (? & H2 & INJ).
          congruence.
        }
        destruct n2.
        red. intros ofs0 H.
        eapply PERM; eauto.
        eapply inject_perm_condition_writable; constructor.
      + destruct n1.
        red. intros ofs0 H.
        replace ofs0 with ofs by omega.
        assumption.
    - assumption.
  }
  + intros b H3.
    destruct (f b) as [ [ ] | ] eqn:F; auto.
    specialize (Delta0 _ _ _ F).
    subst.
    destruct H3.
    eapply VB; eauto.
  + intros b b' delta H3.
    specialize (Delta0 _ _ _ H3).
    subst.
    eapply VB; eauto.
  + unfold meminj_no_overlap.
    intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 H3 H4 H5 H6 H7.
    generalize (Delta0 _ _ _ H4). intro; subst.
    generalize (Delta0 _ _ _ H5). intro; subst.
    left.
    intro; subst.
    destruct H3; eauto.
  + intros b b' delta H3.
    specialize (Delta0 _ _ _ H3).
    subst.
    split.
    * omega.
    * intros. rewrite Z.add_0_r. apply Ptrofs.unsigned_range_2.
  + intros b1 ofs b2 delta k p H3 H4.
    exploit Delta0; eauto. intro; subst.
    eapply PERMINV; eauto.
    replace ofs with (ofs + 0) by omega.
    assumption.
Qed.

(** The following is a consequence of the above. It is needed by
    ValueDomain, to prove mmatch_inj. *)

Lemma self_inject f m:
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> Mem.valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  Mem.inject f (flat_frameinj (length (stack_adt m))) m m.
Proof.
  intros H H0 H1.
  apply zero_delta_inject.
  + intros b1 b2 delta H2.
    destruct (H b1); congruence.
  + intros b1 b2 H2.
    destruct (H b1); try congruence.
    replace b2 with b1 by congruence.
    assert (f b1 <> None) by congruence.
    auto.
  + intros b1 p H2 b2 H3.
    destruct (H b1); destruct (H b2); congruence.
  + intros b1 b2 H2 o k p H3.
    destruct (H b1); congruence.
  + intros b1 b2 H2 o k p H3.
    destruct (H b1); intuition congruence.
  + intros b1 b2 H2 o v1 H3.
    destruct (H b1); try congruence.
    replace b2 with b1 by congruence.
    esplit.
    split; eauto.
    destruct v1 as [ | | v]; try constructor.
    destruct v as [ | | | | | b ]; try constructor.
    apply H1 in H3; try congruence.
    destruct (H b); try congruence.
    econstructor; eauto.
    rewrite Ptrofs.add_zero.
    reflexivity.
  + unfold flat_frameinj. constructor.
    * red; intros. destr_in H3; destr_in H4. 
    * intros i1 f1 i2 FAP EQ; destr_in EQ; inv EQ. 
      exists f1; intuition.
      eapply self_inject_frame; eauto.
    * intros b1 b2 delta FB i1 f1 FAP IFR.
      destruct (H b1) as [A|A]; rewrite A in FB; inv FB.
      exists i1, f1; intuition.
      apply frame_at_pos_lt in FAP. destr.
    * intros.
      destruct (H b1); try congruence.
      rewrite H2 in H9; inv H9.
      exfalso; apply H3. eapply in_frames_in_frame; eauto.
    * intros i j A; destr_in A.
    * intros; exists i; destr.
    * intros i j A; repeat destr_in A. omega.
    * intros i1 i2 f1 f2 FAP1 FAP2 A; repeat destr_in A.
      assert (f1=f2) by (eapply frame_at_same_pos; eauto). subst. auto.
Qed.

(** Composing two memory injections. *)

Lemma mem_inj_compose:
  forall f f' g g' m1 m2 m3,
    mem_inj f g m1 m2 -> mem_inj f' g' m2 m3 -> frameinj_surjective g (length (stack_adt m2)) ->
    mem_inj (compose_meminj f f') (compose_frameinj g g') m1 m3.
Proof.
  intros f f' g g' m1 m2 m3 H H0 SURJ.
  unfold compose_meminj. inv H; inv H0; constructor.
  - (* perm *)
    intros b1 b2 delta ofs k p CINJ PERM IPC.
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv CINJ.
    replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega.
    eauto.
  - (* align *)
    intros b1 b2 delta chunk ofs p CINJ RP.
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv CINJ.
    apply Z.divide_add_r.
    eapply mi_align0; eauto.
    eapply mi_align1 with (ofs := ofs + delta') (p := Nonempty); eauto.
    red; intros. replace ofs0 with ((ofs0 - delta') + delta') by omega.
    eapply mi_perm0; eauto. eapply perm_implies. apply RP. omega.
    constructor.
    apply inject_perm_condition_writable; constructor.
  - (* memval *)
    intros b1 ofs b2 delta CINJ PERM.
    destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
    destruct (f' b') as [[b'' delta''] |] eqn:?; inv CINJ.
    replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by omega.
    eapply memval_inject_compose; eauto.
    eapply mi_memval1; eauto.
    eapply mi_perm0; eauto.
    eapply inject_perm_condition_writable; constructor.
  - (* stack adt *)
    eapply stack_inject_compose; eauto.
Qed.

Theorem inject_compose:
  forall f f' g g' m1 m2 m3,
    inject f g m1 m2 -> inject f' g' m2 m3 ->
    frameinj_surjective g (length (stack_adt m2)) ->
    inject (compose_meminj f f') (compose_frameinj g g') m1 m3.
Proof.
  intros f f' g g' m1 m2 m3 H H0 SURJ.
  unfold compose_meminj; inv H; inv H0. constructor.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; omega.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H2. eauto. eapply inject_perm_condition_writable; constructor.
    eapply perm_inj. eauto. eexact H3. eauto. eapply inject_perm_condition_writable; constructor.
  intuition omega.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  exploit mi_representable1. eauto. intros [C D]. 
  split; auto. omega.
  intros.
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
    exploit D. instantiate (1 := ofs').
  rewrite H0.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by omega.
  destruct H; eauto using perm_inj.
  left; eapply mi_perm; eauto.
  eapply inject_perm_condition_writable; constructor.
  right; eapply mi_perm; eauto.
  eapply inject_perm_condition_writable; constructor.
  rewrite H0. omega.
(* perm inv *)
  intros. 
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by omega.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
  eapply inject_perm_condition_writable; constructor.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

Lemma lt_lt_eq:
  (forall a b, a = b <-> (forall i, i < a <-> i < b))%nat.
Proof.
  split; intros; subst. tauto.
  destruct (lt_dec a b).
  specialize (H a). omega.
  destruct (lt_dec b a).
  specialize (H b). omega.
  omega.
Qed.

Lemma extends_inject_compose:
  forall f g m1 m2 m3,
  extends m1 m2 -> inject f g m2 m3 -> inject f g m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj inject_id f).
  replace g with (compose_frameinj (flat_frameinj (length (stack_adt m1))) g).
  eapply mem_inj_compose; eauto.
  {
    rewrite mext_length_stack0; apply frameinj_surjective_flat; auto.
  }
  {
    apply extensionality. unfold compose_frameinj. intros.
    unfold flat_frameinj. destruct lt_dec. auto.
    destruct (g x) eqn:GX; auto.
    inv mi_inj0.
    eapply stack_inject_range in GX; eauto.
    erewrite <- mext_length_stack0 in n. omega.
   }
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
  eapply inject_perm_condition_writable; constructor.
  eapply inject_perm_condition_writable; constructor.
  (* representable *)
  exploit mi_representable0; try eassumption.
  intros [A B]; split; auto.
  intros; eapply B; eauto.
  destruct H1; [left|right]; eapply perm_extends; eauto.
  eapply inject_perm_condition_writable; constructor.
  eapply inject_perm_condition_writable; constructor.
  (* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
  eapply inject_perm_condition_writable; constructor.
Qed.

Lemma inject_extends_compose:
  forall f g m1 m2 m3,
    frameinj_surjective g (length (stack_adt m2)) ->
    inject f g m1 m2 -> extends m2 m3 -> inject f g m1 m3.
Proof.
  intros f g m1 m2 m3 SURJ H H0. inv H; inversion H0. constructor; intros.
(* inj *)
  replace f with (compose_meminj f inject_id).
  replace g with (compose_frameinj g (flat_frameinj (length (stack_adt m2)))).
  eapply mem_inj_compose; eauto.
  {
    apply extensionality. unfold compose_frameinj. intros.
    unfold flat_frameinj. destr. 
    inv mi_inj0.
    eapply stack_inject_range in Heqo; eauto.
    destr.
   }
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. omega.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
  eapply inject_perm_condition_writable; constructor.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; inversion H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  replace (flat_frameinj (length (stack_adt m1))) with
      (compose_frameinj (flat_frameinj (length (stack_adt m1))) (flat_frameinj (length (stack_adt m2)))).
  eapply mem_inj_compose; eauto.
  rewrite mext_same_length0; apply surj_flat.
  {
    apply frameinj_surjective_flat. omega.
  }
  {
    apply extensionality; intros. unfold compose_frameinj, flat_frameinj.
    destruct lt_dec; auto.
    erewrite mext_length_stack0; eauto.
    destr.
  }
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A]. 
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
  eapply inject_perm_condition_writable; constructor.
  congruence.
Qed.

Remark flat_inj_no_overlap:
  forall thr m, meminj_no_overlap (flat_inj thr) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (plt b1 thr); inversion H0; subst.
  destruct (plt b2 thr); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (nextblock m) m -> inject (flat_inj (nextblock m)) (flat_frameinj (length (stack_adt m))) m m.
Proof.
  intros. constructor.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (plt b (nextblock m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (plt b (nextblock m)); inv H0. split; auto. omega. intros. generalize (Ptrofs.unsigned_range_2 ofs); omega.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (plt b1 (nextblock m)); inv H0.
  rewrite Zplus_0_r in H1; auto.
Qed.

Theorem empty_inject_neutral:
  forall thr, inject_neutral thr empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H.
  replace (ofs + 0) with ofs by omega; auto.
(* align *)
  unfold flat_inj; intros. destruct (plt b1 thr); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. rewrite ! PMap.gi. rewrite ! ZMap.gi. constructor.
  (* stack adt *)
  apply stack_inject_nil.
Qed.

Theorem alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m'.
Proof.
  intros; red.
  erewrite alloc_stack_adt; eauto.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Zdivide_0.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. omega.
  unfold flat_inj. apply pred_dec_true.
  rewrite (alloc_result _ _ _ _ _ H). auto.
  intros. exfalso; apply H2. apply stack_valid. eapply in_frames_in_frame; eauto.
  rewrite <- (alloc_stack_adt _ _ _ _ _ H); eauto.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  eauto.
  replace (ofs + 0) with ofs by omega.
  intros [m'' [A B]].
  erewrite store_stack_adt; eauto. congruence.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  (* inject_perm_condition Freeable -> *)
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto.
  3: unfold flat_inj; apply pred_dec_true; eauto.
  repeat rewrite Zplus_0_r. eapply range_perm_drop_1. eauto.
  apply flat_inj_no_overlap.
  repeat rewrite Zplus_0_r. intros [m'' [A B]].
  erewrite drop_perm_stack_adt; eauto.
  congruence.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Lemma unchanged_on_refl:
  forall m, unchanged_on P m m.
Proof.
  intros; constructor. apply Ple_refl. tauto. tauto. 
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on P m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_nextblock in H. xomega.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on P m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto. 
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on P m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on P m1 m2 -> unchanged_on P m2 m3 -> unchanged_on P m1 m3.
Proof.
  intros; constructor.
- apply Ple_trans with (nextblock m2); eapply unchanged_on_nextblock; eauto.
- intros. transitivity (perm m2 b ofs k p); eapply unchanged_on_perm; eauto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); eapply unchanged_on_contents; eauto.
  eapply perm_unchanged_on; eauto.
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite nat_of_Z_eq in H by omega.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). omega.
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b ofs,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  destruct v as (A & B & C). rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H2. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  split; auto. inversion 1.
  rewrite pred_dec_false. auto.
  red; intros [A [B C]]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
  split; auto. inversion 1.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs v,
  unchanged_on P m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_store _ _ _ _ _ _ H). apply Ple_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). omega. auto.
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_storebytes _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite PMap.gsspec.
  destruct (peq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z_of_nat (length bytes))); auto.
  elim (H0 ofs0). omega. auto.
Qed.

Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on P m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_alloc _ _ _ _ _ H). apply Ple_succ.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  rewrite PMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_free _ _ _ _ _ H). apply Ple_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). omega. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

Lemma drop_perm_unchanged_on:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros; constructor; intros.
- rewrite (nextblock_drop _ _ _ _ _ _ H). apply Ple_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0. 
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; omega.
  eapply perm_drop_4; eauto. 
- unfold drop_perm in H. 
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto.
Qed. 


End UNCHANGED_ON.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
- auto.
- apply unchanged_on_perm0; auto. 
- apply unchanged_on_contents0; auto. 
  apply H0; auto. eapply perm_valid_block; eauto. 
Qed.

(** The following property is needed by Separation, to prove minjection. *)

Lemma inject_unchanged_on j g m0 m m' :
   inject j g m0 m ->
   unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack_adt m' = stack_adt m ->
   inject j g m0 m' .
Proof.
  intro INJ.
  set (img := fun b' ofs => exists b delta, j b = Some(b', delta) /\ perm m0 b (ofs - delta) Max Nonempty) in *.
  assert (IMG: forall b1 b2 delta ofs k p,
           j b1 = Some (b2, delta) -> perm m0 b1 ofs k p -> img b2 (ofs + delta)).
  { intros. red. exists b1, delta; split; auto. 
    replace (ofs + delta - delta) with ofs by omega.
    eauto with mem. }
  inversion INJ; constructor.
- destruct mi_inj0. constructor; intros.
+ eapply perm_unchanged_on; eauto.
+ eauto.
+ rewrite (unchanged_on_contents _ _ _ H); eauto.
  eapply mi_perm0; eauto.
  eapply inject_perm_condition_writable; constructor.
+ rewrite H0; auto.
- assumption.
- intros. eapply valid_block_unchanged_on; eauto.
- assumption.
- assumption.
- intros. destruct (perm_dec m0 b1 ofs Max Nonempty); auto.
  eapply mi_perm_inv; eauto. 
  eapply perm_unchanged_on_2; eauto.
Qed.

(* Properties of unrecord_stack_block *)

Lemma unrecord_stack_block_mem_unchanged:
  mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2).
Proof.
  red; intros.
  unfold_unrecord; simpl; repeat split; eauto.
  simpl. xomega.
  unfold load. intros.
  simpl.
  repeat match goal with
           |- context [match ?a with _ => _ end] => destruct a eqn:?; simpl; intros; try intuition congruence
         end.
  exfalso. apply n.
  destruct v as (v1 & v2 & v3) ; simpl in *; repeat split; eauto. inversion 1.
  exfalso. apply n.
  destruct v as (v1 & v2 & v3) ; simpl in *; repeat split; eauto. inversion 1.
Qed.

Lemma unrecord_stack_adt:
   forall m m',
     unrecord_stack_block m = Some m' ->
     exists b,
       stack_adt m = b :: stack_adt m'.
Proof.
  intros. unfold_unrecord. simpl. rewrite H0. eauto.
Qed.

Lemma stack_adt_eq_get_frame_info:
  forall m m' b,
    stack_adt m = stack_adt m' ->
    get_frame_info (stack_adt m) b = get_frame_info (stack_adt m') b.
Proof.
  unfold get_frame_info. congruence.
Qed.

Lemma stack_adt_eq_is_stack_top:
  forall m m' b,
    stack_adt m = stack_adt m' ->
    is_stack_top (stack_adt m) b <-> is_stack_top (stack_adt m') b.
Proof.
  unfold is_stack_top, get_stack_top_blocks. intros m m' b H. rewrite H. tauto.
Qed.

Lemma record_stack_blocks_mem_unchanged:
  forall f, mem_unchanged (fun m1 m2 => record_stack_blocks m1 f m2).
Proof.
  red; intros. inv H. 
  simpl; repeat split; eauto.
  simpl. xomega.
  unfold load. intros.
  simpl.
  repeat match goal with
           |- context [match ?a with _ => _ end] => destruct a eqn:?; simpl; intros; try intuition congruence
         end.
  exfalso. apply n.
  destruct v as (v1 & v2 & v3) ; simpl in *; repeat split; eauto. inversion 1.
  exfalso. apply n.
  destruct v as (v1 & v2 & v3) ; simpl in *; repeat split; eauto. inversion 1.
Qed.

Lemma unrecord_stack_block_succeeds:
   forall m b r,
     stack_adt m = b :: r ->
     exists m',
       unrecord_stack_block m = Some m'
       /\ stack_adt m' = r.
Proof.
  unfold unrecord_stack_block.
  intros.
  setoid_rewrite H. eexists; split; eauto. simpl. rewrite H; reflexivity.
Qed.

Lemma inject_stack_adt:
   forall f g m1 m2,
     inject f g m1 m2 ->
     stack_inject f g (perm m1) (stack_adt m1) (stack_adt m2).
Proof.
  intros f g m1 m2 INJ.
  inv INJ. inv mi_inj0. auto. 
Qed.

Lemma extends_stack_adt:
   forall m1 m2,
     extends m1 m2 ->
     stack_inject inject_id (flat_frameinj (length (stack_adt m1))) (perm m1) (stack_adt m1) (stack_adt m2).
Proof.
  intros m1 m2 INJ.
  inv INJ. inv mext_inj0. auto. 
Qed.

Lemma public_stack_access_inj:
  forall f g m1 m2 b1 b2 delta lo hi p
    (MINJ : mem_inj f g m1 m2)
    (FB : f b1 = Some (b2, delta))
    (RP: range_perm m1 b1 lo hi Cur p)
    (NPSA: public_stack_access (stack_adt m1) b1 lo hi),
    public_stack_access (stack_adt m2) b2 (lo + delta) (hi + delta).
Proof.
  unfold public_stack_access.
  intros f g m1 m2 b1 b2 delta lo hi p MINJ FB RP.
  generalize (get_frame_info_inj _ _ _ _ _ _ _ MINJ FB).
  inversion 1.
  - (* None -> None *)
    auto.
  - (* Some a -> Some a*)
    destruct (zlt lo hi).
    + generalize (stack_perms m1); rewrite Forall_forall; intro A.
      edestruct get_assoc_spec as (ll & n & IN1 & IN2). setoid_rewrite <- H0. eauto.
      specialize (A _ IN1).
      red in A. simpl in *.
      specialize (fun o => A _ o Cur p IN2).
      generalize (A lo), (A (hi - 1)); intros B C.
      trim B. apply RP. omega.
      trim C. apply RP. omega.
      apply public_stack_range_shift; auto; omega.
    + red; intros. omega.
  - intros _.
    red. intros.
    replace ofs with ((ofs - delta) + delta) by omega.
    eapply H2.
    eapply perm_implies with (p2:=Nonempty). apply RP. omega.
    constructor.
    eapply inject_perm_condition_writable; constructor.
Qed.

Lemma public_stack_access_extends:
   forall m1 m2 b lo hi p,
     extends m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     public_stack_access (stack_adt m1) b lo hi ->
     public_stack_access (stack_adt m2) b lo hi.
Proof.
  intros.
  destruct H.
  eapply public_stack_access_inj in H1; eauto.
  2: unfold inject_id; reflexivity.
  rewrite ! Z.add_0_r in H1. auto.
Qed.

Lemma public_stack_access_inject:
   forall f g m1 m2 b b' delta lo hi p,
     f b = Some (b', delta) ->
     inject f g m1 m2 ->
     public_stack_access (stack_adt m1) b lo hi ->
     range_perm m1 b lo hi Cur p ->
     public_stack_access (stack_adt m2) b' (lo + delta) (hi + delta).
Proof.
  intros; eapply public_stack_access_inj; eauto. inv H0; eauto.
Qed.

Lemma frame_at_pos_cons:
  forall l i f a,
    frame_at_pos l i f ->
    frame_at_pos (a::l) (S i) f.
Proof.
  intros l i f a H; inv H; econstructor.
  simpl.
  auto.
Qed.

Lemma frame_at_pos_last:
  forall l a f,
    frame_at_pos (a::l) 0 f ->
    f = a.
Proof.
  intros l a f H. inv H. simpl in H0. congruence.
Qed.

Lemma frame_at_pos_same_frame:
  forall s i1 i2 f b,
    frame_at_pos s i1 f ->
    frame_at_pos s i2 f ->
    in_frame f b ->
    nodup s ->
    i1 = i2.
Proof.
  induction s; simpl; intros; eauto.
  - inv H.  rewrite nth_error_nil in H3. easy.
  - inv H; inv H0.
    destruct (Nat.eq_dec i1 i2); auto.
    exfalso.
    destruct (Nat.eq_dec i1 O).
    + subst. simpl in H3. inv H3.
      destruct i2. congruence. simpl in H. apply nth_error_In in H.
      inv H2. specialize (H5 _ H1). apply H5.
      eapply in_frames_in_frame; eauto.
    + destruct (Nat.eq_dec i2 0).
      * subst.
        simpl in H. inv H.
        destruct i1. congruence. simpl in H3. apply nth_error_In in H3.
        inv H2. specialize (H5 _ H1). apply H5.
        eapply in_frames_in_frame; eauto.
      * destruct i1, i2; try congruence. simpl in *.
        apply n. f_equal. eapply IHs; eauto.
        constructor; auto. constructor; auto.
        apply nodup_tl in H2.
        simpl in *; auto.
Qed.

Open Scope nat_scope.

Definition packed_frameinj (g: nat -> option nat) (s1 s2: nat) :=
  forall j,
    j < s2 ->
    exists lo hi,
      lo < hi <= s1 /\ (forall o, lo <= o < hi <-> g o = Some j).



Lemma preserves_order_inv:
  forall g,
    frameinj_preserves_order g ->
    forall j1 j2 i1 i2,
      j1 < j2 ->
      g i1 = Some j1 ->
      g i2 = Some j2 ->
      i1 < i2.
Proof.
  unfold frameinj_preserves_order.
  intros.
  destruct (le_lt_dec i2 i1); auto.
  eapply H in l. 2: eauto. 2: eauto.  omega.
Qed.


Definition frameinj_surjective_after (g: frameinj) (s2: nat) (thr: nat) :=
  forall j, thr <= j < s2 -> exists i, g i = Some j.

Lemma frameinj_S_spec:
  forall g n1 n2
    (FPO: frameinj_preserves_order g)
    (RNG: forall i j : nat, g i = Some j -> i < n1 /\ j < n2)
    (EX: frameinj_surjective_after g n2 1)
    (PACK : forall i j : nat, g i = Some j -> j <= i),
  forall j i : nat, g (S i) = Some j -> forall j0, g i = Some j0 -> j = j0 \/ j = S j0.
Proof.
  induction j; simpl; intros; eauto.
  - exploit FPO. 2: apply H0. 2: apply H. omega. intros. assert (j0 = 0) by omega. subst. auto.
  - generalize (PACK _ _ H0), (PACK _ _ H). intros.
    exploit (FPO i (S i)); eauto. intro.
    destruct (Nat.eq_dec j0 (S j)); subst; auto.
    destruct (Nat.eq_dec (S j0) (S j)); subst; auto.
    destruct (EX (S j0)). split. omega.
    eapply le_lt_trans with (S j).  omega.
    eapply RNG. eauto.
    exploit (preserves_order_inv _ FPO j0 (S j0)). omega. eauto. eauto.
    exploit (preserves_order_inv _ FPO (S j0) (S j)). omega. eauto. eauto.
    intros. omega.
Qed.

Lemma unrecord_stack_block_mem_inj_left:
  forall (m1 m1' m2 : mem) (j : meminj) g,
    mem_inj j g m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    frameinj_surjective g (length (stack_adt m2)) -> 
    g 1 = Some 0 ->
    (forall b, is_stack_top (stack_adt m1) b -> forall o k p, ~ Mem.perm m1 b o k p) ->
    mem_inj j (fun n => g (S n)) m1' m2.
Proof.
  intros m1 m1' m2 j g MI USB SURJ EXOTHERS TOPNOPERM.
  unfold_unrecord.
  inv MI; constructor; simpl; intros; eauto.
  eapply stack_inject_invariant_strong.
  - intros b ofs k p b' delta JB PERM. change (perm m1 b ofs k p) in PERM. eauto.
  - rewrite H in *. simpl in *.
    destruct mi_stack_blocks0; constructor; auto.
    + red; intros.
      simpl in *. eapply stack_inject_preserves_order. 2: apply H1. 2: apply H2. omega.
    + intros i1 f1 i2 FAP GS.
      eapply frame_at_pos_cons in FAP.
      edestruct stack_inject_frames as (f2 & FAP2 & FI); eauto.
    + intros.
      exploit frame_at_pos_cons. exact H1. intro FAP2.
      exploit stack_inject_compat. 2: eauto. 2: eauto. eauto.
      intros (i2 & f2 & FAP3 & IFR3 & XI). exists i2,f2; intuition.
    + simpl. intros b1 b2 delta f2 fi JB NIN INS INF FINFO o k p PERM IPC.
      destruct (in_frame_dec f b1).
      * eapply TOPNOPERM in PERM; eauto. easy.
      * eapply stack_inject_not_in_frames; eauto. simpl. intros [A|A]. congruence. congruence.
    + intros i j0 GS. 
      eapply stack_inject_range in GS. simpl in *.
      destruct GS; split; omega.
    + intros.
      destruct (stack_inject_exists_l (S i)); eauto. simpl; omega.
    (* + intros. *)
    (*   destruct (stack_inject_exists_r j0); eauto. *)
    (*   destruct (Nat.eq_dec x O). *)
    (*   * subst. *)
    (*     assert (j0 = 0). apply stack_inject_pack in H1. omega. subst; exists 0; auto. *)
    (*   * destruct x. congruence. eauto.  *)
    + generalize (frameinj_S_spec _ _ _ stack_inject_preserves_order stack_inject_range SURJ stack_inject_pack).
      intros GSSpec.
      induction i; simpl; intros; eauto.
      specialize (GSSpec _ _ H0).
      destruct (stack_inject_exists_l (S i)).
      apply stack_inject_range in H0. intuition.
      specialize (GSSpec _ H1). specialize (IHi _ H1).
      destruct GSSpec; subst. eauto. omega.
    + intros i1 i2 f1 f2 FAP1 FAP2 GS LT.
      eapply frame_at_pos_cons in FAP1. eapply stack_inject_sizes; eauto.
      intros i GI. destruct i. omega. apply Peano.le_n_S. apply LT. auto.
Qed.

Lemma frame_at_pos_cons_inv:
  forall a s i f,
    frame_at_pos (a::s) i f ->
    O < i ->
    frame_at_pos s (pred i) f.
Proof.
  intros a s i f FAP LT ; inv FAP.
  destruct i. omega.
  simpl in H. simpl. constructor; auto.
Qed.

Lemma unrecord_stack_block_mem_inj_parallel:
  forall (m1 m1' m2 : mem) (j : meminj) g
    (MINJ:  mem_inj j g m1 m2)
    (PACK: frameinj_pack_after O g)
    (USB: unrecord_stack_block m1 = Some m1')
    (NO0: forall i j, g i = Some j -> O < i -> O < j),
    exists m2',
      unrecord_stack_block m2 = Some m2' /\
      mem_inj j (fun n => option_map pred (g (S n))) m1' m2'.
Proof.
  intros.
  unfold_unrecord.
  destruct (stack_adt m2) eqn: STK2.
  {
    exfalso.
    inv MINJ. inv mi_stack_blocks0. 
    destruct (stack_inject_exists_l O). rewrite H. simpl; omega.
    apply stack_inject_range in H0. rewrite STK2 in H0. simpl in *. omega.
  }
  unfold unrecord_stack_block.
  setoid_rewrite STK2. eexists; split; eauto.
  inv MINJ; constructor; simpl; intros; eauto.
  {
    change (perm m1 b1 ofs k p) in H1.
    change (perm m2 b2 (ofs + delta) k p). eauto.
  }
  eapply stack_inject_invariant_strong.
  - intros b ofs k p b' delta JB PERM. change (perm m1 b ofs k p) in PERM. eauto.
  - rewrite H, STK2 in *. simpl in *.
    destruct mi_stack_blocks0; constructor; auto.
    + red; intros.
      unfold option_map in H1, H2. destr_in H1. destr_in H2. inv H1; inv H2.
      apply Nat.pred_le_mono. eapply stack_inject_preserves_order. 2-3 : eauto.  omega.
    + intros i1 f1 i2 FAP GS.
      unfold option_map in GS; repeat destr_in GS.
      eapply frame_at_pos_cons in FAP.
      edestruct stack_inject_frames as (f2 & FAP2 & FI); eauto.
      exploit NO0. eauto. omega. intro LT.
      apply frame_at_pos_cons_inv in FAP2; eauto.
    + intros.
      exploit frame_at_pos_cons. exact H1. intro FAP2.
      exploit stack_inject_compat. 2: eauto. 2: eauto. eauto.
      intros (i2 & f2 & FAP3 & IFR3 & XI).
      exploit NO0; eauto. omega. intro LT.
      apply frame_at_pos_cons_inv in FAP3; eauto.
      exists (pred i2),f2; intuition. rewrite XI. simpl. auto.
    + simpl. intros b1 b2 delta f2 fi JB NIN INS INF FINFO o k p PERM IPC.
      destruct (in_frame_dec f b1).
      * generalize (stack_inject_compat _ _ _ JB 0 f). intro A. trim A.
        constructor; simpl; auto. trim A; auto.
        destruct A as (i2 & f2' & FAP & INF' & G0).
        exploit PACK. 2: eauto. omega. intros. assert (i2 = 0) by omega.
        subst. inv FAP. simpl in H1. inv H1.
        exploit nodup_nodup'. apply stack_norepet. rewrite STK2.
        simpl; left; auto.
        rewrite STK2. simpl; right. eauto. eauto. eauto. intro; subst.
        exploit stack_norepet. rewrite STK2. intro A; inv A.
        exploit H4. eauto. eapply in_frames_in_frame; eauto. easy.
      * eapply stack_inject_not_in_frames; eauto. simpl. intros [A|A]. congruence. congruence.
        simpl; right; auto.
    + intros i j0 GS.
      unfold option_map in GS; repeat destr_in GS.
      exploit NO0; eauto. omega. intro. destruct n. omega. simpl.
      apply stack_inject_range in Heqo. simpl in *. omega.
    + intros.
      destruct (stack_inject_exists_l (S i)). simpl; omega. rewrite H1. simpl; eauto.
    (* + intros. *)
    (*   destruct (stack_inject_exists_r (S j0)); eauto. simpl; omega. *)
    (*   destruct (Nat.eq_dec x O). *)
    (*   * subst. *)
    (*     exploit stack_inject_pack; eauto. intros. omega.  *)
    (*   * destruct x. congruence. *)
    (*     exists (x); rewrite H1. simpl. auto. *)
    +
      intros.
      unfold option_map in H0. destr_in H0; inv H0.
      exploit stack_inject_pack; eauto. simpl.
      omega.
    + intros i1 i2 f1 f2 FAP1 FAP2 GS LT.
      unfold option_map in GS; destr_in GS; inv GS.
      eapply frame_at_pos_cons in FAP1.
      eapply frame_at_pos_cons in FAP2.
      eapply stack_inject_sizes; eauto.
      destruct n. eapply NO0 in Heqo. omega. omega. simpl. eauto.
      destruct n. eapply NO0 in Heqo. intros; omega. omega. simpl. eauto.
      intros i GI. destruct i. omega. apply Peano.le_n_S. apply LT. 
      rewrite GI. simpl. auto.
Qed.

Lemma unrecord_stack_block_inject_left:
  forall (m1 m1' m2 : mem) (j : meminj) g,
    inject j g m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    frameinj_surjective g (length (stack_adt m2)) ->
    g 1 = Some 0 ->
    (forall b, is_stack_top (stack_adt m1) b -> forall o k p, ~ Mem.perm m1 b o k p) ->
    inject j (fun n => g (S n)) m1' m2.
Proof.
  intros m1 m1' m2 j g INJ USB SURJ EXOTHERS NOPERM.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB). simpl. intros (NB & PERM & UNCH & LOAD).
  inv INJ; constructor; eauto.
  - eapply unrecord_stack_block_mem_inj_left; eauto. 
  - unfold valid_block; rewrite NB; eauto.
  - red; intros. rewrite PERM in H2, H3. eauto.
  - intros. exploit mi_representable0.  eauto. intros (A & B).
    split; auto. intros ofs. rewrite ! PERM. eauto.
  - intros. rewrite ! PERM; eauto.
Qed.

Lemma unrecord_stack_block_inject_parallel:
  forall (m1 m1' m2 : mem) (j : meminj) g,
    inject j g m1 m2 ->
    unrecord_stack_block m1 = Some m1' ->
    frameinj_pack_after O g ->
    (forall i j0, g i = Some j0 -> 0 < i -> 0 < j0) ->
    exists m2',
      unrecord_stack_block m2 = Some m2' /\
      inject j (fun n => option_map pred (g (S n))) m1' m2'.
Proof.
  intros m1 m1' m2 j g INJ USB PACK NOOTHER.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB). simpl. intros (NB & PERM & UNCH & LOAD).
  edestruct unrecord_stack_block_mem_inj_parallel as (m2' & USB' & MINJ); eauto. inv INJ; eauto.
  generalize (unrecord_stack_block_mem_unchanged _ _ USB'). simpl. intros (NB' & PERM' & UNCH' & LOAD').
  exists m2'; split; eauto.
  inv INJ; constructor; eauto.
  - unfold valid_block; rewrite NB; eauto.
  - unfold valid_block; rewrite NB'; eauto.
  - red; intros. rewrite PERM in H2, H3. eauto.
  - intros. exploit mi_representable0.  eauto. intros (A & B).
    split; auto. intros ofs. rewrite ! PERM. eauto.
  - intros. rewrite PERM' in H0. rewrite ! PERM; eauto.
Qed.

Lemma stack_inject_ext:
  forall j g g' P s1 s2,
    stack_inject j g P s1 s2 ->
    (forall x, g x = g' x) ->
    stack_inject j g' P s1 s2.
Proof.
  intros j g g' P s1 s2 SI EXT; inv SI; constructor; eauto.
  - red; intros; rewrite <- ! EXT in *; eauto.
  - intros; rewrite <- ! EXT in *; eauto.
  - intros; rewrite <- ! EXT in *; eauto.
  - intros; rewrite <- ! EXT in *; eauto.
  - intros; rewrite <- ! EXT in *; eauto.
  (* - intros. eapply stack_inject_exists_r in H; eauto. destruct H; eexists; eauto. *)
  (*   rewrite EXT in H; eauto.  *)
  - intros; rewrite <- ! EXT in *; eauto.
  - intros; rewrite <- ! EXT in *; eauto.
    eapply stack_inject_sizes; eauto.
    intros; rewrite ! EXT in *; eauto.
Qed.

Lemma mem_inj_frame_inj_ext:
  forall j g g' m1 m2,
    mem_inj j g m1 m2 ->
    (forall x, g x = g' x) ->
    mem_inj j g' m1 m2.
Proof.
  intros j g g' m1 m2 INJ EXT; inv INJ; constructor; auto.
  eapply stack_inject_ext; eauto.
Qed.

Lemma unrecord_stack_block_extends:
    forall m1 m2 m1',
      extends m1 m2 ->
      unrecord_stack_block m1 = Some m1' ->
      exists m2',
        unrecord_stack_block m2 = Some m2' /\
        extends m1' m2'.
Proof.
  intros.
  exploit unrecord_stack_block_mem_inj_parallel. inv H; eauto. eauto. eauto.
  unfold flat_frameinj. intros i j A; destr_in A; inv A.
  intros (m2' & A & B).
  eexists; split; eauto.
  exploit unrecord_stack_block_mem_unchanged. apply H0.
  intros (Eqnb1 & Perm1 & UNCH1 & LOAD1).
  exploit unrecord_stack_block_mem_unchanged. apply A.
  intros (Eqnb2 & Perm2 & UNCH2 & LOAD2).
  simpl in *.
  inv H. constructor; auto. congruence.
  eapply mem_inj_frame_inj_ext. eauto.
  simpl. unfold flat_frameinj. intros.
  destruct (unrecord_stack_adt _ _ H0). rewrite H. simpl.
  destr. destr. omega. destr; omega.
  intros b ofs k p.
  rewrite ! Perm1. rewrite Perm2; auto.
  destruct (unrecord_stack_adt _ _ H0). rewrite H in mext_length_stack0.
  destruct (unrecord_stack_adt _ _ A). rewrite H1 in mext_length_stack0.
  simpl in mext_length_stack0; congruence.  
Qed.

Lemma valid_frame_extends:
  forall m1 m2 fi,
    extends m1 m2 ->
    valid_frame fi m1 ->
    valid_frame fi m2.
Proof.
  intros. destruct (valid_frame_dec fi m2); auto.
  red; intros.
  erewrite <- valid_block_extends; eauto.
Qed.

Lemma size_stack_mem_inj:
  forall j g m1 m2,
    mem_inj j g m1 m2 ->
    frameinj_surjective g (length (stack_adt m2)) ->
    (size_stack (stack_adt m2) <= size_stack (stack_adt m1))%Z.
Proof.
  intros. inv H.
  eapply size_stack_stack_inject; eauto.
Qed.

Lemma size_stack_extends:
  forall m1 m2,
    extends m1 m2 ->
    (size_stack (stack_adt m2) <= size_stack (stack_adt m1))%Z.
Proof.
  intros.
  eapply size_stack_mem_inj; eauto.
  inv H; eauto.
  erewrite <- mext_length_stack; eauto.
  apply frameinj_surjective_flat; auto.
Qed.

Lemma size_stack_inject:
  forall j g m1 m2,
    inject j g m1 m2 ->
    frameinj_surjective g (length (stack_adt m2)) ->
    (size_stack (stack_adt m2) <= size_stack (stack_adt m1))%Z.
Proof.
  intros.
  eapply size_stack_mem_inj; eauto.
  inv H; eauto. 
Qed.

Lemma flat_frameinj_preserves_order:
  forall n,
    frameinj_preserves_order (flat_frameinj n).
Proof.
  unfold flat_frameinj; red; intros; eauto.
  destr_in H0; destr_in H1.
Qed.

Lemma record_stack_blocks_mem_inj:
    forall j g m1 m2 f1 f2 m1',
      mem_inj j g m1 m2 ->
      record_stack_blocks m1 f1 m1' ->
      frame_inject' j (perm m1) f1 f2 ->
      valid_frame f2 m2 ->
      (forall b, in_frames (stack_adt m2) b -> ~ in_frame f2 b) ->
      (forall b fi, in_frame f2 b ->
            frame_adt_info f2 = Some fi ->
            forall o k p, Mem.perm m2 b o k p -> (0 <= o < frame_size fi)%Z
      ) ->
      (forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2) ->
      frame_adt_size f1 = frame_adt_size f2 ->
      frameinj_surjective g (length (stack_adt m2)) ->
      exists m2',
        record_stack_blocks m2 f2 m2'
        /\ mem_inj j (fun n => if Nat.eq_dec n 0 then Some 0 else option_map S (g (pred n))) m1' m2'.
Proof.
  intros j g m1 m2 f1 f2 m1' INJ ADT FI VB NIN2 BNDS2 INF EQsz SURJ; autospe.
  inv ADT.
  eexists; split.
  apply rsb_intro. Unshelve. 
  - inversion INJ; subst; constructor; simpl; intros; eauto.
    + eapply mi_perm0; eauto.
    + eapply stack_inject_invariant_strong.
      intros. change (perm m1 b ofs k p) in H0. apply H0.
      destruct mi_stack_blocks0.
      constructor.
      * red; intros. destr_in H0. destr_in H1. inv H0. omega.
        destr_in H1. inv H1. omega.
        unfold option_map in H0, H1. destr_in H0. destr_in H1. inv H0; inv H1. apply le_n_S.
        eapply stack_inject_preserves_order. 2-3:eauto. omega.
      * intros.
        repeat destr_in H0. inv H; simpl in H0. inv H0.
        -- exists f2; split. constructor; simpl; auto. auto.
        -- unfold option_map in H2; repeat destr_in H2.
           apply frame_at_pos_cons_inv in H.
           edestruct stack_inject_frames as (f7 & FAP & FI'); eauto. 2: omega.
           exists f7; split. constructor; simpl; auto. inv FAP; auto. auto.
      * intros. destr.
        -- subst. inv H0. simpl in H2; inv H2.
           exists 0, f2; repeat refine (conj _ _); auto.
           constructor; reflexivity.
           exploit frame_inject_inj. eauto. rewrite Forall_forall. intro A; eapply A; eauto.
        -- apply frame_at_pos_cons_inv in H0; try omega.
           edestruct stack_inject_compat as (i3 & f7 & FAP' & IF7 & OMAP); eauto.
           rewrite OMAP. simpl.
           exists (S i3), f7; simpl. split.
           constructor; simpl; auto. inv FAP'; auto.
           split; auto.
      * intros.
        simpl in H1.
        destruct H1.
        -- subst.
           erewrite <- INF in H2; eauto.
           exfalso; apply H0. simpl; auto.
        -- eapply stack_inject_not_in_frames; eauto. simpl in H0; intuition.
      * intros. destr_in H. inv H. simpl; split; omega.
        unfold option_map in H; destr_in H. inv H.
        apply stack_inject_range in Heqo. simpl; omega.
      * intros. destr. eauto. 
        edestruct stack_inject_exists_l; eauto. 2: rewrite H0.  simpl in H. omega.  simpl; eauto.
      (* * intros. destruct (Nat.eq_dec j0 O); subst. *)
      (*   exists O; destr. *)
      (*   edestruct stack_inject_exists_r; eauto. *)
      (*   2: (exists (S x); simpl; rewrite H0). *)
      (*   instantiate (1:= pred j0). simpl in H; omega. *)
      (*   simpl. f_equal. omega. *)
      * intros. destr_in H; inv H. omega.
        unfold option_map in H1; destr_in H1. inv H1.
        apply stack_inject_pack in Heqo. omega.
      * intros. destr_in H1.
        -- subst. inv H. simpl in H3. inv H1. inv H3.
           inv H0. simpl in H; inv H. auto.
        --
          unfold option_map in H1; destr_in H1. inv H1. 
          apply frame_at_pos_cons_inv in H.
          apply frame_at_pos_cons_inv in H0.
          eapply stack_inject_sizes. eauto. eauto.
          simpl. auto.
          intros. destruct (Nat.eq_dec i 0). omega.
          generalize (H2 (S i)). destr. simpl. rewrite H1. simpl.
          intro A; trim A. auto. omega.
          omega. omega.

  - generalize (size_stack_mem_inj _ _ _ _ INJ SURJ). rewrite <- EQsz. omega.
  - rewrite Forall_forall. intros; eapply BNDS2; eauto.
  - rewrite Forall_forall; intros b INF' INS; eapply NIN2; eauto.
  - auto.
Qed.

Lemma stack_inject_g0_0:
  forall j g p s1 s2,
    stack_inject j g p s1 s2 ->
    frameinj_pack_after O g ->
    0 < length s1 ->
    0 < length s2 ->
    g 0 = Some 0.
Proof.
  intros j g p s1 s2 SI PACK LT1 LT2.
  inv SI.
  destruct (stack_inject_exists_l _ LT1). rewrite H. apply PACK in H. 
  f_equal; omega. omega.
Qed.

Lemma record_stack_blocks_mem_inj_left:
    forall j g m1 m2 f1 f2 m1',
      mem_inj j g m1 m2 ->
      record_stack_blocks m1 f1 m1' ->
      frame_at_pos (stack_adt m2) O f2 ->
      frame_inject' j (perm m1) f1 f2 ->
      (forall b1 b2 delta, j b1 = Some (b2, delta) -> in_frame f1 b1 -> in_frame f2 b2) ->
      frameinj_pack_after O g ->
      frameinj_surjective g (length (stack_adt m2)) ->
      mem_inj j (fun n => if Nat.eq_dec n 0 then Some 0 else g (pred n)) m1' m2.
Proof.
  intros j g m1 m2 f1 f2 m1' INJ ADT FAP FI INF G0 SURJ ; autospe.
  inv ADT.
  inversion INJ; subst; constructor; simpl; intros; eauto.
  eapply stack_inject_invariant_strong.
  intros. change (perm m1 b ofs k p) in H0. apply H0.
  inversion mi_stack_blocks0.
  constructor.
  - red; intros. destr_in H0. inv H0. omega.
    destr_in H1. omega. 
    eapply stack_inject_preserves_order. 2-3:eauto. omega.
  - intros.
    repeat destr_in H0. inv H; simpl in H0. inv H0.
    + exists f2; split; auto.
    + apply frame_at_pos_cons_inv in H.
      edestruct stack_inject_frames as (f7 & FAP' & FI'); eauto. omega.
  - intros. destr.
    + subst. inv H0. simpl in H2; inv H2.
      exists 0, f2; repeat refine (conj _ _); auto.
      exploit frame_inject_inj. eauto. rewrite Forall_forall. intro A; eapply A; eauto.
    + apply frame_at_pos_cons_inv in H0; try omega.
      edestruct stack_inject_compat as (i3 & f7 & FAP' & IF7 & OMAP); eauto.
  - intros. eapply stack_inject_not_in_frames; eauto. simpl in H0; intuition.
  - intros. destr_in H. inv H. simpl; split. omega.
    eapply frame_at_pos_lt. eauto.
    apply stack_inject_range in H. simpl; omega.
  - intros. destr. eauto. 
    edestruct stack_inject_exists_l; eauto.  simpl in H.
    omega.
  (* - intros. destruct (Nat.eq_dec j0 O); subst. *)
  (*   exists O; destr. *)
  (*   edestruct stack_inject_exists_r; eauto. *)
  (*   exists (S x); simpl; rewrite H0. auto. *)
  - intros. destr_in H; inv H. omega.
    apply stack_inject_pack in H1. omega.
  - intros. destr_in H1.
    + subst. inv H1. specialize (H2 1). trim H2. destr.
      simpl. eapply stack_inject_g0_0. eauto. eauto.
      exploit stack_inject_length_stack. eauto. eauto. eauto.
      apply frame_at_pos_lt in H0. omega.
      apply frame_at_pos_lt in H0. omega.
      omega.
    + apply frame_at_pos_cons_inv in H; try omega.
      eapply stack_inject_sizes; eauto.
      intros. specialize (H2 (S i)). destr_in H2. simpl in H2. trim H2; auto. omega.
Qed.

Lemma record_stack_blocks_valid:
  forall m1 fi m2,
    record_stack_blocks m1 fi m2 ->
    valid_frame fi m1.
Proof.
  inversion 1; intros; autospe; auto.
Qed.

Lemma record_stack_blocks_bounds:
  forall m1 fi m2,
    record_stack_blocks m1 fi m2 ->
    Forall (fun b : block =>
           forall (o : Z) (k : perm_kind) (p : permission),
           perm m1 b o k p -> forall fi0 : frame_info, frame_adt_info fi = Some fi0 -> (0 <= o < frame_size fi0)%Z) (frame_blocks fi).
Proof.
  inversion 1; intros; autospe; auto.
Qed.

Lemma record_stack_blocks_stack_adt:
  forall m f m',
    record_stack_blocks m f m' ->
    stack_adt m' = f::(stack_adt m).
Proof.
  inversion 1; intros; autospe; auto.
Qed.

Lemma record_stack_blocks_extends:
    forall m1 m2 fi m1',
      extends m1 m2 ->
      record_stack_blocks m1 fi m1' ->
      (forall bb, in_frame fi bb -> ~ in_frames (stack_adt m2) bb) ->
      Forall (fun b : block =>
                forall (o : Z) (k : perm_kind) (p : permission),
                  perm m2 b o k p -> forall fi0 : frame_info, frame_adt_info fi = Some fi0 -> (0 <= o < frame_size fi0)%Z)
             (frame_blocks fi) ->
      exists m2',
        record_stack_blocks m2 fi m2'
        /\ extends m1' m2'.
Proof.
  intros m1 m2 fi m1' EXT ADT NIN BNDS; autospe.
  inversion EXT.
  exploit record_stack_blocks_mem_inj; eauto.
  - eapply inject_frame_id.
  - red. red. rewrite <- mext_next0.
    eapply record_stack_blocks_valid; eauto.
  - intros b INS INF. eapply NIN; eauto.
  - intros. rewrite Forall_forall in BNDS. eapply BNDS; eauto.
  - inversion 1. subst. tauto.
  - rewrite mext_length_stack0.
    apply frameinj_surjective_flat; auto.
  - intros (m2' & ADT' & INJ). 
    eexists; split; eauto.
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT) as (NB1 & PERM1 & _) ;
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT') as (NB & PERM & _); simpl in *.
    constructor; simpl; intros; eauto.
    congruence.
    eapply mem_inj_frame_inj_ext; eauto. simpl.
    intros; unfold flat_frameinj.
    rewrite (record_stack_blocks_stack_adt _ _ _ ADT). simpl.
    destr. subst.
    destr. omega. destr. destr. simpl. f_equal. omega. omega.
    destr. omega.
    rewrite ! PERM1, PERM in *. eauto.
    rewrite (record_stack_blocks_stack_adt _ _ _ ADT). simpl.
    rewrite (record_stack_blocks_stack_adt _ _ _ ADT'). simpl.
    auto.
Qed.

Lemma free_list_stack_blocks:
    forall bl m m',
      free_list m bl = Some m' ->
      stack_adt m' = stack_adt m.
Proof.
  induction bl; simpl; intros; autospe. auto.
  eapply free_stack_adt in Heqo; congruence.
Qed.

Lemma in_frames_valid:
  forall m b,
    in_frames (stack_adt m) b -> valid_block m b.
Proof.
  apply stack_valid.
Qed.

Lemma record_stack_block_inject:
   forall m1 m1' m2 j g f1 f2
     (INJ: inject j g m1 m2)
     (FI: frame_inject' j (perm m1) f1 f2)
     (NOIN: forall b, in_frames (stack_adt m2) b -> ~ in_frame f2 b)
     (VF: valid_frame f2 m2)
     (BOUNDS: forall b fi,
         in_frame f2 b ->
          frame_adt_info f2 = Some fi -> forall (o : Z) (k : perm_kind) (p : permission), perm m2 b o k p -> (0 <= o < frame_size fi)%Z)
     (EQINF: forall (b1 b2 : block) (delta : Z), j b1 = Some (b2, delta) -> in_frame f1 b1 <-> in_frame f2 b2)
     (EQsz: frame_adt_size f1 = frame_adt_size f2)
     (SURJ: frameinj_surjective g (length (stack_adt m2)))
     (RSB: record_stack_blocks m1 f1 m1'),
     exists m2',
       record_stack_blocks m2 f2 m2' /\
       inject j (fun n : nat => if Nat.eq_dec n 0 then Some 0 else option_map S (g (Init.Nat.pred n))) m1' m2'.
Proof.
  intros.
  exploit record_stack_blocks_mem_inj; eauto. inversion INJ; eauto.
  intros (m2' & ADT & INJ').
  eexists; split; eauto.
  edestruct (record_stack_blocks_mem_unchanged _ _ _ RSB) as (NB1 & PERM1 & U1 & C1) ;
    edestruct (record_stack_blocks_mem_unchanged _ _ _ ADT) as (NB & PERM & U & C); simpl in *.
  inversion INJ; econstructor; simpl; intros; eauto.
  + eapply mi_freeblocks0; eauto.
    unfold valid_block in H; rewrite NB1 in H; eauto.
  + unfold valid_block; rewrite NB; eauto.
    eapply mi_mappedblocks0; eauto.
  + red; intros.
    rewrite PERM1 in H3, H2.
    eapply mi_no_overlap0; eauto.
  + exploit mi_representable0; eauto.
    intros (A & B); split; auto. intro ofs; rewrite ! PERM1. eauto.
  + rewrite ! PERM1. rewrite PERM in H0. eapply mi_perm_inv0 in H0; eauto.
Qed.

Lemma record_stack_block_inject_left:
   forall m1 m1' m2 j g f1 f2
     (INJ: inject j g m1 m2)
     (FAP: frame_at_pos (stack_adt m2) 0 f2)
     (FI: frame_inject' j (perm m1) f1 f2)
     (SURJ: frameinj_surjective g (length (stack_adt m2)))
     (RSB: record_stack_blocks m1 f1 m1'),
     inject j (fun n : nat => if Nat.eq_dec n 0 then Some 0 else g (Init.Nat.pred n)) m1' m2.
Proof.
  intros.
  inversion INJ; eauto.
  exploit record_stack_blocks_mem_inj_left; eauto.
  - intros. inv FI. rewrite Forall_forall in frame_inject_inj.
    eapply frame_inject_inj; eauto.
  - inv mi_inj0.
    exploit stack_inject_length_stack. eauto. eauto. intros.
    exploit frame_at_pos_lt; eauto. intro LT.
    eapply stack_inject_g0_0; eauto. omega.
  - intro MINJ.
    edestruct (record_stack_blocks_mem_unchanged _ _ _ RSB) as (NB1 & PERM1 & U1 & C1) ; simpl in *.
    inversion INJ; econstructor; simpl; intros; eauto.
    + eapply mi_freeblocks0; eauto.
      unfold valid_block in H; rewrite NB1 in H; eauto.
    + red; intros.
      rewrite PERM1 in H3, H2.
      eapply mi_no_overlap0; eauto.
    + exploit mi_representable0; eauto.
      intros (A & B); split; auto. intro ofs; rewrite ! PERM1. eauto.
    + rewrite ! PERM1. eapply mi_perm_inv0 in H0; eauto.
Qed.

Lemma public_stack_access_magree: forall P (m1 m2 : mem) (b : block) (lo hi : Z) p,
    magree m1 m2 P ->
    range_perm m1 b lo hi Cur p ->
    public_stack_access (stack_adt m1) b lo hi ->
    public_stack_access (stack_adt m2) b lo hi.
Proof.
  inversion 1. 
  unfold public_stack_access.
  intros.
  generalize (get_frame_info_magree _ _ _ b H); eauto. inversion 1; subst.
  - auto. 
  -
    destruct (zlt lo hi).
    generalize (stack_perms m1).
    rewrite Forall_forall; intro FAP.
    exploit get_assoc_spec. setoid_rewrite <- H3. eauto.
    intros (ll & n & IN & INF).
    specialize (FAP _ IN). red in FAP. simpl in FAP.
    rewrite <- H3 in *. eapply public_stack_range_shift in H1; eauto. rewrite ! Z.add_0_r in H1. auto.
    eapply FAP; eauto. apply H0. omega.
    cut (hi - 1 < frame_size a)%Z. omega.
    eapply FAP; eauto. apply H0. omega.
    red; intros; omega.
  - red; intros. eapply H5. 
    eapply perm_implies with (p2:= Nonempty).
    apply H0. auto.
    constructor.
    eapply inject_perm_condition_writable; constructor.
Qed.

Lemma inject_frame_flat m a thr:
  frame_inject' (flat_inj thr) m a a.
Proof.
  destruct a; try (econstructor; inversion 1; tauto).
  econstructor. apply Forall_forall. unfold flat_inj; intros. destr_in H0. 
  red.
  simpl. repeat destr. apply Forall_forall. subst.
  intros. unfold flat_inj in H0; destr_in H0; inv H0.
  eapply shift_frame_id.
Qed.

Lemma record_stack_blocks_sep:
  forall m1 fi m2,
    record_stack_blocks m1 fi m2 ->
    forall b : block, in_frames (stack_adt m1) b -> ~ in_frame fi b.
Proof.
  inversion 1; intros; autospe.
  clear - NOTIN H1. rewrite Forall_forall in NOTIN.
  intro IFR. eapply NOTIN in IFR; eauto.
Qed.

Lemma record_stack_blocks_inject_neutral:
  forall thr m fi m',
    inject_neutral thr m ->
    record_stack_blocks m fi m' ->
    inject_neutral thr m'.
Proof.
  unfold inject_neutral; intros.
  exploit record_stack_blocks_mem_inj. eauto. eauto.
  apply inject_frame_flat.
  eapply record_stack_blocks_valid; eauto. 
  eapply record_stack_blocks_sep; eauto.
  generalize (record_stack_blocks_bounds _ _ _ H0). rewrite Forall_forall. intro A; intros; eapply A; eauto.
  unfold flat_inj. intros. destr_in H1.
  auto.
  apply frameinj_surjective_flat. auto.
  intros (m2' & RSB & MI).
  exploit record_stack_block_det. exact H0. exact RSB. intro; subst.
  eapply mem_inj_frame_inj_ext; eauto.
  intros; unfold flat_frameinj.
  rewrite (record_stack_blocks_stack_adt _ _ _ H0). simpl.
  destr. subst.
  destr. omega. destr. destr. simpl. f_equal. omega. omega.
  destr. omega.
Qed.

Lemma unrecord_stack_block_inject_neutral:
  forall thr m m',
    inject_neutral thr m ->
    unrecord_stack_block m = Some m' ->
    inject_neutral thr m'.
Proof.
  intros.
  exploit unrecord_stack_block_mem_inj_parallel. eauto. eauto. eauto.
  unfold flat_frameinj. intros. destr_in H1.
  intros (m2' & RSB & MI). rewrite H0 in RSB; inv RSB.
  eapply mem_inj_frame_inj_ext; eauto.
  intros; unfold flat_frameinj.
  destruct (unrecord_stack_adt _ _ H0). rewrite H1. simpl.
  destr. 
  destr. omega. destr. omega. 
Qed.

Lemma store_no_abstract:
  forall (chunk : memory_chunk) (b : block) (o : Z) (v : val),
    abstract_unchanged (fun m1 m2 : mem => store chunk m1 b o v = Some m2).
Proof.
  red; intros. eapply store_stack_adt; simpl; eauto. 
Qed.

Lemma storebytes_no_abstract:
  forall (b : block) (o : Z) (bytes : list memval),
    abstract_unchanged (fun m1 m2 : mem => storebytes m1 b o bytes = Some m2).
Proof.
  red; intros. eapply storebytes_stack_adt; simpl; eauto. 
Qed.

Lemma alloc_no_abstract: forall (lo hi : Z) (b : block),
 abstract_unchanged (fun m1 m2 : mem => alloc m1 lo hi = (m2, b)).
Proof.
  red; intros. eapply alloc_stack_adt; simpl; eauto. 
Qed.

Lemma free_no_abstract:
 forall (lo hi : Z) (b : block),
 abstract_unchanged (fun m1 m2 : mem => free m1 b lo hi = Some m2).
Proof.
  red; intros. eapply free_stack_adt; simpl; eauto. 
Qed.

Lemma freelist_no_abstract:
 forall bl : list (block * Z * Z),
 abstract_unchanged (fun m1 m2 : mem => free_list m1 bl = Some m2).
Proof.
  red; intros. eapply free_list_stack_blocks; simpl; eauto. 
Qed.

Lemma drop_perm_no_abstract:
 forall (b : block) (lo hi : Z) (p : permission),
 abstract_unchanged (fun m1 m2 : mem => drop_perm m1 b lo hi p = Some m2).
Proof.
  red; intros. eapply drop_perm_stack_adt; simpl; eauto. 
Qed.

End WITHINJPERM.

Local Instance memory_model_prf:
  MemoryModel mem.
Proof.
  split.
  exact valid_not_valid_diff.
  exact perm_implies.
  exact perm_cur_max.
  exact perm_cur.
  exact perm_max.
  exact perm_valid_block.
  exact range_perm_implies.
  exact range_perm_cur.
  exact range_perm_max.
  exact valid_access_implies.
  exact valid_access_valid_block.
  exact valid_access_perm.
  exact valid_pointer_nonempty_perm.
  exact valid_pointer_valid_access.
  exact weak_valid_pointer_spec.
  exact valid_pointer_implies.
  exact nextblock_empty.
  exact perm_empty.
  exact valid_access_empty.
  exact valid_access_load.
  exact load_valid_access.
  exact load_type.
  exact load_cast.
  exact load_int8_signed_unsigned.
  exact load_int16_signed_unsigned.
  exact loadv_int64_split.
  exact range_perm_loadbytes.
  exact loadbytes_range_perm.
  exact loadbytes_load.
  exact load_loadbytes.
  exact loadbytes_length.
  exact loadbytes_empty.
  exact loadbytes_concat.
  exact loadbytes_split.
  exact nextblock_store.
  exact store_valid_block_1.
  exact store_valid_block_2.
  exact perm_store_1.
  exact perm_store_2.
  exact valid_access_store'.
  exact store_valid_access_1.
  exact store_valid_access_2.
  exact store_valid_access_3.
  exact load_store_similar.
  exact load_store_similar_2.
  exact load_store_same.
  exact load_store_other.
  exact load_store_pointer_overlap.
  exact load_store_pointer_mismatch.
  exact load_pointer_store.
  exact loadbytes_store_same.
  exact loadbytes_store_other.
  exact store_signed_unsigned_8.
  exact store_signed_unsigned_16.
  exact store_int8_zero_ext.
  exact store_int8_sign_ext.
  exact store_int16_zero_ext.
  exact store_int16_sign_ext.
  exact storev_int64_split.
  exact range_perm_storebytes'.
  exact storebytes_range_perm.
  exact storebytes_stack_access_3.
  exact perm_storebytes_1.
  exact perm_storebytes_2.
  exact storebytes_valid_access_1.
  exact storebytes_valid_access_2.
  exact nextblock_storebytes.
  exact storebytes_valid_block_1.
  exact storebytes_valid_block_2.
  exact storebytes_store.
  exact store_storebytes.
  exact loadbytes_storebytes_same.
  exact loadbytes_storebytes_disjoint.
  exact loadbytes_storebytes_other.
  exact load_storebytes_other.
  exact storebytes_concat.
  exact storebytes_split.
  exact alloc_result.
  exact nextblock_alloc.
  exact valid_block_alloc.
  exact fresh_block_alloc.
  exact valid_new_block.
  exact valid_block_alloc_inv.
  exact perm_alloc_1.
  exact perm_alloc_2.
  exact perm_alloc_3.
  exact perm_alloc_4.
  exact perm_alloc_inv.
  exact valid_access_alloc_other.
  exact valid_access_alloc_same.
  exact valid_access_alloc_inv.
  exact load_alloc_unchanged.
  exact load_alloc_other.
  exact load_alloc_same.
  exact load_alloc_same'.
  exact loadbytes_alloc_unchanged.
  exact loadbytes_alloc_same.
  exact range_perm_free'.
  exact free_range_perm.
  exact nextblock_free.
  exact valid_block_free_1.
  exact valid_block_free_2.
  exact perm_free_1.
  exact perm_free_2.
  exact perm_free_3.
  exact valid_access_free_1.
  exact valid_access_free_2.
  exact valid_access_free_inv_1.
  exact valid_access_free_inv_2.
  exact load_free.
  exact loadbytes_free_2.
  exact nextblock_drop.
  exact drop_perm_valid_block_1.
  exact drop_perm_valid_block_2.
  exact range_perm_drop_1.
  exact range_perm_drop_2'.
  exact perm_drop_1.
  exact perm_drop_2.
  exact perm_drop_3.
  exact perm_drop_4.
  exact loadbytes_drop.
  exact load_drop.
  intros; eapply extends_refl; eauto.
  intros; eapply load_extends; eauto.
  intros; eapply loadv_extends; eauto.
  intros; eapply loadbytes_extends; eauto.
  intros; eapply store_within_extends; eauto.
  intros; eapply store_outside_extends; eauto.
  intros; eapply storev_extends; eauto.
  intros; eapply storebytes_within_extends; eauto.
  intros; eapply storebytes_outside_extends; eauto.
  intros; eapply alloc_extends; eauto.
  intros; eapply free_left_extends; eauto.
  intros; eapply free_right_extends; eauto.
  intros; eapply free_parallel_extends; eauto.
  intros; eapply valid_block_extends; eauto.
  intros; eapply perm_extends; eauto.
  intros; eapply valid_access_extends; eauto.
  intros; eapply valid_pointer_extends; eauto.
  intros; eapply weak_valid_pointer_extends; eauto.
  intros; eapply ma_perm; eauto.
  intros; eapply magree_monotone; eauto.
  intros; eapply mextends_agree; eauto.
  intros; eapply magree_extends; eauto.
  intros; eapply magree_loadbytes; eauto.
  intros; eapply magree_load; eauto.
  intros; eapply magree_storebytes_parallel; eauto.
  intros; eapply magree_storebytes_left; eauto.
  intros; eapply magree_store_left; eauto.
  intros; eapply magree_free; eauto.
  intros; eapply magree_valid_access; eauto.
  intros; eapply mi_no_overlap; eauto.
  intros; eapply delta_pos; eauto.
  intros; eapply valid_block_inject_1; eauto.
  intros; eapply valid_block_inject_2; eauto.
  intros; eapply perm_inject; eauto.
  intros; eapply range_perm_inject; eauto.
  intros; eapply valid_access_inject; eauto.
  intros; eapply valid_pointer_inject; eauto.
  intros; eapply weak_valid_pointer_inject; eauto.
  intros; eapply address_inject; eauto.
  intros; eapply address_inject' ; eauto.
  intros; eapply valid_pointer_inject_no_overflow; eauto.
  intros; eapply weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply valid_pointer_inject_val; eauto.
  intros; eapply weak_valid_pointer_inject_val; eauto.
  intros; eapply inject_no_overlap; eauto.
  intros; eapply different_pointers_inject; eauto.
  intros; eapply disjoint_or_equal_inject; eauto.
  intros; eapply aligned_area_inject; eauto.
  intros; eapply load_inject; eauto.
  intros; eapply loadv_inject; eauto.
  intros; eapply loadbytes_inject; eauto.
  intros; eapply store_mapped_inject; eauto.
  intros; eapply store_unmapped_inject; eauto.
  intros; eapply store_outside_inject; eauto.
  intros; eapply storev_mapped_inject; eauto.
  intros; eapply storebytes_mapped_inject; eauto.
  intros; eapply storebytes_unmapped_inject; eauto.
  intros; eapply storebytes_outside_inject; eauto.
  intros; eapply storebytes_empty_inject; eauto.
  intros; eapply alloc_right_inject; eauto.
  intros; eapply alloc_left_unmapped_inject; eauto.
  intros; eapply alloc_left_mapped_inject; eauto.
  intros; eapply alloc_parallel_inject; eauto.
  intros; eapply free_inject; eauto.
  intros; eapply free_left_inject; eauto.
  intros; eapply free_list_left_inject; eauto.
  intros; eapply free_right_inject; eauto.
  intros; eapply free_parallel_inject; eauto.
  intros; eapply drop_outside_inject; eauto.
  intros; eapply self_inject; eauto.
  {
    intros; eapply mi_stack_blocks. inv H; auto.
  }
  {
    intros; eapply mi_stack_blocks. inv H; auto.
  }
  intros; eapply extends_inject_compose; eauto.
  intros; eapply extends_extends_compose; eauto.
  intros; eapply neutral_inject; eauto.
  intros; eapply empty_inject_neutral; eauto.
  reflexivity.
  intros; eapply alloc_inject_neutral; eauto.
  intros; eapply store_inject_neutral; eauto.
  intros; eapply drop_inject_neutral; eauto.
  intros; eapply drop_perm_stack_adt; eauto.
  tauto.
  intros; eapply unchanged_on_nextblock; eauto.
  intros; eapply unchanged_on_refl; eauto.
  intros; eapply unchanged_on_trans; eauto.
  intros; eapply unchanged_on_trans; eauto.
  intros; eapply perm_unchanged_on; eauto.
  intros; eapply perm_unchanged_on_2; eauto.
  intros; eapply loadbytes_unchanged_on_1; eauto.
  intros; eapply loadbytes_unchanged_on; eauto.
  intros; eapply load_unchanged_on_1; eauto.
  intros; eapply load_unchanged_on; eauto.
  intros; eapply store_unchanged_on; eauto.
  intros; eapply storebytes_unchanged_on; eauto.
  intros; eapply alloc_unchanged_on; eauto.
  intros; eapply free_unchanged_on; eauto.
  intros; eapply drop_perm_unchanged_on; eauto.
  intros; eapply unchanged_on_implies; eauto.
  intros; eapply unchanged_on_implies; eauto.
  intros; eapply inject_unchanged_on; eauto.
  intros; eapply store_no_abstract; eauto.
  intros; eapply storebytes_no_abstract; eauto.
  intros; eapply alloc_no_abstract; eauto.
  intros; eapply free_no_abstract; eauto.
  intros; eapply freelist_no_abstract; eauto.
  intros; eapply drop_perm_no_abstract; eauto.
  simpl. intros. eapply record_stack_block_inject_left; simpl in *; eauto.
  simpl. intros. eapply record_stack_block_inject; simpl in *; eauto.
  { intros; eapply record_stack_blocks_extends; eauto. }
  intros; eapply record_stack_blocks_mem_unchanged; eauto.
  {
    simpl; intros.
    inv H; reflexivity.
  }
  intros; eapply record_stack_blocks_inject_neutral; eauto.
  intros; eapply unrecord_stack_block_inject_parallel; eauto.
  intros; eapply unrecord_stack_block_inject_left; eauto.
  intros; eapply unrecord_stack_block_extends; eauto.
  intros; eapply unrecord_stack_block_mem_unchanged; eauto.
  intros; eapply unrecord_stack_adt; eauto.
  intros; eapply unrecord_stack_block_succeeds; eauto.
  intros; eapply unrecord_stack_block_inject_neutral; eauto.
  intros; eapply public_stack_access_extends; eauto.
  intros; eapply public_stack_access_inject; eauto.
  intros; eapply public_stack_access_magree; eauto.
  intros; eapply in_frames_valid; eauto.
  intros; eapply is_stack_top_extends; eauto.
  intros; eapply is_stack_top_inject; eauto.
  simpl. vm_compute. intuition congruence.
  simpl. unfold stack_limit. exists 512; omega.
  intros. simpl. eapply stack_below_limit.
  apply push_frame_alloc_record.
  apply alloc_record_push_frame.
  apply record_stack_blocks_none_correct.
Qed.


End Mem.

Global Opaque Mem.alloc Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.
