(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** This file defines the interface for the memory model that
  is used in the dynamic semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Coqlib.
Require Intv.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memdata.

(** Memory states are accessed by addresses [b, ofs]: pairs of a block
  identifier [b] and a byte offset [ofs] within that block.
  Each address is associated to permissions, also known as access rights.
  The following permissions are expressible:
- Freeable (exclusive access): all operations permitted
- Writable: load, store and pointer comparison operations are permitted,
  but freeing is not.
- Readable: only load and pointer comparison operations are permitted.
- Nonempty: valid, but only pointer comparisons are permitted.
- Empty: not yet allocated or previously freed; no operation permitted.

The first four cases are represented by the following type of permissions.
Being empty is represented by the absence of any permission.
*)

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.

(** In the list, each permission implies the other permissions further down the
    list.  We reflect this fact by the following order over permissions. *)

Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.

Hint Constructors perm_order: mem.

Lemma perm_order_trans:
  forall p1 p2 p3, perm_order p1 p2 -> perm_order p2 p3 -> perm_order p1 p3.
Proof.
  intros. inv H; inv H0; constructor.
Qed.

(** Each address has not one, but two permissions associated
  with it.  The first is the current permission.  It governs whether
  operations (load, store, free, etc) over this address succeed or
  not.  The other is the maximal permission.  It is always at least as
  strong as the current permission.  Once a block is allocated, the
  maximal permission of an address within this block can only
  decrease, as a result of [free] or [drop_perm] operations, or of
  external calls.  In contrast, the current permission of an address
  can be temporarily lowered by an external call, then raised again by
  another external call. *)

Inductive perm_kind: Type :=
  | Max: perm_kind
  | Cur: perm_kind.


Record segment :=
  {
    seg_ofs: Z;
    seg_size: Z;
  }.

Definition empty_segment : segment :=
  {|
    seg_ofs := 0;
    seg_size:= 0;
  |}.

Definition in_segment (ofs: Z) (seg: segment) : Prop :=
  seg_ofs seg <= ofs < seg_ofs seg + seg_size seg.

Fixpoint in_segments o (l: list segment)  :=
  match l with
    nil => False
  | a::r => in_segment o a \/ in_segments o r
  end.

Fixpoint segments_disjoint (l: list segment) :=
  match l with
    nil => True
  | a::r => segments_disjoint r /\ forall o, in_segment o a -> ~ in_segments o r
  end.

Record frame_info :=
  {
    frame_size: Z;
    frame_link: segment;
    frame_retaddr: segment;
    frame_locals: segment;
    frame_outgoings: segment;
    frame_callee_saves: segment;
    frame_data: segment;
    frame_disjoints:
      segments_disjoint
        (frame_link :: frame_retaddr :: frame_locals :: frame_outgoings
                    :: frame_callee_saves :: frame_data :: nil);
    frame_retaddr_size:
      seg_size frame_retaddr = size_chunk Mptr;
    frame_link_size:
      seg_size frame_link = size_chunk Mptr;
  }.


Program Definition empty_frame : frame_info :=
  {|
    frame_size := 0;
    frame_link:= {| seg_ofs := 0; seg_size := size_chunk Mptr |};
    frame_retaddr:= {| seg_ofs := size_chunk Mptr; seg_size := size_chunk Mptr |};
    frame_locals := empty_segment;
    frame_outgoings := empty_segment;
    frame_callee_saves := empty_segment;
    frame_data := empty_segment;
  |}.
Next Obligation.
  unfold in_segment; simpl.
  intuition omega.
Qed.

Inductive frame_adt: Type :=
| frame_with_info: block -> option frame_info -> frame_adt
| frame_without_info: list block -> frame_adt.

Fixpoint get_assoc (l: list (option frame_adt * Z)) (a: block) : option frame_info :=
  match l with
    nil => None
  | (Some (frame_with_info b fi), n)::r => if eq_block a b then fi else get_assoc r a
  | (Some (frame_without_info bl),n)::r => if in_dec eq_block a bl then None else get_assoc r a
  | (None,_)::r => get_assoc r a
  end.

Definition in_frame (f: option frame_adt) (a: block) : Prop :=
  match f with
  | Some (frame_with_info b fi) => a = b
  | Some (frame_without_info bl) => In a bl
  | None => False
  end.

Fixpoint in_frames (l: list (option frame_adt * Z)) (b: block) :=
  match l with
    nil => False
  | (f, _) :: r => in_frame f b \/ in_frames r b
  end.

Lemma in_frame_dec:
  forall f b, {in_frame f b} + {~ in_frame f b}.
Proof.
  destruct f; simpl; intros; auto.
  destruct f; simpl; intros.
  apply eq_block.
  apply in_dec. apply eq_block.
Defined.

Lemma in_frames_dec:
  forall l b, {in_frames l b} + {~ in_frames l b}.
Proof.
  induction l; simpl; intros; eauto.
  destruct a. 
  destruct (in_frame_dec o b); auto.
  destruct (IHl b); eauto. right; intros [A|A]; auto.
Defined.

Lemma not_in_frames_get_assoc:
  forall l b,
    ~ in_frames l b ->
    get_assoc l b = None.
Proof.
  induction l; simpl; intros; eauto.
  destruct a. destruct o; auto. destruct f; auto.
  - destruct (eq_block b b0); auto. intuition.
  - destruct (in_dec eq_block b l0); intuition.
Qed.


Definition in_stack_data (lo hi: Z) (fi: frame_info) : Prop :=
  forall ofs, lo <= ofs < hi -> in_segment ofs (frame_data fi).

Class InjectPerm :=
  {
    inject_perm_condition: permission -> Prop;
    inject_perm_condition_writable: forall p, perm_order Writable p -> inject_perm_condition p;
  }.

Inductive frame_inject' {injperm: InjectPerm} (f: meminj) (P: block -> Z -> perm_kind -> permission -> Prop):
  frame_adt -> frame_adt -> Prop :=
| frame_inject_with_info:
    forall b1 b2 fi
      (FB: forall b' delta, f b1 = Some (b', delta) -> b' = b2 /\ delta = 0)
      (INJ: forall b' delta, f b' = Some (b2, delta) -> b' = b1),
      frame_inject' f P (frame_with_info b1 fi) (frame_with_info b2 fi)
| frame_inject_without_info:
    forall bl1 bl2
      (INJlist: forall b b' delta, f b = Some (b', delta) -> (In b bl1 <-> In b' bl2)),
      frame_inject' f P (frame_without_info bl1) (frame_without_info bl2)
| frame_inject_without_info_with_info:
    forall bl b2 ofi
      (INDATA:
         forall fi,
           ofi = Some fi ->
           forall b1 delta,
             In b1 bl ->
             f b1 = Some (b2, delta) ->
             forall ofs k p,
               P b1 ofs k p ->
               inject_perm_condition p ->
               in_segment (ofs + delta) (frame_data fi))
      (INJlist: forall b b' delta, f b = Some (b', delta) -> (In b bl <-> b' = b2)),
      frame_inject' f P (frame_without_info bl) (frame_with_info b2 ofi)
| frame_with_info_add_info:
    forall b1 b2 fi
      (INDATA: forall delta,
          f b1 = Some (b2, delta) ->
          forall ofs k p,
            P b1 ofs k p ->
            inject_perm_condition p ->
            in_segment (ofs + delta) (frame_data fi))
      (INJ: forall b1' b2' delta, f b1' = Some (b2', delta) -> (b1' = b1 <-> b2' = b2)),
      frame_inject' f P (frame_with_info b1 None) (frame_with_info b2 (Some fi)).

Module Mem.

Definition locset := block -> Z -> Prop.

Class MemoryModelOps
      (** The abstract type of memory states. *)
 (mem: Type)

: Type
 :=
{

(** * Operations on memory states *)

(** [empty] is the initial memory state. *)
  empty: mem;

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
 alloc: forall (m: mem) (lo hi: Z), mem * block;

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not writable. *)
 free: forall (m: mem) (b: block) (lo hi: Z), option mem;

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
 load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val;

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
 store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem;

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
 loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval);

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
 storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem;

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

 drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem;

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

 nextblock: mem -> block;

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
 perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop;

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
 range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p;

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)

 valid_pointer: forall (m: mem) (b: block) (ofs: Z), bool;

(** * Relating two memory states. *)

(** ** Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by relaxing the permissions of [m1] (for instance, allocating larger
  blocks) and replacing some of the [Vundef] values stored in [m1] by
  more defined values stored in [m2] at the same addresses. *)

 extends: forall {injperm: InjectPerm}, mem -> mem -> Prop;

(** The [magree] predicate is a variant of [extends] where we
  allow the contents of the two memory states to differ arbitrarily
  on some locations.  The predicate [P] is true on the locations whose
  contents must be in the [lessdef] relation.
  Needed by Deadcodeproof. *)

 magree: forall {injperm: InjectPerm} (m1 m2: mem) (P: locset), Prop;

(** ** Memory injections *)

(** A memory injection [f] is a function from addresses to either [None]
  or [Some] of an address and an offset.  It defines a correspondence
  between the blocks of two memory states [m1] and [m2]:
- if [f b = None], the block [b] of [m1] has no equivalent in [m2];
- if [f b = Some(b', ofs)], the block [b] of [m2] corresponds to
  a sub-block at offset [ofs] of the block [b'] in [m2].

A memory injection [f] defines a relation [Val.inject] between values
that is the identity for integer and float values, and relocates pointer
values as prescribed by [f].  (See module [Values].)

Likewise, a memory injection [f] defines a relation between memory states
that we now axiomatize. *)

 inject: forall {injperm: InjectPerm}, meminj -> mem -> mem -> Prop;

(** Memory states that inject into themselves. *)

 inject_neutral: forall {injperm: InjectPerm} (thr: block) (m: mem), Prop;

(** ** Invariance properties between two memory states *)

 unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (** Necessary to distinguish from [unchanged_on], used as
 postconditions to external function calls, whereas
 [strong_unchanged_on] will be used for ordinary memory operations. *)

 strong_unchanged_on: forall (P: block -> Z -> Prop) (m_before m_after: mem), Prop
 ;

 (* Stack ADT and methods *)
 stack_adt: mem -> list (option frame_adt * Z);
 record_stack_blocks: mem -> option frame_adt -> Z -> option mem;
 unrecord_stack_block: mem -> option mem;
 frame_inject {injperm: InjectPerm} f m := frame_inject' f (perm m)
}.


Section WITHMEMORYMODELOPS.
Context `{memory_model_ops: MemoryModelOps}.
Context {injperm: InjectPerm}.

Lemma frame_inject_invariant:
  forall m m' f f1 f2,
    (forall b ofs k p b' delta, f b = Some (b', delta) -> perm m' b ofs k p -> perm m b ofs k p) ->
    frame_inject _ f m f1 f2 ->
    frame_inject _ f m' f1 f2.
Proof.
  intros m m' f f1 f2 PERM FI.
  destruct FI; try now (econstructor; eauto).
Qed.

Lemma list_forall2_frame_inject_invariant:
  forall m m' f f1 f2,
    (forall b ofs k p b' delta, f b = Some (b', delta) -> perm m' b ofs k p -> perm m b ofs k p) ->
    list_forall2 (frame_inject _ f m) f1 f2 ->
    list_forall2 (frame_inject _ f m') f1 f2.
Proof.
  intros m m' f f1 f2 PERM FI.
  eapply list_forall2_imply. eauto.
  intros.
  eapply frame_inject_invariant; eauto.
Qed.

Lemma inject_frame_id m a:
  frame_inject _ inject_id m a a.
Proof.
  destruct a; try (econstructor; inversion 1; tauto).
Qed.

Definition option_frame_inject f m1 (x y: option frame_adt * Z) :=
  match fst x, fst y with
    Some f1, Some f2 => frame_inject _ f m1 f1 f2
  | None, Some f => False
  | _, _ => True
  end /\ snd x = snd y.


Lemma list_inject_frame_id m:
  list_forall2 (option_frame_inject inject_id m) (stack_adt m) (stack_adt m).
Proof.
  generalize (stack_adt m); induction l; simpl; intros; constructor; auto.
  constructor; simpl; auto.
  destruct a. simpl. destruct o; auto. eapply inject_frame_id.
Qed.

Lemma frame_inject_incr:
  forall f f' m f1 f2,
    inject_incr f f' ->
    (forall b b' delta, f b = None -> f' b = Some (b', delta) ->
                   ~ in_frame f1 b /\ ~ in_frame f2 b' /\
                   forall b1 delta', in_frame f1 b1 -> f b1 = Some (b', delta') -> False)
    ->
    forall f1' f2',
      f1 = Some f1' ->
      f2 = Some f2' ->
    frame_inject _ f m f1' f2' ->
    frame_inject _ f' m f1' f2'.
Proof.
  intros f f' m f1 f2 INCR NEW f1' f2' EQf1 EQf2 FI. subst.
  inversion FI; try now (econstructor; eauto).
  - econstructor.
    intros.
    destruct (f b1) as [[b delta0]|] eqn:EQ.
    + exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
      eapply FB; eauto. 
    +
      specialize (NEW _ _ _ EQ H1).
      destruct NEW  as (A & B & C).
      subst. simpl in *. congruence.
    + intros. destruct (f b') as [[b delta0]|] eqn:EQ.
      exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
      eapply INJ; eauto. 
      specialize (NEW _ _ _ EQ H1).
      destruct NEW  as (A & B & C).
      subst. simpl in *. congruence.
  - econstructor; eauto. intros.
    destruct (f b) as [[b2' delta0]|] eqn:EQ.
    exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
    eapply INJlist. eauto.
    subst. simpl in *.
    split; intros.
    generalize (proj1 (NEW _ _ _ EQ H1)). congruence.
    generalize (proj1 (proj2 (NEW _ _ _ EQ H1))). congruence.
  - econstructor; eauto. intros.
    + destruct (f b1) as [[b' delta0]|] eqn:EQ.
      exploit INCR. rewrite EQ. eauto. rewrite H3. inversion 1; subst.
      eapply INDATA; eauto.
      generalize (proj1 (NEW _ _ _ EQ H3)). subst. simpl. congruence.
    + intros. destruct (f b) as [[b1 delta0]|] eqn:EQ.
      exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
      eapply INJlist. eauto.
      subst. simpl in *.
      split; intros.
      generalize (proj1 (NEW _ _ _ EQ H1)). congruence.
      generalize (proj1 (proj2 (NEW _ _ _ EQ H1))). congruence.
  - econstructor; eauto.
    + intros.
      destruct (f b1) as [[b delta']|] eqn:EQ.
      exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
      eapply INDATA; eauto.
      generalize (NEW _ _ _ EQ H1). subst; simpl. intuition congruence.
    + intros.
      destruct (f b1') as [[b delta']|] eqn:EQ.
      exploit INCR. rewrite EQ. eauto. rewrite H1. inversion 1; subst.
      eapply INJ. eauto.
      generalize (NEW _ _ _ EQ H1). subst; simpl. intuition congruence.
Qed.

Lemma frame_inject_in_frame:
  forall f m v1 v2 b b' delta,
    frame_inject _ f m v1 v2 ->
    in_frame (Some v1) b ->
    f b = Some (b', delta) ->
    in_frame (Some v2) b'.
Proof.
  inversion 1; intros IFF FBB; simpl in *; 
    try first [
        intuition congruence
        | rewrite <- INJlist; eauto ].
  subst. autospe. auto.
  subst. autospe. intuition.
Qed.

Lemma self_inject_frame f m a:
  (forall b, f b = None \/ f b = Some (b,0)) ->
  frame_inject _ f m a a.
Proof.
  intros SELF.
  destruct a;  constructor; auto; intros; autospe; try intuition congruence.
  destruct (SELF b); try congruence. rewrite H in H0; inv H0. auto.
  destruct (SELF b'); try congruence.
  destruct (SELF b). congruence.
  assert (b = b') by congruence. subst. tauto.
Qed.

Lemma self_inject_list_frames f m a:
  (forall b, f b = None \/ f b = Some (b,0)) ->
  list_forall2 (frame_inject _ f m) a a.
Proof.
  induction a; intros SELF; constructor; auto.
  apply self_inject_frame; eauto.
Qed.

Lemma frame_inject_compose:
  forall (f f' : meminj) m1 l1 l2,
    frame_inject _ f m1 l1 l2 ->
    forall m2 l3,
      frame_inject _ f' m2 l2 l3 ->
      (forall b1 b2 delta o k p,
          f b1 = Some (b2, delta) ->
          perm m1 b1 o k p ->
          inject_perm_condition p ->
          perm m2 b2 (o + delta) k p) ->
      frame_inject _ (compose_meminj f f') m1 l1 l3.
Proof.
  intros f f' m1 l1 l2 H m2 l3 H0 PERM.
  inv H; inv H0; unfold compose_meminj.
  - econstructor; eauto; intros; autospe; auto.
  - econstructor; eauto; intros; autospe; auto.
    eapply INDATA; eauto. replace ofs with (ofs + 0). eapply PERM; eauto.
    omega.
    split; intros; subst; autospe; intuition subst.
    eapply INJ; eauto.
  - econstructor; eauto. intros; autospe. intuition.
  - econstructor; eauto.
    + intros; autospe.
      replace (ofs + (z + z0)) with ((ofs + z) + z0).
      eapply INDATA; eauto. intuition.
      omega.
    + intros; autospe. intuition.
  - econstructor; eauto; intros; autospe; intuition subst.
    rewrite Z.add_0_r. eapply INDATA; eauto.
    eapply FB; eauto.
    eapply H0. eapply INJ; eauto.
  - econstructor; eauto; intros; autospe; intuition subst.
    replace (ofs + (z + z0)) with ((ofs + z) + z0) by omega.
    eapply INDATA0; eauto. 
  - econstructor; eauto; intros; autospe; intuition subst.
    rewrite Z.add_0_r. eapply INDATA; eauto.
    eapply FB; eauto.
    apply H0. eapply INJ0; eauto.
Qed.

Lemma list_frame_inject_compose:
  forall (f f' : meminj) m1 l1 l2,
    list_forall2 (frame_inject _ f m1) l1 l2 ->
    forall m2 l3,
      list_forall2 (frame_inject _ f' m2) l2 l3 ->
      (forall b1 b2 delta o k p,
          f b1 = Some (b2, delta) ->
          perm m1 b1 o k p ->
          inject_perm_condition p ->
          perm m2 b2 (o + delta) k p) ->
    list_forall2 (frame_inject _ (compose_meminj f f') m1) l1 l3.
Proof.
  induction 1; simpl; intros; eauto.
  inv H. constructor.
  inv H1.
  constructor; auto.
  eapply frame_inject_compose; eauto.
  eapply IHlist_forall2; eauto.
Qed.

Definition get_stack_top_blocks (m: mem) : list block :=
  match stack_adt m with
    nil => nil
  | (Some (frame_with_info b fi),_)::r => b :: nil
  | (Some (frame_without_info bl),_)::r => bl
  | (None,_)::r => nil
  end.

Definition is_stack_top (m: mem) (b: block) :=
  In b (get_stack_top_blocks m).

Definition get_frame_info (m: mem) : block -> option frame_info :=
  get_assoc (stack_adt m).

Definition strong_non_private_stack_access (m: mem) (b: block) (lo hi: Z) : Prop :=
  match get_frame_info m b with
    Some fi => in_stack_data lo hi fi
  | None => True
  end.

Definition not_retaddr_or_link_ofs (m: mem) (b: block) (o: Z) : Prop :=
  match get_frame_info m b with
    Some fi => ~ in_segment o (frame_link fi)
               /\ ~ in_segment o (frame_retaddr fi)
  | None => True
  end.

Definition range_not_retaddr_or_link_ofs (m: mem) (b: block) (lo hi: Z) : Prop :=
  forall o, lo <= o < hi -> not_retaddr_or_link_ofs m b o.

Lemma lo_ge_hi_strong_non_private_stack_access:
  forall m b lo hi,
    lo >= hi ->
    strong_non_private_stack_access m b lo hi.
Proof.
  red. intros.
  destruct (get_frame_info m b); try tauto.
  red; intros. omega.
Qed.

Definition non_private_stack_access (m: mem) (b: block) (lo hi: Z) : Prop :=
  (is_stack_top m b /\ range_not_retaddr_or_link_ofs m b lo hi) \/
  (~ is_stack_top m b /\ strong_non_private_stack_access m b lo hi).

Lemma is_stack_top_dec : forall m b,
  {is_stack_top m b} + {~is_stack_top m b}.
Proof.
  intros. unfold is_stack_top. apply in_dec. 
  apply eq_block.
Qed.

Lemma lo_ge_hi_non_private_stack_access:
  forall m b lo hi,
    lo >= hi ->
    non_private_stack_access m b lo hi.
Proof.
  unfold non_private_stack_access.
  intros.
  destruct (is_stack_top_dec m b);[left|right].
  split; auto; red; intros. omega.
  split; auto. eapply lo_ge_hi_strong_non_private_stack_access. auto.
Qed.

Lemma lo_ge_hi_not_retaddr:
  forall m b lo hi,
    lo >= hi ->
    range_not_retaddr_or_link_ofs m b lo hi.
Proof.
  unfold range_not_retaddr_or_link_ofs.
  intros; omega. 
Qed.

Lemma not_in_frames_no_frame_info:
  forall m b,
    ~ in_frames (stack_adt m) b ->
    get_frame_info m b = None.
Proof.
  unfold get_frame_info.
  intro; generalize (stack_adt m).
  induction l; simpl; intros; eauto.
  intuition.
  destruct a, o; simpl in *. destruct f; simpl in *.
  rewrite pred_dec_false; eauto.
  rewrite pred_dec_false; eauto.
  apply not_in_frames_get_assoc; auto.
Qed.

Lemma is_stack_top_stack_blocks:
  forall m b,
    is_stack_top m b <-> (exists f n r, in_frame f b /\ stack_adt m = (f,n)::r).
Proof.
  unfold is_stack_top, get_stack_top_blocks.
  intros.
  destruct (stack_adt m) eqn:?; intuition.
  decompose [ex and] H; intuition congruence.
  destruct p, o. repeat eexists. destruct f; simpl in *; intuition.
  easy.
  destruct p,o. decompose [ex and] H; intuition. inv H2.
  destruct f; simpl in *; intuition.
  decompose [ex and] H. inv H2. simpl in H1. easy.
Qed.

Lemma in_stack_data_inside:
  forall fi lo hi lo' hi',
    in_stack_data lo hi fi ->
    lo <= lo' ->
    hi' <= hi ->
    in_stack_data lo' hi' fi.
Proof.
  intros fi lo hi lo' hi' NPSA LO HI.
  do 2 red in NPSA |- *.
  intros; apply NPSA. omega.
Qed.

Lemma strong_non_private_stack_access_inside:
  forall m b lo hi lo' hi',
    strong_non_private_stack_access m b lo hi ->
    lo <= lo' ->
    hi' <= hi ->
    strong_non_private_stack_access m b lo' hi'.
Proof.
  intros m b lo hi lo' hi' NPSA LO HI.
  unfold strong_non_private_stack_access in *.
  destruct (get_frame_info m b); auto.
  eapply in_stack_data_inside in NPSA; eauto.
Qed.

Lemma non_private_stack_access_inside:
  forall m b lo hi lo' hi',
    non_private_stack_access m b lo hi ->
    lo <= lo' ->
    hi' <= hi ->
    non_private_stack_access m b lo' hi'.
Proof.
  intros m b lo hi lo' hi' NPSA LO HI.
  unfold non_private_stack_access in *.
  destruct NPSA as [[IST RNROLO]|NPSA]; auto.
  left; split; auto.
  red; intros. apply RNROLO. omega.
  destruct NPSA. right. split; auto.
  eapply strong_non_private_stack_access_inside; eauto.
Qed.

Lemma in_segment_dec : forall ofs seg,
  {in_segment ofs seg} + {~in_segment ofs seg}.
Proof.
  unfold in_segment. intros.
  destruct (zle (seg_ofs seg) ofs).
  - destruct (zlt ofs (seg_ofs seg + seg_size seg)).
    + left. auto. 
    + right. omega. 
  - right. omega.
Qed.    

Lemma in_stack_data_dec : forall lo hi f,
  {in_stack_data lo hi f} + {~in_stack_data lo hi f}.
Proof.
  unfold in_stack_data. intros. 
  edestruct (Intv.forall_rec (fun ofs => in_segment ofs (frame_data f))
                             (fun ofs => ~ in_segment ofs (frame_data f))) with (lo:=lo) (hi:=hi).
  - simpl. intros. apply in_segment_dec.
  - auto.
  - right. intro A.
    destruct e as (x & IN & NIN).
    apply NIN. apply A. auto.
Qed.


Lemma strong_non_private_stack_access_dec : forall m b lo hi,
  {strong_non_private_stack_access m b lo hi} + 
  {~strong_non_private_stack_access m b lo hi}.
Proof.
  unfold strong_non_private_stack_access.
  intros.
  destruct (get_frame_info m b); auto.
  apply in_stack_data_dec.
Qed.


Lemma not_retaddr_or_link_ofs_dec : forall m b o,
  {not_retaddr_or_link_ofs m b o} + 
  {~not_retaddr_or_link_ofs m b o}.
Proof.
  unfold not_retaddr_or_link_ofs.
  intros. destr.
  destruct (in_segment_dec o (frame_link f)), (in_segment_dec o (frame_retaddr f)); intuition.  
Qed.

Lemma range_not_retaddr_or_link_ofs_dec : forall m b lo hi,
  {range_not_retaddr_or_link_ofs m b lo hi} + 
  {~range_not_retaddr_or_link_ofs m b lo hi}.
Proof.
  unfold range_not_retaddr_or_link_ofs.
  intros.
  edestruct (Intv.forall_rec (fun ofs => lo <= ofs < hi -> not_retaddr_or_link_ofs m b ofs)
                             (fun ofs => ~ (lo <= ofs < hi -> not_retaddr_or_link_ofs m b ofs))
            ) with (lo0:=lo) (hi0:=hi).
  - simpl. intros.
    destruct (zle lo x).
    destruct (zlt x hi).
    destruct (not_retaddr_or_link_ofs_dec m b x); intuition.
    left; intro; omega.
    left; intro; omega.
  - left; auto.
  - right; intro O.
    destruct e as (x & RNG & NO).
    apply NO. intros. eauto.
Qed.

Lemma non_private_stack_access_dec : forall m b lo hi,
  {non_private_stack_access m b lo hi} + 
  {~non_private_stack_access m b lo hi}.
Proof.
  intros. unfold non_private_stack_access.
  destruct (is_stack_top_dec m b); auto.
  destruct (range_not_retaddr_or_link_ofs_dec m b lo hi); auto.
  destruct (strong_non_private_stack_access_dec m b lo hi); auto.
  right; intuition.
  right. intro A. destruct A. intuition. intuition.
  destruct (strong_non_private_stack_access_dec m b lo hi); auto.
  right. intuition. 
Qed.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).


Definition valid_frame f m :=
  forall b, in_frame f b -> valid_block m b.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs)
  /\ (perm_order p Writable -> non_private_stack_access m b ofs (ofs + size_chunk chunk)).

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

(** Integrity of pointer values. *)

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Definition flat_inj (thr: block) : meminj :=
  fun (b: block) => if plt b thr then Some(b, 0) else None.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Definition abstract_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 -> Mem.stack_adt m2 = Mem.stack_adt m1.

Definition mem_unchanged (T: mem -> mem -> Prop) :=
  forall m1 m2, T m1 m2 ->
           nextblock m2 = nextblock m1
           /\ (forall b o k p, perm m2 b o k p <-> perm m1 b o k p)
           /\ (forall P, strong_unchanged_on P m1 m2)
           /\ (forall b o chunk, Mem.load chunk m2 b o = Mem.load chunk m1 b o).

Lemma stack_adt_eq_get_frame_info:
  forall m m' b,
    stack_adt m = stack_adt m' ->
    get_frame_info m b = get_frame_info m' b.
Proof.
  unfold get_frame_info. congruence.
Qed.

Lemma stack_adt_eq_is_stack_top:
  forall m m' b,
    stack_adt m = stack_adt m' ->
    is_stack_top m b <-> is_stack_top m' b.
Proof.
  unfold is_stack_top, get_stack_top_blocks. intros m m' b H. rewrite H. tauto.
Qed.

Lemma stack_adt_eq_strong_non_private_stack_access:
  forall m m1 ,
    stack_adt m1 = stack_adt m ->
    forall b' lo hi,
      strong_non_private_stack_access m1 b' lo hi <-> strong_non_private_stack_access m b' lo hi.
Proof.
  intros.
  unfold strong_non_private_stack_access.
  erewrite stack_adt_eq_get_frame_info; eauto. tauto.
Qed.

Lemma stack_adt_eq_non_private_stack_access:
  forall m m1 ,
    stack_adt m1 = stack_adt m ->
    forall b' lo hi,
      non_private_stack_access m1 b' lo hi <-> non_private_stack_access m b' lo hi.
Proof.
  intros.
  unfold non_private_stack_access.
  erewrite stack_adt_eq_strong_non_private_stack_access; eauto.
  unfold is_stack_top, range_not_retaddr_or_link_ofs.
  unfold get_stack_top_blocks, strong_non_private_stack_access, not_retaddr_or_link_ofs.
  unfold get_frame_info.
  rewrite H. tauto.
Qed.

End WITHMEMORYMODELOPS.


Class MemoryModel mem `{memory_model_ops: MemoryModelOps mem} {injperm: InjectPerm}
  : Prop :=
{

 valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b';

(** Logical implications between permissions *)

 perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2;

(** The current permission is always less than or equal to the maximal permission. *)

 perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p;
 perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p;
 perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p;

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
 perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b;

 range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2;

 range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p;

 range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p;

 valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2;

 valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b;

 valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p;

 valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty;
 valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty;

 weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true;
 valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true;

(** * Properties of the memory operations *)

(** ** Properties of the initial memory state. *)

 nextblock_empty: nextblock empty = 1%positive;
 perm_empty: forall b ofs k p, ~perm empty b ofs k p;
 valid_access_empty:
  forall chunk b ofs p, ~valid_access empty chunk b ofs p;

(** ** Properties of [load]. *)

(** A load succeeds if and only if the access is valid for reading *)
 valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v;
 load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable;

(** The value returned by [load] belongs to the type of the memory quantity
  accessed: [Vundef], [Vint] or [Vptr] for an integer quantity,
  [Vundef] or [Vfloat] for a float quantity. *)
 load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk);

(** For a small integer or float type, the value returned by [load]
  is invariant under the corresponding cast. *)
 load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end;

 load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs);

 load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs);

 loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv  Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2);

(** ** Properties of [loadbytes]. *)

(** [loadbytes] succeeds if and only if we have read permissions on the accessed
    memory area. *)

 range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes;
 loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable;

(** If [loadbytes] succeeds, the corresponding [load] succeeds and
  returns a value that is determined by the
  bytes read by [loadbytes]. *)
 loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes);

(** Conversely, if [load] returns a value, the corresponding
  [loadbytes] succeeds and returns a list of bytes which decodes into the
  result of [load]. *)
 load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes;

(** [loadbytes] returns a list of length [n] (the number of bytes read). *)
 loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = nat_of_Z n;

 loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil;

(** Composing or decomposing [loadbytes] operations at adjacent addresses. *)
 loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2);
 loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2;

(** ** Properties of [store]. *)

(** [store] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [store] succeeds if and only if the corresponding access
  is valid for writing. *)

 nextblock_store:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  nextblock m2 = nextblock m1;
 store_valid_block_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 store_valid_block_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

 perm_store_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_store_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;

 valid_access_store':
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  exists m2: mem, store chunk m1 b ofs v = Some m2;
 store_valid_access_1:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 store_valid_access_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 store_valid_access_3:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  valid_access m1 chunk b ofs Writable;

(** Load-store properties. *)

 load_store_similar:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v';
 load_store_similar_2:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v);

 load_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  load chunk m2 b ofs = Some (Val.load_result chunk v);

 load_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs';

 load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef;
 load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef;
 load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs');

(** Load-store properties for [loadbytes]. *)

 loadbytes_store_same:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v);
 loadbytes_store_other:
  forall chunk m1 b ofs v m2, store chunk m1 b ofs v = Some m2 ->
  forall b' ofs' n,
  b' <> b \/ n <= 0 \/ ofs' + n <= ofs \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n;

(** [store] is insensitive to the signedness or the high bits of
  small integer quantities. *)

 store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v;
 store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v;
 store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n);
 store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n);
 store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n);
 store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n);
 storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m';

(** ** Properties of [storebytes]. *)

(** [storebytes] preserves block validity, permissions, access validity, and bounds.
  Moreover, a [storebytes] succeeds if and only if we have write permissions
  on the addressed memory area. *)

 range_perm_storebytes' :
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    non_private_stack_access m1 b ofs (ofs + Z_of_nat (length bytes)) ->
  exists m2 : mem, storebytes m1 b ofs bytes = Some m2;
 storebytes_range_perm:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
                       range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable;
 storebytes_non_private_stack_access:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
     non_private_stack_access m1 b ofs (ofs + Z_of_nat (length bytes)) ;
 perm_storebytes_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p;
 perm_storebytes_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p;
 storebytes_valid_access_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p;
 storebytes_valid_access_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p;
 nextblock_storebytes:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  nextblock m2 = nextblock m1;
 storebytes_valid_block_1:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 storebytes_valid_block_2:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b', valid_block m2 b' -> valid_block m1 b';

(** Connections between [store] and [storebytes]. *)

 storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2;

 store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2;

(** Load-store properties. *)

 loadbytes_storebytes_same:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  loadbytes m2 b ofs (Z_of_nat (length bytes)) = Some bytes;
 loadbytes_storebytes_disjoint:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z_of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 loadbytes_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len;
 load_storebytes_other:
  forall m1 b ofs bytes m2, storebytes m1 b ofs bytes = Some m2 ->
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z_of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs';

(** Composing or decomposing [storebytes] operations at adjacent addresses. *)

 storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2;
 storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z_of_nat(length bytes1)) bytes2 = Some m2;

(** ** Properties of [alloc]. *)

(** The identifier of the freshly allocated block is the next block
  of the initial memory state. *)

 alloc_result:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  b = nextblock m1;

(** Effect of [alloc] on block validity. *)

 nextblock_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  nextblock m2 = Psucc (nextblock m1);

 valid_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m1 b' -> valid_block m2 b';
 fresh_block_alloc:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  ~(valid_block m1 b);
 valid_new_block:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  valid_block m2 b;
 valid_block_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b';

(** Effect of [alloc] on permissions. *)

 perm_alloc_1:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p;
 perm_alloc_2:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable;
 perm_alloc_3:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi;
 perm_alloc_4:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p;
 perm_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p;

(** Effect of [alloc] on access validity. *)

 valid_access_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p;
 valid_access_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable;
 valid_access_alloc_inv:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p;

(** Load-alloc properties. *)

 load_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs;
 load_alloc_other:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v;
 load_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef;
 load_alloc_same':
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef;
 loadbytes_alloc_unchanged:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n;
 loadbytes_alloc_same:
  forall m1 lo hi m2 b, alloc m1 lo hi = (m2, b) ->
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef;

(** ** Properties of [free]. *)

(** [free] succeeds if and only if the correspond range of addresses
  has [Freeable] current permission. *)

 range_perm_free' :
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  exists m2: mem, free m1 b lo hi = Some m2;
 free_range_perm:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
                    range_perm m1 bf lo hi Cur Freeable;

(** Block validity is preserved by [free]. *)

 nextblock_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  nextblock m2 = nextblock m1;
 valid_block_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m1 b -> valid_block m2 b;
 valid_block_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b, valid_block m2 b -> valid_block m1 b;

(** Effect of [free] on permissions. *)

 perm_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p;
 perm_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p;
 perm_free_3:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p;

(** Effect of [free] on access validity. *)

 valid_access_free_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p;
 valid_access_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p);
 valid_access_free_inv_1:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p;
 valid_access_free_inv_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs;

(** Load-free properties *)

 load_free:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs;
 loadbytes_free_2:
  forall m1 bf lo hi m2, free m1 bf lo hi = Some m2 ->
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes;

(** ** Properties of [drop_perm]. *)

 nextblock_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  nextblock m' = nextblock m;
 drop_perm_valid_block_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m b' -> valid_block m' b';
 drop_perm_valid_block_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b', valid_block m' b' -> valid_block m b';

 range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  range_perm m b lo hi Cur Freeable;
 range_perm_drop_2' :
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> exists m', drop_perm m b lo hi p = Some m';

 perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p;
 perm_drop_2:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p';
 perm_drop_3:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p';
 perm_drop_4:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p';

 loadbytes_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n;
 load_drop:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' ->
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs;


(** ** Properties of [extends]. *)

 extends_refl:
  forall m, extends m m;

 load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2;

 loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2;

 loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2;

 store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2';

 store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2';

 storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2';

 storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2';

 storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z_of_nat (length bytes2) -> False) ->
  extends m1 m2';

 alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2';

 free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2;

 free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2';

 free_parallel_extends:
  forall m1 m2 b lo hi m1',
    extends m1 m2 ->
    inject_perm_condition Freeable ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2';

 valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b);
 perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> inject_perm_condition p -> perm m2 b ofs k p;
 valid_access_extends:
  forall m1 m2 chunk b ofs p,
    extends m1 m2 -> valid_access m1 chunk b ofs p -> inject_perm_condition p ->
    valid_access m2 chunk b ofs p;
 valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true;
 weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true;

  
(** ** Properties of [magree]. *)
 ma_perm:
   forall m1 m2 (P: locset),
     magree m1 m2 P ->
     forall b ofs k p,
       perm m1 b ofs k p ->
       inject_perm_condition p ->
       perm m2 b ofs k p;

 magree_monotone:
  forall m1 m2 (P Q: locset),
  magree m1 m2 P ->
  (forall b ofs, Q b ofs -> P b ofs) ->
  magree m1 m2 Q;

 mextends_agree:
  forall m1 m2 P, extends m1 m2 -> magree m1 m2 P;

 magree_extends:
  forall m1 m2 (P: locset),
  (forall b ofs, P b ofs) ->
  magree m1 m2 P -> extends m1 m2;

 magree_loadbytes:
  forall m1 m2 P b ofs n bytes,
  magree m1 m2 P ->
  loadbytes m1 b ofs n = Some bytes ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  exists bytes', loadbytes m2 b ofs n = Some bytes' /\ list_forall2 memval_lessdef bytes bytes';

 magree_load:
  forall m1 m2 P chunk b ofs v,
  magree m1 m2 P ->
  load chunk m1 b ofs = Some v ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  exists v', load chunk m2 b ofs = Some v' /\ Val.lessdef v v';

 magree_storebytes_parallel:
  forall m1 m2 (P Q: locset) b ofs bytes1 m1' bytes2,
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall b' i, Q b' i ->
                b' <> b \/ i < ofs \/ ofs + Z_of_nat (length bytes1) <= i ->
                P b' i) ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2', storebytes m2 b ofs bytes2 = Some m2' /\ magree m1' m2' Q;

 magree_storebytes_left:
  forall m1 m2 P b ofs bytes1 m1',
  magree m1 m2 P ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes1) -> ~(P b i)) ->
  magree m1' m2 P;

 magree_store_left:
  forall m1 m2 P chunk b ofs v1 m1',
  magree m1 m2 P ->
  store chunk m1 b ofs v1 = Some m1' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~(P b i)) ->
  magree m1' m2 P;

 magree_free:
  forall m1 m2 (P Q: locset) b lo hi m1',
    magree m1 m2 P ->
    inject_perm_condition Freeable ->
    free m1 b lo hi = Some m1' ->
    (forall b' i, Q b' i ->
             b' <> b \/ ~(lo <= i < hi) ->
             P b' i) ->
    exists m2', free m2 b lo hi = Some m2' /\ magree m1' m2' Q;

 magree_valid_access:
  forall m1 m2 (P: locset) chunk b ofs p,
  magree m1 m2 P ->
  valid_access m1 chunk b ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b ofs p;

(** ** Properties of [inject]. *)
 mi_no_overlap:
   forall f m1 m2,
   inject f m1 m2 ->
   meminj_no_overlap f m1;

 mi_delta_pos:
   forall f m1 m2 b1 b2 delta,
     inject f m1 m2 ->
     f b1 = Some (b2, delta) ->
     delta >= 0;

 valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1;

 valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2;

 perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p ->
  inject_perm_condition p ->
  perm m2 b2 (ofs + delta) k p;

 range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  inject_perm_condition p ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p;

 valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  inject_perm_condition p ->
  valid_access m2 chunk b2 (ofs + delta) p;

 valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true;

 weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true;

 address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 (** The following is needed by Separation, to prove storev_parallel_rule *)
 address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta;

 valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned;

 valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true;

 inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2;

 different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2));

 disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1;

 aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta);

 load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2;

 loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2;

 loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2;

 store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2;

 store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2;

 store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2';

 storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2;

 storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2;

 storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2;

 storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z_of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2';

 storebytes_empty_inject:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f m1' m2';

 alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2';

 alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  inject f m1 m2 ->
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
  ~ in_frames (stack_adt m2) b2 ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b);

 alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b);

 free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2';

 free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2;
 free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2;

 free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2';

 free_parallel_inject:
  forall f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  inject_perm_condition Freeable ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f m1' m2';

 drop_outside_inject:
  forall f m1 m2 b lo hi p m2',
    inject f m1 m2 ->
    drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2';

(** The following property is needed by ValueDomain, to prove mmatch_inj. *)

 self_inject f m:
  (forall b, f b = None \/ f b = Some (b, 0)) ->
  (forall b, f b <> None -> Mem.valid_block m b) ->
  (forall b,
     f b <> None ->
     forall o b' o' q n,
       loadbytes m b o 1 = Some (Fragment (Vptr b' o') q n :: nil) ->
       f b' <> None) ->
  Mem.inject f m m;

 inject_stack_adt:
   forall f m1 m2,
     inject f m1 m2 ->
     list_forall2
       (fun x y =>
          match fst x, fst y with
            Some f1, Some f2 => frame_inject _ f m1 f1 f2
          | None, Some _ => False
          | _, _ => True
          end
          /\ snd x = snd y)
       (stack_adt m1) (stack_adt m2);

 extends_stack_adt:
   forall m1 m2,
     extends m1 m2 ->
     list_forall2
       (fun x y =>
          match fst x, fst y with
            Some f1, Some f2 => frame_inject _ inject_id m1 f1 f2
          | None, Some _ => False
          | _, _ => True
          end
          /\ snd x = snd y)
       (stack_adt m1) (stack_adt m2);

(* Needed by Stackingproof, with Linear2 to Mach,
   to compose extends (in Linear2) and inject. *)
 extends_inject_compose:
   forall f m1 m2 m3,
     extends m1 m2 -> inject f m2 m3 -> inject f m1 m3;

 (* Needed by EraseArgs. *)
 extends_extends_compose:
   forall m1 m2 m3,
     extends m1 m2 -> extends m2 m3 -> extends m1 m3;


(** ** Properties of [inject_neutral] *)

 neutral_inject:
  forall m, inject_neutral (nextblock m) m ->
  inject (flat_inj (nextblock m)) m m;

 empty_inject_neutral:
  forall thr, inject_neutral thr empty;

 empty_stack_adt:
   stack_adt empty = nil;

 alloc_inject_neutral:
  forall thr m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral thr m ->
  Plt (nextblock m) thr ->
  inject_neutral thr m';

 store_inject_neutral:
  forall chunk m b ofs v m' thr,
  store chunk m b ofs v = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  Val.inject (flat_inj thr) v v ->
  inject_neutral thr m';

 drop_inject_neutral:
  forall m b lo hi p m' thr,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral thr m ->
  Plt b thr ->
  inject_neutral thr m';
drop_perm_stack_adt:
  forall m1 b lo hi p m1',
    drop_perm m1 b lo hi p = Some m1' ->
    stack_adt m1' = stack_adt m1;

(** ** Properties of [unchanged_on] and [strong_unchanged_on] *)

 strong_unchanged_on_weak P m1 m2:
  strong_unchanged_on P m1 m2 ->
  unchanged_on P m1 m2;
 unchanged_on_nextblock P m1 m2:
  unchanged_on P m1 m2 ->
  Ple (nextblock m1) (nextblock m2);
 strong_unchanged_on_refl:
  forall P m, strong_unchanged_on P m m;
 unchanged_on_trans:
  forall P m1 m2 m3, unchanged_on P m1 m2 -> unchanged_on P m2 m3 -> unchanged_on P m1 m3;
 strong_unchanged_on_trans:
  forall P m1 m2 m3, strong_unchanged_on P m1 m2 -> strong_unchanged_on P m2 m3 -> strong_unchanged_on P m1 m3;
 perm_unchanged_on:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p;
 perm_unchanged_on_2:
  forall P m m' b ofs k p,
  unchanged_on P m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p;
 loadbytes_unchanged_on_1:
  forall P m m' b ofs n,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n;
 loadbytes_unchanged_on:
   forall P m m' b ofs n bytes,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + n -> P b i) ->
     loadbytes m b ofs n = Some bytes ->
     loadbytes m' b ofs n = Some bytes;
 load_unchanged_on_1:
  forall P m m' chunk b ofs,
  unchanged_on P m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs;
 load_unchanged_on:
   forall P m m' chunk b ofs v,
     unchanged_on P m m' ->
     (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
     load chunk m b ofs = Some v ->
     load chunk m' b ofs = Some v;
 store_strong_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    strong_unchanged_on P m m';
 storebytes_strong_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  strong_unchanged_on P m m';
 alloc_strong_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     strong_unchanged_on P m m';
 free_strong_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  strong_unchanged_on P m m';
 drop_perm_strong_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     strong_unchanged_on P m m';
 unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     unchanged_on Q m m'
 ;
 strong_unchanged_on_implies:
   forall (P Q: block -> Z -> Prop) m m',
     strong_unchanged_on P m m' ->
     (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
     strong_unchanged_on Q m m'
 ;

(** The following property is needed by Separation, to prove
minjection. HINT: it can be used only for [strong_unchanged_on], not
for [unchanged_on]. *)

 inject_strong_unchanged_on j m0 m m' :
   inject j m0 m ->
   strong_unchanged_on
     (fun (b : block) (ofs : Z) =>
        exists (b0 : block) (delta : Z),
          j b0 = Some (b, delta) /\
          perm m0 b0 (ofs - delta) Max Nonempty) m m' ->
   stack_adt m' = stack_adt m ->
   inject j m0 m';

 (* Original operations don't modify the abstract part. *)
 store_no_abstract:
   forall chunk b o v, abstract_unchanged (fun m1 m2 => Mem.store chunk m1 b o v = Some m2);

 storebytes_no_abstract:
   forall b o bytes, abstract_unchanged (fun m1 m2 => Mem.storebytes m1 b o bytes = Some m2);

 alloc_no_abstract:
   forall lo hi b, abstract_unchanged (fun m1 m2 => Mem.alloc m1 lo hi = (m2, b));

 free_no_abstract:
   forall lo hi b, abstract_unchanged (fun m1 m2 => Mem.free m1 b lo hi = Some m2);

 freelist_no_abstract:
   forall bl, abstract_unchanged (fun m1 m2 => Mem.free_list m1 bl = Some m2);

 drop_perm_no_abstract:
   forall b lo hi p, abstract_unchanged (fun m1 m2 => Mem.drop_perm m1 b lo hi p = Some m2);

 (* Properties of record_stack_block *)

 record_stack_blocks_inject:
   forall m1 m1' m2 j fi1 fi2 n,
     inject j m1 m2 ->
     match fi1, fi2 with
     | Some fi1, Some fi2 => frame_inject _ j m1 fi1 fi2
     | None, Some _ => False
     | _, _ => True
     end ->
     (forall (b0 b'0 : block) (delta0 : Z),
         in_frames (stack_adt m1) b0 -> j b0 = Some (b'0, delta0) ->
         ~ in_frame fi1 b0 /\ ~ in_frame fi2 b'0) ->
     (valid_frame fi2 m2) ->
     record_stack_blocks m1 fi1 n = Some m1' ->
     exists m2',
       record_stack_blocks m2 fi2 n = Some m2' /\
       inject j m1' m2';

 record_stack_blocks_extends:
    forall m1 m2 m1' fi n,
      extends m1 m2 ->
      record_stack_blocks m1 fi n = Some m1' ->
      (forall b, in_frame fi b -> ~ in_frames (stack_adt m1) b ) ->
      exists m2',
        record_stack_blocks m2 fi n = Some m2' /\
        extends m1' m2';

 record_stack_blocks_mem_unchanged:
   forall bfi n,
     mem_unchanged (fun m1 m2 => record_stack_blocks m1 bfi n = Some m2);

 record_stack_blocks_stack_adt:
   forall m fi m' n,
     record_stack_blocks m fi n = Some m' ->
     stack_adt m' = (fi, n) :: stack_adt m;

 record_stack_blocks_inject_neutral:
   forall thr m fi m' n,
     inject_neutral thr m ->
     record_stack_blocks m fi n = Some m' ->
     (match fi with
        Some (frame_with_info b _) => Plt b thr
      | _ => True
      end) ->
     inject_neutral thr m';

 (* Properties of unrecord_stack_block *)

 unrecord_stack_block_inject:
   forall (m1 m1' m2 m2' : mem) (j : meminj),
     inject j m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\ inject j m1' m2';

 unrecord_stack_block_extends:
   forall m1 m2 m1',
     extends m1 m2 ->
     unrecord_stack_block m1 = Some m1' ->
     exists m2',
       unrecord_stack_block m2 = Some m2' /\
       extends m1' m2';

 unrecord_stack_block_mem_unchanged:
   mem_unchanged (fun m1 m2 => unrecord_stack_block m1 = Some m2);

 unrecord_stack_adt:
   forall m m',
     unrecord_stack_block m = Some m' ->
     exists b,
       stack_adt m = b :: stack_adt m';

 unrecord_stack_block_succeeds:
   forall m b r,
     stack_adt m = b :: r ->
     exists m',
       unrecord_stack_block m = Some m'
       /\ stack_adt m' = r;

 unrecord_stack_block_inject_neutral:
   forall thr m m',
     inject_neutral thr m ->
     unrecord_stack_block m = Some m' ->
     inject_neutral thr m';


 (* Other properties *)

 strong_non_private_stack_access_extends:
   forall m1 m2 b lo hi p,
     extends m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     strong_non_private_stack_access m1 b lo hi ->
     strong_non_private_stack_access m2 b lo hi;

 strong_non_private_stack_access_inject:
   forall f m1 m2 b b' delta lo hi p,
     f b = Some (b', delta) ->
     inject f m1 m2 ->
     range_perm m1 b lo hi Cur p ->
     strong_non_private_stack_access m1 b lo hi ->
     strong_non_private_stack_access m2 b' (lo + delta) (hi + delta);

 strong_non_private_stack_access_magree: forall P (m1 m2 : mem) (b : block) (lo hi : Z) p,
     magree m1 m2 P ->
     range_perm m1 b lo hi Cur p ->
     strong_non_private_stack_access m1 b lo hi ->
     strong_non_private_stack_access m2 b lo hi;


 not_in_frames_extends:
   forall m1 m2 b,
     extends m1 m2 ->
     ~ in_frames ((stack_adt m1)) b ->
     ~ in_frames ((stack_adt m2)) b;


 not_in_frames_inject:
   forall f m1 m2 b b' delta,
     f b = Some (b', delta) ->
     inject f m1 m2 ->
     ~ in_frames ((stack_adt m1)) b ->
     ~ in_frames ((stack_adt m2)) b';

 (* same_frame_extends: *)
 (*   forall m1 m2 b fi r n, *)
 (*     Mem.extends m1 m2 -> *)
 (*     Mem.stack_adt m1 = (Some frame_with_info b (Some fi), n) :: r -> *)
 (*     exists r', *)
 (*       Mem.stack_adt m2 = (frame_with_info b (Some fi), n) :: r'; *)
 in_frames_valid:
   forall m b,
     in_frames (stack_adt m) b -> valid_block m b;

 is_stack_top_extends:
   forall m1 m2 b
     (MINJ: extends m1 m2)
     (IST: is_stack_top m1 b),
     is_stack_top m2 b \/ exists n r, stack_adt m2 = (None,n)::r;

 is_stack_top_inject:
   forall f m1 m2 b1 b2 delta
     (MINJ: inject f m1 m2)
     (FB: f b1 = Some (b2, delta))
     (IST: is_stack_top m1 b1),
     is_stack_top m2 b2  \/ exists n r, stack_adt m2 = (None,n)::r;

}.

Section WITHMEMORYMODEL.

Context `{memory_model_prf: MemoryModel}.

Lemma stack_top_valid:
  forall m b, is_stack_top m b -> valid_block m b.
Proof.
  intros. rewrite is_stack_top_stack_blocks in H.
  decompose [ex and] H.
  eapply in_frames_valid. rewrite H2; simpl; auto.
Qed.

Lemma get_frame_info_in_frames:
  forall m b f, get_frame_info m b = Some f -> in_frames ((stack_adt m)) b.
Proof.
  intros.
  destruct (in_frames_dec (stack_adt m) b); auto.
  rewrite not_in_frames_no_frame_info in H; auto. congruence.
Qed.

Lemma get_frame_info_valid:
  forall m b f, get_frame_info m b = Some f -> valid_block m b.
Proof.
  intros. eapply in_frames_valid. eapply get_frame_info_in_frames; eauto.
Qed.

Lemma invalid_block_non_private_stack_access:
  forall m b lo hi,
    ~ valid_block m b ->
    non_private_stack_access m b lo hi.
Proof.
  right. split.
  intro ISP. apply stack_top_valid in ISP. auto.
  red.
  rewrite not_in_frames_no_frame_info. auto.
  intro IN; apply in_frames_valid in IN; congruence.
Qed.

Lemma store_get_frame_info:
  forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
  forall b', get_frame_info m2 b' = get_frame_info m1 b'.
Proof.
  intros. 
  eapply stack_adt_eq_get_frame_info, store_no_abstract; eauto.
Qed.

Lemma store_stack_blocks:
  forall m1 sp chunk o v m2,
    store chunk m1 sp o v = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof.
  intros. 
  eapply store_no_abstract; eauto.
Qed.

Lemma store_is_stack_top:
   forall chunk m1 b o v m2 (STORE: store chunk m1 b o v = Some m2),
   forall b', is_stack_top m2 b' <-> is_stack_top m1 b'.
Proof.
  intros; eapply stack_adt_eq_is_stack_top, store_no_abstract; eauto.
Qed.

Lemma storebytes_get_frame_info:
   forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
   forall b', get_frame_info m2 b' = get_frame_info m1 b'.
Proof.
  intros; eapply stack_adt_eq_get_frame_info, storebytes_no_abstract; eauto.
Qed.

Lemma storebytes_is_stack_top:
  forall m1 b o v m2 (STOREBYTES: storebytes m1 b o v = Some m2),
  forall b', is_stack_top m2 b' <-> is_stack_top m1 b'.
Proof.
  intros; eapply stack_adt_eq_is_stack_top, storebytes_no_abstract; eauto.
Qed.

Lemma alloc_get_frame_info:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', get_frame_info m2 b' = get_frame_info m1 b'.
Proof.
  intros; eapply stack_adt_eq_get_frame_info, alloc_no_abstract; eauto.
Qed.
Lemma alloc_is_stack_top:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
  forall b', is_stack_top m2 b' <-> is_stack_top m1 b'.
Proof.
  intros; eapply stack_adt_eq_is_stack_top, alloc_no_abstract; eauto.
Qed.

Lemma alloc_get_frame_info_fresh:
  forall m1 lo hi m2 b (ALLOC: alloc m1 lo hi = (m2, b)),
    get_frame_info m2 b = None.
Proof.
  intros; eapply not_in_frames_no_frame_info.
  rewrite alloc_no_abstract; eauto.
  intro IN; apply in_frames_valid in IN.
  eapply fresh_block_alloc in IN; eauto.
Qed.

Lemma alloc_stack_blocks:
  forall m1 lo hi m2 b,
    alloc m1 lo hi = (m2, b) ->
    stack_adt m2 = stack_adt m1.
Proof. intros; eapply alloc_no_abstract; eauto. Qed.

Lemma free_stack_blocks:
  forall m1 b lo hi m2,
    free m1 b lo hi = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof. intros; eapply free_no_abstract; eauto. Qed.

Lemma free_get_frame_info:
  forall m1 b lo hi m2 b',
    free m1 b lo hi = Some m2 ->
    get_frame_info m2 b' = get_frame_info m1 b'.
Proof.
  intros; eapply stack_adt_eq_get_frame_info, free_no_abstract; eauto.
Qed.

Lemma storebytes_stack_blocks:
  forall m1 b o bytes m2,
    storebytes m1 b o bytes = Some m2 ->
    stack_adt m2 = stack_adt m1.
Proof.
  intros; eapply storebytes_no_abstract; eauto.
Qed.

Lemma free_list_stack_blocks:
  forall m bl m',
    free_list m bl = Some m' ->
    stack_adt m' = stack_adt m.
Proof.
  intros; eapply freelist_no_abstract; eauto.
Qed.

Lemma record_stack_block_unchanged_on:
  forall m bfi m' n (P: block -> Z -> Prop),
    record_stack_blocks m bfi n = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros; eapply record_stack_blocks_mem_unchanged; eauto.
Qed.

Lemma record_stack_block_perm:
  forall m bfi m' n,
    record_stack_blocks m bfi n = Some m' ->
    forall b' o k p,
      perm m' b' o k p ->
      perm m b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_perm'
  : forall m m' bofi n,
    record_stack_blocks m bofi n = Some m' ->
    forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
      perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply record_stack_blocks_mem_unchanged in H; eauto.
  apply H; eauto.
Qed.

Lemma record_stack_block_valid:
  forall m bf n m',
    record_stack_blocks m bf n = Some m' ->
    forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  destruct H. rewrite H. auto.
Qed.

Lemma record_stack_block_nextblock:
  forall m bf n m',
    record_stack_blocks m bf n = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros.
  eapply record_stack_blocks_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma record_stack_block_is_stack_top:
  forall m b fi n m',
    record_stack_blocks m fi n = Some m' ->
    in_frame fi b ->
    Mem.is_stack_top m' b.
Proof.
  unfold is_stack_top, get_stack_top_blocks.
  intros.
  erewrite record_stack_blocks_stack_adt; eauto. simpl. red in H0.
  destruct fi; simpl; auto.
  destruct f; simpl; auto.
Qed.

Lemma unrecord_stack_block_unchanged_on:
  forall m m' P,
    unrecord_stack_block m = Some m' ->
    strong_unchanged_on P m m'.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_perm:
   forall m m',
     unrecord_stack_block m = Some m' ->
     forall b' o k p,
       perm m' b' o k p ->
       perm m b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_perm'
     : forall m m' : mem,
       unrecord_stack_block m = Some m' ->
       forall (b' : block) (o : Z) (k : perm_kind) (p : permission),
       perm m b' o k p -> perm m' b' o k p.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition. apply H; auto.
Qed.

Lemma unrecord_stack_block_nextblock:
  forall m m',
    unrecord_stack_block m = Some m' ->
    nextblock m' = nextblock m.
Proof.
  intros. eapply unrecord_stack_block_mem_unchanged in H; eauto.
  intuition.
Qed.

Lemma unrecord_stack_block_get_frame_info:
   forall m m' b,
     Mem.unrecord_stack_block m = Some m' ->
     ~ Mem.is_stack_top m b ->
     Mem.get_frame_info m' b = Mem.get_frame_info m b.
Proof.
  unfold is_stack_top, get_stack_top_blocks, get_frame_info. intros.
  exploit unrecord_stack_adt. eauto. intros (b0 & EQ).
  rewrite EQ in *. simpl. destruct b0,o. simpl. destruct f; intuition.
  destruct eq_block; simpl in *; intuition.
  destruct in_dec; simpl in *; intuition.
  auto.
Qed.

Lemma valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros m1 chunk b ofs v H.
  destruct (store _ _ _ _ _) eqn:STORE; eauto.
  exfalso.
  eapply @valid_access_store' with (v := v) in H; eauto.
  destruct H.
  congruence.
Defined.

Lemma range_perm_storebytes:
  forall m1 b ofs bytes,
    range_perm m1 b ofs (ofs + Z_of_nat (length bytes)) Cur Writable ->
    non_private_stack_access m1 b ofs (ofs + Z_of_nat (length bytes)) ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros m1 b ofs bytes H NPSA.
  destruct (storebytes _ _ _ _) eqn:STOREBYTES; eauto.
  exfalso.
  apply range_perm_storebytes' in H.
  destruct H.
  congruence.
  apply NPSA.
Defined.

Lemma range_perm_free:
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

Lemma range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> { m' | drop_perm m b lo hi p = Some m' }.
Proof.
  intros m b lo hi p H.
  destruct (drop_perm _ _ _ _ _) eqn:DROP; eauto.
  exfalso.
  eapply @range_perm_drop_2' with (p := p) in H; eauto.
  destruct H.
  congruence.
Defined.

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
  split. eapply Mem.perm_free_3; eauto.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Lemma unchanged_on_refl:
  forall P m, unchanged_on P m m.
Proof.
  intros. apply strong_unchanged_on_weak. apply strong_unchanged_on_refl.
Qed.

Lemma store_unchanged_on:
  forall P chunk m b ofs v m',
    store chunk m b ofs v = Some m' ->
    (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
    unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply store_strong_unchanged_on; eauto.
Qed.

Lemma storebytes_unchanged_on:
  forall P m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z_of_nat (length bytes) -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply storebytes_strong_unchanged_on; eauto.
Qed.

Lemma alloc_unchanged_on:
   forall P m lo hi m' b,
     alloc m lo hi = (m', b) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply alloc_strong_unchanged_on; eauto.
Qed.

Lemma free_unchanged_on:
  forall P m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply free_strong_unchanged_on; eauto.
Qed.

Lemma drop_perm_unchanged_on:
   forall P m b lo hi p m',
     drop_perm m b lo hi p = Some m' ->
     (forall i, lo <= i < hi -> ~ P b i) ->
     unchanged_on P m m'.
Proof.
  intros. apply strong_unchanged_on_weak. eapply drop_perm_strong_unchanged_on; eauto.
Qed.

Lemma perm_free m b lo hi m':
  free m b lo hi = Some m' ->
  forall b' o' k p,
    perm m' b' o' k p <->
    ((~ (b' = b /\ lo <= o' < hi)) /\ perm m b' o' k p).
Proof.
  intros H b' o' k p.
  assert (~ (b' = b /\ lo <= o' < hi) -> perm m b' o' k p -> perm m' b' o' k p) as H0.
  {
    intro H0.
    eapply perm_free_1; eauto.
    destruct (peq b' b); try tauto.
    subst.
    intuition xomega.
  }
  assert (b' = b /\ lo <= o' < hi -> ~ perm m' b' o' k p) as H1.
  destruct 1; subst; eapply perm_free_2; eauto.
  generalize (perm_free_3 _ _ _ _ _ H b' o' k p).
  tauto.
Qed.

Lemma store_non_private_stack_access:
  forall chunk m b o v m1 ,
    Mem.store chunk m b o v = Some m1 ->
    forall b' lo hi,
      Mem.non_private_stack_access m1 b' lo hi <-> Mem.non_private_stack_access m b' lo hi.
Proof.
  intros; eapply stack_adt_eq_non_private_stack_access, store_no_abstract; eauto.
Qed.

End WITHMEMORYMODEL.

End Mem.
