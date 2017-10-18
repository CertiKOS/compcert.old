Require Import Coqlib.
Require Import MemPerm.
Require Import Memdata.
Require Import AST.
Require Import Values.
Require Intv.

(** This file holds definitions related to our stack abstract data type (ADT).   *)

(** * Segments  *)

(** Segments are building blocks of the abstract data we attach to stack blocks.
They specify the offset at which the segment begins, and the size of the
segment. *)

Record segment :=
  {
    seg_ofs: Z;
    seg_size: Z;
  }.

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

(** * Frame information  *)
(** A frame information [frame_info] contains a list of segments corresponding
to the actual frame layout used at the Stacking phase, at a late compilation
phase. This dependent record also contains well-formedness properties that
assert the disjointness of all the segments and fix the size of the special
segments for the return address and the link to the parent frame, which are
known to be the size of a pointer. *)

Inductive stack_permission: Type :=
  Public
| Private
| Readonly.

Definition stack_perm_eq: forall (p1 p2: stack_permission), {p1=p2} + {p1 <> p2}.
Proof.
  decide equality.
Qed.

Record frame_info :=
  {
    frame_size: Z;
    frame_link: segment;
    frame_perm: Z -> stack_permission;
    frame_link_size:
      seg_size frame_link = size_chunk Mptr;
    frame_link_readonly:
      forall i, in_segment i frame_link -> frame_perm i = Readonly;
  }.

Definition frame_public f o := frame_perm f o = Public.
Definition frame_private f o := frame_perm f o = Private.
Definition frame_readonly f o := frame_perm f o = Readonly.

Definition frame_public_dec: forall f o, {frame_public f o} + {~ frame_public f o}.
Proof.
  unfold frame_public; intros; apply stack_perm_eq.
Qed.

Definition frame_private_dec: forall f o, {frame_private f o} + {~ frame_private f o}.
Proof.
  unfold frame_private; intros; apply stack_perm_eq.
Qed.

Definition frame_readonly_dec: forall f o, {frame_readonly f o} + {~ frame_readonly f o}.
Proof.
  unfold frame_readonly; intros; apply stack_perm_eq.
Qed.

(** We define empty segments and frames for the sole purpose of being able to
provide a dummy frame for initialization purposes in backend/Asmexpand.ml. These
empty frames are never actually used in the compiler. *)

Definition empty_segment : segment :=
  {|
    seg_ofs := 0;
    seg_size:= 0;
  |}.

Program Definition empty_frame   : frame_info :=
  {|
    frame_size := 0;
    frame_link:= {| seg_ofs := 0; seg_size := size_chunk Mptr |};
    frame_perm o := Readonly;
  |}.


Fixpoint range_Z (o: Z) (n: nat) : list Z :=
  match n with
    O => nil
  | Datatypes.S m => o :: range_Z (o+1) m
  end.

Definition range_eqb (o size: Z) (f: Z -> bool) : bool:=
  forallb f (range_Z o (Z.to_nat size)).


Lemma in_range_Z:
  forall n s o,
    In o (range_Z s n) ->
    s <= o < s + Z.of_nat n.
Proof.
  induction n; intros. easy.
  destruct H. subst. simpl. generalize (Pos2Z.is_pos (Pos.of_succ_nat n)). omega.
  apply IHn in H. split. omega. rewrite Nat2Z.inj_succ. omega.
Qed.

Lemma range_eqb_forall:
  forall lo s f,
    (forall o, lo <= o < lo + s -> f o = true) ->
    0 <= s ->
    range_eqb lo s f = true.
Proof.
  unfold range_eqb. intros lo s f H POS.
  rewrite forallb_forall. intros.
  apply in_range_Z in H0.
  apply H. rewrite Z2Nat.id in H0. omega.  auto.
Qed.

Lemma range_eqb_and:
  forall lo1 lo2 s1 s2 f,
    0 <= s1 -> 0 <= s2 ->
    (forall o, lo1 <= o < lo1 + s1 \/ lo2 <= o < lo2 + s2 -> f o = true) ->
    range_eqb lo1 s1 f = true /\
    range_eqb lo2 s2 f = true.
Proof.
  intros.
  rewrite ! range_eqb_forall; auto.
Qed.

Definition disjointb lo1 n1 lo2 n2 : bool :=
  range_eqb lo1 n1 (fun o1 => range_eqb lo2 n2 (fun o2 => negb (Z.eqb o1 o2))).

Lemma in_range_Z':
  forall n s o,
    s <= o < s + Z.of_nat n ->
    In o (range_Z s n).
Proof.
  induction n; intros. simpl in H. omega.
  simpl in *.
  destruct (zeq s o); auto.
  right. apply IHn. split. omega.
  rewrite Zpos_P_of_succ_nat in H. omega.
Qed.

Lemma range_eqb_forall':
  forall lo s f,
    0 <= s ->
    range_eqb lo s f = true ->
    (forall o, lo <= o < lo + s -> f o = true).
Proof.
  unfold range_eqb. intros lo s f POS RE.
  rewrite forallb_forall in RE. intros.
  apply RE.
  apply in_range_Z'.
  rewrite Z2Nat.id. omega.  auto.
Qed.

Lemma disjointb_disjoint:
  forall lo1 n1 lo2 n2,
    disjointb lo1 n1 lo2 n2 = true ->
    forall o,
      lo1 <= o < lo1 + n1 ->
      lo2 <= o < lo2 + n2 ->
      False.
Proof.
  intros lo1 n1 lo2 n2 DISJ o IN1 IN2.
  unfold disjointb in DISJ.
  eapply range_eqb_forall' in DISJ; eauto.
  2: omega.
  eapply range_eqb_forall' in DISJ; eauto.
  2: omega.
  apply negb_true_iff in DISJ.
  apply Z.eqb_neq in DISJ. congruence.
Qed.

Lemma disjoint_disjointb:
  forall lo1 n1 lo2 n2,
  (forall o,
      lo1 <= o < lo1 + n1 ->
      lo2 <= o < lo2 + n2 ->
      False) ->
  0 <= n1 ->
  0 <= n2 ->
  disjointb lo1 n1 lo2 n2 = true .
Proof.
  intros lo1 n1 lo2 n2 DISJ P1 P2.
  unfold disjointb.
  eapply range_eqb_forall; eauto.
  intros.
  eapply range_eqb_forall; eauto.
  intros.
  apply negb_true_iff.
  apply Z.eqb_neq. intro; subst. eapply DISJ; eauto.
Qed.



(** * Frame ADT  *)

(** The following definition [frame_adt] enumerates the kinds of frames that are
relevant in CompCert. The first kind [frame_with_info] denotes a single stack
block for each function, optionnally associated with a [frame_info]. The frame
information will be absent in languages up to Linear, and will be the actual
layout of the frame after that. The second kind [frame_without_info] denotes a
set of blocks that represents the set of local variables and parameters of the
current function. This is used in the higher-level languages from C to
Csharpminor. *)

Inductive frame_adt: Type :=
| frame_with_info: block -> option frame_info -> frame_adt
| frame_without_info: list block -> frame_adt.

(** We model our stack of frames as a [list (option frame_adt * Z)]. The obvious
definition would probably be [list frame_adt]. Let us explain why we differ.

First, we attach a [Z] to each element of our stack to account for stack
consumption. Each stack frame is associated with a number [n:Z] that represent
the number of bytes that this stack frame will use once it is compiled. It is
left as a parameter for the most part of the compiler, and we have a way to
instantiate this parameter right at the end when we compose the simulation
proofs of individual passes together. This number, together with properties that
we associate with it in the memory model, are instrumental to the proof of
correctness of merging stack blocks, in [RawAsmgen].

Second, we maintain a list of [option frame_adt] instead of simply [frame_adt].
This is again related to the way we handle the merging of stack blocks into a
unique consecutive stack block. Indeed, once we merge different stack blocks,
each with a different frame information representing distinct blocks, into a
unique stack block, we cannot construct a frame ADT in the target, i.e. in the
program with a unique stack block, that respects the frame injection that we
define below. In short, this would break the fact that each block is mentionned
at most once in all the frame informations of the whole stack, which is useful
in our way of axiomatizing the memory model.

Note: there would probably be a way to generalize the injection so that a block
can be mentionned multiple times in different frame information, but preliminary
investigations seem to indicate that this would require talking about injection
of [frame_info] and segments, and retrieving the information attached to one
block would require either to iterate over all the frame_adt that mention it or
merge them all in some sense. This is still to be investigated as it would make
the model cleaner, in my optionion. *)

(** The following function [get_assoc] is used to retrieve the frame information
attached to a given block [b]. It returns [None] when the block [b] is not part
of the stack of frames; or when [b] is part of the stack of frames but is either
in a list of blocks ([frame_without_info]) or in a [frame_with_info] with no
abstract information attached. In the other case, i.e. when [b] is in a
[frame_with_info] with some information [fi] attached, it returns [Some fi]. *)

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

Lemma in_frame_dec:
  forall f b, {in_frame f b} + {~ in_frame f b}.
Proof.
  destruct f; simpl; intros; auto.
  destruct f; simpl; intros.
  apply eq_block.
  apply in_dec. apply eq_block.
Defined.

Fixpoint in_frames (l: list (option frame_adt * Z)) (b: block) :=
  match l with
    nil => False
  | (f, _) :: r => in_frame f b \/ in_frames r b
  end.

Lemma in_frames_dec:
  forall l b, {in_frames l b} + {~ in_frames l b}.
Proof.
  induction l; simpl; intros; eauto.
  destruct a. 
  destruct (in_frame_dec o b); auto.
  destruct (IHl b); eauto. right; intros [A|A]; auto.
Defined.


Class InjectPerm :=
  {
    inject_perm_condition: permission -> Prop;
    inject_perm_condition_writable: forall p, perm_order Writable p -> inject_perm_condition p;
  }.

Section INJ.
  Context {injperm: InjectPerm}.

  (** * Injection of frames *)

  (** The following predicate [frame_inject' f P f1 f2] asserts that the frames
[f1] and [f2] are in injection according to [f], a memory injection, and [P], a
predicate that represents the permissions for the source memory [m1] in which
[f1] lives. We identify 4 cases for frame injection. *)

  Inductive frame_inject' {injperm: InjectPerm} (f: meminj) (P: block -> Z -> perm_kind -> permission -> Prop):
    frame_adt -> frame_adt -> Prop :=
  | frame_inject_with_info:
      (** Identity injection for single stack block. This requires that the blocks
        [b1] and [b2] are in injection with at most each other. In other words,
        if [b1] is injected, then that is into [b2] at offset [0], and
        conversely, if [b2] is the image of some block, then it is of the block
        [b1]. *)
      forall b1 b2 fi
        (FB: forall b' delta, f b1 = Some (b', delta) -> b' = b2 /\ delta = 0)
        (INJ: forall b' delta, f b' = Some (b2, delta) -> b' = b1),
        frame_inject' f P (frame_with_info b1 fi) (frame_with_info b2 fi)
  | frame_inject_without_info:
      (** Identity injection for sets of blocks. We require that the sets of
        blocks are related by injection. More precisely, if [b1] and [b2] are in
        injection by [f], then if [b1] is in [bl1], then [b2] is in [bl2] and
        vice-versa. *)
      forall bl1 bl2
        (INJlist: forall b b' delta, f b = Some (b', delta) -> (In b bl1 <-> In b' bl2)),
        frame_inject' f P (frame_without_info bl1) (frame_without_info bl2)
  | frame_inject_without_info_with_info:
      (** From a set of blocks to a unique stack block. For this case, we require
    a similar condition as in the previous case ([b ∈ bl ↔ b' = b2]). Moreover,
    we also need to assert that if the right-hand-side has frame information
    attached to it, then all the blocks of [bl] that inject into [b2] inject
    into the public part of the frame information, i.e. the stack data part. *)
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
                 frame_public fi (ofs + delta))
        (INJlist: forall b b' delta, f b = Some (b', delta) -> (In b bl <-> b' = b2)),
        frame_inject' f P (frame_without_info bl) (frame_with_info b2 ofi)
  | frame_with_info_add_info:
      (** Going from no information to some information. Similar to the previous case. *)
      forall b1 b2 fi
        (INDATA: forall delta,
            f b1 = Some (b2, delta) ->
            forall ofs k p,
              P b1 ofs k p ->
              inject_perm_condition p ->
              frame_public fi (ofs + delta))
        (INJ: forall b1' b2' delta, f b1' = Some (b2', delta) -> (b1' = b1 <-> b2' = b2)),
        frame_inject' f P (frame_with_info b1 None) (frame_with_info b2 (Some fi)).

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

  Definition public_stack_range (lo hi: Z) (fi: frame_info) : Prop :=
    forall ofs, lo <= ofs < hi -> frame_public fi ofs.

  Fixpoint size_stack {A} (l: list (A * Z)) : Z :=
    match l with
      nil => 0
    | (a,n)::r => size_stack r + align (Z.max 0 n) 8
    end.

  Lemma frame_inject_invariant:
    forall (P P': block -> Z -> perm_kind -> permission -> Prop) f f1 f2,
      (forall b ofs k p b' delta, f b = Some (b', delta) -> P' b ofs k p -> P b ofs k p) ->
      frame_inject' f P f1 f2 ->
      frame_inject' f P' f1 f2.
  Proof.
    intros m m' f f1 f2 PERM FI.
    destruct FI; try now (econstructor; eauto).
  Qed.

  Lemma list_forall2_frame_inject_invariant:
    forall (P P': block -> Z -> perm_kind -> permission -> Prop) f f1 f2,
      (forall b ofs k p b' delta, f b = Some (b', delta) -> P' b ofs k p -> P b ofs k p) ->
      list_forall2 (frame_inject' f P) f1 f2 ->
      list_forall2 (frame_inject' f P') f1 f2.
  Proof.
    intros m m' f f1 f2 PERM FI.
    eapply list_forall2_imply. eauto.
    intros.
    eapply frame_inject_invariant; eauto.
  Qed.

  Lemma inject_frame_id m a:
    frame_inject' inject_id m a a.
  Proof.
    destruct a; try (econstructor; inversion 1; tauto).
  Qed.

  Definition option_frame_inject f m1 (x y: option frame_adt * Z) :=
    match fst x, fst y with
      Some f1, Some f2 => frame_inject' f m1 f1 f2
    | None, Some f => False
    | _, _ => True
    end /\ snd x = snd y.

  Lemma list_inject_frame_id m l:
    list_forall2 (option_frame_inject inject_id m) l l.
  Proof.
    induction l; simpl; intros; constructor; auto.
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
        frame_inject' f m f1' f2' ->
        frame_inject' f' m f1' f2'.
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
      frame_inject' f m v1 v2 ->
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
    frame_inject' f m a a.
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
    list_forall2 (frame_inject' f m) a a.
  Proof.
    induction a; intros SELF; constructor; auto.
    apply self_inject_frame; eauto.
  Qed.

  Lemma frame_inject_compose:
    forall (f f' : meminj) P1 l1 l2,
      frame_inject' f P1 l1 l2 ->
      forall P2 l3,
        frame_inject' f' P2 l2 l3 ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            P1 b1 o k p ->
            inject_perm_condition p ->
            P2 b2 (o + delta) k p) ->
        frame_inject' (compose_meminj f f') P1 l1 l3.
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
      list_forall2 (frame_inject' f m1) l1 l2 ->
      forall m2 l3,
        list_forall2 (frame_inject' f' m2) l2 l3 ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            m1 b1 o k p ->
            inject_perm_condition p ->
            m2 b2 (o + delta) k p) ->
        list_forall2 (frame_inject' (compose_meminj f f') m1) l1 l3.
  Proof.
    induction 1; simpl; intros; eauto.
    inv H. constructor.
    inv H1.
    constructor; auto.
    eapply frame_inject_compose; eauto.
    eapply IHlist_forall2; eauto.
  Qed.
  
  Definition get_stack_top_blocks (l: list (option frame_adt * Z)) : list block :=
    match l with
      nil => nil
    | (Some (frame_with_info b fi),_)::r => b :: nil
    | (Some (frame_without_info bl),_)::r => bl
    | (None,_)::r => nil
    end.

  Definition is_stack_top l (b: block) :=
    In b (get_stack_top_blocks l).

  Definition get_frame_info l : block -> option frame_info :=
    get_assoc l.

  Definition public_stack_access l (b: block) (lo hi: Z) : Prop :=
    match get_frame_info l b with
      Some fi => public_stack_range lo hi fi
    | None => True
    end.

  Definition not_readonly_ofs l (b: block) (o: Z) : Prop :=
    match get_frame_info l b with
      Some fi => ~ frame_readonly fi o
    | None => True
    end.

  Definition range_not_readonly_ofs l (b: block) (lo hi: Z) : Prop :=
    forall o, lo <= o < hi -> not_readonly_ofs l b o.

  Lemma lo_ge_hi_public_stack_access:
    forall m b lo hi,
      lo >= hi ->
      public_stack_access m b lo hi.
  Proof.
    red. intros.
    destruct (get_frame_info m b); try tauto.
    red; intros. omega.
  Qed.

  Definition stack_access m (b: block) (lo hi: Z) : Prop :=
    (is_stack_top m b /\ range_not_readonly_ofs m b lo hi) \/
    (~ is_stack_top m b /\ public_stack_access m b lo hi).

  Lemma is_stack_top_dec : forall m b,
      {is_stack_top m b} + {~is_stack_top m b}.
  Proof.
    intros. unfold is_stack_top. apply in_dec. 
    apply eq_block.
  Qed.

  Lemma lo_ge_hi_stack_access:
    forall m b lo hi,
      lo >= hi ->
      stack_access m b lo hi.
  Proof.
    unfold stack_access.
    intros.
    destruct (is_stack_top_dec m b);[left|right].
    split; auto; red; intros. omega.
    split; auto. eapply lo_ge_hi_public_stack_access. auto.
  Qed.

  Lemma lo_ge_hi_not_retaddr:
    forall m b lo hi,
      lo >= hi ->
      range_not_readonly_ofs m b lo hi.
  Proof.
    unfold range_not_readonly_ofs.
    intros; omega. 
  Qed.

  Lemma not_in_frames_no_frame_info:
    forall m b,
      ~ in_frames m b ->
      get_frame_info m b = None.
  Proof.
    unfold get_frame_info.
    induction m; simpl; intros; eauto.
    intuition.
    destruct a, o; simpl in *. destruct f; simpl in *.
    rewrite pred_dec_false; eauto.
    rewrite pred_dec_false; eauto.
    apply not_in_frames_get_assoc; auto.
  Qed.

  Lemma is_stack_top_stack_blocks:
    forall m b,
      is_stack_top m b <-> (exists f n r, in_frame f b /\ m = (f,n)::r).
  Proof.
    unfold is_stack_top, get_stack_top_blocks.
    intros.
    destruct m eqn:?; intuition.
    decompose [ex and] H; intuition congruence.
    destruct p, o. repeat eexists. destruct f; simpl in *; intuition.
    easy.
    destruct p,o. decompose [ex and] H; intuition. inv H2.
    destruct f; simpl in *; intuition.
    decompose [ex and] H. inv H2. simpl in H1. easy.
  Qed.

  Lemma in_stack_data_inside:
    forall fi lo hi lo' hi',
      public_stack_range lo hi fi ->
      lo <= lo' ->
      hi' <= hi ->
      public_stack_range lo' hi' fi.
  Proof.
    intros fi lo hi lo' hi' NPSA LO HI.
    do 2 red in NPSA |- *.
    intros; apply NPSA. omega.
  Qed.

  Lemma public_stack_access_inside:
    forall m b lo hi lo' hi',
      public_stack_access m b lo hi ->
      lo <= lo' ->
      hi' <= hi ->
      public_stack_access m b lo' hi'.
  Proof.
    intros m b lo hi lo' hi' NPSA LO HI.
    unfold public_stack_access in *.
    destruct (get_frame_info m b); auto.
    eapply in_stack_data_inside in NPSA; eauto.
  Qed.

  Lemma stack_access_inside:
    forall m b lo hi lo' hi',
      stack_access m b lo hi ->
      lo <= lo' ->
      hi' <= hi ->
      stack_access m b lo' hi'.
  Proof.
    intros m b lo hi lo' hi' NPSA LO HI.
    unfold stack_access in *.
    destruct NPSA as [[IST RNROLO]|NPSA]; auto.
    left; split; auto.
    red; intros. apply RNROLO. omega.
    destruct NPSA. right. split; auto.
    eapply public_stack_access_inside; eauto.
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

  Lemma public_stack_range_dec : forall lo hi f,
      {public_stack_range lo hi f} + {~public_stack_range lo hi f}.
  Proof.
    unfold public_stack_range. intros. 
    edestruct (Intv.forall_rec (frame_public f) (fun ofs => ~ frame_public f ofs)) with (lo:=lo) (hi:=hi).
    - apply frame_public_dec. 
    - auto.
    - right. intro A.
      destruct e as (x & IN & NIN).
      apply NIN. apply A. auto.
  Qed.

  Lemma public_stack_access_dec : forall m b lo hi,
      {public_stack_access m b lo hi} + 
      {~public_stack_access m b lo hi}.
  Proof.
    unfold public_stack_access.
    intros.
    destruct (get_frame_info m b); auto.
    apply public_stack_range_dec.
  Qed.

  Lemma not_readonly_ofs_dec : forall m b o,
      {not_readonly_ofs m b o} + 
      {~not_readonly_ofs m b o}.
  Proof.
    unfold not_readonly_ofs.
    intros. destr.
    destruct (frame_readonly_dec f o); intuition.
  Qed.

  Lemma range_not_readonly_ofs_dec : forall m b lo hi,
      {range_not_readonly_ofs m b lo hi} + 
      {~range_not_readonly_ofs m b lo hi}.
  Proof.
    unfold range_not_readonly_ofs.
    intros.
    edestruct (Intv.forall_rec (fun ofs => lo <= ofs < hi -> not_readonly_ofs m b ofs)
                               (fun ofs => ~ (lo <= ofs < hi -> not_readonly_ofs m b ofs))
              ) with (lo0:=lo) (hi0:=hi).
    - simpl. intros.
      destruct (zle lo x).
      destruct (zlt x hi).
      destruct (not_readonly_ofs_dec m b x); intuition.
      left; intro; omega.
      left; intro; omega.
    - left; auto.
    - right; intro O.
      destruct e as (x & RNG & NO).
      apply NO. intros. eauto.
  Qed.

  Lemma stack_access_dec : forall m b lo hi,
      {stack_access m b lo hi} + 
      {~stack_access m b lo hi}.
  Proof.
    intros. unfold stack_access.
    destruct (is_stack_top_dec m b); auto.
    destruct (range_not_readonly_ofs_dec m b lo hi); auto.
    destruct (public_stack_access_dec m b lo hi); auto.
    right; intuition.
    right. intro A. destruct A. intuition. intuition.
    destruct (public_stack_access_dec m b lo hi); auto.
    right. intuition. 
  Qed.


  Lemma get_frame_info_in_frames:
    forall m b f, get_frame_info m b = Some f -> in_frames m b.
  Proof.
    intros.
    destruct (in_frames_dec m b); auto.
    rewrite not_in_frames_no_frame_info in H; auto. congruence.
  Qed.


End INJ.
