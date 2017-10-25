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

(* Inductive frame_adt: Type := *)
(* | frame_with_info: block -> option frame_info -> frame_adt *)
(* | frame_without_info: list block -> frame_adt. *)

Definition frame_adt : Type := list block * option frame_info * Z.

Definition frame_blocks (f: frame_adt) :=
  let '(bl,_,_) := f in bl.

Definition frame_adt_info (f: frame_adt) :=
  let '(_,fi,_) := f in fi.

Definition frame_adt_size (f: frame_adt) :=
  let '(_,_,x) := f in x.

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

Fixpoint get_assoc (l: list frame_adt) (a: block) : option frame_info :=
  match l with
    nil => None
  | (bl,fi,z)::r => if in_dec eq_block a bl then fi else get_assoc r a
  end.

Definition in_frame (f: frame_adt) (a: block) : Prop :=
  In a (frame_blocks f).

Lemma in_frame_dec:
  forall f b, {in_frame f b} + {~ in_frame f b}.
Proof.
  intros; apply in_dec, eq_block.
Defined.

Fixpoint in_frames (l: list frame_adt) (b: block) :=
  match l with
    nil => False
  | f :: r => in_frame f b \/ in_frames r b
  end.

Lemma in_frames_dec:
  forall l b, {in_frames l b} + {~ in_frames l b}.
Proof.
  induction l; simpl; intros; eauto.
  destruct (in_frame_dec a b); auto.
  destruct (IHl b); eauto. right; intros [A|A]; auto.
Defined.

Class InjectPerm :=
  {
    inject_perm_condition: permission -> Prop;
    inject_perm_condition_writable: forall p, perm_order Writable p -> inject_perm_condition p;
    ipc_dec: forall p, {inject_perm_condition p} + {~inject_perm_condition p};
  }.

Section INJ.
  Context {injperm: InjectPerm}.

  (** * Injection of frames *)

  (** The following predicate [frame_inject' f P f1 f2] asserts that the frames
[f1] and [f2] are in injection according to [f], a memory injection, and [P], a
predicate that represents the permissions for the source memory [m1] in which
[f1] lives. We identify 4 cases for frame injection. *)

  Record shift_segment delta s s' :=
    {
      shift_segment_start: seg_ofs s' = seg_ofs s + delta;
      shift_segment_size: seg_size s' = seg_size s;
    }.

  Lemma shift_segment_id:
    forall s,
      shift_segment 0 s s.
  Proof.
    constructor; auto. omega.
  Qed.

  Hint Resolve shift_segment_id.

  Record shift_frame delta fi fi' :=
    {
      shift_link: shift_segment delta (frame_link fi) (frame_link fi');
      shift_perm: forall o, 0 <= o < frame_size fi -> frame_perm fi o = frame_perm fi' (o + delta);
      shift_size:
        forall o, 0 <= o < frame_size fi -> 0 <= o + delta < frame_size fi';
    }.

  Lemma shift_frame_id:
    forall f,
      shift_frame 0 f f.
  Proof.
    constructor; auto. 
    intros; rewrite Z.add_0_r. auto.
    intros; omega.
  Qed.

  Hint Resolve shift_frame_id.

  Definition shift_option_frame delta fi fi' :=
    match fi, fi' with
      None, None => True
    | Some fi, Some fi' => shift_frame delta fi fi'
    | _,_ => False
    end.

  Lemma shift_option_frame_id:
    forall o,
      shift_option_frame 0 o o.
  Proof.
    unfold shift_option_frame.
    destruct o; auto.
  Qed.

  Hint Resolve shift_option_frame_id.

  Definition frame_inject_frame_def (f: meminj) (P: block -> Z -> perm_kind -> permission -> Prop) f1 f2 :=
    match (frame_adt_info f1, frame_adt_info f2) with
    | (None, None) => True
    | (Some fi, None) => False
    | (None, Some fi) =>
      Forall (fun b1 =>
                forall b2 delta,
                  f b1 = Some (b2, delta) ->
                  forall o (RNG: 0 <= o + delta < frame_size fi) k p,
                    P b1 o k p ->
                    inject_perm_condition p ->
                    frame_public fi (o + delta))
             (frame_blocks f1)
    | (Some fi, Some fi') =>
      Forall
        (fun b1 =>
           forall b2 delta, f b1 = Some (b2, delta) -> shift_frame delta fi fi')
        (frame_blocks f1)
    end.

  Record frame_inject' {injperm: InjectPerm} f (P: block -> Z -> perm_kind -> permission -> Prop) (f1 f2: frame_adt) :=
    {
      frame_inject_inj:
        Forall (fun b1 =>
                  forall b2 delta,
                    f b1 = Some (b2, delta) ->
                    In b2 (frame_blocks f2))
               (frame_blocks f1);
      frame_inject_frame:
        frame_inject_frame_def f P f1 f2;
    }.

  (* Inductive frame_inject' {injperm: InjectPerm} (f: meminj) (P: block -> Z -> perm_kind -> permission -> Prop): *)
  (*   frame_adt -> frame_adt -> Prop := *)
  (* | frame_inject_with_info: *)
  (*     (** Identity injection for single stack block. This requires that the blocks *)
  (*       [b1] and [b2] are in injection with at most each other. In other words, *)
  (*       if [b1] is injected, then that is into [b2] at offset [0], and *)
  (*       conversely, if [b2] is the image of some block, then it is of the block *)
  (*       [b1]. *) *)
  (*     forall b1 b2 fi fi' *)
  (*       (FB: forall b' delta, f b1 = Some (b', delta) -> b' = b2 /\ shift_option_frame delta fi fi'), *)
  (*       frame_inject' f P (frame_with_info b1 fi) (frame_with_info b2 fi') *)
  (* | frame_inject_without_info: *)
  (*     (** Identity injection for sets of blocks. We require that the sets of *)
  (*       blocks are related by injection. More precisely, if [b1] and [b2] are in *)
  (*       injection by [f], then if [b1] is in [bl1], then [b2] is in [bl2] and *)
  (*       vice-versa. *) *)
  (*     forall bl1 bl2 *)
  (*       (INJlist: forall b b' delta, f b = Some (b', delta) -> In b bl1 -> In b' bl2), *)
  (*       frame_inject' f P (frame_without_info bl1) (frame_without_info bl2) *)
  (* | frame_inject_without_info_with_info: *)
  (*     (** From a set of blocks to a unique stack block. For this case, we require *)
  (*   a similar condition as in the previous case ([b ∈ bl ↔ b' = b2]). Moreover, *)
  (*   we also need to assert that if the right-hand-side has frame information *)
  (*   attached to it, then all the blocks of [bl] that inject into [b2] inject *)
  (*   into the public part of the frame information, i.e. the stack data part. *) *)
  (*     forall bl b2 ofi *)
  (*       (INDATA: *)
  (*          forall fi, *)
  (*            ofi = Some fi -> *)
  (*            forall b1 delta, *)
  (*              In b1 bl -> *)
  (*              f b1 = Some (b2, delta) -> *)
  (*              forall ofs k p, *)
  (*                P b1 ofs k p -> *)
  (*                inject_perm_condition p -> *)
  (*                frame_public fi (ofs + delta)) *)
  (*       (INJlist: forall b b' delta, f b = Some (b', delta) -> In b bl -> b' = b2), *)
  (*       frame_inject' f P (frame_without_info bl) (frame_with_info b2 ofi) *)
  (* | frame_with_info_add_info: *)
  (*     (** Going from no information to some information. Similar to the previous case. *) *)
  (*     forall b1 b2 fi *)
  (*       (INDATA: forall delta, *)
  (*           f b1 = Some (b2, delta) -> *)
  (*           forall ofs k p, *)
  (*             P b1 ofs k p -> *)
  (*             inject_perm_condition p -> *)
  (*             frame_public fi (ofs + delta)) *)
  (*       (INJ: forall b2' delta, f b1 = Some (b2', delta) -> b2' = b2), *)
  (*       frame_inject' f P (frame_with_info b1 None) (frame_with_info b2 (Some fi)). *)

  Lemma not_in_frames_get_assoc:
    forall l b,
      ~ in_frames l b ->
      get_assoc l b = None.
  Proof.
    induction l; simpl; intros; eauto.
    repeat destr. eauto. 
  Qed.

  Definition public_stack_range (lo hi: Z) (fi: frame_info) : Prop :=
    forall ofs, lo <= ofs < hi -> frame_public fi ofs.

  Fixpoint size_stack (l: list frame_adt) : Z :=
    match l with
      nil => 0
    | (_,_,n)::r => size_stack r + align (Z.max 0 n) 8
    end.

  Lemma frame_inject_invariant:
    forall (P P': block -> Z -> perm_kind -> permission -> Prop) f f1 f2,
      (forall b ofs k p b' delta, f b = Some (b', delta) -> P' b ofs k p -> P b ofs k p) ->
      frame_inject' f P f1 f2 ->
      frame_inject' f P' f1 f2.
  Proof.
    intros m m' f f1 f2 PERM FI.
    destruct FI; try (econstructor; eauto).
    unfold frame_inject_frame_def in *.
    repeat destr; intros.
    eapply Forall_impl. 2: eauto. eauto.
  Qed.

  Lemma inject_frame_id m a:
    frame_inject' inject_id m a a.
  Proof.
    destruct a; try (econstructor; inversion 1; tauto).
    econstructor. apply Forall_forall. inversion 2; subst. auto.
    red.
    simpl. repeat destr. apply Forall_forall. subst.
    inversion 2; subst; eauto.
  Qed.

  Lemma frame_inject_incr:
    forall f f' m f1 f2,
      inject_incr f f' ->
      (forall b b' delta, f b = None -> f' b = Some (b', delta) ->
                     ~ in_frame f1 b (* /\ ~ in_frame f2 b' /\ *)
                     (* forall b1 delta', in_frame f1 b1 -> f b1 = Some (b', delta') -> False *))
      ->
      frame_inject' f m f1 f2 ->
      frame_inject' f' m f1 f2.
  Proof.
    intros.
    inv H1.
    red in frame_inject_frame0.
    Ltac injincrtac:=
      match goal with
        INCR: inject_incr ?f ?f',
              H: ?f' ?b = Some _,
                 NEW: forall _ _ _, ?f _ = None -> ?f' _ = Some _ -> _ |- _ =>
        let b' := fresh "b'" in
        let delta := fresh "delta" in
        let FB := fresh "FB" in
        destruct (f b) as [[b' delta]|] eqn:FB;
        [ generalize (INCR _ _ _ FB); rewrite H;
          let A := fresh in intro A; inv A
        | generalize (NEW _ _ _ FB H)
        ]
      end.
    constructor.
    - rewrite Forall_forall in *; subst; intros; injincrtac; autospe; eauto. 
    - red. destruct f1, f2. simpl in *. repeat destr.
      + rewrite Forall_forall in *. subst. intros. injincrtac; autospe. eauto.
      + rewrite Forall_forall in *. subst. intros. injincrtac; autospe. eauto.
  Qed.

  Lemma frame_inject_in_frame:
    forall f m v1 v2 b b' delta,
      frame_inject' f m v1 v2 ->
      in_frame v1 b ->
      f b = Some (b', delta) ->
      in_frame v2 b'.
  Proof.
    inversion 1. red in frame_inject_frame0.
    rewrite Forall_forall in frame_inject_inj0.
    intros IFF FBB; simpl in *.
    repeat destr_in frame_inject_frame0;
      unfold in_frame in *;
      try rewrite Forall_forall in *;
    subst; simpl in *; autospe;  eauto.
  Qed.

  Lemma self_inject_frame f m a:
    (forall b, f b = None \/ f b = Some (b,0)) ->
    frame_inject' f m a a.
  Proof.
    intros SELF.
    destruct a.
    constructor.
    - rewrite Forall_forall; intros. destruct (SELF x); try congruence.
    - red. simpl. repeat destr. subst.
      rewrite Forall_forall; intros.
      destruct (SELF x); try congruence. rewrite H0 in H1; inv H1. eauto.
  Qed.

  Lemma shift_segment_trans:
    forall s1 s2 s3 delta1 delta2,
      shift_segment delta1 s1 s2 ->
      shift_segment delta2 s2 s3 ->
      shift_segment (delta1 + delta2) s1 s3.
  Proof.
    intros s1 s2 s3 delta1 delta2 A B; inv A; inv B; constructor; omega.
  Qed.

  Hint Resolve shift_segment_trans.

  Lemma shift_frame_trans:
    forall f1 f2 f3 delta1 delta2,
      shift_frame delta1 f1 f2 ->
      shift_frame delta2 f2 f3 ->
      shift_frame (delta1 + delta2) f1 f3.
  Proof.
    intros f1 f2 f3 delta1 delta2 A B; inv A; inv B; constructor; eauto.
    intros.
    rewrite shift_perm0; auto.
    rewrite Z.add_assoc.
    apply shift_perm1. auto. intros.
    apply shift_size0 in H. apply shift_size1 in H. omega.
  Qed.

  Hint Resolve shift_frame_trans.

  Lemma shift_option_frame_trans:
    forall o1 o2 o3 delta1 delta2,
      shift_option_frame delta1 o1 o2 ->
      shift_option_frame delta2 o2 o3 ->
      shift_option_frame (delta1 + delta2) o1 o3.
  Proof.
    unfold shift_option_frame.
    intros o1 o2 o3 delta1 delta2 A B.
    destruct o1, o2, o3; eauto; easy.
  Qed.

  Hint Resolve shift_option_frame_trans.

  Lemma shift_option_frame_inv:
    forall z ofi fi,
      shift_option_frame z ofi (Some fi) ->
      exists f, ofi = Some f /\ shift_frame z f fi.
  Proof.
    intros. 
    destruct ofi; simpl in H; try easy.
    eauto. 
  Qed.

  Definition frame_agree_perms (P: block -> Z -> perm_kind -> permission -> Prop) (f: frame_adt) : Prop :=
    forall b o k p,
      P b o k p ->
      match frame_adt_info f with
        Some fi => 0 <= o < frame_size fi
      | None => True
      end.

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
        frame_agree_perms P2 l2 ->
        frame_inject' (compose_meminj f f') P1 l1 l3.
  Proof.
    intros f f' m1 l1 l2 H m2 l3 H0 PERM FAP.
    inv H; inv H0; unfold compose_meminj.
    constructor.
    - rewrite Forall_forall in *. intros b1 IN b2 delta F.
      repeat destr_in F.
      eapply frame_inject_inj1; eauto.
    - red in frame_inject_frame0, frame_inject_frame1 |- *.
      destr_in frame_inject_frame0.
      + destr_in frame_inject_frame0.
        destr_in frame_inject_frame1.
        rewrite Forall_forall in *.
        intros b1 IN b2 delta F.
        repeat destr_in F.
        eauto.
      + destr.
        rewrite Forall_forall in *.
        intros b1 IN b2 delta F o RNG k p PP IPC.
        repeat destr_in F.
        exploit frame_inject_inj0; eauto. intro.
        destr_in frame_inject_frame0.
        * rewrite Forall_forall in *.
          rewrite Z.add_assoc.
          exploit frame_inject_frame0; eauto.
          red in FAP. rewrite Heqo3 in FAP. eapply FAP.
          eapply PERM; eauto.
          exploit frame_inject_frame1; eauto. inversion 1.
          intros; red; erewrite <- shift_perm; eauto.
          exploit FAP. eauto. destruct l2. simpl in *.
          destr. 
        * rewrite Z.add_assoc.
          rewrite Forall_forall in *.
          exploit frame_inject_frame1; eauto.
          omega.
  Qed.

  Definition get_stack_top_blocks (l: list frame_adt) : list block :=
    match l with
      nil => nil
    | f::r => frame_blocks f
    end.

  Definition is_stack_top l (b: block) :=
    In b (get_stack_top_blocks l).

  Fixpoint stack_position (s: list frame_adt) b : option nat :=
    match s with
      nil => None
    | f::r => if in_frame_dec f b
             then Some O
             else option_map S (stack_position r b)
    end.

  Definition option_prop {A} (P: A -> Prop) (oa: option A): Prop :=
    match oa with
      Some a => P a
    | None => True
    end.

  Definition option_prop2 {A} (P: A -> A -> Prop) (oa ob: option A): Prop :=
    match oa, ob with
      Some a, Some b => P a b
    | Some a, None => False
    | _, _ => True
    end.

  Definition inb {A} (Aeq: forall (a b: A), {a=b} + {a<>b}) a l : bool :=
    match find (fun b => if Aeq a b then true else false) l with
      Some _ => true
    | None => false
    end.

  Lemma inb_In:
    forall {A} Aeq (l: list A) x,
      In x l <-> inb Aeq x l = true.
  Proof.
    induction l; simpl; intros; eauto.
    - unfold inb. simpl. split; easy.
    - rewrite IHl. unfold inb. simpl.
      destruct (Aeq x a); subst; auto.
      split; auto. intuition.
  Qed.

  Lemma inb_In_false:
    forall {A} Aeq (l: list A) x,
      ~ In x l <-> inb Aeq x l = false.
  Proof.
    intros; erewrite (inb_In Aeq). destruct (inb Aeq x l); intuition.
  Qed.

  Definition has_blocks_inject (f: meminj) f1 f2 :=
    existsb (fun b => match f b with
                   | Some (b', delta) => inb peq b' (frame_blocks f2) 
                   | None => false
                   end)
            (frame_blocks f1).

  Definition latest {A} (P: A -> Prop) (l: list A) (a: A) : Prop :=
    P a /\
    exists l1 l2,
      l = l1 ++ a :: l2 /\ Forall (fun a => ~ P a) l2.

  Record stack_inject (f: meminj) m (s1 s2: list frame_adt) :=
    {
      stack_inject_frames:
        forall f1, 
          In f1 s1 ->
          exists f2,
            In f2 s2 /\
            frame_inject' f m f1 f2;
      stack_inject_frames_rev:
        forall f2, 
          In f2 s2 ->
          exists f1,
            In f1 s1 /\
            frame_inject' f m f1 f2;
      stack_inject_rev:
        forall b1 b2 delta,
          f b1 = Some (b2, delta) ->
          in_frames s2 b2 ->
          in_frames s1 b1;
      stack_inject_sizes:
        forall f1 f2,
          In f2 s2 ->
          latest (fun f1 => frame_inject' f m f1 f2) s1 f1 ->
          frame_adt_size f2 <= frame_adt_size f1;
      stack_inject_order:
        forall b1 b2 delta,
          f b1 = Some (b2, delta) ->
          option_prop2 le (stack_position s2 b2) (stack_position s1 b1);
    }.

  Lemma stack_inject_frames' f m s1 s2:
    stack_inject f m s1 s2 ->
    forall f1 b1 b2 delta,
      in_frame f1 b1 ->
      f b1 = Some (b2, delta) ->
      In f1 s1 ->
      exists f2,
        In f2 s2 /\
        in_frame f2 b2 /\
        frame_inject' f m f1 f2.
  Proof.
    destruct 1; intros f1 b1 b2 delta IFR FB IFS.
    destruct (stack_inject_frames0 _ IFS) as (f2 & IFS2 & FI).
    exists f2; split; auto. split; auto.
    destruct FI. rewrite Forall_forall in frame_inject_inj0. eapply frame_inject_inj0; eauto. 
  Qed.

  Lemma is_stack_top_stack_position:
    forall s b, is_stack_top s b <-> stack_position s b = Some O.
  Proof.
    intros s b; split; intros H.
    - red in H. 
      destruct s; simpl in H. easy.
      simpl. destr.
      exfalso; apply n. auto. 
    - destruct s; simpl in *. congruence.
      destr_in H.
      red. simpl.
      clear Heqs0. 
      destruct f; simpl in *; subst; intuition.
      unfold option_map in H; destr_in H.
  Qed.

  Lemma in_frames_app:
    forall l1 l2 b,
      in_frames l1 b \/ in_frames l2 b ->
      in_frames (l1 ++ l2) b.
  Proof.
    induction l1; simpl; intros; eauto.
    intuition.
    apply or_assoc in H. destruct H; auto.
  Qed.

  Lemma stack_top_in_frames:
    forall s b,
      is_stack_top s b ->
      exists f,
        in_frame f b /\ In f s.
  Proof.
    unfold is_stack_top; destruct s; simpl; intros. easy.
    exists f; split; auto.
  Qed.

  Lemma stack_position_none:
    forall s b,
      stack_position s b = None ->
      ~ in_frames s b.
  Proof.
    induction s; simpl; intros; eauto.
    destr_in H.
    unfold option_map in H; destr_in H. eapply IHs in Heqo; eauto. intuition.
  Qed.

  Lemma in_frames_in_frame:
    forall s f b,
      In f s ->
      in_frame f b ->
      in_frames s b.
  Proof.
    induction s; simpl; intros; eauto.
    destruct H. subst. left. simpl. auto.
    eapply IHs in H; eauto.
  Qed.
 
  Lemma stack_inject_is_stack_top:
    forall f m s1 s2,
      stack_inject f m s1 s2 ->
      forall b1 b2 delta,
        f b1 = Some (b2, delta) ->
        is_stack_top s1 b1 ->
        is_stack_top s2 b2.
  Proof.
    intros f m s1 s2 SI b1 b2 delta FB IST.
    destruct (stack_top_in_frames _ _ IST) as (ff & INF & INS).
    edestruct stack_inject_frames' as (f2 & INS2 & INF2 & FI); eauto.
    rewrite is_stack_top_stack_position in *.
    destruct SI.
    apply stack_inject_order0 in FB. unfold option_prop2 in FB.
    rewrite IST in FB.
    destr_in FB. f_equal. omega.
    apply stack_position_none in Heqo.
    exfalso; apply Heqo.
    eapply in_frames_in_frame; eauto.
  Qed.

  Lemma option_prop_le_trans:
    forall l1 l2 l3 b1 b2 b3,
      option_prop2 le (stack_position l2 b2) (stack_position l1 b1) ->
      option_prop2 le (stack_position l3 b3) (stack_position l2 b2) ->
      option_prop2 le (stack_position l3 b3) (stack_position l1 b1).
  Proof.
    unfold option_prop2; simpl; intros.
    destr. destr_in H0. destr_in H. omega.
  Qed.

  Definition inject_in_dec l (o: option (block * Z)): {match o with
                                                       | Some (b2,_) => In b2 l
                                                       | None => True
                                                       end} + { ~ match o with
                                                       | Some (b2,_) => In b2 l
                                                       | None => True
                                                                  end}.
  Proof.
    intros. destruct o; auto. destruct p. apply in_dec.
    apply peq.
  Defined.

  Definition shift_segment_dec delta f1 f2 : { shift_segment delta f1 f2 } + {~ shift_segment delta f1 f2 }.
  Proof.
    destruct (zeq (seg_ofs f2) (seg_ofs f1 + delta)).
    destruct (zeq (seg_size f2) (seg_size f1)).
    left; constructor; auto.
    right; inversion 1; omega.
    right; inversion 1; omega.
  Defined.


  Section FORALL.

    Variables P: Z -> Prop.
    Variable f: forall (x: Z), {P x} + {~ P x}.
    Variable lo: Z.
    Require Import Zwf.

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

  Definition in_range_dec lo hi o : { lo <= o < hi } + {~ (lo <= o < hi) }.
  Proof.
    destruct (zle lo o), (zlt o hi); try (right; omega). left; omega.
  Qed.

  Definition shift_frame_dec delta f1 f2 : { shift_frame delta f1 f2 } + {~ shift_frame delta f1 f2 }.
  Proof.
    destruct (shift_segment_dec delta (frame_link f1) (frame_link f2)).
    destruct (forall_rec _ (fun o => stack_perm_eq (frame_perm f1 o) (frame_perm f2 (o + delta))) 0 (frame_size f1))
      as [FORALL|NFORALL].
        destruct (forall_rec _ (fun o => in_range_dec 0 (frame_size f2) (o + delta)) 0 (frame_size f1))
      as [FORALL2|NFORALL2].
    left; constructor; auto.
    right; inversion 1; tauto.
    right; inversion 1; tauto.
    right; inversion 1; tauto.
  Defined.

  Definition perm_kind_pred_dec:
    forall (P: perm_kind -> Prop)
      (Pdec: forall k, {P k} + {~ P k}),
      {forall k, P k} + {~forall k, P k}.
  Proof.
    intros. destruct (Pdec Cur), (Pdec Max); try (right; intro A; eauto; fail).
    left; destruct k; auto.
  Defined.

  Definition permission_pred_dec:
    forall (P: permission -> Prop)
      (Pdec: forall p, {P p} + {~ P p}),
      {forall p, P p} + {~forall p, P p}.
  Proof.
    intros. destruct (Pdec Freeable), (Pdec Writable), (Pdec Readable), (Pdec Nonempty); try (right; intro A; eauto; fail).
    left; destruct p3; auto.
  Defined.

  Definition impl_dec:
    forall P Q,
    P ->
    {Q} + {~Q} ->
    {P -> Q} + {~(P -> Q)}.
  Proof.
    intros.
    destruct H;[left| right]; intuition.
  Qed.

  Definition frame_inject_frame_def_dec f (P: block -> Z -> perm_kind -> permission -> Prop)
             (Pdec: forall b o k p, {P b o k p} + {~ P b o k p})
             f1 f2:
    { frame_inject_frame_def f P f1 f2 } + { ~ frame_inject_frame_def f P f1 f2 }.
  Proof.
    unfold frame_inject_frame_def.
    repeat destr.
    - apply Forall_dec. intros b1.
      destruct (f b1). destruct p.
      + destruct (shift_frame_dec z f0 f3); eauto.
        left; inversion 1; subst; eauto.
      + left; congruence.
    - apply Forall_dec. simpl. intros b1.
      destruct (f b1). destruct p.
      +
        cut (  {(forall (o : Z) (RNG: 0 <= o + z < frame_size f0) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))} +
               {~(forall (o : Z) (RNG: 0 <= o + z < frame_size f0) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))}).
        intros [A|A];[left|right]. inversion 1; subst; eauto.
        intro B; apply A. eapply B. eauto.
        cut (  {(forall (o : Z) (RNG: 0 - z <= o < frame_size f0 - z) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))} +
               {~(forall (o : Z) (RNG: 0 - z <= o < frame_size f0 - z) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))}).
        intros [A|A];[left|right]. intros; eapply A; eauto. omega.
        intro B; apply A. intros; eapply B; eauto. omega.
        apply forall_rec. intro o.
        apply perm_kind_pred_dec. intro k.
        apply permission_pred_dec. intro p.
        destruct (Pdec b1 o k p).
        2: left; intuition.
        apply impl_dec. auto.
        destruct (ipc_dec p).
        2: left; intuition.
        apply impl_dec; auto.
        apply frame_public_dec.
      + left; congruence.
  Qed.

  Definition frame_inject_dec f m f1 f2
             (mdec: forall b o k p, {m b o k p} + {~ m b o k p})
    : {frame_inject' f m f1 f2} + {~frame_inject' f m f1 f2}.
  Proof.
    destruct (Forall_dec _ (inject_in_dec (frame_blocks f2)) (map f (frame_blocks f1))).
    - destruct (frame_inject_frame_def_dec f m mdec f1 f2).
      + left; constructor; auto.
        rewrite Forall_forall in *.
        intros b1 IN.
        intros.
        exploit f0. rewrite in_map_iff. exists b1; split; simpl; auto. rewrite H. auto.
      + right; inversion 1; tauto.
    - right; inversion 1.
      apply n.
      apply Forall_forall; intros b IN.
      rewrite in_map_iff in IN; destruct IN as (bb & EQ & IN).
      destr. destruct p. subst.
      rewrite Forall_forall in frame_inject_inj0.
      eauto.
  Defined.


  Lemma latest_has_prop:
    forall {A} (P: A -> Prop) s f,
      latest P s f ->
      P f.
  Proof.
    destruct 1; auto.
  Qed.

  Lemma exists_latest:
    forall {A} (P: A -> Prop) (Pdec: forall a, {P a} + {~ P a}) s,
      Exists P s ->
      exists f,
        latest P s f.
  Proof.
    induction s.
    inversion 1. intros EX.
    destruct (Exists_dec _ s Pdec).
    - destruct (IHs) as (f & LAT); auto.
      destruct LAT as (PF & l1 & l2 & SPLIT & FN).
      exists f. split; auto.
      exists  (a::l1), l2; split; auto. subst; reflexivity.
    - inv EX; intuition. exists a; split; auto.
      exists nil, s; split; auto.
      rewrite Forall_Exists_neg. auto. 
  Qed.

  Lemma in_frame_inject_exists_latest:
    forall f m
      (mdec: forall b o k p, {m b o k p} + {~ m b o k p})
      s f1 f2,
      In f1 s ->
      frame_inject' f m f1 f2 ->
      exists f1,
        latest (fun f1 => frame_inject' f m f1 f2) s f1.
  Proof.
    intros.
    edestruct (exists_latest _ (fun f1 => frame_inject_dec f m f1 f2 mdec)) as (fl & LAT).
    apply Exists_exists. eexists; split; eauto.
    eauto.
  Qed.

  Lemma latest_in:
    forall {A} (P: A -> Prop) l x,
      latest P l x ->
      In x l.
  Proof.
    intros A P l x (Px & l1 & l2 & SPLIT & NF); subst; rewrite in_app; simpl; auto.
  Qed.

  Lemma stack_inject_compose:
    forall (f f' : meminj) m1 l1 l2,
      stack_inject f m1 l1 l2 ->
      forall m2 l3,
        stack_inject f' m2 l2 l3 ->
        (forall b o k p, {m1 b o k p} + {~ m1 b o k p}) ->
        (forall b o k p, {m2 b o k p} + {~ m2 b o k p}) ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            m1 b1 o k p ->
            inject_perm_condition p ->
            m2 b2 (o + delta) k p) ->
        Forall (frame_agree_perms m2) l2 ->
        stack_inject (compose_meminj f f') m1 l1 l3.
  Proof.
    intros f f' m1 l1 l2 SI1 m2 l3 SI2 mdec1 mdec2 PERM FAP.
    destruct SI1, SI2.
    split.
    - intros f1 INF.
      exploit stack_inject_frames0; eauto. intros (f2 & INS2 & FI).
      exploit stack_inject_frames1; eauto. intros (f3 & INS3 & FI2).
      exists f3; split; eauto. 
      eapply frame_inject_compose; eauto.
      rewrite Forall_forall in FAP. apply FAP in INS2. simpl in INS2. auto.
    - intros f3 INF.
      exploit stack_inject_frames_rev1; eauto. intros (f2 & INS2 & FI2).
      exploit stack_inject_frames_rev0; eauto. intros (f1 & INS1 & FI1).
      exists f1; split; eauto. 
      eapply frame_inject_compose; eauto.
      rewrite Forall_forall in FAP. apply FAP in INS2. simpl in INS2. auto.
    - unfold compose_meminj. intros b1 b2 delta COMPINJ INF.
      repeat destr_in COMPINJ. eauto.
    - intros f1 f3 IN LATEST.
      
      cut (exists f2, latest (fun f2 => frame_inject' f' m2 f2 f3) l2 f2 /\ latest (fun f1 => frame_inject' f m1 f1 f2) l1 f1).
      {
        intros (f2 & L1 & L2).
        etransitivity.
        eapply stack_inject_sizes1; eauto.
        eapply stack_inject_sizes0; eauto. eapply latest_in; eauto.
      }
      {
        (* destruct LATEST as (Pf1 & l11 & l12 & SPLIT & FN). *)
        destruct (stack_inject_frames_rev1 f3 IN) as (f2 & INF2 & FI23).
        destruct (fun pf => in_frame_inject_exists_latest _ _ mdec2 l2 _ _ pf FI23) as (f2l & F2L). auto.
        clear f2 INF2 FI23.
        exists f2l; split; auto.
        (* destruct F2L as (FI23 & l21 & l22 & SPLIT2 & NF).  *)
        rename f2l into f2.
        assert (IN2: In f2 l2) by (eapply latest_in; eauto).
        destruct (stack_inject_frames_rev0 f2 IN2) as (f1' & INF1 & FI12).
        destruct (in_frame_inject_exists_latest _ _ mdec1 l1 _ _ INF1 FI12) as (f1l & F1L).
        clear f1' INF1 FI12.


        Definition suffix {A} (l l2: list A) := exists l1, l = l1 ++ l2.


        Lemma suffix_same_size:
          forall {A} (s1 s2 l: list A),
            suffix l s1 ->
            suffix l s2 ->
            length s1 = length s2 ->
            s1 = s2.
        Proof.
          intros.
          unfold suffix in *.
          destruct H, H0. subst.
          generalize H0; intro Ha.
          apply f_equal with (f:=length (A:=A)) in Ha.
          rewrite ! app_length in Ha.
          revert x x0 s1 s2 H0 H1 Ha.
          induction x; simpl; intros; eauto.
          assert (length x0 = O) by omega.
          rewrite length_zero_iff_nil in H. subst. reflexivity.
          destruct x0. simpl in *. omega.
          simpl in H0. inv H0. apply IHx in H3; auto.
        Qed.

        Lemma suffix_tl:
          forall {A} s l (a:A),
            suffix l s ->
            suffix (a::l) s.
        Proof.
          unfold suffix.
          intros. destruct H; subst.
          exists (a::x). reflexivity.
        Qed.

        Lemma smaller_suffix:
          forall {A} s l (a:A),
            suffix l (a::s) ->
            suffix l s.
        Proof.
          unfold suffix.
          intros. destruct H; subst.
          exists (x++a::nil). rewrite app_ass; reflexivity.
        Qed.

        Lemma suffix_prop:
          forall {A} (s2 s1 l: list A),
            suffix l s1 ->
            suffix l s2 ->
            (length s1 < length s2)%nat ->
            suffix s2 s1.
        Proof.
          induction s2; simpl; intros; eauto.
          - omega. 
          - destruct (lt_dec (length s1) (length s2)).
            apply suffix_tl.
            eapply IHs2. eauto. eapply smaller_suffix; eauto. auto.
            assert (length s1 = length s2) by omega.
            exists (a::nil). simpl. f_equal.
            eapply suffix_same_size; eauto.
            eapply smaller_suffix; eauto.
        Qed.
        

        Lemma latest_inj:
          forall {A} (P: A -> Prop) l x1 x2,
            latest P l x1 ->
            latest P l x2 ->
            x1 = x2.
        Proof.
          intros A P l x1 x2 L1 L2.
          destruct L1 as (P1 & l11 & l12 & SPLIT1 & NF1).
          destruct L2 as (P2 & l21 & l22 & SPLIT2 & NF2).
          subst.
          assert (In x1 (l11 ++ x1 :: l12)) by (rewrite in_app; simpl; auto).
          rewrite SPLIT2 in H.
          rewrite in_app in H; simpl in H.
          destruct H.
          - destruct (lt_dec (length l12) (length l22)).
            assert (S1: suffix (l11 ++ x1 :: l12) (x1 :: l12)).
            exists l11; reflexivity.
            assert (S2: suffix (l21 ++ x2 :: l22) (x2 :: l22)).
            exists l21; reflexivity.
            rewrite SPLIT2 in S1.
            generalize (suffix_prop _ _ _ S1 S2). intro B. trim B.
            simpl; omega.
            destruct B.
            destruct x. simpl in H0; inv H0. auto. simpl in H0.
            assert (In x1 l22). inv H0. rewrite in_app; simpl; auto.
            rewrite Forall_forall in NF2; apply NF2 in H1. congruence.
            destruct (lt_dec (length l22) (length l12)).
            assert (S1: suffix (l11 ++ x1 :: l12) (x1 :: l12)).
            exists l11; reflexivity.
            assert (S2: suffix (l21 ++ x2 :: l22) (x2 :: l22)).
            exists l21; reflexivity.
            rewrite <- SPLIT2 in S2.
            generalize (suffix_prop _ _ _ S2 S1). intro B. trim B.
            simpl; omega.
            destruct B.
            destruct x. simpl in H0; inv H0. auto. simpl in H0.
            assert (In x2 l12). inv H0. rewrite in_app; simpl; auto.
            rewrite Forall_forall in NF1; apply NF1 in H1. congruence.
            assert (length l22 = length l12) by omega.
            assert (x1::l12 = x2::l22).
            eapply suffix_same_size.
            instantiate (1 := l11++x1::l12). exists (l11). reflexivity.
            rewrite SPLIT2. exists l21. reflexivity. simpl; congruence. inv H1; auto.
          - destruct H; auto.
            rewrite Forall_forall in NF2. apply NF2 in H. congruence.
        Qed.

        cut (f1 = f1l).
        {
          intro; subst; auto.
        }
        eapply latest_inj. apply LATEST.
        split.
        - destruct F1L, F2L.
          eapply frame_inject_compose; eauto.
          rewrite Forall_forall in FAP; eauto.
        - destruct F1L as (Pf1 & l11 & l12 & SPLIT & FN).
          exists l11, l12; split; auto.
          rewrite Forall_forall in FN |- *.
          intros x IN12 FI.
          
        }

        exploit @latest_has_prop. apply LATEST. simpl.
        intros (FI13_1 & FI13_2).


        destruct F1L as (FI12 & l11' & l12' & SPLIT' & NF').
        assert (In f1l l1).
        {
          rewrite SPLIT', in_app; simpl; auto.
        }
        rewrite SPLIT in H. rewrite in_app in H.
        destruct H.


        destruct (stack_inject_frames0 f1) as (f2 & INF2 & FI12). subst; rewrite in_app; simpl; auto.
        destruct (stack_inject_frames1 f2) as (f3' & INF3 & FI23). auto.


        destruct (fun pf => in_frame_inject_exists_latest _ _ mdec1 l1 _ _ pf FI12) as (f1l & F1L).
        subst; rewrite in_app; simpl; auto.


        exists f2l; split; auto.
        subst; rewrite in_app; simpl; auto.
        

      }

      etransitivity.
      eapply stack_inject_sizes1. auto.
      2: eapply stack_inject_sizes0.
    - unfold compose_meminj.
      intros b1 b2 delta F.
      repeat destr_in F.
      eapply option_prop_le_trans; eauto.
  Qed.
  
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
    destruct a; simpl in *. 
    destruct p.
    rewrite pred_dec_false; eauto.
  Qed.

  Lemma is_stack_top_stack_blocks:
    forall m b,
      is_stack_top m b <-> (exists f r, in_frame f b /\ m = f::r).
  Proof.
    unfold is_stack_top, get_stack_top_blocks.
    intros.
    destruct m eqn:?; intuition.
    - decompose [ex and] H; intuition congruence.
    - repeat eexists. eauto.
    - subst.    
      decompose [ex and] H; intuition. inv H2.
      eauto. 
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
