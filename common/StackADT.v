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
    frame_link: list segment;
    frame_perm: Z -> stack_permission;
    frame_link_size:
      Forall (fun fl => seg_size fl = size_chunk Mptr) frame_link;
    frame_link_rng:
      Forall (fun fl => forall o, seg_ofs fl <= o < seg_ofs fl + seg_size fl -> 0 <= o < frame_size) frame_link;
    frame_link_readonly:
      Forall (fun fl => forall i, in_segment i fl -> frame_perm i = Readonly) frame_link;
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
    frame_link:= nil;
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

Definition stack_adt := list frame_adt.

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

  Definition stack_perm_le (sp1 sp2: stack_permission) :=
    match sp1, sp2 with
      Readonly, _ => True
    | Private, Readonly => False
    | Private, _ => True
    | Public, Public => True
    | Public, _ => False
    end.

  Lemma stack_perm_le_public:
    forall fi p o,
      (forall x, frame_perm fi x = Public) ->
      stack_perm_le p (frame_perm fi o).
  Proof.
    intros fi p o PUB; rewrite PUB.
    destruct p; red; auto.
  Qed.

  Lemma stack_perm_le_refl:
    forall p,
      stack_perm_le p p.
  Proof.
    destruct p; red; auto.
  Qed.

  Lemma stack_perm_le_trans:
    forall p1 p2 p3,
      stack_perm_le p1 p2 ->
      stack_perm_le p2 p3 ->
      stack_perm_le p1 p3.
  Proof.
    destruct p1,p2,p3; unfold stack_perm_le; intros; congruence.
  Qed.

  Record shift_frame delta fi fi' :=
    {
      (* shift_link: list_forall2 (fun fl1 fl2 => shift_segment delta fl1 fl2) (frame_link fi) (frame_link fi'); *)
      shift_perm: forall o, 0 <= o < frame_size fi -> stack_perm_le (frame_perm fi o) (frame_perm fi' (o + delta));
      shift_size:
        forall o, 0 <= o < frame_size fi -> 0 <= o + delta < frame_size fi';
    }.

  Lemma shift_frame_id:
    forall f,
      shift_frame 0 f f.
  Proof.
    constructor; auto.
    intros; rewrite Z.add_0_r. eapply stack_perm_le_refl; auto.
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
    Forall
      (fun b1 =>
         forall b2 delta,
           f b1 = Some (b2, delta) ->
           match (frame_adt_info f1, frame_adt_info f2) with
           | (None, None) => True
           | (Some fi, None) => False
           | (None, Some fi) =>
             forall o  k p,
               P b1 o k p ->
               inject_perm_condition p ->
               0 <= o + delta < frame_size fi /\ frame_public fi (o + delta)
           | (Some fi, Some fi') =>
             shift_frame delta fi fi'
           end)
      (frame_blocks f1).

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


  Lemma inject_frame_id m a:
    frame_inject' inject_id m a a.
  Proof.
    destruct a, p; try (econstructor; inversion 1; tauto).
    econstructor.
    - apply Forall_forall. inversion 2; subst. auto.
    - apply Forall_forall. inversion 2; subst.
      simpl. destr. eauto.
  Qed.

  Lemma frame_inject_incr:
    forall f f' m f1 f2,
      inject_incr f f' ->
      (forall b b' delta,
          f b = None ->
          f' b = Some (b', delta) ->
          ~ in_frame f1 b) ->
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
    - red. destruct f1, f2. destruct p, p0. simpl in *. 
      rewrite Forall_forall in *. intros. injincrtac; autospe. eauto. eauto. eauto.
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
    destruct a, p.
    constructor.
    - rewrite Forall_forall; intros. destruct (SELF x); try congruence.
    - red. 
      rewrite Forall_forall; intros. simpl.
      destruct (SELF x); try congruence. rewrite H0 in H1; inv H1.
      destr; eauto.
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
    (* - destruct f1,f2,f3. simpl in *. *)
    (*   clear - shift_link0 shift_link1. *)
    (*   revert frame_link0 frame_link1 delta1 shift_link0 frame_link2 delta2 shift_link1. *)
    (*   induction 1; inversion 1; constructor; eauto. *)
    - intros.
      eapply stack_perm_le_trans; eauto.
      rewrite Z.add_assoc. eauto.
    - intros.
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
      In b (frame_blocks f) -> 
      P b o k p ->
      match frame_adt_info f with
        Some fi => 0 <= o < frame_size fi
      | None => True
      end.

  Lemma frame_inject_frame_def_alt:
    forall f P f1 f2,
      frame_agree_perms P f1 ->
      frame_inject_frame_def f P f1 f2 ->
       Forall
         (fun b1 =>
            forall b2 delta,
              f b1 = Some (b2, delta) ->
              forall o k p fi,
                frame_adt_info f2 = Some fi ->
                P b1 o k p -> inject_perm_condition p ->
                0 <= o + delta < frame_size fi /\
                stack_perm_le (match frame_adt_info f1 with
                               | None => Public
                               | Some fi1 => frame_perm fi1 o
                               end) (frame_perm fi (o+delta))
         )
         (frame_blocks f1).
  Proof.
    intros f P f1 f2 FAP FIFD.
    red in FAP. red in FIFD. rewrite Forall_forall in *.
    intros b IN b2 delta FB o k p fi FIFO PERM IPC.
    specialize (FIFD _ IN _ _ FB).
    specialize (FAP _ _ _ _ IN PERM).
    destr_in FIFD.
    - destr_in FIFD. inv FIFO.
      inv FIFD. split; eauto.
    - destr_in FIFD; eauto. inv FIFO.
      exploit FIFD; eauto. intros (A & B); split; auto.
      rewrite B. auto.
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
      rewrite Forall_forall in *.
      intros b1 IN b2 delta F.
      repeat destr_in F.
      destr_in frame_inject_frame0.
      + destr_in frame_inject_frame0; eauto.
        destr_in frame_inject_frame1; eauto.
        destr_in frame_inject_frame1; eauto.

        exfalso; eauto.
      + destr.
        exploit frame_inject_inj0; eauto. intro.
        destr_in frame_inject_frame0.
        * intros. rewrite Z.add_assoc.
          exploit frame_inject_frame0; eauto. intros (A & B).
          exploit frame_inject_frame1; eauto. 
          inversion 1.
          unfold frame_public.
          split; auto.
          generalize (shift_perm0 _ A).
          rewrite B. destruct (frame_perm f0 (o + z + z0)); intuition.
        * intros; rewrite Z.add_assoc.
          exploit frame_inject_frame1; eauto.
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

  (* Definition latest {A B} (P: A -> B -> Prop) (l1: list A) (l2: list B) (a: A) (b: B) : Prop := *)
  (*   P a b /\ *)
  (*   forall ia ib, *)
  (*     nth_error l1 ia = Some a -> *)
  (*     nth_error l2 ib = Some b -> *)
  (*     forall ia' a', *)
  (*       (ia < ia')%nat -> *)
  (*       nth_error l1 ia' = Some a' -> *)
  (*       forall ib' b', *)
  (*         nth_error l2 ib' = Some b' -> *)
  (*         P a' b' -> *)
  (*         (ib < ib')%nat. *)

  Lemma compose_decompose:
    forall f f' b1 b3 delta,
      (compose_meminj f f') b1 = Some (b3, delta) ->
      exists b2 z1 z2,
        f b1 = Some (b2,z1) /\ f' b2 = Some (b3,z2) /\ delta = z1 + z2.
  Proof.
    unfold compose_meminj.
    intros f f' b1 b3 delta INJ.
    repeat destr_in INJ.
    do 3 eexists; eauto.
  Qed.


  Definition latest' {A} (P: A -> Prop) (l: list A) (a: A) : Prop :=
    P a /\
    exists l1 l2,
      l = l1 ++ a :: l2 /\ Forall (fun a => ~ P a) l2.


  (* The injection of stacks is parameterized by a frame injection function,
  called [g] below. This function associates frame positions in the source and
  target stacks. I.e. [g n1 = Some n2] means that the frame at position [n1] in
  the source memory injects into the frame at position [n2] in the target
  memory.

  The frame positions evolve throughout execution. Frame position 0 refers to
  the top of the stack.

   *)

  Inductive frame_at_pos (s: stack_adt) n f :=
  |frame_at_pos_intro:
     nth_error s n = Some f -> frame_at_pos s n f.

  Definition frameinj := nat -> option nat.

  Definition flat_frameinj thr := (fun n => if lt_dec n thr then Some n else None).

  Open Scope nat_scope.

  Definition frameinj_preserves_order (g: frameinj) :=
    forall i1 i2,
      i1 <= i2 ->
      forall i1' i2',
        g i1 = Some i1' ->
        g i2 = Some i2' ->
        i1' <= i2'.

  Definition frameinj_preserves_order' (g: frameinj) (s s': nat) :=
    forall i1 i2,
      s - i1 <= s - i2 ->
      forall i1' i2',
        g i1 = Some i1' ->
        g i2 = Some i2' ->
        s' - i1' <= s' - i2'.

  Lemma fpo_eq:
    forall g s s',
      (forall i1 i2, g i1 = Some i2 -> i1 < s /\ i2 < s') ->
      frameinj_preserves_order g <-> frameinj_preserves_order' g s s'.
  Proof.
    unfold frameinj_preserves_order, frameinj_preserves_order'.
    split; intros.
    - generalize (H _ _ H2), (H _ _ H3). intuition.
      assert (i2 <= i1) by omega.
      generalize (H0 _ _ H5 _ _ H3 H2). omega.
    - exploit (H0 i2 i1); eauto. omega. 
      generalize (H _ _ H2), (H _ _ H3). omega.
  Qed.

  Definition frameinj_surjective (g: frameinj) n2 :=
    forall j, j < n2 -> exists i, g i = Some j.
  
  Record stack_inject (f: meminj) (g: frameinj) m (s1 s2: list frame_adt) :=
    {
      stack_inject_preserves_order: frameinj_preserves_order g;
      stack_inject_frames:
        forall i1 f1 i2,
          frame_at_pos s1 i1 f1 ->
          g i1 = Some i2 ->
          exists f2,
            frame_at_pos s2 i2 f2 /\ 
            frame_inject' f m f1 f2;
      stack_inject_not_in_frames:
        forall b1 b2 delta f2 fi,
          f b1 = Some (b2, delta) ->
          ~ in_frames s1 b1 ->
          In f2 s2 ->
          in_frame f2 b2 ->
          frame_adt_info f2 = Some fi ->
          forall o k p,
            m b1 o k p ->
            inject_perm_condition p ->
            frame_public fi (o + delta);
      stack_inject_range:
        forall i j, g i = Some j -> i < length s1 /\ j < length s2;
      stack_inject_exists_l:
        forall i, i < length s1 -> exists j, g i = Some j;
      stack_inject_pack:
        forall i j, g i = Some j -> j <= i;
      stack_inject_sizes:
        forall i1 i2 f1 f2,
          frame_at_pos s1 i1 f1 ->
          frame_at_pos s2 i2 f2 ->
          g i1 = Some i2 ->
          (forall i, g i = Some i2 -> i <= i1) ->
          (frame_adt_size f2 <= frame_adt_size f1)%Z;
    }.

  Lemma frame_at_pos_lt:
    forall s n f,
      frame_at_pos s n f ->
      n < length s.
  Proof.
    intros s n f FAP; inv FAP.
    apply nth_error_Some. congruence.
  Qed.

  Lemma stack_inject_compat:
    forall f g P s1 s2,
      stack_inject f g P s1 s2 ->
    forall b1 b2 delta,
      f b1 = Some (b2, delta) ->
      forall i1 f1,
        frame_at_pos s1 i1 f1 ->
        in_frame f1 b1 ->
        exists i2 f2,
          frame_at_pos s2 i2 f2 /\
          in_frame f2 b2 /\
          g i1 = Some i2.
  Proof.
    intros f g P s1 s2 SI b1 b2 delta FB i1 f1 FAP IN.
    exploit frame_at_pos_lt. eauto. intro LT.
    exploit stack_inject_exists_l. eauto. eauto. intros (j & GI1).
    exploit stack_inject_frames. eauto. eauto. eauto.
    intros (f2 & FAP2 & FI).
    exists j, f2; split; auto. split; auto.
    destruct FI. rewrite Forall_forall in *.
    eapply frame_inject_inj0; eauto.
  Qed.

  (* Definition stack_injection f m s1 s2 : Prop := *)
  (*   exists g, *)
  (*     stack_inject f g m s1 s2. *)

  Lemma in_frame_at_pos:
    forall s f,
      In f s ->
      exists n, frame_at_pos s n f.
  Proof.
    intros s f IN; apply In_nth_error in IN; destruct IN as (n & NTH).
    exists n; econstructor; eauto.
  Qed.


  Lemma frame_at_pos_In:
    forall s f n,
      frame_at_pos s n f ->
      In f s.
  Proof.
    intros s f n FAP; inv FAP. eapply nth_error_In; eauto. 
  Qed.

  Lemma frame_at_same_pos:
    forall s n f1 f2,
      frame_at_pos s n f1 ->
      frame_at_pos s n f2 ->
      f1 = f2.
  Proof.
    intros s n f1 f2 FAP1 FAP2; inv FAP1; inv FAP2; congruence.
  Qed.

  Lemma stack_inject_frames' f g m s1 s2:
    stack_inject f g m s1 s2 ->
    forall f1 b1 b2 delta,
      in_frame f1 b1 ->
      f b1 = Some (b2, delta) ->
      In f1 s1 ->
      exists f2,
        In f2 s2 /\
        in_frame f2 b2 /\
        frame_inject' f m f1 f2.
  Proof.
    inversion 1; intros f1 b1 b2 delta IFR FB IFS.
    eapply in_frame_at_pos in IFS. destruct IFS as (n & FAP).
    exploit stack_inject_compat; eauto.
    intros (i2 & f2 & FAP2 & IF2 & GN).
    destruct (stack_inject_frames0 _ _ _ FAP GN) as (f2' & FAP2' & IFR2).
    assert (f2 = f2') by (eapply frame_at_same_pos; eauto). subst.
    exists f2'; split; auto. eapply frame_at_pos_In; eauto.
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

  Lemma stack_inject_block_inject:
    forall f g m s1 s2
      (SI: stack_inject f g m s1 s2)
      b1 b2 delta,
      f b1 = Some (b2, delta) ->
      forall i1 f1,
        frame_at_pos s1 i1 f1 ->
        in_frame f1 b1 ->
        exists i2 f2,
          frame_at_pos s2 i2 f2 /\
          in_frame f2 b2 /\
          g i1 = Some i2 /\
          frame_inject' f m f1 f2 /\
           i2 <=  i1 /\
          ((forall i, g i = Some i2 -> i <= i1) -> (frame_adt_size f2 <= frame_adt_size f1)%Z).
  Proof.
    intros f g m s1 s2 SI b1 b2 delta FB i1 f1 FAP IFR.
    edestruct stack_inject_compat as (i2 & f2 & FAP2 & IFR2 & GI1); eauto.
    exists i2, f2; split; auto.
    split; auto.
    split; auto.
    edestruct stack_inject_frames as (f2' & FAP2' & FI); eauto.
    assert (f2 = f2') by (eapply frame_at_same_pos; eauto). subst.
    split; eauto.
    split.
    eapply stack_inject_pack; eauto.
    eapply stack_inject_sizes; eauto.
  Qed.

  Lemma stack_top_frame_at_position:
    forall s b,
      is_stack_top s b ->
      exists f, frame_at_pos s 0 f /\ in_frame f b.
  Proof.
    destruct s; simpl; intros. easy.
    red in H. simpl in H.
    exists f; split.
    econstructor. simpl. auto.
    auto.
  Qed.

  Lemma frame_at_position_stack_top:
    forall s f b,
      frame_at_pos s 0 f ->
      in_frame f b ->
      is_stack_top s b.
  Proof.
    destruct s; simpl; intros. inv H. simpl in H1. congruence.
    inv H. simpl in H1.
    inv H1. simpl; auto.
  Qed.


  Lemma stack_inject_is_stack_top:
    forall f g m s1 s2,
      stack_inject f g m s1 s2 ->
      forall b1 b2 delta,
        f b1 = Some (b2, delta) ->
        is_stack_top s1 b1 ->
        is_stack_top s2 b2.
  Proof.
    intros f g m s1 s2 SI b1 b2 delta FB IST.
    destruct (stack_top_frame_at_position _ _ IST) as (ff & FAP1 & IFR1).
    edestruct stack_inject_block_inject as (i2 & f2 & FAP2 & IFR2 & GI1 & FI & LE & SZ); eauto.
    eapply frame_at_position_stack_top; eauto.
    constructor.
    replace i2 with O in * by omega. 
    inv FAP2. auto.
  Qed.

  (* Lemma option_prop_le_trans: *)
  (*   forall l1 l2 l3 b1 b2 b3, *)
  (*     option_prop2 le (stack_position l2 b2) (stack_position l1 b1) -> *)
  (*     option_prop2 le (stack_position l3 b3) (stack_position l2 b2) -> *)
  (*     option_prop2 le (stack_position l3 b3) (stack_position l1 b1). *)
  (* Proof. *)
  (*   unfold option_prop2; simpl; intros. *)
  (*   destr. destr_in H0. destr_in H. omega. *)
  (* Qed. *)

  (* Definition inject_in_dec l (o: option (block * Z)): {match o with *)
  (*                                                      | Some (b2,_) => In b2 l *)
  (*                                                      | None => True *)
  (*                                                      end} + { ~ match o with *)
  (*                                                      | Some (b2,_) => In b2 l *)
  (*                                                      | None => True *)
  (*                                                                 end}. *)
  (* Proof. *)
  (*   intros. destruct o; auto. destruct p. apply in_dec. *)
  (*   apply peq. *)
  (* Defined. *)

  (* Definition shift_segment_dec delta f1 f2 : { shift_segment delta f1 f2 } + {~ shift_segment delta f1 f2 }. *)
  (* Proof. *)
  (*   destruct (zeq (seg_ofs f2) (seg_ofs f1 + delta)). *)
  (*   destruct (zeq (seg_size f2) (seg_size f1)). *)
  (*   left; constructor; auto. *)
  (*   right; inversion 1; omega. *)
  (*   right; inversion 1; omega. *)
  (* Defined. *)


  (* Section FORALL. *)

  (*   Variables P: Z -> Prop. *)
  (*   Variable f: forall (x: Z), {P x} + {~ P x}. *)
  (*   Variable lo: Z. *)
  (*   Require Import Zwf. *)

  (*   Program Fixpoint forall_rec (hi: Z) {wf (Zwf lo) hi}: *)
  (*     {forall x, lo <= x < hi -> P x} *)
  (*     + {~ forall x, lo <= x < hi -> P x} := *)
  (*     if zlt lo hi then *)
  (*       match f (hi - 1) with *)
  (*       | left _ => *)
  (*         match forall_rec (hi - 1) with *)
  (*         | left _ => left _ _ *)
  (*         | right _ => right _ _ *)
  (*         end *)
  (*       | right _ => right _ _ *)
  (*       end *)
  (*     else *)
  (*       left _ _ *)
  (*   . *)
  (*   Next Obligation. *)
  (*     red. omega. *)
  (*   Qed. *)
  (*   Next Obligation. *)
  (*     assert (x = hi - 1 \/ x < hi - 1) by omega. *)
  (*     destruct H2. congruence. auto. *)
  (*   Qed. *)
  (*   Next Obligation. *)
  (*     intro F. apply wildcard'. intros; apply F; eauto. omega. *)
  (*   Qed. *)
  (*   Next Obligation. *)
  (*     intro F. apply wildcard'. apply F. omega. *)
  (*   Qed. *)
  (*   Next Obligation. *)
  (*     omegaContradiction. *)
  (*   Defined. *)

  (* End FORALL. *)

  (* Definition in_range_dec lo hi o : { lo <= o < hi } + {~ (lo <= o < hi) }. *)
  (* Proof. *)
  (*   destruct (zle lo o), (zlt o hi); try (right; omega). left; omega. *)
  (* Qed. *)

  (* Definition shift_frame_dec delta f1 f2 : { shift_frame delta f1 f2 } + {~ shift_frame delta f1 f2 }. *)
  (* Proof. *)
  (*   destruct (shift_segment_dec delta (frame_link f1) (frame_link f2)). *)
  (*   destruct (forall_rec _ (fun o => stack_perm_eq (frame_perm f1 o) (frame_perm f2 (o + delta))) 0 (frame_size f1)) *)
  (*     as [FORALL|NFORALL]. *)
  (*       destruct (forall_rec _ (fun o => in_range_dec 0 (frame_size f2) (o + delta)) 0 (frame_size f1)) *)
  (*     as [FORALL2|NFORALL2]. *)
  (*   left; constructor; auto. *)
  (*   right; inversion 1; tauto. *)
  (*   right; inversion 1; tauto. *)
  (*   right; inversion 1; tauto. *)
  (* Defined. *)

  (* Definition perm_kind_pred_dec: *)
  (*   forall (P: perm_kind -> Prop) *)
  (*     (Pdec: forall k, {P k} + {~ P k}), *)
  (*     {forall k, P k} + {~forall k, P k}. *)
  (* Proof. *)
  (*   intros. destruct (Pdec Cur), (Pdec Max); try (right; intro A; eauto; fail). *)
  (*   left; destruct k; auto. *)
  (* Defined. *)

  (* Definition permission_pred_dec: *)
  (*   forall (P: permission -> Prop) *)
  (*     (Pdec: forall p, {P p} + {~ P p}), *)
  (*     {forall p, P p} + {~forall p, P p}. *)
  (* Proof. *)
  (*   intros. destruct (Pdec Freeable), (Pdec Writable), (Pdec Readable), (Pdec Nonempty); try (right; intro A; eauto; fail). *)
  (*   left; destruct p3; auto. *)
  (* Defined. *)

  (* Definition impl_dec: *)
  (*   forall P Q, *)
  (*   P -> *)
  (*   {Q} + {~Q} -> *)
  (*   {P -> Q} + {~(P -> Q)}. *)
  (* Proof. *)
  (*   intros. *)
  (*   destruct H;[left| right]; intuition. *)
  (* Qed. *)

  (* Definition frame_inject_frame_def_dec f (P: block -> Z -> perm_kind -> permission -> Prop) *)
  (*            (Pdec: forall b o k p, {P b o k p} + {~ P b o k p}) *)
  (*            f1 f2: *)
  (*   { frame_inject_frame_def f P f1 f2 } + { ~ frame_inject_frame_def f P f1 f2 }. *)
  (* Proof. *)
  (*   unfold frame_inject_frame_def. *)
  (*   repeat destr. *)
  (*   - apply Forall_dec. intros b1. *)
  (*     destruct (f b1). destruct p. *)
  (*     + destruct (shift_frame_dec z f0 f3); eauto. *)
  (*       left; inversion 1; subst; eauto. *)
  (*     + left; congruence. *)
  (*   - apply Forall_dec. simpl. intros b1. *)
  (*     destruct (f b1). destruct p. *)
  (*     + *)
  (*       cut (  {(forall (o : Z) (RNG: 0 <= o + z < frame_size f0) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))} + *)
  (*              {~(forall (o : Z) (RNG: 0 <= o + z < frame_size f0) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))}). *)
  (*       intros [A|A];[left|right]. inversion 1; subst; eauto. *)
  (*       intro B; apply A. eapply B. eauto. *)
  (*       cut (  {(forall (o : Z) (RNG: 0 - z <= o < frame_size f0 - z) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))} + *)
  (*              {~(forall (o : Z) (RNG: 0 - z <= o < frame_size f0 - z) (k : perm_kind) (p : permission), P b1 o k p -> inject_perm_condition p -> frame_public f0 (o + z))}). *)
  (*       intros [A|A];[left|right]. intros; eapply A; eauto. omega. *)
  (*       intro B; apply A. intros; eapply B; eauto. omega. *)
  (*       apply forall_rec. intro o. *)
  (*       apply perm_kind_pred_dec. intro k. *)
  (*       apply permission_pred_dec. intro p. *)
  (*       destruct (Pdec b1 o k p). *)
  (*       2: left; intuition. *)
  (*       apply impl_dec. auto. *)
  (*       destruct (ipc_dec p). *)
  (*       2: left; intuition. *)
  (*       apply impl_dec; auto. *)
  (*       apply frame_public_dec. *)
  (*     + left; congruence. *)
  (* Qed. *)

  (* Definition frame_inject_dec f m f1 f2 *)
  (*            (mdec: forall b o k p, {m b o k p} + {~ m b o k p}) *)
  (*   : {frame_inject' f m f1 f2} + {~frame_inject' f m f1 f2}. *)
  (* Proof. *)
  (*   destruct (Forall_dec _ (inject_in_dec (frame_blocks f2)) (map f (frame_blocks f1))). *)
  (*   - destruct (frame_inject_frame_def_dec f m mdec f1 f2). *)
  (*     + left; constructor; auto. *)
  (*       rewrite Forall_forall in *. *)
  (*       intros b1 IN. *)
  (*       intros. *)
  (*       exploit f0. rewrite in_map_iff. exists b1; split; simpl; auto. rewrite H. auto. *)
  (*     + right; inversion 1; tauto. *)
  (*   - right; inversion 1. *)
  (*     apply n. *)
  (*     apply Forall_forall; intros b IN. *)
  (*     rewrite in_map_iff in IN; destruct IN as (bb & EQ & IN). *)
  (*     destr. destruct p. subst. *)
  (*     rewrite Forall_forall in frame_inject_inj0. *)
  (*     eauto. *)
  (* Defined. *)


  (* Lemma latest_has_prop: *)
  (*   forall {A} (P: A -> Prop) s f, *)
  (*     latest P s f -> *)
  (*     P f. *)
  (* Proof. *)
  (*   destruct 1; auto. *)
  (* Qed. *)

  (* Lemma exists_latest: *)
  (*   forall {A} (P: A -> Prop) (Pdec: forall a, {P a} + {~ P a}) s, *)
  (*     Exists P s -> *)
  (*     exists f, *)
  (*       latest P s f. *)
  (* Proof. *)
  (*   induction s. *)
  (*   inversion 1. intros EX. *)
  (*   destruct (Exists_dec _ s Pdec). *)
  (*   - destruct (IHs) as (f & LAT); auto. *)
  (*     destruct LAT as (PF & l1 & l2 & SPLIT & FN). *)
  (*     exists f. split; auto. *)
  (*     exists  (a::l1), l2; split; auto. subst; reflexivity. *)
  (*   - inv EX; intuition. exists a; split; auto. *)
  (*     exists nil, s; split; auto. *)
  (*     rewrite Forall_Exists_neg. auto.  *)
  (* Qed. *)

  (* Lemma in_frame_inject_exists_latest: *)
  (*   forall f m *)
  (*     (mdec: forall b o k p, {m b o k p} + {~ m b o k p}) *)
  (*     s f1 f2, *)
  (*     In f1 s -> *)
  (*     frame_inject' f m f1 f2 -> *)
  (*     exists f1, *)
  (*       latest (fun f1 => frame_inject' f m f1 f2) s f1. *)
  (* Proof. *)
  (*   intros. *)
  (*   edestruct (exists_latest _ (fun f1 => frame_inject_dec f m f1 f2 mdec)) as (fl & LAT). *)
  (*   apply Exists_exists. eexists; split; eauto. *)
  (*   eauto. *)
  (* Qed. *)

  (* Lemma latest_in: *)
  (*   forall {A} (P: A -> Prop) l x, *)
  (*     latest P l x -> *)
  (*     In x l. *)
  (* Proof. *)
  (*   intros A P l x (Px & l1 & l2 & SPLIT & NF); subst; rewrite in_app; simpl; auto. *)
  (* Qed. *)

  (* Lemma frame_inject_empty: *)
  (*   forall f m f1 f2, *)
  (*     frame_blocks f1 = nil -> *)
  (*     (forall fi, frame_adt_info f1 = Some fi -> exists fi', frame_adt_info f2 = Some fi') -> *)
  (*     frame_inject' f m f1 f2. *)
  (* Proof. *)
  (*   constructor. *)
  (*   rewrite H. constructor. *)
  (*   red. repeat destr. *)
  (*   rewrite H; constructor. *)
  (*   edestruct H0; eauto. congruence. *)
  (*   rewrite H; constructor. *)
  (* Qed. *)




  (* Definition suffix {A} (l l2: list A) := exists l1, l = l1 ++ l2. *)


  (* Lemma suffix_same_size: *)
  (*   forall {A} (s1 s2 l: list A), *)
  (*     suffix l s1 -> *)
  (*     suffix l s2 -> *)
  (*     length s1 = length s2 -> *)
  (*     s1 = s2. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold suffix in *. *)
  (*   destruct H, H0. subst. *)
  (*   generalize H0; intro Ha. *)
  (*   apply f_equal with (f:=length (A:=A)) in Ha. *)
  (*   rewrite ! app_length in Ha. *)
  (*   revert x x0 s1 s2 H0 H1 Ha. *)
  (*   induction x; simpl; intros; eauto. *)
  (*   assert (length x0 = O) by omega. *)
  (*   rewrite length_zero_iff_nil in H. subst. reflexivity. *)
  (*   destruct x0. simpl in *. omega. *)
  (*   simpl in H0. inv H0. apply IHx in H3; auto. *)
  (* Qed. *)

  (* Lemma suffix_tl: *)
  (*   forall {A} s l (a:A), *)
  (*     suffix l s -> *)
  (*     suffix (a::l) s. *)
  (* Proof. *)
  (*   unfold suffix. *)
  (*   intros. destruct H; subst. *)
  (*   exists (a::x). reflexivity. *)
  (* Qed. *)

  (* Lemma smaller_suffix: *)
  (*   forall {A} s l (a:A), *)
  (*     suffix l (a::s) -> *)
  (*     suffix l s. *)
  (* Proof. *)
  (*   unfold suffix. *)
  (*   intros. destruct H; subst. *)
  (*   exists (x++a::nil). rewrite app_ass; reflexivity. *)
  (* Qed. *)

  (* Lemma suffix_prop: *)
  (*   forall {A} (s2 s1 l: list A), *)
  (*     suffix l s1 -> *)
  (*     suffix l s2 -> *)
  (*     length s1 < length s2 -> *)
  (*     suffix s2 s1. *)
  (* Proof. *)
  (*   induction s2; simpl; intros; eauto. *)
  (*   - omega.  *)
  (*   - destruct (lt_dec (length s1) (length s2)). *)
  (*     apply suffix_tl. *)
  (*     eapply IHs2. eauto. eapply smaller_suffix; eauto. auto. *)
  (*     assert (length s1 = length s2) by omega. *)
  (*     exists (a::nil). simpl. f_equal. *)
  (*     eapply suffix_same_size; eauto. *)
  (*     eapply smaller_suffix; eauto. *)
  (* Qed. *)
  

  (* Lemma latest_inj: *)
  (*   forall {A} (P: A -> Prop) l x1 x2, *)
  (*     latest P l x1 -> *)
  (*     latest P l x2 -> *)
  (*     x1 = x2. *)
  (* Proof. *)
  (*   intros A P l x1 x2 L1 L2. *)
  (*   destruct L1 as (P1 & l11 & l12 & SPLIT1 & NF1). *)
  (*   destruct L2 as (P2 & l21 & l22 & SPLIT2 & NF2). *)
  (*   subst. *)
  (*   assert (In x1 (l11 ++ x1 :: l12)) by (rewrite in_app; simpl; auto). *)
  (*   rewrite SPLIT2 in H. *)
  (*   rewrite in_app in H; simpl in H. *)
  (*   destruct H. *)
  (*   - destruct (lt_dec (length l12) (length l22)). *)
  (*     assert (S1: suffix (l11 ++ x1 :: l12) (x1 :: l12)). *)
  (*     exists l11; reflexivity. *)
  (*     assert (S2: suffix (l21 ++ x2 :: l22) (x2 :: l22)). *)
  (*     exists l21; reflexivity. *)
  (*     rewrite SPLIT2 in S1. *)
  (*     generalize (suffix_prop _ _ _ S1 S2). intro B. trim B. *)
  (*     simpl; omega. *)
  (*     destruct B. *)
  (*     destruct x. simpl in H0; inv H0. auto. simpl in H0. *)
  (*     assert (In x1 l22). inv H0. rewrite in_app; simpl; auto. *)
  (*     rewrite Forall_forall in NF2; apply NF2 in H1. congruence. *)
  (*     destruct (lt_dec (length l22) (length l12)). *)
  (*     assert (S1: suffix (l11 ++ x1 :: l12) (x1 :: l12)). *)
  (*     exists l11; reflexivity. *)
  (*     assert (S2: suffix (l21 ++ x2 :: l22) (x2 :: l22)). *)
  (*     exists l21; reflexivity. *)
  (*     rewrite <- SPLIT2 in S2. *)
  (*     generalize (suffix_prop _ _ _ S2 S1). intro B. trim B. *)
  (*     simpl; omega. *)
  (*     destruct B. *)
  (*     destruct x. simpl in H0; inv H0. auto. simpl in H0. *)
  (*     assert (In x2 l12). inv H0. rewrite in_app; simpl; auto. *)
  (*     rewrite Forall_forall in NF1; apply NF1 in H1. congruence. *)
  (*     assert (length l22 = length l12) by omega. *)
  (*     assert (x1::l12 = x2::l22). *)
  (*     eapply suffix_same_size. *)
  (*     instantiate (1 := l11++x1::l12). exists (l11). reflexivity. *)
  (*     rewrite SPLIT2. exists l21. reflexivity. simpl; congruence. inv H1; auto. *)
  (*   - destruct H; auto. *)
  (*     rewrite Forall_forall in NF2. apply NF2 in H. congruence. *)
  (* Qed. *)
  
  Definition compose_frameinj (g g' : frameinj) n :=
    match g n with
    | Some m => g' m
    | None => None
    end.

  Lemma compose_frameinj_decompose g g':
    forall i k,
      compose_frameinj g g' i = Some k ->
      exists j,
        g i = Some j /\ g' j = Some k.
  Proof.
    unfold compose_frameinj; intros i k CFI; repeat destr_in CFI; eauto.
  Qed.


  Lemma compose_frameinj_smallest:
    forall g g' i1 i3,
      frameinj_preserves_order g ->
      (* frameinj_preserves_order g' -> *)
      (forall j k, g' j = Some k -> exists i, g i = Some j) ->
      compose_frameinj g g' i1 = Some i3 ->
      (forall i, compose_frameinj g g' i = Some i3 -> i <= i1) ->
      exists i2,
        g i1 = Some i2 /\ g' i2 = Some i3 /\
        (forall i, g i = Some i2 -> i <= i1) /\
        (forall i, g' i = Some i3 -> i <= i2).
  Proof.
    unfold compose_frameinj.
    intros g g' i1 i3 FPO COMP CINJ LATEST.
    destruct (g i1) as [i2|] eqn:GI1; try congruence.
    exists i2; split; auto. split; auto.
    assert (LATE1: (forall i, g i = Some i2 -> (i <= i1))).
    {
      intros i GI.
      specialize (LATEST i); rewrite GI in LATEST. auto.
    }
    split; auto.
    intros i GI.
    destruct (COMP _ _ GI) as (ii & GI').
    generalize (LATEST ii); rewrite GI'. intro B; trim B. auto.
    eapply FPO; eauto.
  Qed.

  Lemma frameinj_preserves_order_compose:
    forall g g',
      frameinj_preserves_order g ->
      frameinj_preserves_order g' ->
      frameinj_preserves_order (compose_frameinj g g').
  Proof.
    unfold frameinj_preserves_order.
    unfold compose_frameinj.
    intros. destr_in H2. destr_in H3.
    eauto. 
  Qed.

  Lemma in_frames_in_frame_ex:
    forall s b,
      in_frames s b ->
      exists f, In f s /\ in_frame f b.
  Proof.
    induction s; simpl; intros; eauto. easy.
    destruct H.
    exists a; eauto.
    edestruct IHs as (x & A & B); eauto.
  Qed.


  Lemma frame_at_pos_ex:
    forall i s,
      i < length s ->
      exists f,
        frame_at_pos s i f.
  Proof.
    intros.
    rewrite <- nth_error_Some in H.
    destruct (nth_error s i) eqn:?; try congruence.
    repeat econstructor; eauto.
  Qed.

  Inductive nodup: stack_adt -> Prop :=
  | nodup_nil:
      nodup nil
  | nodup_cons:
      forall f l,
        nodup l ->
        (forall b, in_frame f b -> ~ in_frames l b) ->
        nodup (f::l).

  Definition nodup' (s: stack_adt) :=
    forall b f1 f2,
      In f1 s ->
      In f2 s ->
      in_frame f1 b ->
      in_frame f2 b ->
      f1 = f2.

  Lemma nodup_nodup': forall l, nodup l -> nodup' l.
  Proof.
    induction l; simpl; intros; eauto.
    red; intros; easy.
    red; intros.
    simpl in *.
    destruct H0.
    - destruct H1. congruence.
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_frame. eauto. eauto.
    - destruct H1. 
      subst.
      inv H.
      exfalso; eapply H6. eauto. eapply in_frames_in_frame. eauto. eauto.
      inv H. eapply IHl; eauto.
  Qed.

  Lemma public_stack_shift:
    forall f1 f2 delta,
      shift_frame delta f1 f2 ->
      forall o,
        (0 <= o < frame_size f1)%Z ->
        frame_public f1 o ->
        frame_public f2 (o+delta).
  Proof.
    unfold frame_public. intros.
    generalize (shift_perm _ _ _ H _ H0); eauto.
    rewrite H1.
    destruct (frame_perm f2); simpl; intuition.
  Qed.

  Close Scope nat_scope.

  Lemma public_stack_range_shift:
    forall f1 f2 delta,
      shift_frame delta f1 f2 ->
      forall lo hi,
        0 <= lo -> hi <= frame_size f1 ->
        public_stack_range lo hi f1 ->
        public_stack_range (lo+delta) (hi+delta) f2.
  Proof.
    unfold public_stack_range; intros.
    replace ofs with (ofs-delta+delta) by omega.
    eapply public_stack_shift; eauto. omega.
    apply H2; omega.
  Qed.

  Lemma stack_inject_compose:
    forall (f f' : meminj) g g' m1 l1 l2,
      stack_inject f g m1 l1 l2 ->
      frameinj_surjective g (length l2) ->
      forall m2 l3,
        stack_inject f' g' m2 l2 l3 ->
        nodup l2 ->
        nodup l3 ->
        (forall b1 b2 delta o k p,
            f b1 = Some (b2, delta) ->
            m1 b1 o k p ->
            inject_perm_condition p ->
            m2 b2 (o + delta) k p) ->
        Forall (frame_agree_perms m2) l2 ->
        stack_inject (compose_meminj f f') (compose_frameinj g g') m1 l1 l3.
  Proof.
    intros f f' g g' m1 l1 l2 SI1 SURJ m2 l3 SI2 ND2 ND3 PERM FAP.
    inversion SI1; inversion SI2.
    split.
    - eapply frameinj_preserves_order_compose; eauto.
    - intros i1 f1 i3 FAP1 CFI.
      destruct (compose_frameinj_decompose _ _ _ _ CFI) as (i2 & GI12 & GI23).
      destruct (stack_inject_frames0 _ _ _ FAP1 GI12) as (f2 & FAP2 & FI12).
      destruct (stack_inject_frames1 _ _ _ FAP2 GI23) as (f3 & FAP3 & FI23).
      exists f3; split; auto.
      eapply frame_inject_compose; eauto.
      rewrite Forall_forall in FAP; eapply FAP; eauto. eapply frame_at_pos_In; eauto.
    - intros b1 b3 delta f3 fi CINJ NIN1 INS3 INF3 FINFO3 o k p PERMS IPC.
      unfold compose_meminj in CINJ.
      destruct (f b1) as [[b2 delta1]|] eqn:FB1; try congruence.
      destruct (f' b2) as [[b33 delta2]|] eqn:FB2; try congruence.
      inv CINJ.
      destruct (in_frames_dec l2 b2).
      + destruct (in_frames_in_frame_ex _ _ i) as (f2 & INS2 & INF2).
        destruct (in_frame_at_pos _ _ INS2) as (n2 & FAP2).
        exploit stack_inject_compat; eauto. intros (i3 & f3' & FAP3 & IFR3 & G').
        exploit stack_inject_frames; eauto. intros (f3'' & FAP3' & FI23).
        assert (f3' = f3''). inv FAP3; inv FAP3'; congruence. subst.
        assert (f3 = f3''). apply nodup_nodup' in ND3. eapply ND3; eauto. eapply frame_at_pos_In; eauto. subst.
        destruct FI23. red in frame_inject_frame0.
        rewrite FINFO3 in frame_inject_frame0.
        destr_in frame_inject_frame0.
        * rewrite Z.add_assoc.
          rewrite Forall_forall in frame_inject_frame0. specialize (frame_inject_frame0 _ INF2).
          eapply public_stack_shift. eauto.
          rewrite Forall_forall in FAP; specialize (FAP _ INS2).
          red in FAP. rewrite Heqo0 in FAP. eapply FAP. eauto. eapply PERM; eauto.
          eapply stack_inject_not_in_frames0; eauto.
        * rewrite Z.add_assoc.
          rewrite Forall_forall in frame_inject_frame0. specialize (frame_inject_frame0 _ INF2).
          eapply frame_inject_frame0; eauto.
      + rewrite Z.add_assoc.
        eapply stack_inject_not_in_frames1; eauto.
    - unfold compose_frameinj; intros i j CINJ; repeat destr_in CINJ.
      exploit stack_inject_range0; eauto. intros (A & B); split; auto.
      eapply stack_inject_range1; eauto.
    - intros. unfold compose_frameinj.
      edestruct stack_inject_exists_l0; eauto.
      rewrite H0.
      apply stack_inject_range0 in H0. destruct H0. eauto.
    - unfold compose_frameinj.
      intros i j CINJ; destr_in CINJ.
      eapply stack_inject_pack0 in Heqo.
      eapply stack_inject_pack1 in CINJ. omega.
    - unfold compose_frameinj.
      intros i1 i3 f1 f3 FAP1 FAP3 CINJ LT.
      destr_in CINJ.
      destruct (stack_inject_frames0 _ _ _ FAP1 Heqo) as (f2 & FAP2 & FI12).
      destruct (stack_inject_frames1 _ _ _ FAP2 CINJ) as (f3' & FAP3' & FI23).
      edestruct (compose_frameinj_smallest g g') as (i2 & G12 & G23 & SMALLEST12 & SMALLEST23); eauto.
      intros. eapply SURJ. eapply stack_inject_range1. eauto.
      unfold compose_frameinj; rewrite Heqo, CINJ. auto.
      assert (f3 = f3') by (eapply frame_at_same_pos; eauto). subst.
      assert (n =i2) by congruence. subst.
      transitivity (frame_adt_size f2); eauto. 
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


  Inductive option_le {A: Type} (Pns: A -> Prop) (Pss: A -> A -> Prop) (delta: Z): option A -> option A -> Prop :=
  | option_le_none_none : option_le Pns Pss delta None None
  | option_le_some_some a b : Pss a b -> option_le Pns Pss delta (Some a) (Some b)
  | option_le_none_some a: Pns a -> option_le Pns Pss delta None (Some a).


  Lemma get_assoc_spec:
    forall s b f,
      get_assoc s b = Some f ->
      exists l n, In (l,Some f,n) s /\ in_frame (l, Some f, n) b.
  Proof.
    induction s; simpl; intros; eauto. congruence.
    destruct a,p.
    destr_in H.
    - subst. exists l, z; split; simpl; auto.
    - edestruct IHs as (l0 & z0 & IN1 & IN2); eauto.
  Qed.

  (* Inductive norepet_stack_blocks : list frame_adt -> Prop := *)
  (* | norepet_stack_blocks_nil: norepet_stack_blocks nil *)
  (* | norepet_stack_blocks_cons: *)
  (*     forall f l, *)
  (*       norepet_stack_blocks l -> *)
  (*       (forall b, in_frame f b -> ~ in_frames l b) -> *)
  (*       norepet_stack_blocks (f::l). *)



  Lemma In_tl:
    forall {A} (l: list A) x,
      In x (tl l) ->
      In x l.
  Proof.
    induction l; simpl; intros; eauto.
  Qed.

  Lemma nodup_tl:
    forall l,
      nodup l ->
      nodup (tl l).
  Proof.
    intros l ND; inv ND; simpl; auto. constructor.
  Qed.


  Lemma get_assoc_intro:
    forall s (NR: nodup s) b f,
      In f s -> in_frame f b ->
      get_assoc s b = frame_adt_info f.
  Proof.
    induction s; simpl; intros; eauto. easy. 
    destruct H. subst.
    destruct f,p.
    red in H0. simpl in *. destr. intuition.
    destruct a, p.
    generalize NR; intro NR0.
    apply nodup_nodup' in NR0.
    specialize (NR0 b (l,o,z) f).
    trim NR0. simpl; auto.
    trim NR0. simpl; auto.
    unfold in_frame in *. simpl in *. destr.
    rewrite <- NR0; auto. eapply IHs; eauto.
    apply nodup_tl in NR; simpl in *; auto.
  Qed.

  Lemma get_frame_info_inj_gen:
    forall f g m1 s1 s2 b1 b2 delta
      (SI: stack_inject f g m1 s1 s2)
      (ND1: nodup s1)
      (ND2: nodup s2)
      (FB : f b1 = Some (b2, delta)),
      option_le (fun fi => 
                   forall ofs k p,
                     m1 b1 ofs k p ->
                     inject_perm_condition p ->
                     frame_public fi (ofs + delta))
                (shift_frame delta)
                delta
                (get_frame_info s1 b1)
                (get_frame_info s2 b2).
  Proof.
    intros.
    unfold get_frame_info.
    destruct (in_frames_dec s1 b1).
    edestruct in_frames_in_frame_ex as (ff & INF & INS); eauto.
    destruct (get_assoc s1 b1) eqn:STK1.
    - destruct (get_assoc_spec _ _ _ STK1) as (l & n & IN1 & IN2).
      edestruct (stack_inject_frames' _ _ _ _ _ SI _ _ _ _ IN2 FB IN1) as (f2 & IN3 & IN4 & injbl & FI).
      erewrite get_assoc_intro; eauto.
      red in FI.
      simpl in *.
      rewrite Forall_forall in *.
      specialize (injbl _ IN2 _ _ FB). specialize (FI _ IN2 _ _ FB).
      destr_in FI.
      constructor; auto.
    - edestruct stack_inject_frames' as (f2 & INS2 & INF2 & injbl & FI); eauto.
      erewrite get_assoc_intro; eauto.
      red in FI; simpl in *.
      rewrite Forall_forall in *.
      specialize (FI _ INS _ _ FB).
      destr_in FI. destr_in FI.
      + erewrite get_assoc_intro in STK1; eauto. congruence.
      + destr_in FI. 
        * constructor.
          intros; eapply FI; eauto.
        * constructor.
    - rewrite not_in_frames_get_assoc; auto.
      destruct (get_assoc s2 b2) eqn:FI2; constructor.
      edestruct get_assoc_spec as (l & nn & IN & INR); eauto.
      intros; eapply stack_inject_not_in_frames; eauto.
  Qed.

  Lemma is_stack_top_inj_gen:
    forall P f g s1 s2 b1 b2 delta
      (MINJ: stack_inject f g P s1 s2)
      (FB: f b1 = Some (b2, delta))
      (IST: is_stack_top s1 b1),
      is_stack_top s2 b2.
  Proof.
    intros.
    eapply stack_inject_is_stack_top; eauto.
  Qed.

  Lemma stack_access_inj_gen:
    forall f g m1 s1 s2 b1 b2 delta lo hi p
      (MINJ : stack_inject f g m1 s1 s2)
      (* (PERMS: forall b1 b2 delta, *)
      (*     f b1 = Some (b2, delta) -> *)
      (*     forall o k p, *)
      (*       m1 b1 o k p -> *)
      (*       inject_perm_condition p -> *)
      (*       m2 b2 (o+delta) k p) *)
      (ND1: nodup s1)
      (ND2: nodup s2)
      (FAP: Forall (frame_agree_perms m1) s1)
      (FB : f b1 = Some (b2, delta))
      (RP: forall o, lo <= o < hi -> m1 b1 o Cur p)
      (IPC: inject_perm_condition p)
      (NPSA: stack_access s1 b1 lo hi),
      stack_access s2 b2 (lo + delta) (hi + delta).
  Proof.
    unfold stack_access, public_stack_access.
    intros. revert NPSA.
    intros [[A B]|[A B]].
    - exploit is_stack_top_inj_gen; eauto. intros IST2; left; split; auto.
      generalize (get_frame_info_inj_gen _ _ _ _ _ _ _ _ MINJ ND1 ND2 FB). intro GFIJ.
      do 2 red in B |- *.
      inv GFIJ; auto.
      + rewrite <- H in B. 
        intros. unfold frame_readonly.
        assert (lo <= o - delta < hi) by omega.
        apply B in H3. unfold frame_readonly in H3.
        generalize (shift_perm _ _ _ H1 (o - delta)).
        intro C. trim C. rewrite Forall_forall in FAP.
        unfold get_frame_info in H. symmetry in H.
        apply get_assoc_spec in H.
        destruct H as (l & n & IN1 & IN2).
        specialize (FAP _ IN1). red in FAP. simpl in FAP. eapply FAP. eauto. apply RP. omega.
        intro FP; apply H3.
        replace (o - delta + delta) with o in C by omega.
        red in C. repeat destr_in C.
      + intros.
        unfold frame_readonly.
        replace o with (o - delta + delta) by omega.
        setoid_rewrite H1; eauto. congruence. apply RP. omega.
    - 
      assert (forall fi, get_frame_info s2 b2 = Some fi -> public_stack_range (lo+delta) (hi+delta) fi).
      {
        intros.
        assert (in_frames s2 b2).
        exploit get_assoc_spec. eauto. intros (l & n & IN1 & IN2).
        eapply in_frames_in_frame; eauto.
        generalize (get_frame_info_inj_gen _ _ _ _ _ _ _ _ MINJ ND1 ND2 FB). rewrite H. intro GFIJ.
        inv GFIJ. 
        * rewrite <- H1 in B.
          unfold get_frame_info in H1.
          symmetry in H1.
          apply get_assoc_spec in H1.
          destruct H1 as (l & n & IN1 & IN2).
          rewrite Forall_forall in FAP. specialize (FAP _ IN1).
          red in FAP.
          assert (forall o, lo <= o < hi -> 0 <= o < frame_size a).
          intros.
          eapply FAP. eauto. apply RP. auto.
          red. intros.
          eapply public_stack_range_shift; eauto.
          apply H1; auto. omega.
          cut (hi - 1 < frame_size a). omega.
          apply H1; auto. omega.
        * clear B.
          red.  intros.
          replace ofs with (ofs-delta+delta) by omega. eapply H3.
          apply RP. omega. auto.
      }     
      unfold range_not_readonly_ofs.
      unfold not_readonly_ofs.
      destr.
      specialize (H _ eq_refl).
      destruct (is_stack_top_dec s2 b2); [left; split; auto|right;split;auto].
      intros. apply H in H0. congruence.
      destruct (is_stack_top_dec s2 b2); [left; split; auto|right;split;auto].
  Qed.



  Lemma frame_inject_invariant:
    forall (P P': block -> Z -> perm_kind -> permission -> Prop)
      thr f f1 f2,
      (forall b o k p b' delta,
          f b = Some (b', delta) ->
          Plt b thr ->
          P' b o k p ->
          P b o k p) ->
      (forall b, in_frame f1 b -> Plt b thr) -> 
      frame_inject' f P f1 f2 ->
      frame_inject' f P' f1 f2.
  Proof.
    intros P P' thr f f1 f2 PERMS PLT FI.
    destruct FI; constructor; auto.
    red in frame_inject_frame0 |- *.
    repeat destr.
    rewrite Forall_forall in frame_inject_frame0 |- *.
    intros b1 IN; specialize (frame_inject_frame0 _ IN).
    intros; eapply frame_inject_frame0; eauto.
  Qed.

  Lemma stack_inject_invariant:
    forall (m m': block -> _ -> _ -> _ -> Prop) f g s1 s2 thr,
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          Plt b thr ->
          m' b ofs k p -> m b ofs k p) ->
      Forall (fun f1 => forall b, in_frame f1 b -> Plt b thr) s1 ->
      (forall b1 b2 delta, f b1 = Some (b2, delta) ->
                      ~ Plt b1 thr ->
                      forall f2 fi,
                        In f2 s2 ->
                        in_frame f2 b2 ->
                        frame_adt_info f2 = Some fi ->
                        forall o k pp,
                          m' b1 o k pp ->
                          inject_perm_condition pp ->
                          frame_public fi (o + delta)) ->
      stack_inject f g m s1 s2 ->
      stack_inject f g m' s1 s2.
  Proof.
    intros m m' f g s1 s2 thr PERM PLT PLT' FI.
    destruct FI. constructor; auto.
    - intros i1 f0 i2 FAP G.
      exploit stack_inject_frames0; eauto.
      intros (f3 & FAP2 & FI).
      exists f3; intuition. 
      eapply frame_inject_invariant; eauto.
      rewrite Forall_forall in PLT.
      intros; eapply PLT. eapply frame_at_pos_In; eauto. auto.
    - intros. destruct (plt b1 thr).
      + intros; eapply stack_inject_not_in_frames0; eauto.
      + eapply PLT'; eauto.
  Qed.

  Lemma stack_inject_invariant':
    forall (m m': block -> _ -> _ -> _ -> Prop) f g f1 f2 thr,
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          Plt b thr ->
          m' b ofs k p -> m b ofs k p) ->
      Forall (fun f1 => forall b, in_frame f1 b -> Plt b thr) f1 ->
      (forall b1 b2 delta, f b1 = Some (b2, delta) ->
                      ~ Plt b1 thr -> ~ in_frames f2 b2) ->
      stack_inject f g m f1 f2 ->
      stack_inject f g m' f1 f2.
  Proof.
    intros m m' f g f1 f2 thr PERM PLT PLT' FI.
    destruct FI. constructor; auto.
    intros i1 f0 i2 FAP G.
    exploit stack_inject_frames0; eauto.
    intros (f3 & FAP2 & FI).
    exists f3; intuition. 
    eapply frame_inject_invariant; eauto.
    rewrite Forall_forall in PLT.
    intros; eapply PLT. eapply frame_at_pos_In; eauto. auto.
    intros. destruct (plt b1 thr).
    intros; eapply stack_inject_not_in_frames0; eauto.
    eapply PLT' in H.  exfalso; apply H; eapply in_frames_in_frame; eauto. auto. 
  Qed.

  Lemma frame_inject_invariant_strong:
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

  Lemma stack_inject_invariant_strong:
    forall (m m': block -> _ -> _ -> _ -> Prop) f g f1 f2,
      (forall b ofs k p b' delta,
          f b = Some (b', delta) ->
          m' b ofs k p -> m b ofs k p) ->
      stack_inject f g m f1 f2 ->
      stack_inject f g m' f1 f2.
  Proof.
    intros m m' f g f1 f2 PERM FI.
    destruct FI. constructor; auto.
    - intros i1 f0 i2 FAP G.
      exploit stack_inject_frames0; eauto.
      intros (f3 & FAP2 & FI).
      exists f3; intuition. 
      eapply frame_inject_invariant_strong; eauto.
    - intros. eapply stack_inject_not_in_frames0; eauto. 
  Qed.

  Definition frameinj_order_strict (g: frameinj) :=
    forall i1 i2 i1' i2',
      (i1 < i2)%nat ->
      g i1 = Some i1' ->
      g i2 = Some i2' ->
      (i1' < i2')%nat.

  Lemma frameinj_order_strict_stack_inject0:
    forall g j P s1 s2,
      stack_inject j g P s1 s2 ->
      frameinj_order_strict g ->
      forall i j0 : nat, g i = Some j0 -> (0 < i)%nat -> (0 < j0)%nat.
  Proof.
    intros.
    inv H.
    edestruct (stack_inject_exists_l0 O). apply stack_inject_range0 in H1; omega.
    exploit H0. apply H2. eauto. eauto. omega.
  Qed.

  Lemma frameinj_order_strict_push g:
    frameinj_order_strict g ->
    frameinj_order_strict
      (fun n : nat => if Nat.eq_dec n 0 then Some 0%nat else option_map Datatypes.S (g (Init.Nat.pred n))).
  Proof.
    red; intros.
    unfold option_map in *.
    repeat destr_in H1; repeat destr_in H2.
    - omega.
    - omega.
    - exploit H. 2: exact Heqo. 2: exact Heqo0. omega. omega.
  Qed.

  Lemma frameinj_order_strict_flat:
    forall n,
      frameinj_order_strict (flat_frameinj n).
  Proof.
    unfold flat_frameinj; red; intros.
    repeat destr_in H0; repeat destr_in H1.
  Qed.


  Lemma stack_inject_nil:
    forall f p,
      stack_inject f (fun _ => None) p nil nil.
  Proof.
    constructor.
    - red. congruence.
    -  congruence.
    - simpl. congruence.
    - congruence.
    - simpl; intros; omega.
    - congruence.
    - congruence.
  Qed.

  Lemma frameinj_surjective_flat n x:
    (x <= n)%nat ->
    frameinj_surjective (flat_frameinj n) x.
  Proof.
    red; intros.
    unfold flat_frameinj.
    exists j; destr. omega.
  Qed.


  Lemma stack_inject_length_stack:
    forall j g P s1 s2,
      stack_inject j g P s1 s2 ->
      frameinj_surjective g (length s2) ->
      (length s2 <= length s1)%nat.
  Proof.
    intros j g P s1 s2 SI SURJ.
    inversion SI.
    destruct (Nat.eq_dec (length s2) 0). omega.
    destruct (SURJ (length s2 - 1)%nat).
    omega.
    exploit stack_inject_range; eauto.
    intros (C & D).
    destruct (stack_inject_exists_l0 (length s1 - 1)%nat).
    omega.
    exploit stack_inject_range0. apply H0. intros (A & B).     
    exploit stack_inject_preserves_order. eauto.
    2: apply H. 2: apply H0.
    omega.
    intros.
    assert (x0 = length s2 - 1)%nat by omega.
    subst.
    apply stack_inject_pack0 in H0.
    omega.
  Qed.

  Lemma size_stack_pos:
    forall s,
      (0 <= size_stack s)%Z.
  Proof.
    induction s; simpl; intros; eauto. omega.
    destruct a,p.
    generalize (align_le (Z.max 0 z) 8) (Z.le_max_l 0 z); omega.
  Qed.

  Fixpoint list_nats n :=
    match n with
      O => nil
    | S m => m :: list_nats m
    end.

  Lemma in_list_nats:
    forall n m,
      In m (list_nats n) <-> (m < n)%nat.
  Proof.
    induction n; simpl; split; intros.
    - easy.
    - omega.
    - destruct H; subst. omega. apply IHn in H; omega.
    - destruct (Nat.eq_dec m n); auto. right; rewrite IHn. omega.
  Qed.

  Lemma option_eq_true:
    forall {A} Aeq (o1 o2: option A),
      proj_sumbool (option_eq Aeq o1 o2) = true <-> o1 = o2.
  Proof.
    intros.
    destruct (option_eq Aeq o1 o2); try congruence.
    subst; tauto. split; inversion 1. congruence.
  Qed.

  Fixpoint filteri {A} (f: nat -> A -> bool) (l: list (nat * A)) : list (A) :=
    match l with
      nil => nil
    | (i,a)::r => let r' := filteri f r in
             if f i a then a :: r' else r'
    end.

  Definition latest (g: frameinj) i1 s1 :=
    exists i2, g i1 = Some i2 /\ (forall i, i < s1 -> g i = Some i2 -> i <= i1)%nat.

  Definition latestb (g: frameinj) i1 s1 :=
    match g i1 with
      Some i2 =>
      forallb (fun i => negb (option_eq Nat.eq_dec (g i) (Some i2)) || le_dec i i1) (list_nats s1)
    | None => false
    end.

  Lemma latest_latestb:
    forall g i1 s1,
      latest g i1 s1 <-> latestb g i1 s1  = true.
  Proof.
    unfold latest,latestb; split; intros.
    - destruct H as (i2 & EQ & F). rewrite EQ.
      rewrite forallb_forall. intro x. rewrite in_list_nats. intros.
      destruct (option_eq Nat.eq_dec (g x) (Some i2)); simpl; auto.
      specialize (F _ H e).
      destruct le_dec; auto.
    - destr_in H.
      rewrite forallb_forall in H.
      eexists; split; eauto. intros.
      rewrite <- in_list_nats in H0.
      specialize (H _ H0). rewrite H1 in H.
      erewrite (proj2 (option_eq_true _ _ _)) in H; auto.
      simpl in H.
      destruct (le_dec i i1); auto. inv H.
  Qed.

  Lemma le_add_pos:
    (forall a b,
        0 <= b ->
        a <= a + b)%Z.
  Proof.
    intros; omega.
  Qed.

  Fixpoint pairi {A} (l: list A) i : list (nat * A) :=
    match l with
      nil => nil
    | a::r => (i,a)::(pairi r (S i))
    end.

  Lemma size_stack_filteri:
    forall s1 n f,
      (size_stack (filteri f (pairi s1 n)) <= size_stack s1)%Z.
  Proof.
    induction s1; simpl; intros; eauto.
    omega.
    destruct a, p.
    destr. simpl.
    specialize (IHs1 (S n) f). omega.
    etransitivity. apply IHs1. apply le_add_pos.
    etransitivity. 2: apply align_le. 2: omega.
    apply Z.le_max_l.
  Qed.

  Fixpoint sorted_fst {A} (l: list (nat * A)) :=
    match l with
      nil => True
    | (x,_)::r =>
      match r with
        (y,t)::r' => (x < y)%nat /\ sorted_fst r
      | nil => True
      end
    end.

  Lemma sorted_tl:
    forall {A} (l: list (nat * A)),
      sorted_fst l ->
      sorted_fst (tl l).
  Proof.
    destruct l; auto.
    simpl. destruct p. destruct l; auto.
    destruct p; tauto.
  Qed.


  Lemma sorted_fst_lt:
    forall {A} (l: list (nat * A)) i1 f1 i2 f2,
      In (i1, f1) l ->
      sorted_fst ((i2,f2)::l) ->
      (i2 < i1)%nat.
  Proof.
    induction l; simpl; intros; eauto. easy.
    destruct a. destruct H0.
    destruct H. inv H. auto.
    eapply IHl; simpl; eauto.
    destruct l. auto. destruct p.
    destruct H1; split; auto. omega.
    Unshelve. auto.
  Qed.

  Lemma sorted_fst_lt_map:
    forall {A} (l: list (nat * A)) i1 i2 f2,
      In i1 (map fst l) ->
      sorted_fst ((i2,f2)::l) ->
      (i2 < i1)%nat.
  Proof.
    intros. rewrite in_map_iff in H.
    destruct H as (x & EQ & IN). destruct x. simpl in EQ. subst.
    eapply sorted_fst_lt; eauto.
  Qed.

  
  Opaque sorted_fst.



  Ltac elim_div :=
    unfold Zdiv, Zmod in *;
    repeat
      match goal with
      |  H : context[ Zdiv_eucl ?X ?Y ] |-  _ =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      |  |-  context[ Zdiv_eucl ?X ?Y ] =>
         generalize (Z_div_mod_full X Y) ; destruct (Zdiv_eucl X Y)
      end; unfold Remainder.
  
  Lemma align_ge1:
    forall sz al,
      al > 0 ->
      exists b, 0 <= b < al /\
           align sz al = sz + b /\ 
           b = (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
  Proof.
    intros.
    generalize (align_le sz al H).
    destruct (align_divides sz al H).
    rewrite H0.
    intros. 
    unfold align in H0.
    rewrite <- H0.
    replace ((sz+al-1)/al) with (1+ ((sz-1)/al)).
    {
      replace ((1+ ((sz-1)/al))*al) with (al + (sz -1)/al *al).
      {
        rewrite Z.mul_comm.
        replace (al * ((sz - 1) / al)) with
        (al * ((sz - 1) / al) + (sz-1) mod al - (sz-1) mod al) by omega.
        rewrite <- Z.div_mod by omega.
        rewrite Z.mod_eq by omega.
        exists (al - 1 - (sz - 1 - al * ((sz - 1) / al))).
        split; try omega.
        {
          elim_div. assert (al <> 0) by omega. intuition.
        }
      }
      rewrite Z.mul_add_distr_r. omega.
    }
    {
      replace (sz + al - 1) with ((sz -1) + 1*al) by omega.
      rewrite Z_div_plus_full by omega.
      omega.
    }
  Qed.
  
  Lemma align_mono:
    forall al sz sz',
      al > 0 ->
      0 <= sz <= sz' ->
      align sz al <= align sz' al.
  Proof.
    intros.
    generalize (align_ge1 sz al H)
               (align_ge1 sz' al H).
    intros [b [A [B C]]] [c [D [E F]]].
    destruct (zlt (sz'-sz) al); try intuition omega.
    assert (exists d, 0 <= d < al /\ sz' = sz + d).
    {
      clear - H0 H l.
      exists (sz'-sz). intuition try omega.
    }
    destruct H1 as [d [ENC EQ]]. rewrite EQ in *.
    clear EQ.
    rewrite B; rewrite E.
    cut (      al * ((sz - 1) / al) <=
               (   al * ((sz + d - 1) / al))); intros; try omega.  
    apply Z.mul_le_mono_nonneg_l; try  omega.
    apply Z.div_le_mono; try omega.
  Qed.
  
  Lemma size_stack_filteri_le:
    forall (s1 s2: list (nat * frame_adt))
      (SORT1: sorted_fst s1)
      (SORT2: sorted_fst s2)
      g
      (SIZELE: forall i1 i2 f1 f2,
          In (i1, f1) s1 ->
          In (i2, f2) s2 ->
          g i1 = Some i2 ->
          (forall i, g i = Some i2 -> (i <= i1)%nat) ->
          frame_adt_size f2 <= frame_adt_size f1)
      (EX: forall i j fi, In (i,fi) s1 -> g i = Some j -> exists fj, In (j,fj) s2)
      (* (LEN: (length s2 <= length s1)%nat) *)
      (EXX: forall i (IN: In i (map fst s1)) i1 (LE: (i <= i1)%nat) j (GJ: g i1 = Some j),
          In i1 (map fst s1))
      n
      (LT: (forall i j, g i = Some j -> i < n)%nat)
      (ORDER: forall i1 i2 j1 j2, (i1 <= i2 -> g i1 = Some j1 -> g i2 = Some j2 -> j1 <= j2)%nat)
      (EXR: forall j f, In (j,f) s2 -> exists i, In i (map fst s1) /\ g i = Some j)
    ,
      size_stack (map snd s2) <=
      size_stack (filteri (fun (i1 : nat) (_ : frame_adt) => latestb g i1 n) s1).
  Proof.
    induction s1; simpl; intros.
    - destruct s2. simpl; omega.
      destruct p. specialize (EXR _ _ (or_introl eq_refl)). destruct EXR as [i [[] ?]].
    - destruct a. destr.
      + destruct s2. simpl. destruct f, p.
        apply Z.add_nonneg_nonneg.
        apply size_stack_pos.
        etransitivity. 2: apply align_le. 2: omega. apply Z.le_max_l.
        simpl. destruct p. simpl. destruct f0. destruct p, f, p. simpl.
        apply latest_latestb in Heqb. destruct Heqb as (xx & Gxx & LATEST).
        destruct (EX _ _ _ (or_introl eq_refl) Gxx) as (fj & INJ).
        simpl in INJ.
        destruct INJ. inv H.
        apply Z.add_le_mono.
        * apply IHs1.
          -- destruct s1. auto. destruct p. apply SORT1.
          -- apply sorted_tl in SORT2; auto.
          -- intros; eapply SIZELE; simpl; eauto.
          -- intros; exploit EX. right; eauto. eauto. intros (fj & INJ).
             simpl in INJ. destruct INJ; eauto.
             inv H1.
             apply LATEST in H0.
             eapply sorted_fst_lt in H; eauto. omega. 
             eauto.
          -- intros. simpl in *.
             specialize (EXX _ (or_intror IN) _ LE _ GJ).
             destruct EXX; auto. subst. rewrite Gxx in GJ. inv GJ.
             eapply sorted_fst_lt_map in IN; eauto. omega.
          -- auto.
          -- auto.
          -- intros. specialize (EXR _ _ (or_intror H)). destruct EXR as (i & IN & GI).
             destruct IN; eauto.
             simpl in H0. subst. 
             rewrite GI in Gxx. inv Gxx. eapply sorted_fst_lt in H; eauto. omega.
        * specialize (SIZELE _ _ _ _ (or_introl eq_refl) (or_introl eq_refl) Gxx).
          apply align_mono. omega.
          split. apply Z.le_max_l.
          apply Z.max_le_compat_l. apply SIZELE.
          intros i GI. apply LATEST; eauto.
        * exfalso.
          exploit (sorted_fst_lt s2). eauto. eauto. intro LTn.
          destruct (EXR _ _ (or_introl eq_refl)) as (i & IN & GI).
          destruct IN. simpl in H0; subst. rewrite Gxx in GI; inv GI. omega.
          apply in_map_iff in H0.
          destruct H0 as (x & EQ & IN). subst. destruct x. simpl in *.
          exploit (sorted_fst_lt s1); eauto. intro LTnn.
          exploit (ORDER n0 n2). omega. eauto. eauto. omega.
      + apply IHs1; eauto.
        * apply sorted_tl in SORT1; eauto.
        * intros.
          destruct (EXX _ (or_intror IN) _ LE _ GJ); auto. simpl in H; subst.
          eapply sorted_fst_lt_map in IN; eauto. omega.
        * intros.
          destruct (EXR _ _ H) as (i & IN & GI).
          destruct IN; eauto.
          inv H0. simpl in *.
          assert (~ latest g n0 n). rewrite latest_latestb. congruence.
          unfold latest in H0.
          rewrite GI in H0.
          assert (~ forall i0, g i0 = Some j -> i0 <= n0)%nat.
          intro F.
          apply H0.
          eexists; split; eauto.
          assert (exists i0, g i0 = Some j /\ n0 < i0)%nat.
          apply Classical_Pred_Type.not_all_not_ex.
          intro F; apply H1. intros.
          specialize (F i0). rewrite H2 in F.
          destruct (le_dec i0 n0); auto. exfalso; apply F; split; auto. omega.
          clear H0 H1.
          destruct H2 as (i0 & GI0 & LTi0).
          exists i0; split; auto.
          specialize (EXX _ (or_introl eq_refl) i0). trim EXX. omega.
          specialize (EXX _ GI0).
          destruct EXX; auto. subst. omega.
  Qed.

  Lemma map_snd_pairi:
    forall {A} (l: list A) n,
      map snd (pairi l n) = l.
  Proof.
    induction l; simpl; intros; eauto.
    rewrite IHl. auto.
  Qed.

  Lemma sorted_fst_pairi:
    forall {A} (l: list A) n,
      sorted_fst (pairi l n).
  Proof.
    Transparent sorted_fst.
    induction l; simpl; intros; eauto.
    destr. rewrite <- Heql0. destruct p. split; eauto.
    destruct l; simpl in *. inv Heql0. inv Heql0. omega.
  Qed.

  Lemma In_pairi_lt:
    forall {A} i1 f1 (s1: list A) n,
      In (i1, f1) (pairi s1 n) ->
      (n <= i1)%nat.
  Proof.
    induction s1; simpl; intros; eauto. easy.
    destruct H as [H|H]. inv H.
    auto.
    apply IHs1 in H. omega.
  Qed.
  
  Lemma In_pairi_nth:
    forall {A} i1 f1 (s1: list A) n,
      In (i1, f1) (pairi s1 n) ->
      nth_error s1 (i1 - n) = Some f1.
  Proof.
    induction s1; simpl; intros; eauto. easy.
    destruct H. inv H. replace (i1 - i1)%nat with O by omega. reflexivity.
    specialize (IHs1 _ H). apply In_pairi_lt in H.
    replace (i1 - n)%nat with (S (i1 - S n)) by omega. simpl. auto.
  Qed.

  Lemma nth_In_pairi:
    forall {A} f1 (s1: list A) n i1,
      nth_error s1 i1 = Some f1 ->
      In (i1 + n, f1)%nat (pairi s1 n).
  Proof.
    induction s1; simpl; intros; eauto. rewrite nth_error_nil in H. easy.
    destruct i1 eqn:?; simpl in H. inv H.
    left. f_equal. 
    eapply IHs1 with (n:= S n) in H. right.
    rewrite plus_Snm_nSm; auto.
  Qed.

  Lemma In_map_fst_pairi:
    forall {A} (s1: list A) i1 n,
      (i1 < length s1)%nat ->
      In (i1 + n)%nat (map fst (pairi s1 n)).
  Proof.
    induction s1; simpl; intros; eauto.
    omega.
    destruct i1. left; auto.
    rewrite plus_Snm_nSm.
    right; apply IHs1. omega.    
  Qed.
        
  
  Lemma size_stack_stack_inject:
    forall j g P s1 s2,
      stack_inject j g P s1 s2 ->
      frameinj_surjective g (length s2) ->
      (size_stack s2 <= size_stack s1)%Z.
  Proof.
    intros j g P s1 s2 SI SURJ.
    transitivity (size_stack (filteri (fun i1 _ => latestb g i1 (length s1)) (pairi s1 O))).
    2: apply size_stack_filteri.
    erewrite <- (map_snd_pairi s2).
    instantiate (1:=O).
    apply size_stack_filteri_le.
    apply sorted_fst_pairi.
    apply sorted_fst_pairi.
    - intros. apply In_pairi_nth in H.
      apply In_pairi_nth in H0.
      rewrite <- minus_n_O in *.
      eapply stack_inject_sizes; eauto; try constructor; eauto.
    - intros.
      apply In_pairi_nth in H. rewrite <- minus_n_O in H.
      exploit stack_inject_frames; eauto. constructor; eauto. intros (f2 & FAP & FI).
      inv FAP. eapply nth_In_pairi with (n:=O) in H1.
      rewrite plus_0_r in H1. eauto.
    - intros.
      rewrite in_map_iff in IN.
      destruct IN as ((ii & f) & EQ & IN). subst. simpl in *.
      eapply In_pairi_nth in IN. rewrite <- minus_n_O in IN.
      eapply stack_inject_range in GJ; eauto.
      destruct GJ as (LTi1 & LTj0).
      replace (i1) with (i1+O)%nat by omega. eapply In_map_fst_pairi. auto.
    - intros; eapply stack_inject_range in H; eauto. tauto.
    - intros. inv SI. eauto.
    - intros j0 f IN.
      eapply In_pairi_nth in IN. rewrite <- minus_n_O in IN.
      destruct (SURJ j0). rewrite <- nth_error_Some. congruence.
      exists x; split; auto.
      replace (x) with (x+O)%nat by omega. eapply In_map_fst_pairi. 
      eapply stack_inject_range in H; eauto. tauto.
  Qed.

  Lemma stack_inject_g0_0:
    forall j g p s1 s2,
      stack_inject j g p s1 s2 ->
      (0 < length s1 ->
       0 < length s2 ->
       g 0 = Some 0)%nat.
  Proof.
    intros j g p s1 s2 SI LT1 LT2.
    inv SI.
    destruct (stack_inject_exists_l0 _ LT1). rewrite H. apply stack_inject_pack0 in H. 
    f_equal; omega.
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
    - inversion 1; eauto. intros; exfalso; apply H0. eapply in_frames_in_frame; eauto.
    - intros i j H; destr_in H; inv H.
    - intros. exists i; destr.
    - intros i j H; destr_in H; inv H. omega.
    - intros i1 i2 f1 f2 FAP1 FAP2 H; repeat destr_in H.
      assert (f1 = f2) by (eapply frame_at_same_pos; eauto). subst. omega.
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
  inversion SI; constructor; eauto.
  - intros i1 f1 i2 FAP GI.
    exploit stack_inject_frames; eauto.
    intros (f2 & FP & FI).
    exists f2; intuition.
    eapply frame_inject_incr; eauto.
    intros b b' delta NONE SOME IFR.
    eapply NEW in SOME; eauto. destruct SOME as (NIN & _) ; eapply NIN. eapply in_frames_in_frame; eauto.
    eapply frame_at_pos_In; eauto.
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


End INJ.
