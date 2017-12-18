Require Import Coqlib List.

Section ASSOC.
  Variables A B: Type.

  Variable Aeq: forall (a1 a2: A), {a1=a2}+{a1<>a2}.

  Fixpoint get_assoc (l: list (A*B)) (b: A) : option B :=
    match l with
      nil => None
    | (k,v)::r => if Aeq k b then Some v else get_assoc r b
    end.

  Lemma get_assoc_in_fst:
    forall (l: list (A*B)) b r,
      get_assoc l b = Some r ->
      In b (map fst l).
  Proof.
    induction l; simpl; intros; eauto. inv H.
    repeat destr_in H. simpl. right.
    eauto.
  Qed.

  Lemma get_assoc_in:
    forall (l: list (A*B)) b r,
      get_assoc l b = Some r ->
      In (b,r) l.
  Proof.
    induction l; simpl; intros; eauto. inv H.
    repeat destr_in H. simpl. right.
    eauto.
  Qed.

  Lemma in_lnr_get_assoc:
    forall l b f,
      list_norepet (map fst l) ->
      In (b,f) l ->
      get_assoc l b = Some f.
  Proof.
    induction l; intros b f LNR IN; simpl in *. easy.
    destruct IN. subst. destr.
    inv LNR. erewrite IHl; eauto.
    repeat destr. subst. simpl in *.
    exfalso; apply H2; apply in_map_iff.
    exists (b,f); split; auto.
  Qed.

End ASSOC.


(* 

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



  Definition inject_option_frame delta fi fi' :=
    match fi, fi' with
      None, None => True
    | Some fi, Some fi' => inject_frame_info delta fi fi'
    | _,_ => False
    end.

  Lemma inject_option_frame_id:
    forall o,
      inject_option_frame 0 o o.
  Proof.
    unfold inject_option_frame.
    destruct o; auto.
  Qed.

  Hint Resolve inject_option_frame_id.

  Lemma inject_option_frame_trans:
    forall o1 o2 o3 delta1 delta2,
      inject_option_frame delta1 o1 o2 ->
      inject_option_frame delta2 o2 o3 ->
      inject_option_frame (delta1 + delta2) o1 o3.
  Proof.
    unfold inject_option_frame.
    intros o1 o2 o3 delta1 delta2 A B.
    destruct o1, o2, o3; eauto; easy.
  Qed.

  Hint Resolve inject_option_frame_trans.

  Lemma inject_option_frame_inv:
    forall z ofi fi,
      inject_option_frame z ofi (Some fi) ->
      exists f, ofi = Some f /\ inject_frame_info z f fi.
  Proof.
    intros. 
    destruct ofi; simpl in H; try easy.
    eauto. 
  Qed.


 *)