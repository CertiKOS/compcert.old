
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.

Module Res.
  Section RESOLVE.
    Context (L: Smallstep.semantics).
    Context (internal: query -> bool).

    Definition cont: Type := reply -> state L -> Prop.

    Definition external_event (t: trace) :=
      match t with
        | Event_extcall _ _ q r :: nil => internal q = false
        | _ => True
      end.

    Definition current_continuation (s: Smallstep.state L) f sg q: cont :=
      fun r s' =>
        Smallstep.step L (globalenv L) s (Event_extcall f sg q r :: nil) s'.

    Inductive state := State (s: Smallstep.state L) (k: list cont).

    Inductive initial_state (q: query): state -> Prop :=
      | initial_state_intro s:
          Smallstep.initial_state L q s ->
          initial_state q (State s nil).

    Inductive final_state: state -> reply -> Prop :=
      | final_state_intro s r:
          Smallstep.final_state L s r ->
          final_state (State s nil) r.

    Inductive step ge : state -> trace -> state -> Prop :=
      | step_internal s t s' stk:
          Smallstep.step L ge s t s' ->
          external_event t ->
          step ge (State s stk) t (State s' stk)
      | step_call s stk f sg q si:
          let k := current_continuation s f sg q in
          (exists r s', k r s') ->
          Smallstep.initial_state L q si ->
          step ge (State s stk) E0 (State si (k::stk))
      | step_return si (k: cont) stk r s:
          Smallstep.final_state L si r ->
          k r s ->
          step ge (State si (k::stk)) E0 (State s stk).

    Definition semantics: Smallstep.semantics :=
      {|
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := globalenv L;
        Smallstep.symbolenv := symbolenv L;
      |}.

    Lemma step_external_event ge s t s':
      step ge s t s' ->
      external_event t.
    Proof.
      destruct 1; simpl; eauto.
    Qed.
  End RESOLVE.
End Res.

(** * Flat composition *)

Module FComp.
  Section FLATCOMP.
    Context (ge: Senv.t).
    Context {I} (L: I -> semantics).

    Definition genv := forall i, genvtype (L i).

    Definition state := { i : I & state (L i) }.

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      step_intro i s t s':
        Smallstep.step (L i) (ge i) s t s' ->
        step ge (existT _ i s) t (existT _ i s').

    Inductive initial_state (q: query): state -> Prop :=
      initial_state_intro i s:
        Smallstep.initial_state (L i) q s ->
        initial_state q (existT _ i s).

    Definition final_state (s: state) (r: reply): Prop :=
      let (i, si) := s in Smallstep.final_state (L i) si r.

    Definition semantics :=
      {|
        Smallstep.genvtype := genv;
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := fun i => Smallstep.globalenv (L i);
        Smallstep.symbolenv := ge;
      |}.
    End FLATCOMP.
End FComp.


(** * Horizontal composition *)

Module HComp.
  Section HCOMP.
    Context (ge: Senv.t).
    Context {I} (L: I -> semantics).
    Context (internal: query -> bool).

    Definition semantics :=
      Res.semantics (FComp.semantics ge L) internal.
  End HCOMP.
End HComp.
