
Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Smallstep.

(** * Flat composition *)

(** The flat composition of transition systems essentially corresponds
  to the union of strategies: if component [i] handles a given query,
  then the flat composition will handle it in a similar way. However,
  the components cannot call each other. *)

Module FComp.
  Section FLATCOMP.
    Context (ge: Senv.t).
    Context {li1 li2 I} (L: I -> semantics li1 li2).

    Definition genv := forall i, genvtype (L i).

    Definition state := { i : I & state (L i) }.

    Inductive step (ge: genv): state -> trace -> state -> Prop :=
      | step_intro i s t s':
          Smallstep.step (L i) (ge i) s t s' ->
          step ge (existT _ i s) t (existT _ i s').

    Inductive initial_state (q: query li2): state -> Prop :=
      | initial_state_intro i s:
          Smallstep.initial_state (L i) q s ->
          initial_state q (existT _ i s).

    Inductive at_external: state -> query li1 -> Prop :=
      | at_external_intro i s q:
          Smallstep.at_external (L i) s q ->
          at_external (existT _ i s) q.

    Inductive after_external: state -> reply li1 -> state -> Prop :=
      | after_external_intro i s r s':
          Smallstep.after_external (L i) s r s' ->
          after_external (existT _ i s) r (existT _ i s').

    Definition final_state (s: state) (r: reply li2): Prop :=
      let (i, si) := s in Smallstep.final_state (L i) si r.

    Definition semantics :=
      {|
        Smallstep.genvtype := genv;
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.at_external := at_external;
        Smallstep.after_external := after_external;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := fun i => Smallstep.globalenv (L i);
        Smallstep.symbolenv := ge;
      |}.
    End FLATCOMP.
End FComp.

(** * Resolution operator *)

(** To go from the flat composition to horizontal composition, we
  introduce the following resolution operator. [Res] eliminates
  external calls to internal functions by replacing them with a nested
  execution of the transition system. Each [Res.state] is a stack of
  states of [L]: normal execution operates on the topmost state;
  a recursive call into [L] pushes the nested initial state on the
  stack; reaching a final state causes the topmost state to be popped
  and the caller to be resumed, or returns to the environment when
  we reach the last one. *)

Module Res.
  Section RESOLVE.
    Context {li} (L: Smallstep.semantics li li).
    Context (internal: query li -> bool).

    Definition state := list (Smallstep.state L).

    Inductive initial_state (q: query li): state -> Prop :=
      | initial_state_intro s:
          Smallstep.initial_state L q s ->
          initial_state q (s :: nil).

    Inductive at_external: state -> query li -> Prop :=
      | at_external_intro s stk q':
          Smallstep.at_external L s q' ->
          internal q' = false ->
          at_external (s :: stk) q'.

    Inductive after_external: state -> reply li -> state -> Prop :=
      | after_external_intro s stk r' s':
          Smallstep.after_external L s r' s' ->
          after_external (s :: stk) r' (s' :: stk).

    Inductive final_state: state -> reply li -> Prop :=
      | final_state_intro s r:
          Smallstep.final_state L s r ->
          final_state (s :: nil) r.

    Inductive step ge : state -> trace -> state -> Prop :=
      | step_internal s t s' stk:
          Smallstep.step L ge s t s' ->
          step ge (s :: stk) t (s' :: stk)
      | step_call s stk qi si:
          internal qi = true ->
          Smallstep.at_external L s qi ->
          Smallstep.initial_state L qi si ->
          step ge (s :: stk) E0 (si :: s :: stk)
      | step_return si ri s s' stk:
          Smallstep.final_state L si ri ->
          Smallstep.after_external L s ri s' ->
          step ge (si :: s :: stk) E0 (s' :: stk).

    Definition semantics: Smallstep.semantics li li :=
      {|
        Smallstep.state := state;
        Smallstep.step := step;
        Smallstep.initial_state := initial_state;
        Smallstep.at_external := at_external;
        Smallstep.after_external := after_external;
        Smallstep.final_state := final_state;
        Smallstep.globalenv := globalenv L;
        Smallstep.symbolenv := symbolenv L;
      |}.
  End RESOLVE.
End Res.

(** * Horizontal composition *)

(** Applying the resolution operator to the flat composition of
  some transitions systems gives us horizontal composition. *)

Module HComp.
  Section HCOMP.
    Context (ge: Senv.t).
    Context {li I} (L: I -> semantics li li).
    Context (internal: query li -> bool).

    Definition semantics :=
      Res.semantics (FComp.semantics ge L) internal.
  End HCOMP.
End HComp.
