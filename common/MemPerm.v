Require Import Coqlib.

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