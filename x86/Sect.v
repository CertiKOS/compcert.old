Require Import Coqlib.

Definition sect_id:Type := positive.

(* A block of locations (offsets and sizes) in a section *)
Definition sect_block:Type := sect_id * Z * Z.

Definition section_map := sect_id -> option Z.
