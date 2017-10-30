Require Import Coqlib.
Require Import Coq.Lists.List.
Require Import Asm.
Require Import StackADT.
Require Import Integers AST.

Import ListNotations.

Definition sp_adjustment_32 sz := 
  let sz' := (align sz 16) in
  sz' - 4.

Definition linear_addr reg ofs := 
  Addrmode (Some reg) None (inl ofs).

Definition expand_instr (i: instruction) : list instruction :=
  match i with
  | Pallocframe fi ofs_ra ofs_link =>
    let sz := (sp_adjustment_32 (frame_size fi)) in
    let addr1 := linear_addr RSP (sz+4) in
    let addr2 := linear_addr RSP (Ptrofs.unsigned ofs_link) in
    [Psubl_ri RSP (Int.repr sz);
     Pleal RAX addr1;
     Pmovl_mr addr2 RAX]
  | Pfreeframe sz ofs_ra ofs_link => 
    let sz := (sp_adjustment_32 sz) in
    [Paddl_ri RSP (Int.repr sz)]
  | _ => [i]
  end.


Fixpoint expand_code (il: code) : code :=
  match il with
  | nil => nil
  | i::il' => expand_instr i ++ expand_code il'
  end.

Definition transf_function (f: Asm.function) : Asm.function :=
  let c := expand_code f.(fn_code) in 
  mkfunction f.(fn_sig) c (f.(fn_frame)).

Definition transf_fundef (f: Asm.fundef) : Asm.fundef :=
  transf_fundef transf_function f.

Definition transf_program (p: Asm.program) : Asm.program :=
  transform_program transf_fundef p.