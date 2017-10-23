(* Translation from CompCert assembly to Rocksalt assembly *)
(* Author        : Yuting Wang *)
(* Date Created  : 10-23-2017 *)

Require Import Integers AST.
Require Import Asm.
Require Import X86Model.Encode.
Require Import X86Model.X86Syntax.
Require Import Errors.

Local Open Scope error_monad_scope.

(* Mapping from global indentifers to addresses in memory *)
Parameter gmap : ident -> int32.
(* Mapping from labels to addresses in memory *)
Parameter lmap : label -> int32.

(** Translate integer registers *)
Definition transl_ireg (r: ireg) : res register :=
  match r with
  | RAX => OK EAX
  | RBX => OK EBX
  | RCX => OK ECX 
  | RDX => OK EDX
  | RSI => OK ESI 
  | RDI => OK EDI
  | RBP => OK EBP
  | RSP => OK ESP
  | _ => Error nil
  end.

(* Translate integers to bit vectors *)
Definition int_to_bits (i:Int.int) : int32 :=
  (Word.repr (Int.signed i)).

Definition ptrofs_to_bits (i:Ptrofs.int) : int32 :=
  (Word.repr (Ptrofs.signed i)).

(* CompCert: *)

(* Inductive addrmode: Type := *)
(*   | Addrmode (base: option ireg) *)
(*              (ofs: option (ireg * Z)) *)
(*              (const: Z + ident * ptrofs). *)

(* Rocksalt *)

(* Record address : Set := mkAddress { *)
(*   addrDisp : int32 ;  *)
(*   addrBase : option register ;  *)
(*   addrIndex : option (scale * register) *)
(* }. *)

(* Translate the addressing mode *)
Definition transl_addr_mode (m: addrmode) : res address :=
  match m with
  | Addrmode b ofs const =>
    let disp := 
        match const with 
        | inl disp' => Word.repr disp'
        | inr (ident,ptrofs) => Word.add (gmap ident) (ptrofs_to_bits ptrofs)
        end in
    do base_reg <-
         match b with
         | None => OK None
         | Some r => 
           do r' <- transl_ireg r; OK (Some r')
         end;
    do index <-
         match ofs with
         | None => OK None
         | Some (r,scale) => 
           do r' <- transl_ireg r;
             OK (Some (Z_to_scale scale, r'))
         end;
    OK {|
        addrDisp := disp;
        addrBase := base_reg;
        addrIndex := index;
      |}
  end.

(* Translate the types of test conditions *)

(* Inductive testcond: Type := *)
(*   | Cond_e | Cond_ne *)
(*   | Cond_b | Cond_be | Cond_ae | Cond_a *)
(*   | Cond_l | Cond_le | Cond_ge | Cond_g *)
(*   | Cond_p | Cond_np. *)

Definition transl_cond_type (t:testcond) :=
  match t with
  (* equal, zero *)
  | Cond_e => E_ct 
  (* not equal, not zero *)
  | Cond_ne => NE_ct
  (* below, not above or equal *)
  | Cond_b => B_ct
  (* below or equal, not above *)
  | Cond_be => BE_ct
  (* not below, above or equal *)                
  | Cond_ae => NB_ct
  (* not below or equal, above *)
  | Cond_a => NBE_ct
  (* less than, not greater than or equal to *)
  | Cond_l => L_ct
  (* less than or equal to, not greater than *)
  | Cond_le => LE_ct
  (* not less than, greater than or equal to *)
  | Cond_ge => NL_ct
  (* not less than or equal to, greater than *)
  | Cond_g => NLE_ct
  (* parity, parity even *)
  | Cond_p => P_ct
  (* not parity, parity odd *)
  | Cond_np => NP_ct
  end.


Definition transl_instr (f:ident) (i: Asm.instruction) : res instr :=
  match i with
  | Psubl_ri rd n => 
    do rd' <- transl_ireg rd; 
    OK (SUB true (Reg_op rd') (Imm_op (int_to_bits n)))
  | Pleal rd a =>
    do rd' <- transl_ireg rd;
    do a' <- transl_addr_mode a;
    OK (LEA (Reg_op rd') (Address_op a'))
  | Pmovl_mr a rs =>
    do a' <- transl_addr_mode a;
    do rs' <- transl_ireg rs;
    OK (MOV true (Address_op a') (Reg_op rs'))
  | Pmovl_rm rd a =>
    do rd' <- transl_ireg rd;
    do a' <- transl_addr_mode a;
    OK (MOV true (Reg_op rd') (Address_op a'))
  | Ptestl_rr r1 r2 =>
    do r1' <- transl_ireg r1;
    do r2' <- transl_ireg r2;
    OK (TEST true (Reg_op r1') (Reg_op r2'))
  | Pjcc c l =>
    OK (Jcc (transl_cond_type c) (lmap l))
  (* | Pcall_s symb _ => *)
  (*   (* calculate the offset of the call *) *)
  (*   let ofs :=  *)
  (*   OK (CALL true false (Imm_op  *)
  | _ => 
    Error (msg "Instruction not supported")
  end.