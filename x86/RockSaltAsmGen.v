(* Translation from CompCert assembly to Rocksalt assembly *)
(* Author        : Yuting Wang *)
(* Date Created  : 10-23-2017 *)

Require Import Coqlib.
Require Import Integers AST Floats.
Require Import Asm.
Require Import X86Model.Encode.
Require Import X86Model.X86Syntax.
Require Import Errors.
Require Import RockSaltAsm.
Require Import Lists.List.
Import ListNotations.

Local Open Scope error_monad_scope.

(* The memory is layouted as follows:
   1. The data segment holding global variables starts at the address 0;
   2. The code segment holding function definitions immediately follows the data segment;
   3. The stack grows from the highest address downwards to address 0. Its size is determined by stack limit of the memory implementation.
*)

(* Transform global variables *)
Definition DMAP_TYPE := ident -> int32.

Definition default_dmap (d:ident) : int32 := Word.zero.


(** Get the size and offset information of the global variables *)
Fixpoint transf_globvars (gdefs : list (ident * option (globdef Asm.fundef unit))) (ofs:int32) 
  (daccum: list (ident * option (globvar gv_info))) 
  : int32 * list (ident * option (globvar gv_info)) :=
  match gdefs with
  | nil =>  (ofs, daccum)
  | ((id, None) :: gdefs') =>
    transf_globvars gdefs' ofs daccum
  | ((_, Some (Gfun _)) :: gdefs') =>
    transf_globvars gdefs' ofs daccum
  | ((id, Some (Gvar v)) :: gdefs') =>
    let sz := Word.repr (init_data_list_size (gvar_init v)) in
    let info := mkInfo ofs sz in
    let v' := mkglobvar info v.(gvar_init) v.(gvar_readonly) v.(gvar_volatile) in
    transf_globvars gdefs' (Word.add ofs sz) ((id, Some v')::daccum)
  end.

Definition update_dmap (dmap: DMAP_TYPE) (d:ident)  (ofs:int32) : DMAP_TYPE :=
  (fun d' => (if ident_eq d' d then ofs 
           else dmap d')).

Fixpoint gvars_to_dmap (l: list (ident * option (globvar gv_info))) : DMAP_TYPE :=
  match l with
  | nil => default_dmap
  | (id, None) :: l' => (gvars_to_dmap l')
  | (id, Some v)::l' => 
    update_dmap (gvars_to_dmap l') id v.(gvar_info).(gv_offset)
  end.


(** Transform the initial data **)


(* Translation of compcert integers to bits *)
Fixpoint nth_byte (v:int) (n:nat) : int :=
  match n with
  | O =>
    Int.and v (Int.repr 255)
  | S n' =>
    nth_byte (Int.divu v (Int.repr 256)) n'
  end.

Fixpoint nth_byte_64 (v:Integers.int64) (n:nat) : Integers.int64 :=
  match n with
  | O =>
    Int64.and v (Int64.repr 255)
  | S n' =>
    nth_byte_64 (Int64.divu v (Int64.repr 256)) n'
  end.
  
Definition int32_to_bytes (i32:int) :=
  [nth_byte i32 0; nth_byte i32 1; nth_byte i32 2; nth_byte i32 3].

Definition int16_to_bytes (i16:int) :=
  [nth_byte i16 0; nth_byte i16 1].

Definition int64_to_bytes (i64:Integers.int64) :=
  [nth_byte_64 i64 0; nth_byte_64 i64 1; nth_byte_64 i64 2; nth_byte_64 i64 3;
   nth_byte_64 i64 4; nth_byte_64 i64 5; nth_byte_64 i64 6; nth_byte_64 i64 7].

Definition n_zeros (n:nat) : list int8 :=
  List.map (fun _ => Word.zero) (seq 1 n).

Definition transl_init_data (dmap: DMAP_TYPE) (idata: AST.init_data) : ACCUM_DATA :=
  match idata with
  | Init_int8 i => fun data_addr => [Word.repr (Int.unsigned i)]
  | Init_int16 i => fun data_addr => List.map (fun i => Word.repr (Int.unsigned i)) (int16_to_bytes i)
  | Init_int32 i => fun data_addr => List.map (fun i => Word.repr (Int.unsigned i)) (int32_to_bytes i)
  | Init_int64 i => fun data_addr => List.map (fun i => Word.repr (Int64.unsigned i)) (int64_to_bytes i)
  | Init_float32 f => fun data_addr => List.map (fun i => Word.repr (Int64.unsigned i)) 
                              (int64_to_bytes (Float.to_bits (Float.of_single f)))
  | Init_float64 f => fun data_addr => List.map (fun i => Word.repr (Int64.unsigned i)) 
                              (int64_to_bytes (Float.to_bits f))
  | Init_space n => fun data_addr => n_zeros (compcert.lib.Coqlib.nat_of_Z n)
  | Init_addrof id ofs =>
    fun data_addr => 
    let i32 := Word.add data_addr (Word.add (dmap id) (Word.repr (Ptrofs.unsigned ofs))) in
    let i32' := Int.repr (Word.unsigned i32) in
    List.map (fun i => Word.repr (Int.unsigned i)) (int32_to_bytes i32')
  end.

Fixpoint collect_init_data (dmap: DMAP_TYPE) (gvars: list (ident * option (globvar gv_info))) : ACCUM_DATA :=
  match gvars with
  | nil => fun data_addr => nil
  | (_,v)::gvars' =>
    let l' := collect_init_data dmap gvars' in
    match v with
    | None => l'
    | Some v => 
      let init_bytes := flat_map_accum_list (transl_init_data dmap) v.(gvar_init) in
      app_accum_list init_bytes l'
    end
  end.


(* Transform functions and instructions *)
Definition no_prefix : prefix := mkPrefix None None false false.

Definition encode ins := x86_encode no_prefix ins.

(* Fixpoint encode_instr_list (il: list instr) : res (list int8) := *)
(*   match il with *)
(*   | nil => OK nil *)
(*   | i::il' =>  *)
(*     match (encode i) with *)
(*     | None => Error (msg "Encoding instruction list fails") *)
(*     | Some el =>  *)
(*       do eil <- encode_instr_list il'; *)
(*       OK (el ++ eil) *)
(*     end *)
(*   end. *)


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
  (Word.repr (Int.unsigned i)).

Definition ptrofs_to_bits (i:Ptrofs.int) : int32 :=
  (Word.repr (Ptrofs.unsigned i)).

(* Translate the types of test conditions *)

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


Definition FMAP_TYPE := ident -> int32.
Definition LMAP_TYPE := ident -> label -> int32.

Definition update_lmap (lmap: LMAP_TYPE) (f:ident) (l:label) (ofs:int32) : LMAP_TYPE :=
  (fun f' l' => 
     if ident_eq f' f then
       (if ident_eq l' l then ofs 
        else lmap f' l')
     else lmap f' l').

Definition update_fmap (fmap: FMAP_TYPE) (f:ident) (ofs:int32) : FMAP_TYPE :=
  (fun f' => 
     if ident_eq f' f then ofs
     else fmap f').


Definition instr_size (i:instr) : res int32 :=
  match (encode i) with
  | None => Error (msg "instruction has no encoding")
  | Some l => OK (Word.repr (Z.of_nat (length l)))
  end.

Fixpoint instr_list_size (il:list instr) : res int32 :=
  match il with
  | nil => OK Word.zero
  | i::il' =>
    do isz <- instr_size i;
    do ilsz <- instr_list_size il';
    OK (Word.add isz ilsz)
  end.


Section TRANSL.
(* The starting address of the data segments for  *)
(*    holding initialized global data *)
(* Variable data_addr : int32. *)
(* Mapping from global identifiers to their offsets in *)
(*    the data segment *)
Variable dmap : DMAP_TYPE.

(* (* The starting address of the code segment *) *)
(* Parameter text_addr : int32. *)
(* (* Mapping from labels in functions to their offsets in the code segment *) *)
(* Parameter lmap : ident -> label -> option int32. *)
(* (* Mapping from function names to their offsets in the code segment *) *)
(* Parameter fmap : ident -> option int32. *)

(* Translate the scale *)
Definition transl_scale (s:Z) : res scale :=
  match s with
  | 1 => OK Scale1
  | 2 => OK Scale2
  | 4 => OK Scale4
  | 8 => OK Scale8
  | _ => Error (msg "Translation of scale failed")
  end.

(* Translate the addressing mode *)
Definition transl_addr_mode (m: addrmode) : res (int32 -> address) :=
  match m with
  | Addrmode b ofs const =>
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
           do sc <- transl_scale scale;
             OK (Some (sc, r'))
         end;
    OK (fun data_addr =>
      let disp :=
        match const with 
        | inl disp' => (Word.repr disp')
        | inr (ident,ptrofs) => 
          (Word.add data_addr (Word.add (dmap ident) (ptrofs_to_bits ptrofs)))
        end in
      {|
        addrDisp := disp;
        addrBase := base_reg;
        addrIndex := index;
      |})
  end.




(* The translation of an individual instruction. It takes the following arguments as inputs

   1. fmap: the mapping from function identifiers to their offsets in the text segment;
   2. lmap: the mapping from labels in each function to their offsets in the text segment;
   3. f: the function in which the instruction resides;
   4. i: the instruction to be translated;
   5. ofs: the offset at which the resulting instructions should start in the text segment;

   It generates a list of instructions (possibly empty) and updates lmap (if i is Plabel).
*)

Definition transl_instr (fmap: FMAP_TYPE) (lmap: LMAP_TYPE)
           (f:ident) (i: Asm.instruction) (ofs: int32) : 
  res (ACCUM_INSTRS * LMAP_TYPE)  :=
  match i with
  | Pxorl_r rd =>
    do rd' <- transl_ireg rd;
      OK (fun data_addr => [XOR true (Reg_op rd') (Reg_op rd')],lmap)
  | Paddl_ri rd n =>
    do rd' <- transl_ireg rd; 
    OK (fun data_addr => [ADD true (Reg_op rd') (Imm_op (int_to_bits n))], lmap)
  | Psubl_ri rd n => 
    do rd' <- transl_ireg rd; 
    OK (fun data_addr => [SUB true (Reg_op rd') (Imm_op (int_to_bits n))], lmap)
  | Psubl_rr rd r1 => 
    do rd' <- transl_ireg rd; 
    do r1' <- transl_ireg r1; 
    OK (fun data_addr => [SUB true (Reg_op rd') (Reg_op r1')], lmap)
  | Pleal rd a =>
    do rd' <- transl_ireg rd;
    do a' <- transl_addr_mode a;
    OK (fun data_addr => [LEA (Reg_op rd') (Address_op (a' data_addr))], lmap)
  | Pmovl_ri rd n =>
    do rd' <- transl_ireg rd;
    OK (fun data_addr => [MOV true (Reg_op rd') (Imm_op (int_to_bits n))], lmap)
  | Pmov_rr rd r1 =>
    do rd' <- transl_ireg rd;
    do r1' <- transl_ireg r1;
    OK (fun data_addr => [MOV true (Reg_op rd') (Reg_op r1')],lmap)
  | Pmovl_mr a rs =>
    do a' <- transl_addr_mode a;
    do rs' <- transl_ireg rs;
    OK (fun data_addr => [MOV true (Address_op (a' data_addr)) (Reg_op rs')],lmap)
  | Pmov_mr_a a rs =>
    do a' <- transl_addr_mode a;
    do rs' <- transl_ireg rs;
    OK (fun data_addr => [MOV true (Address_op (a' data_addr)) (Reg_op rs')],lmap)
  | Pmovl_rm rd a =>
    do rd' <- transl_ireg rd;
    do a' <- transl_addr_mode a;
    OK (fun data_addr => [MOV true (Reg_op rd') (Address_op (a' data_addr))],lmap)
  | Pmov_rm_a rd a =>
    do rd' <- transl_ireg rd;
    do a' <- transl_addr_mode a;
    OK (fun data_addr => [MOV true (Reg_op rd') (Address_op (a' data_addr))],lmap)
  | Ptestl_rr r1 r2 =>
    do r1' <- transl_ireg r1;
    do r2' <- transl_ireg r2;
    OK (fun data_addr => [TEST true (Reg_op r1') (Reg_op r2')],lmap)
  | Pjcc c l =>
    (* calculate the size of the instruction *)
    do isz <- instr_size (Jcc (transl_cond_type c) Word.zero);
    (* calculate the offset of the jump *)
    let rel_ofs := Word.sub (lmap f l) (Word.add ofs isz) in
    OK (fun data_addr => [Jcc (transl_cond_type c) rel_ofs],lmap)
  | Pcall_s symb _ =>
    (* calculate the size of the instruction *)
    do isz <- instr_size (CALL true false (Imm_op Word.zero) None);
    (* calculate the offset of the call *)
    let rel_ofs := Word.sub (fmap symb) (Word.add ofs isz) in
    OK (fun data_addr => [CALL true false (Imm_op rel_ofs) None],lmap)
  (* | Pcall_r r _ => *)
  (*   do r' <- transl_ireg r; *)
  (*   OK (CALL true false (Reg_op r') None) *)
  | Pret =>
    OK (fun data_addr => [RET true None],lmap)
  | Pimull_rr rd r1 =>
    do rd' <- transl_ireg rd;
    do r1' <- transl_ireg r1;
    OK (fun data_addr => [IMUL false (Reg_op rd') (Some (Reg_op r1')) None],lmap)
  | Pjmp_l l =>
    (* calculate the size of the instruction *)
    do isz <- instr_size (JMP true false (Imm_op Word.zero) None);
    (* calculate the offset of the jump *)
    let rel_ofs := Word.sub (lmap f l) (Word.add ofs isz) in
    OK (fun data_addr => [JMP true false (Imm_op rel_ofs) None],lmap)
  | Pcmpl_rr r1 r2 =>
    do r1' <- transl_ireg r1;
    do r2' <- transl_ireg r2;
    OK (fun data_addr => [CMP true (Reg_op r1') (Reg_op r2')],lmap)
  | Pcmpl_ri r1 n =>
    do r1' <- transl_ireg r1;
    OK (fun data_addr => [CMP true (Reg_op r1') (Imm_op (int_to_bits n))],lmap)
  | Pcltd =>
    OK (fun data_addr => [CDQ], lmap)
  | Pidivl r1 => 
    do r1' <- transl_ireg r1;
    OK (fun data_addr => [IDIV true (Reg_op r1')],lmap)
  | Plabel l =>
    OK (fun data_addr => [], update_lmap lmap f l ofs)
  | _ => 
    Error (MSG (Asm.instr_to_string i) :: MSG " not supported" :: nil)
  end.

Fixpoint transl_instr_list (fmap: FMAP_TYPE) (lmap: LMAP_TYPE)
           (f:ident) (il: list instruction) (ofs: int32) (accum : ACCUM_INSTRS) 
  : res (ACCUM_INSTRS * LMAP_TYPE * int32)  :=
  match il with
  | nil => OK (accum, lmap, ofs)
  | i::il' => 
    do (instrs, lmap') <-
       transl_instr fmap lmap f i ofs;
    do isz <- instr_list_size (instrs Word.zero);
    transl_instr_list fmap lmap' f il' (Word.add ofs isz) 
                      (app_accum_list instrs accum)
  end.

Definition transl_function (fmap: FMAP_TYPE) (lmap: LMAP_TYPE)
         (f:ident) (code:Asm.code) (ofs:int32) (accum: ACCUM_INSTRS)
  : res (ACCUM_INSTRS * FMAP_TYPE * LMAP_TYPE * int32) := 
  do (im, ofs') <- transl_instr_list fmap lmap f code ofs accum;
  let (accum', lmap') := im in
  OK (accum', update_fmap fmap f ofs, lmap', ofs').


(* Collect the functions that needs to be translated *)
Fixpoint transf_globfuns (fmap: FMAP_TYPE) (lmap: LMAP_TYPE) 
  (gdefs : list (ident * option (globdef Asm.fundef unit))) (ofs:int32) 
  (iaccum: ACCUM_INSTRS) (daccum: list (ident * option RockSaltAsm.fundef))
  : res (ACCUM_INSTRS * list (ident * option RockSaltAsm.fundef) * FMAP_TYPE * LMAP_TYPE * int32) :=
  match gdefs with
  | nil =>  OK (iaccum, daccum, fmap, lmap, ofs)
  | ((id, None) :: gdefs') =>
    transf_globfuns fmap lmap gdefs' ofs iaccum daccum
  | ((id, Some (Gvar _)) :: gdefs') =>
    transf_globfuns fmap lmap gdefs' ofs iaccum daccum
  | ((id, Some (Gfun fn)) :: gdefs') =>
    match fn with
    | Internal f => 
      do r <- transl_function fmap lmap id f.(fn_code) ofs iaccum;
      let '(il, fmap', lmap', ofs') := r in
      let f' := mkFun ofs (Word.sub ofs' ofs) in
      transf_globfuns fmap' lmap' gdefs' ofs'
                      il
                      ((id, Some (Internal f')) :: daccum)
    | External ef => 
      transf_globfuns fmap lmap gdefs' ofs iaccum 
                      ((id, Some (External ef)) :: daccum)
    end
  end.

End TRANSL.

  

Definition default_fmap (f:ident) : int32 := Word.zero.
Definition default_lmap (f:ident) (l:label) : int32 := Word.zero.

Definition align_int32 (n: int32) (amount: Z) :int32 :=
  Word.repr (align (Word.unsigned n) amount).


Definition transf_program (p: Asm.program) : res RockSaltAsm.program :=
  (* Transform the global variables *)
  let (data_seg_size, gvars) := 
      transf_globvars p.(AST.prog_defs) Word.zero [] in
  (* Calculate information of the data segment *)
  let dmap := gvars_to_dmap gvars in
  let init_data := collect_init_data dmap gvars in
  (* The first pass of functions gives
     the mapping for functions and labels *)
  do r <- transf_globfuns dmap
             default_fmap default_lmap 
             p.(AST.prog_defs) Word.zero (fun data_addr => []) [];
    let '(_,_,fmap,lmap,_) := r in
  (* The second pass of functions finishes
     the translation using those mappings *)
  do r <- transf_globfuns dmap
             fmap lmap
             p.(AST.prog_defs) Word.zero (fun data_addr => []) [];
  let '(instrs,gfuns,fmap,_,code_seg_size) := r in
  (* Compose the results to form the RockSalt program *)
  let gvars_defs :=
      List.map (fun (e: ident * option (globvar gv_info)) =>
                  let (id,gv) := e in
                  (id, match gv with
                       | None => None
                       | Some gv => Some (Gvar gv)
                       end))
               gvars in
  let gfuns_defs :=
      List.map (fun (e: ident * option fundef) => 
                  let (id,fn) := e in
                  (id, match fn with
                       | None => None
                       | Some fn => Some (Gfun fn)
                       end))
               gfuns in
  let tinstrs := fun data_addr => List.rev (instrs data_addr) in
  (* do instrs_code <- encode_instr_list tinstrs; *)
  (* do stub_code <- create_start_stub (fmap (p.(AST.prog_main))) code_seg_size; *)
  (* let mach_code := instrs_code ++ stub_code in *)
  (* let text_addr := align_int32 (Word.add data_addr data_seg_size) 4 in *)
  OK {|
    prog_defs       := gvars_defs ++ gfuns_defs;
    prog_public     := p.(AST.prog_public);
    prog_main       := p.(AST.prog_main);
    (* text_seg        := mkSegment text_addr (Word.repr (Z_of_nat (length mach_code))); *)
    text_instrs     := tinstrs;
    (* machine_code    := mach_code; *)
    (* entry_ofs       := code_seg_size; *)
    (* data_seg        := mkSegment data_addr data_seg_size; *)
    init_data       := init_data;
    main_ofs        := fmap (p.(AST.prog_main));
  |}.