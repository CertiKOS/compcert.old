Require Import Integers AST.
Require Import X86Model.Encode.
Require Import X86Model.X86Syntax.
Require Import Errors.


(* Segments *)
Record segment := mkSegment {
  seg_offset : int32;  (* offset to the segment in memory*)
  seg_size : int32; (* size of the segment *)  
}.

(* Information of global variables *)
Record gv_info := mkInfo {
  gv_offset : int32;  (* offset to the global variable in the data segment*)
  gv_size : int32 (* size of the global variable *)
}.

(* Information of functions *)
Record function := mkFun {
  fun_offset : int32; (* offset to the function in the text segment*)
  fun_size   : int32; (* size of the function *)
}.

Definition fundef := AST.fundef function.

(* Program *)
Record program := mkProg {
  prog_defs: list (ident * option (globdef fundef gv_info));
  prog_public: list ident;
  prog_main: ident;
  (* text segment *)
  text_seg : segment;
  text_instrs : list instr;
  machine_code : list int8;
  data_seg : segment;
}.

Definition program_of_program (p: program) : AST.program fundef gv_info :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.