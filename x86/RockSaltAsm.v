(* Rocksalt assembly program *)
(* Author        : Yuting Wang *)
(* Date Created  : 10-28-2017 *)

Require Import Integers AST.
Require Import X86Model.Encode.
Require Import X86Model.X86Syntax.
Require Import Errors.


(* Segments *)
(* Record segment := mkSegment { *)
(*   seg_offset : int32;  (* offset to the segment in memory*) *)
(*   seg_size : int32; (* size of the segment *)   *)
(* }. *)

Definition ACCUM_LIST (A:Type) := int32 -> list A.

Definition ACCUM_INSTRS := ACCUM_LIST instr.
Definition ACCUM_DATA   := ACCUM_LIST int8.

Definition app_accum_list {A:Type} (l1 l2 : ACCUM_LIST A) :=
  fun data_addr => (l1 data_addr) ++ (l2 data_addr).

Fixpoint flat_map_accum_list {A B:Type} (f: A -> ACCUM_LIST B) (l: list A) : ACCUM_LIST B :=
  match l with 
  | nil => fun data_addr => nil
  | h::t => app_accum_list (f h) (flat_map_accum_list f t)
  end.
  

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
  (* Instructions in the text segment. 
     They are parameterized by the starting offset to the data segment *)
  text_instrs : ACCUM_INSTRS;
  (* Initial data for the data segment.
     They are parameterized by the starting offset to the data segment *)
  init_data : ACCUM_DATA;
  (* The offset to the main function in the text segment *)
  main_ofs  : int32;
}.

Definition program_of_program (p: program) : AST.program fundef gv_info :=
  {| AST.prog_defs := p.(prog_defs);
     AST.prog_public := p.(prog_public);
     AST.prog_main := p.(prog_main) |}.

Coercion program_of_program: program >-> AST.program.