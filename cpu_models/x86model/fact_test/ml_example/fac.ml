(* An example of generating machine code from 
   a hand-written factorial assembly program in Rocksalt *)
(* Author        : Yuting Wang *)
(* Date Created  : 10-23-2017 *)

open Printf
open Encode
open X86Syntax
open Elf

(* No prefix *)
let null_prefix = {lock_rep = None; seg_override = None; op_override = false; addr_override = false}

(* Convert an integer representing a byte to hexadecimal *)
let byte_dec_to_hex byte =
  sprintf "%02X" byte

(* Encode an instruction with no prefix into hex *)
let encode instr = 
  let bits = x86_encode null_prefix instr in 
  match bits with
  | None -> failwith ("Encoding failed")
  | Some bits -> List.map Big.to_int bits

(* Register operands *)
let eax = Reg_op EAX
let ebx = Reg_op EBX
let ecx = Reg_op ECX
let edx = Reg_op EDX
let edi = Reg_op EDI
let ebp = Reg_op EBP
let esp = Reg_op ESP

let imm n = Imm_op (Big.of_int n)
(* offset to DS *)
let offset i = Offset_op (Big.of_int i)

let addr_reg_ofs r ofs = 
  match r with
  | Reg_op r ->
     Address_op {addrDisp = Big.of_int ofs; addrBase = Some r; addrIndex = None}
  | _ -> failwith "Not a register!"
let addr_glob i =
  Address_op {addrDisp = Big.of_int i; addrBase = None; addrIndex = None}

let je l = Jcc (E_ct, Big.of_int l)

(* Encode a list of Rocksalt instructions into a list of bytes *)
let encode_accum (einstrs, n) instr =
  try
    let ei = encode instr in
    (ei :: einstrs, n+1)
  with
    Failure msg -> failwith (sprintf "Encoding failed at the %d-th instruction" n)

let encode_instrs instrs =
  let (l, _) = List.fold_left encode_accum ([], 0) instrs in
  List.rev l

(* Write encoded instructions to a binary file *)
let write_ecd_instrs file_name little_endian ecd_instrs = 
  let dump_channel = open_out_bin file_name in
  let ecd_instrs' = if little_endian then ecd_instrs
                    else List.map (fun b -> List.rev b) ecd_instrs 
  in
  List.iter (fun instr -> List.iter (fun b -> output_byte dump_channel b) instr) ecd_instrs';
  close_out dump_channel


(* Code of fac *)
let fac_code =
  [
(* fac: *)
    SUB  (true, esp, imm 28);
    LEA  (eax, addr_reg_ofs esp 32);
    MOV  (true, addr_reg_ofs esp 4, eax);
    MOV  (true, addr_reg_ofs esp 8, ebx);
    MOV  (true, ebx, addr_reg_ofs eax 0);
    TEST (true, ebx, ebx);
    je   0x10;
    LEA  (eax, addr_reg_ofs ebx (-1));
    MOV  (true, addr_reg_ofs esp 0, eax);
    CALL (true, false, imm (-0x20), None);
    IMUL (false, ebx, Some eax, None);
    JMP  (true, false, imm 0x5, None);
(* .L100: *)
    MOV  (true, ebx, (imm 1));
(* .L101: *)
    MOV  (true, eax, ebx);
    MOV  (true, ebx, addr_reg_ofs esp 8);
    ADD  (true, esp, imm 28);
    RET  (true, None);
(* End of fac *)
(* main: *)
    SUB  (true, esp, imm 12);
    LEA  (eax, addr_reg_ofs esp 16);
    MOV  (true, addr_reg_ofs esp 4, eax);
    MOV  (true, eax, imm 4);
    MOV  (true, addr_reg_ofs esp 0, eax);
    CALL (true, false, imm (-0x4C), None);
    MOV  (true, addr_glob 0x080490d8, eax);
    ADD  (true, esp, imm 12);
    RET  (true, None)
  ]

let fac_bytes = encode_instrs fac_code
  
let fac_dump_file = "fac_rs"
let () = write_ecd_instrs fac_dump_file true fac_bytes

(* elf header *)
let fac_elf_header = create_386_exec_elf_header 0x80480ca 52 244

(* .text segment *)
let fac_text_seg =
  {
    p_type     = PT_LOAD;
    p_offset   = 0x74;
    p_vaddr    = 0x08048074;
    p_paddr    = 0x08048074;
    p_filesz   = 0x64;
    p_memsz    = 0x64;
    p_flags    = [PF_EXEC; PF_READ];
    p_align    = 0x1000
  }

(* .data segment *)
let fac_data_seg =
  {
    p_type     = PT_LOAD;
    p_offset   = 0xd8;
    p_vaddr    = 0x080490d8;
    p_paddr    = 0x080490d8;
    p_filesz   = 4;
    p_memsz    = 4;
    p_flags    = [PF_WRITE; PF_READ];
    p_align    = 0x1000
  }

(* section headers *)
let fac_text_sec = {
    sh_name       = 0x0b;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_EXECINSTR];
    sh_addr       = 0x08048074;
    sh_offset     = 0x74;
    sh_size       = 0x64;
    sh_addralign  = 1;
  }

let fac_data_sec = {
    sh_name       = 0x11;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_WRITE];
    sh_addr       = 0x080490d8;
    sh_offset     = 0xD8;
    sh_size       = 0x4;
    sh_addralign  = 4;
  }

let fac_shstrtab_sec = {
    sh_name       = 0x01;
    sh_type       = SHT_STRTAB;
    sh_flags      = [];
    sh_addr       = 0;
    sh_offset     = 0xDC;
    sh_size       = 0x17;
    sh_addralign  = 1;
  }


(* Elf file *)
let call_main = CALL (true, false, imm (-0x27), None)
let call_main_bytes = encode call_main
let startstub = 
 ['\x89'; '\xc3';                              (* mov    %eax,%ebx *)
  '\xb8'; '\x01'; '\x00'; '\x00'; '\x00';      (* mov    $0x1,%eax *)
  '\xcd'; '\x80']                              (* int    $0x80 *)
let startstub_bytes = 
  call_main_bytes @ (List.map Char.code startstub)


let fac_elf = {
    ef_header        = fac_elf_header;
    ef_text_sec      = fac_text_sec;
    ef_data_sec      = fac_data_sec;
    ef_shstrtab_sec  = fac_shstrtab_sec;
    ef_text_seg      = fac_text_seg;
    ef_data_seg      = fac_data_seg;
    ef_text          = (List.concat fac_bytes) @ startstub_bytes;
    ef_data          = [0; 0; 0; 0];
  }

let () = write_elf "elf_tst" fac_elf

