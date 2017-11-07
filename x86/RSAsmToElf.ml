(* Translation from RockSalt assembly to ELF files *)
(* Author        : Yuting Wang *)
(* Date Created  : 11-01-2017 *)

open Camlcoq
open Elf
open X86Syntax
open RockSaltAsm
open RockSaltAsmGen
open Errors
(* open RSDebug *)


(* Create the following start stub *)
  (* call   main *)
  (* mov    %eax,%ebx *)
  (* mov    $0x1,%eax *)
  (* int    $0x80 *)
let call_size = 
  let call = CALL (true, false, Imm_op Z.zero, None) in
  match (encode call) with
  | None -> failwith "Failed to calculate the call size"
  | Some bs -> List.length bs

let create_start_stub (main_ofs: int) : int list  = 
  let call_main = CALL (true, false, Imm_op (Z.of_sint main_ofs), None) in
  let call_main_bytes = 
    match (encode call_main) with
    | None -> failwith "Failed to create the start stub"
    | Some bs -> List.map Z.to_int bs
  in
  let startstub = 
    ['\x89'; '\xc3';                              (* mov    %eax,%ebx *)
     '\xb8'; '\x01'; '\x00'; '\x00'; '\x00';      (* mov    $0x1,%eax *)
     '\xcd'; '\x80']                              (* int    $0x80 *)
  in
  call_main_bytes @ (List.map Char.code startstub)

let startstub_size = List.length (create_start_stub 0)

(* We create a simple ELF file with the following layout
   where every section is aligned at 4 bytes:

   1. ELF Header                          (52 bytes)
   2. Program Headers       
      a) Header for the text segment      (32 bytes)
      b) Header for the data segment      (32 bytes)
   3. Text section (instructions)         (TSZ bytes)
   4. Data section (global variables)     (DSZ bytes)
   5. String table                        (24 bytes)
   6. Section headers
      a) Null header                      (40 bytes)
      a) Header for the text section      (40 bytes)
      a) Header for the data section      (40 bytes)
      a) Header for the string table      (40 bytes)

 *)

let align n a =
  if n >= 0 then (n + a - 1) land (-a) else n land (-a)

let align4 n = align n 4

let elf_header_size  = 52
let prog_header_size = 32
let sec_header_size  = 40
let num_prog_headers = 2
let num_sec_headers  = 4
let strtab_size      = 24

let page_alignment   = 0x1000



(* Calculate the size of text and data segments *)
let prog_instrs_size (p:program) : int = 
  match instr_list_size (p.text_instrs Z.zero) with
  | OK sz -> Z.to_int sz
  | Error _ -> failwith "Failed to decode instructions in 'text_seg_size'"

let text_seg_size (p:program) : int =
  align4 (prog_instrs_size p + startstub_size)

let data_seg_size (p:program) : int =
  align4 (List.length (p.init_data Z.zero))

(* Calcualte the virtual/physical addresses of a segment *)
let calculate_seg_vaddr (seg_file_ofs: int) (seg_size: int) (start_addr: int) 
  : (int * int) =
  (* Set the starting address to be aligned at page boundaries *)
  let start_addr = start_addr / page_alignment * page_alignment in
  (* Calculate the offset to the beginning of a page *)
  let ofs_in_page = seg_file_ofs mod page_alignment in
  (* Get the virtual address the segment should begin with *)
  let vaddr = start_addr + ofs_in_page in
  (* Get the virtual address for the first page after the segment *)
  let new_start_addr = align (vaddr + seg_size) page_alignment in
  (vaddr, new_start_addr)


(* Calcualte the virtual/physical addresses of the text and data segments *)
let get_text_p_offset (p:program) = 
  elf_header_size + num_prog_headers*prog_header_size

let get_data_p_offset (p:program) = 
  elf_header_size + num_prog_headers*prog_header_size +
  (text_seg_size p)

let init_addr = 0x08048000
let cal_text_data_vaddrs (p:program) : (int * int) =
  let (text_vaddr, vaddr_data_start) = 
    calculate_seg_vaddr (get_text_p_offset p) (text_seg_size p) init_addr in
  let (data_vaddr, _) =
    calculate_seg_vaddr (get_data_p_offset p) (data_seg_size p) vaddr_data_start in
  (text_vaddr, data_vaddr)

(* Create the program headers from a RockSaltAsm program *)
let gen_text_seg (p:program) : program_header =
  let text_size = text_seg_size p in
  let (text_vaddr, _) = cal_text_data_vaddrs p in
  {
    p_type     = PT_LOAD;
    p_offset   = get_text_p_offset p;
    p_vaddr    = text_vaddr;
    p_paddr    = text_vaddr;
    p_filesz   = text_size;
    p_memsz    = text_size;
    p_flags    = [PF_EXEC; PF_READ];
    p_align    = page_alignment
  }

let gen_data_seg (p:program) : program_header =
  let data_size = data_seg_size p in
  let (_, data_vaddr) = cal_text_data_vaddrs p in
  {
    p_type     = PT_LOAD;
    p_offset   = get_data_p_offset p;
    p_vaddr    = data_vaddr;
    p_paddr    = data_vaddr;
    p_filesz   = data_size;
    p_memsz    = data_size;
    p_flags    = [PF_WRITE; PF_READ];
    p_align    = page_alignment
  }

(* Create the section headers from a RockSalt program *)
let gen_text_sec (p: program) : section_header =
  let text_size = text_seg_size p in
  let (text_vaddr, _) = cal_text_data_vaddrs p in
  {
    sh_name       = 0x0b;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_EXECINSTR];
    sh_addr       = text_vaddr;
    sh_offset     = get_text_p_offset p;
    sh_size       = text_size;
    sh_addralign  = 1;
  }

let gen_data_sec (p: program) : section_header =
  let data_size = data_seg_size p in
  let (_, data_vaddr) = cal_text_data_vaddrs p in
  {
    sh_name       = 0x11;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_WRITE];
    sh_addr       = data_vaddr;
    sh_offset     = get_data_p_offset p;
    sh_size       = data_size;
    sh_addralign  = 1;
  }

let get_strtab_sh_offset (p:program) : int =
  elf_header_size + num_prog_headers*prog_header_size + 
    (text_seg_size p) + (data_seg_size p)

let gen_shstrtab_sec (p:program) : section_header =
  {
    sh_name       = 0x01;
    sh_type       = SHT_STRTAB;
    sh_flags      = [];
    sh_addr       = 0;
    sh_offset     = get_strtab_sh_offset p;
    sh_size       = 0x17;
    sh_addralign  = 1;
  }


(* Create the ELF header from a RockSaltAsm program *)
let get_e_entry (p:program) : int =
  let (text_vaddr, _) = cal_text_data_vaddrs p in
  text_vaddr + prog_instrs_size p

let get_e_phoff (p:program) : int = elf_header_size

let get_e_shoff (p:program) : int =
  elf_header_size + num_prog_headers*prog_header_size + 
  (text_seg_size p) + (data_seg_size p) + strtab_size

let gen_elf_header (p:program) : elf_header =
  create_386_exec_elf_header (get_e_entry p) (get_e_phoff p) (get_e_shoff p)


(* Encode a list of instructions *)
let rec encode_instr_list (il: instr list) : int list =
  match il with
  | [] -> []
  | i::il' ->
    match (encode i) with
    | None -> failwith "Failed to encode the list of instructions"
    | Some bs ->
        (List.map Z.to_int bs) @ (encode_instr_list il')

(* Create the ELF file from a RockSaltAsm program *)
let gen_elf (p:program) : elf_file =
  (* print_rs_globdefs p; *)
  (* Printf.printf "Length of the text segment: %d\n" (List.length p.machine_code); *)
  let (text_vaddr, data_vaddr) = cal_text_data_vaddrs p in
  let main_ofs   = (Z.to_int p.main_ofs) - (prog_instrs_size p + call_size) in
  let startstub_bytes = create_start_stub main_ofs in
  let instrs_bytes = encode_instr_list (p.text_instrs (Z.of_uint data_vaddr)) in
  {
    ef_header        = gen_elf_header p;
    ef_text_sec      = gen_text_sec p;
    ef_data_sec      = gen_data_sec p;
    ef_shstrtab_sec  = gen_shstrtab_sec p;
    ef_text_seg      = gen_text_seg p;
    ef_data_seg      = gen_data_seg p;
    ef_text          = instrs_bytes @ startstub_bytes;
    ef_data          = List.map (fun d -> Z.to_int d) (p.init_data (Z.of_uint data_vaddr));
  }


