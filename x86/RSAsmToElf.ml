(* Translation from RockSalt assembly to ELF files *)
(* Author        : Yuting Wang *)
(* Date Created  : 11-01-2017 *)

open Camlcoq
open Elf
open RockSaltAsm

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

let align n =
  let a = 4 in
  if n >= 0 then (n + a - 1) land (-a) else n land (-a)

let elf_header_size  = 52
let prog_header_size = 32
let sec_header_size  = 40
let num_prog_headers = 2
let num_sec_headers  = 4
let strtab_size      = 24

(* Create the ELF header from a RockSaltAsm program *)
let get_e_entry (p:program) : int =
  Z.to_int (Z.add p.entry_ofs p.text_seg.seg_offset)

let get_e_phoff (p:program) : int = elf_header_size

let get_e_shoff (p:program) : int =
  elf_header_size + num_prog_headers*prog_header_size + 
  (align (Z.to_int p.text_seg.seg_size)) + (align (Z.to_int p.data_seg.seg_size)) +
  strtab_size

let gen_elf_header (p:program) : elf_header =
  create_386_exec_elf_header (get_e_entry p) (get_e_phoff p) (get_e_shoff p)

(* Create the program headers from a RockSaltAsm program *)
let get_text_p_offset (p:program) = 
  elf_header_size + num_prog_headers*prog_header_size

let gen_text_seg (p:program) : program_header =
  {
    p_type     = PT_LOAD;
    p_offset   = get_text_p_offset p;
    p_vaddr    = Z.to_int p.text_seg.seg_offset;
    p_paddr    = Z.to_int p.text_seg.seg_offset;
    p_filesz   = (align (Z.to_int p.text_seg.seg_size));
    p_memsz    = (align (Z.to_int p.text_seg.seg_size));
    p_flags    = [PF_EXEC; PF_READ];
    p_align    = 0x1000
  }

let get_data_p_offset (p:program) = 
  elf_header_size + num_prog_headers*prog_header_size +
  (align (Z.to_int p.text_seg.seg_size))

let gen_data_seg (p:program) : program_header =
  {
    p_type     = PT_LOAD;
    p_offset   = get_data_p_offset p;
    p_vaddr    = Z.to_int p.data_seg.seg_offset;
    p_paddr    = Z.to_int p.data_seg.seg_offset;
    p_filesz   = (align (Z.to_int p.data_seg.seg_size));
    p_memsz    = (align (Z.to_int p.data_seg.seg_size));
    p_flags    = [PF_WRITE; PF_READ];
    p_align    = 0x1000
  }

(* Create the section headers from a RockSalt program *)
let gen_text_sec (p: program) : section_header =
  {
    sh_name       = 0x0b;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_EXECINSTR];
    sh_addr       = Z.to_int p.text_seg.seg_offset;
    sh_offset     = get_text_p_offset p;
    sh_size       = align (Z.to_int p.text_seg.seg_size);
    sh_addralign  = 1;
  }

let gen_data_sec (p: program) : section_header =
  {
    sh_name       = 0x11;
    sh_type       = SHT_PROGBITS;
    sh_flags      = [SHF_ALLOC; SHF_WRITE];
    sh_addr       = Z.to_int p.data_seg.seg_offset;
    sh_offset     = get_data_p_offset p;
    sh_size       = align (Z.to_int p.data_seg.seg_size);
    sh_addralign  = 1;
  }

let get_strtab_sh_offset (p:program) : int =
  elf_header_size + num_prog_headers*prog_header_size + 
    (align (Z.to_int p.text_seg.seg_size)) + (align (Z.to_int p.data_seg.seg_size))

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

(* Create the ELF file from a RockSaltAsm program *)
let gen_elf (p:program) : elf_file =
  {
    ef_header        = gen_elf_header p;
    ef_text_sec      = gen_text_sec p;
    ef_data_sec      = gen_data_sec p;
    ef_shstrtab_sec  = gen_shstrtab_sec p;
    ef_text_seg      = gen_text_seg p;
    ef_data_seg      = gen_data_seg p;
    ef_text          = List.map (fun i -> Z.to_int i) p.machine_code;
    ef_data          = List.map (fun d -> Z.to_int d) p.init_data;
  }

