(* A generator of ELF files from machine code *)
(* Author        : Yuting Wang *)
(* Date Created  : 10-23-2017 *)

(**** Generate the ELF file *****)

let rec gen_list size init =
  if size = 0 then []
  else init :: (gen_list (size-1) init)

let array_overwrite asrc adest offset =
  Array.iteri (fun i e -> Array.set adest (i+offset) e) asrc

(* Function composition *)
let (<|) f g = (fun x -> f (g x))

let rec nth_byte v n =
  if n = 0 then 
    v land 0xFF
  else
    nth_byte (v / 0x100) (n-1)
  
let int32_to_bytes i32 little_endian =
  let bytes = [nth_byte i32 0; nth_byte i32 1; nth_byte i32 2; nth_byte i32 3]
  in 
  if little_endian then bytes else List.rev bytes

let int16_to_bytes i16 little_endian =
  let bytes = [nth_byte i16 0; nth_byte i16 1]
  in 
  if little_endian then bytes else List.rev bytes


  
(* ELF header *)
type elf_data_encoding = | ELFDATANONE 
                         | ELFDATA2LSB   (* little endian *) 
                         | ELFDATA2MSB   (* big endian *)
let ef_encoding_to_byte ecd = 
  match ecd with
  | ELFDATANONE -> 0
  | ELFDATA2LSB -> 1
  | ELFDATA2MSB -> 2

type elf_file_class = | ELFCLASSNONE 
                      | ELFCLASS32  (* 32-bit file *) 
                      | ELFCLASS64  (* 64-bit file *)
let ef_class_to_byte cls =
  match cls with
  | ELFCLASSNONE -> 0
  | ELFCLASS32 -> 1
  | ELFCLASS64 -> 2

type elf_file_type = | ET_NONE 
                     | ET_REL    (* Relocatable *)
                     | ET_EXEC   (* Executable *)
                     | ET_DYN    (* Shared object *)
                     | ET_CORE   (* Core file *)
let ef_type_to_int16 typ =
  match typ with
  | ET_NONE -> 0
  | ET_REL -> 1
  | ET_EXEC -> 2
  | ET_DYN -> 3
  | ET_CORE -> 4

type elf_machine = | EM_NONE | EM_386
let ef_machine_to_int16 mach =
  match mach with
  | EM_NONE -> 0
  | EM_386 -> 3

type elf_header =
  {
    e_encoding   : elf_data_encoding;
    e_class      : elf_file_class;
    e_type       : elf_file_type;
    e_machine    : elf_machine;
    e_entry      : int; (* entry point of the program *)
    e_phoff      : int; (* offset to the first program header *)
    e_shoff      : int; (* offset to the first section header *)
    e_flags      : int; 
    e_ehsize     : int; (* size of the elf header, i.e., 52 bytes *)
    e_phentsize  : int; (* size of a program header *)
    e_phnum      : int; (* number of program headers *)
    e_shentsize  : int; (* size of a section header *)
    e_shnum      : int; (* number of section headers *)
    e_shstrndx   : int; (* index to the section header for the string table *)
  }
(* indexes to the array e_ident *)
let ei_mag0 = 0
let ei_mag1 = 1
let ei_mag2 = 2
let ei_mag3 = 3
let ei_class = 4
let ei_data = 5
let ei_version = 6
let ei_pad = 7
let ei_size = 16


(* Section header *)
type section_type = | SHT_NULL
                    | SHT_PROGBITS  (* program *)
                    | SHT_STRTAB    (* string table *)
                    | SHT_NOBITS    (* unintialized data *)
let sec_type_to_int32 typ =
  match typ with
  | SHT_NULL     -> 0
  | SHT_PROGBITS -> 1
  | SHT_STRTAB   -> 3
  | SHT_NOBITS   -> 8

type section_flag = | SHF_WRITE       (* writable section *)
                    | SHF_ALLOC       (* section will be allocated in memory *)
                    | SHF_EXECINSTR   (* executable section *)
let sec_flag_to_int32 flag =
  match flag with
  | SHF_WRITE -> 1
  | SHF_ALLOC -> 2
  | SHF_EXECINSTR -> 4
let sec_flags_to_int32 flags =
  let bytes = List.map sec_flag_to_int32 flags in
  List.fold_left (fun acc byte -> acc lor byte) 0 bytes


type section_header =
  {
    sh_name        : int;   (* offset in the string table to the name of the section *)
    sh_type        : section_type; 
    sh_flags       : section_flag list;
    sh_addr        : int;   (* starting address of the section in the memory *)
    sh_offset      : int;   (* offset to the beginning of the section in the file *)
    sh_size        : int;   (* size of the section *)
    sh_addralign   : int;   (* alignment of the section *)
  }
let sec_header_to_bytes sh little_endian =
  (int32_to_bytes sh.sh_name little_endian) @
  (int32_to_bytes (sec_type_to_int32 sh.sh_type) little_endian) @
  (int32_to_bytes (sec_flags_to_int32 sh.sh_flags) little_endian) @
  (int32_to_bytes sh.sh_addr little_endian) @
  (int32_to_bytes sh.sh_offset little_endian) @
  (int32_to_bytes sh.sh_size little_endian) @
  (int32_to_bytes 0 little_endian) @ (* link *)
  (int32_to_bytes 0 little_endian) @ (* info *)
  (int32_to_bytes sh.sh_addralign little_endian) @ 
  (int32_to_bytes 0 little_endian) (* entsize *)

let null_section_header = {
    sh_name       = 0;
    sh_type       = SHT_NULL;
    sh_flags      = [];
    sh_addr       = 0;
    sh_offset     = 0;
    sh_size       = 0;
    sh_addralign  = 0;
  }

(* String table *)
(** The default strtab is ' .shstrtab .text .data' *)
let default_strtab = 
 ['\x00'; '.'; 's'; 'h'; 's'; 't'; 'r'; 't'; 'a'; 'b';
  '\x00'; '.'; 't'; 'e'; 'x'; 't';
  '\x00'; '.'; 'd'; 'a'; 't'; 'a']
let default_strtab_bytes =
  List.map Char.code default_strtab

(* Program header *)
type segment_type = | PT_NULL 
                    | PT_LOAD  (* the program segment is loadable to the memory *)
let seg_type_to_int32 typ =
  match typ with
  | PT_NULL -> 0
  | PT_LOAD -> 1

type segment_flag = | PF_EXEC   (* executable *)
                    | PF_WRITE  (* writable *)
                    | PF_READ   (* readable *)
let seg_flag_to_int32 flag =
  match flag with
  | PF_EXEC  -> 1
  | PF_WRITE -> 2
  | PF_READ  -> 4
let seg_flags_to_int32 flags =
  let bytes = List.map seg_flag_to_int32 flags in
  List.fold_left (fun acc byte -> acc lor byte) 0 bytes


type program_header =
  {
    p_type   : segment_type;
    p_offset : int;   (* offset to the beginning of the segment in the file *)
    p_vaddr  : int;   (* the starting address of the segment in the virtual memory *)
    p_paddr  : int;   (* the starting address of the segment in the physical memory *)  
    p_filesz : int;   (* the size of the segment *)
    p_memsz  : int;   (* the size of the memory region the segment occupies, must be no less than p_filesz *)
    p_flags  : segment_flag list;
    p_align  : int;   (* alignment of the segment *)
  }
let prog_header_to_bytes ph little_endian =
  (int32_to_bytes (seg_type_to_int32 ph.p_type) little_endian) @
  (int32_to_bytes ph.p_offset little_endian) @
  (int32_to_bytes ph.p_vaddr little_endian) @
  (int32_to_bytes ph.p_paddr little_endian) @
  (int32_to_bytes ph.p_filesz little_endian) @
  (int32_to_bytes ph.p_memsz little_endian) @
  (int32_to_bytes (seg_flags_to_int32 ph.p_flags) little_endian) @
  (int32_to_bytes ph.p_align little_endian)


(* Elf file *)

(** The simple elf file we have only has three sections:

    1. The .text section holding the program text (executable instructions)
    2. The .data  section holding initialized global data
    3. The .shstrtab section holding the string table

    Correspondently, we have two program segments:

    1. The segment containing executable instruction
    2. The segment for global data

    We may later add more sections and segments.
**)

type elf_file = {
    ef_header       : elf_header;           (* ELF header *)
    ef_text_sec     : section_header;       (* section headers *)
    ef_data_sec     : section_header;
    ef_shstrtab_sec : section_header;
    ef_text_seg     : program_header;       (* program headers *)
    ef_data_seg     : program_header;       
    ef_text         : int list;             (* bytes of the text section *)
    ef_data         : int list;             (* bytes of the data section *)
  }

let elf_file_size ef =
  let h = ef.ef_header in
  h.e_shoff + h.e_shentsize * h.e_shnum

let elf_prog_headers_size ef =
  let h = ef.ef_header in
  h.e_phentsize * h.e_phnum


(* Encoding elf data structure to an array of bytes *)
let elf_header_to_bytes eh little_endian =
  let l = 
  (* e_ident array *)
  [0x7f; (Char.code 'E'); (Char.code 'L'); (Char.code 'F');
   (ef_class_to_byte eh.e_class);
   (ef_encoding_to_byte eh.e_encoding);
   1 (* version is current *)
  ] @
  gen_list (ei_size-ei_pad) 0 @
  (int16_to_bytes (ef_type_to_int16 eh.e_type) little_endian) @
  (int16_to_bytes (ef_machine_to_int16 eh.e_machine) little_endian) @
  (int32_to_bytes  1 little_endian) @ (* version is current *)
  (int32_to_bytes  eh.e_entry      little_endian) @
  (int32_to_bytes  eh.e_phoff      little_endian) @
  (int32_to_bytes  eh.e_shoff      little_endian) @
  (int32_to_bytes  eh.e_flags      little_endian) @
  (int16_to_bytes  eh.e_ehsize     little_endian) @
  (int16_to_bytes  eh.e_phentsize  little_endian) @
  (int16_to_bytes  eh.e_phnum      little_endian) @
  (int16_to_bytes  eh.e_shentsize  little_endian) @
  (int16_to_bytes  eh.e_shnum      little_endian) @
  (int16_to_bytes  eh.e_shstrndx   little_endian)
  in
  Array.of_list l

let elf_program_headers_to_bytes ef little_endian =
  let bytes = (prog_header_to_bytes ef.ef_text_seg little_endian) @
              (prog_header_to_bytes ef.ef_data_seg little_endian) in
  Array.of_list bytes

let elf_section_headers_to_bytes ef little_endian =
  let bytes = (sec_header_to_bytes null_section_header little_endian) @
              (sec_header_to_bytes ef.ef_text_sec little_endian) @
              (sec_header_to_bytes ef.ef_data_sec little_endian) @
              (sec_header_to_bytes ef.ef_shstrtab_sec little_endian) in
  Array.of_list bytes


let elf_to_bytes ef = 
  let sz = elf_file_size ef in
  let fimg = Array.make sz 0 in
  (* Endian of the ELF file *)
  let little_endian = (ef.ef_header.e_encoding = ELFDATA2LSB) in
  (* Write the header *)
  let himg = elf_header_to_bytes ef.ef_header little_endian in
  array_overwrite himg fimg 0;
  (* Write the program headers *)
  let phimg = elf_program_headers_to_bytes ef little_endian in
  (* Printf.printf "phimg size: %d\n ph encoding size: %d\n" (elf_prog_headers_size ef) (Array.length phimg); *)
  (* assert (Array.length phimg = elf_prog_headers_size ef); *)
  array_overwrite phimg fimg ef.ef_header.e_phoff;
  (* Write the section headers *)
  let shimg = elf_section_headers_to_bytes ef little_endian in
  array_overwrite shimg fimg ef.ef_header.e_shoff;
  (* Write the string table *)
  let strtabimg = Array.of_list default_strtab_bytes in
  array_overwrite strtabimg fimg ef.ef_shstrtab_sec.sh_offset;
  (* Write the instructions *)
  array_overwrite (Array.of_list ef.ef_text) fimg ef.ef_text_sec.sh_offset;
  (* Write the data *)
  array_overwrite (Array.of_list ef.ef_data) fimg ef.ef_data_sec.sh_offset;
  fimg 
  
(* Write the file image into a binary file *)
let write_elf fname ef =
  let fimg = elf_to_bytes ef in
  let dump_channel = open_out_bin fname in
  Array.iter (fun i -> output_byte dump_channel i) fimg;
  close_out dump_channel


let create_386_exec_elf_header entry phoff shoff =
  {
    e_encoding  = ELFDATA2LSB;
    e_class     = ELFCLASS32;
    e_type      = ET_EXEC;
    e_machine   = EM_386;
    e_entry     = entry;
    e_phoff     = phoff;
    e_shoff     = shoff;
    e_flags     = 0;
    e_ehsize    = 52;
    e_phentsize = 32;
    e_phnum     = 2;
    e_shentsize = 40;
    e_shnum     = 4;
    e_shstrndx  = 3;
  }

  


