open BinInt
open Bits
open Bool
open Datatypes
open X86Syntax

module X86_PARSER_ARG :
 sig
  type char_p = bool

  val char_dec : char_p -> char_p -> bool

  val char_cmp : char_p -> char_p -> comparison

  type i_instr1 =
  | I_AAA
  | I_AAD
  | I_AAM
  | I_AAS
  | I_CLC
  | I_CLD
  | I_CLI
  | I_CLTS
  | I_CMC
  | I_CPUID
  | I_DAA
  | I_DAS
  | I_HLT
  | I_INT
  | I_INTO
  | I_INVD
  | I_IRET
  | I_LAHF
  | I_LEAVE
  | I_POPA
  | I_POPF
  | I_PUSHA
  | I_PUSHF
  | I_RDMSR
  | I_RDPMC
  | I_RDTSC
  | I_RDTSCP
  | I_RSM
  | I_SAHF
  | I_STC
  | I_STD
  | I_STI
  | I_UD2
  | I_WBINVD
  | I_WRMSR
  | I_XLAT

  type i_instr2 =
  | I_ARPL of operand * operand
  | I_BOUND of operand * operand
  | I_BSF of operand * operand
  | I_BSR of operand * operand
  | I_BSWAP of register
  | I_BT of operand * operand
  | I_CALL of bool * bool * operand * selector option
  | I_IN of bool * port_number option
  | I_INTn of interrupt_type
  | I_INVLPG of operand
  | I_Jcc of condition_type * int32
  | I_JCXZ of int8
  | I_JMP of bool * bool * operand * selector option
  | I_LAR of operand * operand
  | I_LDS of operand * operand
  | I_LEA of operand * operand
  | I_LES of operand * operand
  | I_LFS of operand * operand
  | I_LGDT of operand
  | I_LGS of operand * operand
  | I_LIDT of operand
  | I_LLDT of operand
  | I_LMSW of operand
  | I_LOOP of int8
  | I_LOOPZ of int8
  | I_LOOPNZ of int8
  | I_LSL of operand * operand
  | I_LSS of operand * operand
  | I_LTR of operand

  type i_instr3 =
  | I_MOVCR of bool * control_register * register
  | I_MOVDR of bool * debug_register * register
  | I_MOVSR of bool * segment_register * operand
  | I_MOVBE of operand * operand
  | I_OUT of bool * port_number option
  | I_POP of operand
  | I_POPSR of segment_register
  | I_PUSH of bool * operand
  | I_PUSHSR of segment_register
  | I_RCL of bool * operand * reg_or_immed
  | I_RCR of bool * operand * reg_or_immed
  | I_SETcc of condition_type * operand
  | I_SGDT of operand
  | I_SIDT of operand
  | I_SLDT of operand
  | I_SMSW of operand
  | I_STR of operand
  | I_VERR of operand
  | I_VERW of operand

  type i_instr4 =
  | I_INS of bool
  | I_OUTS of bool
  | I_MOVS of bool
  | I_LODS of bool
  | I_STOS of bool
  | I_RET of bool * int16 option
  | I_CMPS of bool
  | I_SCAS of bool

  type i_instr5 =
  | I_ADC of bool * operand * operand
  | I_ADD of bool * operand * operand
  | I_AND of bool * operand * operand
  | I_BTC of operand * operand
  | I_BTR of operand * operand
  | I_BTS of operand * operand
  | I_CMP of bool * operand * operand
  | I_CMPXCHG of bool * operand * operand
  | I_DEC of bool * operand
  | I_IMUL of bool * operand * operand option * int32 option
  | I_INC of bool * operand
  | I_MOV of bool * operand * operand
  | I_NEG of bool * operand
  | I_NOT of bool * operand
  | I_OR of bool * operand * operand
  | I_SBB of bool * operand * operand
  | I_SUB of bool * operand * operand
  | I_TEST of bool * operand * operand
  | I_XADD of bool * operand * operand
  | I_XCHG of bool * operand * operand
  | I_XOR of bool * operand * operand

  type i_instr6 =
  | I_CDQ
  | I_CMOVcc of condition_type * operand * operand
  | I_CWDE
  | I_DIV of bool * operand
  | I_IDIV of bool * operand
  | I_MOVSX of bool * operand * operand
  | I_MOVZX of bool * operand * operand
  | I_MUL of bool * operand
  | I_NOP of operand
  | I_ROL of bool * operand * reg_or_immed
  | I_ROR of bool * operand * reg_or_immed
  | I_SAR of bool * operand * reg_or_immed
  | I_SHL of bool * operand * reg_or_immed
  | I_SHLD of operand * register * reg_or_immed
  | I_SHR of bool * operand * reg_or_immed
  | I_SHRD of operand * register * reg_or_immed

  type f_instr1 =
  | F_F2XM1
  | F_FABS
  | F_FADD of bool * fp_operand
  | F_FADDP of fp_operand
  | F_FBLD of fp_operand
  | F_FBSTP of fp_operand
  | F_FCHS
  | F_FCMOVcc of fp_condition_type * fp_operand
  | F_FCOM of fp_operand
  | F_FCOMP of fp_operand
  | F_FCOMPP
  | F_FCOMIP of fp_operand
  | F_FCOS
  | F_FDECSTP
  | F_FDIV of bool * fp_operand
  | F_FDIVP of fp_operand
  | F_FDIVR of bool * fp_operand
  | F_FDIVRP of fp_operand
  | F_FFREE of fp_operand
  | F_FIADD of fp_operand
  | F_FICOM of fp_operand
  | F_FICOMP of fp_operand
  | F_FIDIV of fp_operand
  | F_FIDIVR of fp_operand
  | F_FILD of fp_operand
  | F_FIMUL of fp_operand
  | F_FINCSTP
  | F_FIST of fp_operand
  | F_FISTP of fp_operand
  | F_FISUB of fp_operand
  | F_FISUBR of fp_operand
  | F_FLD of fp_operand
  | F_FLD1
  | F_FLDCW of fp_operand
  | F_FLDENV of fp_operand
  | F_FLDL2E
  | F_FLDL2T
  | F_FLDLG2
  | F_FLDLN2
  | F_FLDPI
  | F_FLDZ
  | F_FMUL of bool * fp_operand
  | F_FMULP of fp_operand

  type f_instr2 =
  | F_FNCLEX
  | F_FNINIT
  | F_FNOP
  | F_FNSAVE of fp_operand
  | F_FNSTCW of fp_operand
  | F_FNSTSW of fp_operand option
  | F_FPATAN
  | F_FPREM
  | F_FPREM1
  | F_FPTAN
  | F_FRNDINT
  | F_FRSTOR of fp_operand
  | F_FSCALE
  | F_FSIN
  | F_FSINCOS
  | F_FSQRT
  | F_FST of fp_operand
  | F_FSTENV of fp_operand
  | F_FSTP of fp_operand
  | F_FSUB of bool * fp_operand
  | F_FSUBP of fp_operand
  | F_FSUBR of bool * fp_operand
  | F_FSUBRP of fp_operand
  | F_FTST
  | F_FUCOM of fp_operand
  | F_FUCOMP of fp_operand
  | F_FUCOMPP
  | F_FUCOMI of fp_operand
  | F_FUCOMIP of fp_operand
  | F_FXAM
  | F_FXCH of fp_operand
  | F_FXTRACT
  | F_FYL2X
  | F_FYL2XP1
  | F_FWAIT

  type m_instr =
  | M_EMMS
  | M_MOVD of mmx_operand * mmx_operand
  | M_MOVQ of mmx_operand * mmx_operand
  | M_PACKSSDW of mmx_operand * mmx_operand
  | M_PACKSSWB of mmx_operand * mmx_operand
  | M_PACKUSWB of mmx_operand * mmx_operand
  | M_PADD of mmx_granularity * mmx_operand * mmx_operand
  | M_PADDS of mmx_granularity * mmx_operand * mmx_operand
  | M_PADDUS of mmx_granularity * mmx_operand * mmx_operand
  | M_PAND of mmx_operand * mmx_operand
  | M_PANDN of mmx_operand * mmx_operand
  | M_PCMPEQ of mmx_granularity * mmx_operand * mmx_operand
  | M_PCMPGT of mmx_granularity * mmx_operand * mmx_operand
  | M_PMADDWD of mmx_operand * mmx_operand
  | M_PMULHUW of mmx_operand * mmx_operand
  | M_PMULHW of mmx_operand * mmx_operand
  | M_PMULLW of mmx_operand * mmx_operand
  | M_POR of mmx_operand * mmx_operand
  | M_PSLL of mmx_granularity * mmx_operand * mmx_operand
  | M_PSRA of mmx_granularity * mmx_operand * mmx_operand
  | M_PSRL of mmx_granularity * mmx_operand * mmx_operand
  | M_PSUB of mmx_granularity * mmx_operand * mmx_operand
  | M_PSUBS of mmx_granularity * mmx_operand * mmx_operand
  | M_PSUBUS of mmx_granularity * mmx_operand * mmx_operand
  | M_PUNPCKH of mmx_granularity * mmx_operand * mmx_operand
  | M_PUNPCKL of mmx_granularity * mmx_operand * mmx_operand
  | M_PXOR of mmx_operand * mmx_operand

  type s_instr1 =
  | S_ADDPS of sse_operand * sse_operand
  | S_ADDSS of sse_operand * sse_operand
  | S_ANDNPS of sse_operand * sse_operand
  | S_ANDPS of sse_operand * sse_operand
  | S_CMPPS of sse_operand * sse_operand * int8
  | S_CMPSS of sse_operand * sse_operand * int8
  | S_COMISS of sse_operand * sse_operand
  | S_CVTPI2PS of sse_operand * sse_operand
  | S_CVTPS2PI of sse_operand * sse_operand
  | S_CVTSI2SS of sse_operand * sse_operand
  | S_CVTSS2SI of sse_operand * sse_operand
  | S_CVTTPS2PI of sse_operand * sse_operand
  | S_CVTTSS2SI of sse_operand * sse_operand
  | S_DIVPS of sse_operand * sse_operand
  | S_DIVSS of sse_operand * sse_operand
  | S_LDMXCSR of sse_operand
  | S_MAXPS of sse_operand * sse_operand
  | S_MAXSS of sse_operand * sse_operand
  | S_MINPS of sse_operand * sse_operand
  | S_MINSS of sse_operand * sse_operand
  | S_MOVAPS of sse_operand * sse_operand
  | S_MOVHLPS of sse_operand * sse_operand
  | S_MOVHPS of sse_operand * sse_operand
  | S_MOVLHPS of sse_operand * sse_operand
  | S_MOVLPS of sse_operand * sse_operand
  | S_MOVMSKPS of sse_operand * sse_operand
  | S_MOVSS of sse_operand * sse_operand
  | S_MOVUPS of sse_operand * sse_operand
  | S_MULPS of sse_operand * sse_operand
  | S_MULSS of sse_operand * sse_operand
  | S_ORPS of sse_operand * sse_operand
  | S_RCPPS of sse_operand * sse_operand
  | S_RCPSS of sse_operand * sse_operand
  | S_RSQRTPS of sse_operand * sse_operand
  | S_RSQRTSS of sse_operand * sse_operand

  type s_instr2 =
  | S_SHUFPS of sse_operand * sse_operand * int8
  | S_SQRTPS of sse_operand * sse_operand
  | S_SQRTSS of sse_operand * sse_operand
  | S_STMXCSR of sse_operand
  | S_SUBPS of sse_operand * sse_operand
  | S_SUBSS of sse_operand * sse_operand
  | S_UCOMISS of sse_operand * sse_operand
  | S_UNPCKHPS of sse_operand * sse_operand
  | S_UNPCKLPS of sse_operand * sse_operand
  | S_XORPS of sse_operand * sse_operand
  | S_PAVGB of sse_operand * sse_operand
  | S_PEXTRW of sse_operand * sse_operand * int8
  | S_PINSRW of sse_operand * sse_operand * int8
  | S_PMAXSW of sse_operand * sse_operand
  | S_PMAXUB of sse_operand * sse_operand
  | S_PMINSW of sse_operand * sse_operand
  | S_PMINUB of sse_operand * sse_operand
  | S_PMOVMSKB of sse_operand * sse_operand
  | S_PSADBW of sse_operand * sse_operand
  | S_PSHUFW of sse_operand * sse_operand * int8
  | S_MASKMOVQ of sse_operand * sse_operand
  | S_MOVNTPS of sse_operand * sse_operand
  | S_MOVNTQ of sse_operand * sse_operand
  | S_PREFETCHT0 of sse_operand
  | S_PREFETCHT1 of sse_operand
  | S_PREFETCHT2 of sse_operand
  | S_PREFETCHNTA of sse_operand
  | S_SFENCE

  type tipe =
  | Int_t
  | Register_t
  | BitVector_t of Big.big_int
  | Scale_t
  | Condition_t
  | Address_t
  | Operand_t
  | Reg_or_Immed_t
  | Fp_Debug_Register_t
  | Fp_Operand_t
  | Fp_Condition_t
  | MMX_Granularity_t
  | MMX_Operand_t
  | SSE_Operand_t
  | I_Instr1_t
  | I_Instr2_t
  | I_Instr3_t
  | I_Instr4_t
  | I_Instr5_t
  | I_Instr6_t
  | F_Instr1_t
  | F_Instr2_t
  | M_Instr_t
  | S_Instr1_t
  | S_Instr2_t
  | Instruction_t
  | Control_Register_t
  | Debug_Register_t
  | Segment_Register_t
  | Lock_or_Rep_t
  | Bool_t
  | Prefix_t
  | UPair_t of tipe * tipe

  val coq_Byte_t : tipe

  val coq_Half_t : tipe

  val coq_Word_t : tipe

  val coq_Fpu_Register_t : tipe

  val coq_MMX_Register_t : tipe

  type user_type = tipe

  val byte_explode : int8 -> bool list

  val nat_explode : Big.big_int -> bool list

  type token_id = Big.big_int

  val num_tokens : token_id

  val token_id_to_chars : token_id -> char_p list
 end
