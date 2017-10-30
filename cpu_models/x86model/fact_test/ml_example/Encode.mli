open BiGrammar
open BinInt
open Bits
open Coqlib
open Datatypes
open List0
open Monad
open PeanoNat
open X86BG
open X86Syntax

type __ = Obj.t

type 't coq_Enc = 't option

val coq_EncodingMonad : __ coq_Enc coq_Monad

val invalid : 'a1 coq_Enc

val bits_to_bytes : bool list -> int8 list coq_Enc

val x86_encode : prefix -> instr -> int8 list coq_Enc

val s2bl : char list -> bool list

val enc_reg : register -> bool list

val enc_debug_reg : debug_register -> bool list

val enc_control_reg : control_register -> bool list

val sreg3_2_reg : segment_register -> register

val enc_condition_type : condition_type -> bool list

val enc_scale : scale -> bool list

val enc_SIB : register -> (scale * register) option -> bool list coq_Enc

val int_explode : Big.big_int -> Word.int -> Big.big_int -> bool list

val enc_byte : int8 -> bool list

val repr_in_signed : Big.big_int -> Big.big_int -> Word.int -> bool

val repr_in_signed_byte : int32 -> bool

val repr_in_signed_halfword : int32 -> bool

val enc_byte_i32 : int32 -> bool list coq_Enc

val enc_halfword : int16 -> bool list

val enc_halfword_i32 : int32 -> bool list coq_Enc

val enc_word : Big.big_int -> Word.int -> bool list

val enc_address : bool list -> address -> bool list coq_Enc

val enc_modrm_gen : bool list -> operand -> bool list coq_Enc

val enc_modrm_2 : char list -> operand -> bool list coq_Enc

val enc_imm : bool -> bool -> int32 -> bool list coq_Enc

val enc_bit : bool -> bool list

val enc_dbit : bool -> bool list

val enc_logic_or_arith :
  char list -> char list -> bool -> bool -> operand -> operand -> bool list
  coq_Enc

val enc_BitScan : operand -> operand -> bool list -> bool list coq_Enc

val enc_bit_test :
  char list -> char list -> operand -> operand -> bool list coq_Enc

val enc_div_mul : bool -> operand -> char list -> bool list coq_Enc

val enc_Rotate :
  bool -> operand -> reg_or_immed -> register -> bool list coq_Enc

val enc_op_bool : bool -> bool list

val enc_AAA : bool list coq_Enc

val enc_AAD : bool list coq_Enc

val enc_AAM : bool list coq_Enc

val enc_AAS : bool list coq_Enc

val enc_ADC : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_ADD : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_AND : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_ARPL : operand -> operand -> bool list coq_Enc

val enc_BOUND : operand -> operand -> bool list coq_Enc

val enc_BSF : operand -> operand -> bool list coq_Enc

val enc_BSR : operand -> operand -> bool list coq_Enc

val enc_BSWAP : register -> bool list coq_Enc

val enc_BT : operand -> operand -> bool list coq_Enc

val enc_BTC : operand -> operand -> bool list coq_Enc

val enc_BTR : operand -> operand -> bool list coq_Enc

val enc_BTS : operand -> operand -> bool list coq_Enc

val enc_CALL : bool -> bool -> operand -> selector option -> bool list coq_Enc

val enc_CDQ : bool list coq_Enc

val enc_CLC : bool list coq_Enc

val enc_CLD : bool list coq_Enc

val enc_CLI : bool list coq_Enc

val enc_CLTS : bool list coq_Enc

val enc_CMC : bool list coq_Enc

val enc_CMOVcc : condition_type -> operand -> operand -> bool list coq_Enc

val enc_CMP : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_CMPS : bool -> bool list coq_Enc

val enc_CMPXCHG : bool -> operand -> operand -> bool list coq_Enc

val enc_CPUID : bool list coq_Enc

val enc_CWDE : bool list coq_Enc

val enc_DAA : bool list coq_Enc

val enc_DAS : bool list coq_Enc

val enc_DEC : bool -> operand -> bool list coq_Enc

val enc_DIV : bool -> operand -> bool list coq_Enc

val enc_HLT : bool list coq_Enc

val enc_IDIV : bool -> operand -> bool list coq_Enc

val enc_IMUL :
  bool -> bool -> operand -> operand option -> int32 option -> bool list
  coq_Enc

val enc_IN : bool -> port_number option -> bool list coq_Enc

val enc_INC : bool -> operand -> bool list coq_Enc

val enc_INS : bool -> bool list coq_Enc

val enc_INT : bool list coq_Enc

val enc_INTn : interrupt_type -> bool list coq_Enc

val enc_INTO : bool list coq_Enc

val enc_INVD : bool list coq_Enc

val enc_INVLPG : operand -> bool list coq_Enc

val enc_IRET : bool list coq_Enc

val enc_Jcc : condition_type -> int32 -> bool list coq_Enc

val enc_JCXZ : int8 -> bool list coq_Enc

val enc_JMP : bool -> bool -> operand -> selector option -> bool list coq_Enc

val enc_LAHF : bool list coq_Enc

val enc_LAR : operand -> operand -> bool list coq_Enc

val enc_LDS : operand -> operand -> bool list coq_Enc

val enc_LEA : operand -> operand -> bool list coq_Enc

val enc_LEAVE : bool list coq_Enc

val enc_LES : operand -> operand -> bool list coq_Enc

val enc_LFS : operand -> operand -> bool list coq_Enc

val enc_LGDT : operand -> bool list coq_Enc

val enc_LGS : operand -> operand -> bool list coq_Enc

val enc_LIDT : operand -> bool list coq_Enc

val enc_LLDT : operand -> bool list coq_Enc

val enc_LMSW : operand -> bool list coq_Enc

val enc_LODS : bool -> bool list coq_Enc

val enc_LOOP : int8 -> bool list coq_Enc

val enc_LOOPNZ : int8 -> bool list coq_Enc

val enc_LOOPZ : int8 -> bool list coq_Enc

val enc_LSL : operand -> operand -> bool list coq_Enc

val enc_LSS : operand -> operand -> bool list coq_Enc

val enc_LTR : operand -> bool list coq_Enc

val enc_MOV : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_MOVBE : operand -> operand -> bool list coq_Enc

val enc_MOVCR : bool -> control_register -> register -> bool list coq_Enc

val enc_MOVDR : bool -> debug_register -> register -> bool list coq_Enc

val enc_MOVS : bool -> bool list coq_Enc

val enc_MOVSR : bool -> segment_register -> operand -> bool list coq_Enc

val enc_MOVSX : bool -> operand -> operand -> bool list coq_Enc

val enc_MOVZX : bool -> operand -> operand -> bool list coq_Enc

val enc_MUL : bool -> operand -> bool list coq_Enc

val enc_NEG : bool -> operand -> bool list coq_Enc

val enc_NOP : operand -> bool list coq_Enc

val enc_NOT : bool -> operand -> bool list coq_Enc

val enc_OR : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_OUT : bool -> port_number option -> bool list coq_Enc

val enc_OUTS : bool -> bool list coq_Enc

val enc_POP : operand -> bool list coq_Enc

val enc_POPA : bool list coq_Enc

val enc_POPF : bool list coq_Enc

val enc_POPSR : segment_register -> bool list coq_Enc

val enc_PUSH : bool -> operand -> bool list coq_Enc

val enc_PUSHA : bool list coq_Enc

val enc_PUSHF : bool list coq_Enc

val enc_PUSHSR : segment_register -> bool list coq_Enc

val enc_RCL : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_RCR : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_RDMSR : bool list coq_Enc

val enc_RDPMC : bool list coq_Enc

val enc_RDTSC : bool list coq_Enc

val enc_RDTSCP : bool list coq_Enc

val enc_RET : bool -> int16 option -> bool list coq_Enc

val enc_ROL : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_ROR : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_RSM : bool list coq_Enc

val enc_SAHF : bool list coq_Enc

val enc_SAR : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_SBB : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_SCAS : bool -> bool list coq_Enc

val enc_SETcc : condition_type -> operand -> bool list coq_Enc

val enc_SGDT : operand -> bool list coq_Enc

val enc_SHL : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_SHLD : operand -> register -> reg_or_immed -> bool list coq_Enc

val enc_SHR : bool -> operand -> reg_or_immed -> bool list coq_Enc

val enc_SHRD : operand -> register -> reg_or_immed -> bool list coq_Enc

val enc_SIDT : operand -> bool list coq_Enc

val enc_SLDT : operand -> bool list coq_Enc

val enc_SMSW : operand -> bool list coq_Enc

val enc_STC : bool list coq_Enc

val enc_STD : bool list coq_Enc

val enc_STI : bool list coq_Enc

val enc_STOS : bool -> bool list coq_Enc

val enc_STR : operand -> bool list coq_Enc

val enc_SUB : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_TEST : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_UD2 : bool list coq_Enc

val enc_VERR : operand -> bool list coq_Enc

val enc_VERW : operand -> bool list coq_Enc

val enc_WBINVD : bool list coq_Enc

val enc_WRMSR : bool list coq_Enc

val enc_XADD : bool -> operand -> operand -> bool list coq_Enc

val enc_XCHG : bool -> operand -> operand -> bool list coq_Enc

val enc_XLAT : bool list coq_Enc

val enc_XOR : bool -> bool -> operand -> operand -> bool list coq_Enc

val enc_mmx_reg : mmx_register -> bool list

val enc_fp_modrm : bool list -> fp_operand -> bool list coq_Enc

val enc_comhelper : bool list -> fp_operand -> bool list -> bool list coq_Enc

val enc_fp_int3 : fp_operand -> bool list coq_Enc

val enc_fp_arith :
  bool -> bool list -> bool list -> bool -> fp_operand -> bool list coq_Enc

val enc_F2XM1 : bool list coq_Enc

val enc_FABS : bool list coq_Enc

val enc_FADD : bool -> fp_operand -> bool list coq_Enc

val enc_FADDP : fp_operand -> bool list coq_Enc

val enc_FBLD : fp_operand -> bool list coq_Enc

val enc_FBSTP : fp_operand -> bool list coq_Enc

val enc_FCHS : bool list coq_Enc

val enc_FCMOVcc : fp_condition_type -> fp_operand -> bool list coq_Enc

val enc_FCOM : fp_operand -> bool list coq_Enc

val enc_FCOMP : fp_operand -> bool list coq_Enc

val enc_FCOMPP : bool list coq_Enc

val enc_FCOMIP : fp_operand -> bool list coq_Enc

val enc_FCOS : bool list coq_Enc

val enc_FDECSTP : bool list coq_Enc

val enc_FDIV : bool -> fp_operand -> bool list coq_Enc

val enc_FDIVP : fp_operand -> bool list coq_Enc

val enc_FDIVR : bool -> fp_operand -> bool list coq_Enc

val enc_FDIVRP : fp_operand -> bool list coq_Enc

val enc_FFREE : fp_operand -> bool list coq_Enc

val enc_FI_instrs : char list -> fp_operand -> bool list coq_Enc

val enc_FIADD : fp_operand -> bool list coq_Enc

val enc_FICOM : fp_operand -> bool list coq_Enc

val enc_FICOMP : fp_operand -> bool list coq_Enc

val enc_FIDIV : fp_operand -> bool list coq_Enc

val enc_FIDIVR : fp_operand -> bool list coq_Enc

val enc_FILD : fp_operand -> bool list coq_Enc

val enc_FIMUL : fp_operand -> bool list coq_Enc

val enc_FINCSTP : bool list coq_Enc

val enc_FIST : fp_operand -> bool list coq_Enc

val enc_FISTP : fp_operand -> bool list coq_Enc

val enc_FISUB : fp_operand -> bool list coq_Enc

val enc_FISUBR : fp_operand -> bool list coq_Enc

val enc_FLD : fp_operand -> bool list coq_Enc

val enc_FLD1 : bool list coq_Enc

val enc_FLDCW : fp_operand -> bool list coq_Enc

val enc_FLDENV : fp_operand -> bool list coq_Enc

val enc_FLDL2E : bool list coq_Enc

val enc_FLDL2T : bool list coq_Enc

val enc_FLDLG2 : bool list coq_Enc

val enc_FLDLN2 : bool list coq_Enc

val enc_FLDPI : bool list coq_Enc

val enc_FLDZ : bool list coq_Enc

val enc_FMUL : bool -> fp_operand -> bool list coq_Enc

val enc_FMULP : fp_operand -> bool list coq_Enc

val enc_FNCLEX : bool list coq_Enc

val enc_FNINIT : bool list coq_Enc

val enc_FNSAVE : fp_operand -> bool list coq_Enc

val enc_FNSTSW : fp_operand option -> bool list coq_Enc

val enc_FNOP : bool list coq_Enc

val enc_FPATAN : bool list coq_Enc

val enc_FPREM : bool list coq_Enc

val enc_FPREM1 : bool list coq_Enc

val enc_FPTAN : bool list coq_Enc

val enc_FRNDINT : bool list coq_Enc

val enc_FRSTOR : fp_operand -> bool list coq_Enc

val enc_FSCALE : bool list coq_Enc

val enc_FSIN : bool list coq_Enc

val enc_FSINCOS : bool list coq_Enc

val enc_FSQRT : bool list coq_Enc

val enc_FST : fp_operand -> bool list coq_Enc

val enc_FSTP : fp_operand -> bool list coq_Enc

val enc_FSUB : bool -> fp_operand -> bool list coq_Enc

val enc_FSUBP : fp_operand -> bool list coq_Enc

val enc_FSUBR : bool -> fp_operand -> bool list coq_Enc

val enc_FSUBRP : fp_operand -> bool list coq_Enc

val enc_FTST : bool list coq_Enc

val enc_FUCOM : fp_operand -> bool list coq_Enc

val enc_FUCOMI : fp_operand -> bool list coq_Enc

val enc_FUCOMIP : fp_operand -> bool list coq_Enc

val enc_FUCOMP : fp_operand -> bool list coq_Enc

val enc_FUCOMPP : bool list coq_Enc

val enc_FWAIT : bool list coq_Enc

val enc_FXAM : bool list coq_Enc

val enc_FXCH : fp_operand -> bool list coq_Enc

val enc_FXTRACT : bool list coq_Enc

val enc_FYL2X : bool list coq_Enc

val enc_FYL2XP1 : bool list coq_Enc

val enc_mmx_modrm_gen : bool list -> mmx_operand -> bool list coq_Enc

val enc_gg : mmx_granularity -> bool list

val enc_EMMS : bool list coq_Enc

val enc_MOVD : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_MOVQ : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PACKSSDW : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PACKSSWB : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PACKUSWB : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PADD :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PADDS :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PADDUS :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PAND : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PANDN : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PCMPEQ :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PCMPGT :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PMADDWD : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PMULHUW : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PMULHW : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PMULLW : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_POR : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSLL :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSRA :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSRL :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSUB :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSUBS :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PSUBUS :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PUNPCKH :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PUNPCKL :
  mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_PXOR : mmx_operand -> mmx_operand -> bool list coq_Enc

val enc_xmm_r : sse_register -> bool list

val enc_xmm_modrm_gen : bool list -> sse_operand -> bool list coq_Enc

val enc_mm_modrm_gen : bool list -> sse_operand -> bool list coq_Enc

val enc_ext_op_modrm_sse : bool list -> sse_operand -> bool list coq_Enc

val enc_ADDPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_ADDSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_ANDNPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_ANDPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CMPPS : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_CMPSS : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_COMISS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTPI2PS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTPS2PI : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTSI2SS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTSS2SI : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTTPS2PI : sse_operand -> sse_operand -> bool list coq_Enc

val enc_CVTTSS2SI : sse_operand -> sse_operand -> bool list coq_Enc

val enc_DIVPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_DIVSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_LDMXCSR : sse_operand -> bool list coq_Enc

val enc_MAXPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MAXSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MINPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MINSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVAPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVHLPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVHPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVLHPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVLPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVMSKPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVUPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MULPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MULSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_ORPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_RCPPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_RCPSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_RSQRTPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_RSQRTSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_SHUFPS : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_SQRTPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_SQRTSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_STMXCSR : sse_operand -> bool list coq_Enc

val enc_SUBPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_SUBSS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_UCOMISS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_UNPCKHPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_UNPCKLPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_XORPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PAVGB : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PEXTRW : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_PINSRW : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_PMAXSW : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PMAXUB : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PMINSW : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PMINUB : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PMOVMSKB : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PSADBW : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PSHUFW : sse_operand -> sse_operand -> int8 -> bool list coq_Enc

val enc_MASKMOVQ : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVNTPS : sse_operand -> sse_operand -> bool list coq_Enc

val enc_MOVNTQ : sse_operand -> sse_operand -> bool list coq_Enc

val enc_PREFETCHT0 : sse_operand -> bool list coq_Enc

val enc_PREFETCHT1 : sse_operand -> bool list coq_Enc

val enc_PREFETCHT2 : sse_operand -> bool list coq_Enc

val enc_PREFETCHNTA : sse_operand -> bool list coq_Enc

val enc_SFENCE : bool list coq_Enc

val enc_prefix : prefix -> bool list coq_Enc

val check_pre_rep : prefix -> bool

val check_pre_rep_or_repn : prefix -> bool

val check_pre_lock_with_op_override : prefix -> bool

val check_pre_lock_no_op_override : prefix -> bool

val check_pre_seg_with_op_override : prefix -> bool

val check_pre_seg_op_override : prefix -> bool

val check_pre_seg_override : prefix -> bool

val check_empty_prefix : prefix -> bool

val enc_rep_instr : prefix -> instr -> bool list coq_Enc

val enc_lock_with_op_override_instr : prefix -> instr -> bool list coq_Enc

val enc_lock_no_op_override_instr : prefix -> instr -> bool list coq_Enc

val enc_seg_with_op_override_instr : prefix -> instr -> bool list coq_Enc

val enc_seg_op_override_instr : prefix -> instr -> bool list coq_Enc

val enc_seg_override_instr : prefix -> instr -> bool list coq_Enc

val enc_all_instr : prefix -> instr -> bool list coq_Enc

val enc_instr : prefix -> instr -> bool list coq_Enc

val enc_pre_instr : prefix -> instr -> bool list coq_Enc

val enc_pre_instr_bytes : prefix -> instr -> int8 list coq_Enc
