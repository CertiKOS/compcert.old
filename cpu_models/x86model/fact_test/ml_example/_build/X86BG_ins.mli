open BiGrammar
open BinInt
open Bits
open Coqlib
open Datatypes
open GrammarType
open Nat0
open X86Syntax
open ZArith_dec
open Zpower

val sig_of_bitsn : Big.big_int -> interp -> Big.big_int -> bool

val bitsn_of_sig : Big.big_int -> (Big.big_int -> bool) -> interp

val int_of_bitsn : Big.big_int -> interp -> interp

val bitsn_of_int : Big.big_int -> interp -> interp option

val intn_of_sig : Big.big_int -> (Big.big_int -> bool) -> Word.int

val sig_of_intn : Big.big_int -> Word.int -> Big.big_int -> bool

val intn_of_bitsn : Big.big_int -> interp -> Word.int

val bitsn_of_intn : Big.big_int -> Word.int -> interp

val register_to_Z : register -> Big.big_int

val condition_type_to_Z : condition_type -> Big.big_int

val scale_to_Z : scale -> Big.big_int

val repr_in_signed_dec : Big.big_int -> Big.big_int -> Word.int -> bool

val repr_in_signed_byte_dec : int32 -> bool

val repr_in_signed_halfword_dec : int32 -> bool

val sign_shrink32_8 : Word.int -> Word.int

val sign_shrink32_16 : Word.int -> Word.int

val zero_shrink32_8 : Word.int -> Word.int

val repr_in_unsigned_byte_dec : int32 -> bool

val bit : bool -> bigrammar

val anybit : bigrammar

val bits : char list -> bigrammar

val tuples_of_string : char list -> interp

val bitsmatch : char list -> bigrammar

val bitsleft : char list -> bigrammar -> bigrammar

val field' : Big.big_int -> bigrammar

val field : Big.big_int -> bigrammar

val reg : bigrammar

val int_n : Big.big_int -> bigrammar

val intn_cat : Big.big_int -> Big.big_int -> Word.int -> Word.int -> Word.int

val intn_split1 : Big.big_int -> Big.big_int -> Word.int -> Word.int

val intn_split2 : Big.big_int -> Big.big_int -> Word.int -> Word.int

val intn_cat_little :
  Big.big_int -> Big.big_int -> bigrammar -> bigrammar -> bigrammar

val byte : bigrammar

val halfword : bigrammar

val word : bigrammar

val tttn : bigrammar

val control_reg_b : bigrammar

val debug_reg_b : bigrammar

val segment_reg_b : bigrammar

val field_intn : Big.big_int -> bigrammar

val fpu_reg : bigrammar

val mmx_reg : bigrammar

val sse_reg : bigrammar

val scale_b : bigrammar

val reg_no_esp : bigrammar

val reg_no_ebp : bigrammar

val reg_no_esp_ebp : bigrammar

val si_b : bigrammar

val sib_b : bigrammar

val coq_Address_op_inv : operand -> address option

val coq_SSE_Addr_op_inv : sse_operand -> address option

val rm00 : bigrammar

val rm01 : bigrammar

val rm10 : bigrammar

val modrm_gen_noreg : bigrammar -> bigrammar

val modrm_gen : bigrammar -> bigrammar

val ext_op_modrm_noreg_ret_addr : char list -> bigrammar

val ext_op_modrm_noreg : char list -> bigrammar

val modrm_ret_reg : bigrammar

val modrm : bigrammar

val modrm_noreg : bigrammar

val modrm_bv2_noreg : bigrammar

val ext_op_modrm : char list -> bigrammar

val seg_modrm : bigrammar

val imm_b : bool -> bigrammar

val coq_AAA_b : bigrammar

val coq_AAD_b : bigrammar

val coq_AAM_b : bigrammar

val coq_AAS_b : bigrammar

val logic_or_arith_b : bool -> char list -> char list -> bigrammar

val coq_ADC_b : bool -> bigrammar

val coq_ADD_b : bool -> bigrammar

val coq_AND_b : bool -> bigrammar

val coq_CMP_b : bool -> bigrammar

val coq_OR_b : bool -> bigrammar

val coq_SBB_b : bool -> bigrammar

val coq_SUB_b : bool -> bigrammar

val coq_XOR_b : bool -> bigrammar

val coq_ARPL_b : bigrammar

val coq_BOUND_b : bigrammar

val coq_BSF_b : bigrammar

val coq_BSR_b : bigrammar

val coq_BSWAP_b : bigrammar

val bit_test_b : char list -> char list -> bigrammar

val coq_BT_b : bigrammar

val coq_BTC_b : bigrammar

val coq_BTR_b : bigrammar

val coq_BTS_b : bigrammar

val coq_CALL_b : bigrammar

val coq_CDQ_b : bigrammar

val coq_CLC_b : bigrammar

val coq_CLD_b : bigrammar

val coq_CLI_b : bigrammar

val coq_CLTS_b : bigrammar

val coq_CMC_b : bigrammar

val coq_CMPS_b : bigrammar

val coq_CMPXCHG_b : bigrammar

val coq_CPUID_b : bigrammar

val coq_CWDE_b : bigrammar

val coq_DAA_b : bigrammar

val coq_DAS_b : bigrammar

val coq_DEC_b : bigrammar

val coq_DIV_b : bigrammar

val coq_HLT_b : bigrammar

val coq_IDIV_b : bigrammar

val coq_IMUL_b : bool -> bigrammar

val coq_IN_b : bigrammar

val coq_INC_b : bigrammar

val coq_INS_b : bigrammar

val coq_INTn_b : bigrammar

val coq_INT_b : bigrammar

val coq_INTO_b : bigrammar

val coq_INVD_b : bigrammar

val coq_INVLPG_b : bigrammar

val coq_IRET_b : bigrammar

val coq_Jcc_b : bigrammar

val coq_JCXZ_b : bigrammar

val coq_JMP_b : bigrammar

val coq_LAHF_b : bigrammar

val coq_LAR_b : bigrammar

val coq_LDS_b : bigrammar

val coq_LEA_b : bigrammar

val coq_LEAVE_b : bigrammar

val coq_LES_b : bigrammar

val coq_LFS_b : bigrammar

val coq_LGDT_b : bigrammar

val coq_LGS_b : bigrammar

val coq_LIDT_b : bigrammar

val coq_LLDT_b : bigrammar

val coq_LMSW_b : bigrammar

val coq_LODS_b : bigrammar

val coq_LOOP_b : bigrammar

val coq_LOOPZ_b : bigrammar

val coq_LOOPNZ_b : bigrammar

val coq_LSL_b : bigrammar

val coq_LSS_b : bigrammar

val coq_LTR_b : bigrammar

val coq_CMOVcc_b : bigrammar

val coq_MOV_b : bool -> bigrammar

val coq_MOVCR_b : bigrammar

val coq_MOVDR_b : bigrammar

val coq_MOVSR_b : bigrammar

val coq_MOVBE_b : bigrammar

val coq_MOVS_b : bigrammar

val coq_MOVSX_b : bigrammar

val coq_MOVZX_b : bigrammar

val coq_MUL_b : bigrammar

val coq_NEG_b : bigrammar

val coq_NOP_b : bigrammar

val coq_NOT_b : bigrammar

val coq_OUT_b : bigrammar

val coq_OUTS_b : bigrammar

val coq_POP_b : bigrammar

val coq_POPSR_b : bigrammar

val coq_POPA_b : bigrammar

val coq_POPF_b : bigrammar

val coq_PUSH_b : bigrammar

val coq_PUSHSR_b : bigrammar

val coq_PUSHA_b : bigrammar

val coq_PUSHF_b : bigrammar

val rotate_b : char list -> bigrammar

val coq_RCL_b : bigrammar

val coq_RCR_b : bigrammar

val coq_RDMSR_b : bigrammar

val coq_RDPMC_b : bigrammar

val coq_RDTSC_b : bigrammar

val coq_RDTSCP_b : bigrammar

val coq_RET_b : bigrammar

val coq_ROL_b : bigrammar

val coq_ROR_b : bigrammar

val coq_RSM_b : bigrammar

val coq_SAHF_b : bigrammar

val coq_SAR_b : bigrammar

val coq_SCAS_b : bigrammar

val coq_SETcc_b : bigrammar

val coq_SGDT_b : bigrammar

val coq_SHL_b : bigrammar

val shiftdouble_b : char list -> bigrammar

val coq_SHLD_b : bigrammar

val coq_SHR_b : bigrammar

val coq_SHRD_b : bigrammar

val coq_SIDT_b : bigrammar

val coq_SLDT_b : bigrammar

val coq_SMSW_b : bigrammar

val coq_STC_b : bigrammar

val coq_STD_b : bigrammar

val coq_STI_b : bigrammar

val coq_STOS_b : bigrammar

val coq_STR_b : bigrammar

val coq_TEST_b : bool -> bigrammar

val coq_UD2_b : bigrammar

val coq_VERR_b : bigrammar

val coq_VERW_b : bigrammar

val coq_WBINVD_b : bigrammar

val coq_WRMSR_b : bigrammar

val coq_XADD_b : bigrammar

val coq_XCHG_b : bigrammar

val coq_XLAT_b : bigrammar

val fpu_reg_op_b : bigrammar

val ext_op_modrm_FPM32_noreg : char list -> bigrammar

val ext_op_modrm_FPM64_noreg : char list -> bigrammar

val fp_condition_type_to_Z : fp_condition_type -> Big.big_int

val coq_F2XM1_b : bigrammar

val coq_FABS_b : bigrammar

val fp_arith_b : char list -> char list -> bigrammar

val coq_FADD_b : bigrammar

val coq_FADDP_b : bigrammar

val coq_FBLD_b : bigrammar

val coq_FBSTP_b : bigrammar

val coq_FCHS_b : bigrammar

val coq_FCMOVcc_b : bigrammar

val coq_FCOM_b : bigrammar

val coq_FCOMP_b : bigrammar

val coq_FCOMPP_b : bigrammar

val coq_FCOMIP_b : bigrammar

val coq_FCOS_b : bigrammar

val coq_FDECSTP_b : bigrammar

val coq_FDIV_b : bigrammar

val coq_FDIVP_b : bigrammar

val coq_FDIVR_b : bigrammar

val coq_FDIVRP_b : bigrammar

val coq_FFREE_b : bigrammar

val fp_iarith_b : char list -> bigrammar

val coq_FIADD_b : bigrammar

val coq_FICOM_b : bigrammar

val coq_FICOMP_b : bigrammar

val coq_FIDIV_b : bigrammar

val coq_FIDIVR_b : bigrammar

val coq_FILD_b : bigrammar

val coq_FIMUL_b : bigrammar

val coq_FINCSTP_b : bigrammar

val coq_FIST_b : bigrammar

val coq_FISTP_b : bigrammar

val coq_FISUB_b : bigrammar

val coq_FISUBR_b : bigrammar

val coq_FLD_b : bigrammar

val coq_FLD1_b : bigrammar

val coq_FLDCW_b : bigrammar

val coq_FLDENV_b : bigrammar

val coq_FLDL2E_b : bigrammar

val coq_FLDL2T_b : bigrammar

val coq_FLDLG2_b : bigrammar

val coq_FLDLN2_b : bigrammar

val coq_FLDPI_b : bigrammar

val coq_FLDZ_b : bigrammar

val coq_FMUL_b : bigrammar

val coq_FMULP_b : bigrammar

val coq_FNCLEX_b : bigrammar

val coq_FNINIT_b : bigrammar

val coq_FNOP_b : bigrammar

val coq_FNSAVE_b : bigrammar

val coq_FNSTCW_b : bigrammar

val coq_FNSTSW_b : bigrammar

val coq_FPATAN_b : bigrammar

val coq_FPREM_b : bigrammar

val coq_FPREM1_b : bigrammar

val coq_FPTAN_b : bigrammar

val coq_FRNDINT_b : bigrammar

val coq_FRSTOR_b : bigrammar

val coq_FSCALE_b : bigrammar

val coq_FSIN_b : bigrammar

val coq_FSINCOS_b : bigrammar

val coq_FSQRT_b : bigrammar

val coq_FST_b : bigrammar

val coq_FSTENV_b : bigrammar

val coq_FSTP_b : bigrammar

val coq_FSUB_b : bigrammar

val coq_FSUBP_b : bigrammar

val coq_FSUBR_b : bigrammar

val coq_FSUBRP_b : bigrammar

val coq_FTST_b : bigrammar

val coq_FUCOM_b : bigrammar

val coq_FUCOMP_b : bigrammar

val coq_FUCOMPP_b : bigrammar

val coq_FUCOMI_b : bigrammar

val coq_FUCOMIP_b : bigrammar

val coq_FXAM_b : bigrammar

val coq_FXCH_b : bigrammar

val coq_FXTRACT_b : bigrammar

val coq_FYL2X_b : bigrammar

val coq_FYL2XP1_b : bigrammar

val coq_FWAIT_b : bigrammar

val modrm_mmx_noreg : bigrammar

val modrm_mmx_ret_reg : bigrammar

val modrm_mmx : bigrammar

val mmx_gg_b_8_16_32 : bigrammar

val mmx_gg_b_8_16 : bigrammar

val mmx_gg_b_16_32_64 : bigrammar

val mmx_gg_b_16_32 : bigrammar

val coq_EMMS_b : bigrammar

val coq_MOVD_b : bigrammar

val coq_MOVQ_b : bigrammar

val coq_PACKSSDW_b : bigrammar

val coq_PACKSSWB_b : bigrammar

val coq_PACKUSWB_b : bigrammar

val coq_PADD_b : bigrammar

val coq_PADDS_b : bigrammar

val coq_PADDUS_b : bigrammar

val coq_PAND_b : bigrammar

val coq_PANDN_b : bigrammar

val coq_PCMPEQ_b : bigrammar

val coq_PCMPGT_b : bigrammar

val coq_PMADDWD_b : bigrammar

val coq_PMULHUW_b : bigrammar

val coq_PMULHW_b : bigrammar

val coq_PMULLW_b : bigrammar

val coq_POR_b : bigrammar

val pshift_b : char list -> bigrammar -> bigrammar

val coq_PSLL_b : bigrammar

val coq_PSRA_b : bigrammar

val coq_PSRL_b : bigrammar

val coq_PSUB_b : bigrammar

val coq_PSUBS_b : bigrammar

val coq_PSUBUS_b : bigrammar

val coq_PUNPCKH_b : bigrammar

val coq_PUNPCKL_b : bigrammar

val coq_PXOR_b : bigrammar

val coq_SSE_XMM_Reg_op_b : bigrammar

val coq_SSE_GP_Reg_op_b : bigrammar

val coq_SSE_MM_Reg_op_b : bigrammar

val modrm_xmm_ret_reg : bigrammar

val modrm_xmm : bigrammar

val modrm_mm_ret_reg : bigrammar

val modrm_mm : bigrammar

val modrm_xmm_byte : bigrammar

val ext_op_modrm_sse_noreg : char list -> bigrammar

val coq_ADDPS_b : bigrammar

val coq_ADDSS_b : bigrammar

val coq_ANDNPS_b : bigrammar

val coq_ANDPS_b : bigrammar

val coq_CMPPS_b : bigrammar

val coq_CMPSS_b : bigrammar

val coq_COMISS_b : bigrammar

val coq_CVTPI2PS_b : bigrammar

val coq_CVTPS2PI_b : bigrammar

val coq_CVTSI2SS_b : bigrammar

val ss2si_b : char list -> bigrammar

val coq_CVTSS2SI_b : bigrammar

val coq_CVTTPS2PI_b : bigrammar

val coq_CVTTSS2SI_b : bigrammar

val coq_DIVPS_b : bigrammar

val coq_DIVSS_b : bigrammar

val coq_LDMXCSR_b : bigrammar

val coq_MAXPS_b : bigrammar

val coq_MAXSS_b : bigrammar

val coq_MINPS_b : bigrammar

val coq_MINSS_b : bigrammar

val sse_mov_b : char list -> bigrammar

val coq_MOVAPS_b : bigrammar

val coq_MOVHLPS_b : bigrammar

val sse_mov_ps_b : char list -> bigrammar

val coq_MOVHPS_b : bigrammar

val coq_MOVLHPS_b : bigrammar

val coq_MOVLPS_b : bigrammar

val coq_MOVMSKPS_b : bigrammar

val coq_MOVSS_b : bigrammar

val coq_MOVUPS_b : bigrammar

val coq_MULPS_b : bigrammar

val coq_MULSS_b : bigrammar

val coq_ORPS_b : bigrammar

val coq_RCPPS_b : bigrammar

val coq_RCPSS_b : bigrammar

val coq_RSQRTPS_b : bigrammar

val coq_RSQRTSS_b : bigrammar

val coq_SHUFPS_b : bigrammar

val coq_SQRTPS_b : bigrammar

val coq_SQRTSS_b : bigrammar

val coq_STMXCSR_b : bigrammar

val coq_SUBPS_b : bigrammar

val coq_SUBSS_b : bigrammar

val coq_UCOMISS_b : bigrammar

val coq_UNPCKHPS_b : bigrammar

val coq_UNPCKLPS_b : bigrammar

val coq_XORPS_b : bigrammar

val coq_PAVGB_b : bigrammar

val coq_PEXTRW_b : bigrammar

val coq_PINSRW_b : bigrammar

val coq_PMAXSW_b : bigrammar

val coq_PMAXUB_b : bigrammar

val coq_PMINSW_b : bigrammar

val coq_PMINUB_b : bigrammar

val coq_PMOVMSKB_b : bigrammar

val coq_PSADBW_b : bigrammar

val coq_PSHUFW_b : bigrammar

val coq_MASKMOVQ_b : bigrammar

val coq_MOVNTPS_b : bigrammar

val coq_MOVNTQ_b : bigrammar

val coq_PREFETCHT0_b : bigrammar

val coq_PREFETCHT1_b : bigrammar

val coq_PREFETCHT2_b : bigrammar

val coq_PREFETCHNTA_b : bigrammar

val coq_SFENCE_b : bigrammar
