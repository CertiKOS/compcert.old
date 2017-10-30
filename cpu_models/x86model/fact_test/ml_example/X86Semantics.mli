open BinInt
open Bits
open Coqlib
open Datatypes
open Fappli_IEEE
open List0
open Maps
open Monad
open Nat0
open X86Syntax
open Zpower

type __ = Obj.t

module X86_MACHINE :
 sig
  val size_addr : Big.big_int

  type flag =
  | ID
  | VIP
  | VIF
  | AC
  | VM
  | RF
  | NT
  | IOPL
  | OF
  | DF
  | IF_flag
  | TF
  | SF
  | ZF
  | AF
  | PF
  | CF

  val flag_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag -> 'a1

  val flag_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag -> 'a1

  val flag_eq_dec : flag -> flag -> bool

  type fpu_flag =
  | F_Busy
  | F_C3
  | F_C2
  | F_C1
  | F_C0
  | F_ES
  | F_SF
  | F_PE
  | F_UE
  | F_OE
  | F_ZE
  | F_DE
  | F_IE

  val fpu_flag_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> fpu_flag -> 'a1

  val fpu_flag_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> fpu_flag -> 'a1

  type fpu_ctrl_flag =
  | F_Res15
  | F_Res14
  | F_Res13
  | F_Res7
  | F_Res6
  | F_IC
  | F_PM
  | F_UM
  | F_OM
  | F_ZM
  | F_DM
  | F_IM

  val fpu_ctrl_flag_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> fpu_ctrl_flag -> 'a1

  val fpu_ctrl_flag_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> fpu_ctrl_flag -> 'a1

  val size11 : Big.big_int

  val size48 : Big.big_int

  type int48 = Word.int

  type loc =
  | Coq_reg_loc of register
  | Coq_seg_reg_start_loc of segment_register
  | Coq_seg_reg_limit_loc of segment_register
  | Coq_flag_loc of flag
  | Coq_control_register_loc of control_register
  | Coq_debug_register_loc of debug_register
  | Coq_pc_loc
  | Coq_fpu_stktop_loc
  | Coq_fpu_flag_loc of fpu_flag
  | Coq_fpu_rctrl_loc
  | Coq_fpu_pctrl_loc
  | Coq_fpu_ctrl_flag_loc of fpu_ctrl_flag
  | Coq_fpu_lastInstrPtr_loc
  | Coq_fpu_lastDataPtr_loc
  | Coq_fpu_lastOpcode_loc

  val loc_rect :
    (register -> 'a1) -> (segment_register -> 'a1) -> (segment_register ->
    'a1) -> (flag -> 'a1) -> (control_register -> 'a1) -> (debug_register ->
    'a1) -> 'a1 -> 'a1 -> (fpu_flag -> 'a1) -> 'a1 -> 'a1 -> (fpu_ctrl_flag
    -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> Big.big_int -> loc -> 'a1

  val loc_rec :
    (register -> 'a1) -> (segment_register -> 'a1) -> (segment_register ->
    'a1) -> (flag -> 'a1) -> (control_register -> 'a1) -> (debug_register ->
    'a1) -> 'a1 -> 'a1 -> (fpu_flag -> 'a1) -> 'a1 -> 'a1 -> (fpu_ctrl_flag
    -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> Big.big_int -> loc -> 'a1

  type location = loc

  type arr =
  | Coq_fpu_datareg
  | Coq_fpu_tag

  val arr_rect : 'a1 -> 'a1 -> Big.big_int -> Big.big_int -> arr -> 'a1

  val arr_rec : 'a1 -> 'a1 -> Big.big_int -> Big.big_int -> arr -> 'a1

  type array = arr

  type ('a, 'b) fmap = 'a -> 'b

  val upd :
    ('a1 -> 'a1 -> bool) -> ('a1, 'a2) fmap -> 'a1 -> 'a2 -> ('a1, 'a2) fmap

  val look : ('a1, 'a2) fmap -> 'a1 -> 'a2

  type core_state = { gp_regs : (register, int32) fmap;
                      seg_regs_starts : (segment_register, int32) fmap;
                      seg_regs_limits : (segment_register, int32) fmap;
                      flags_reg : (flag, int1) fmap;
                      control_regs : (control_register, int32) fmap;
                      debug_regs : (debug_register, int32) fmap;
                      pc_reg : RTL.int }

  val gp_regs : core_state -> (register, int32) fmap

  val seg_regs_starts : core_state -> (segment_register, int32) fmap

  val seg_regs_limits : core_state -> (segment_register, int32) fmap

  val flags_reg : core_state -> (flag, int1) fmap

  val control_regs : core_state -> (control_register, int32) fmap

  val debug_regs : core_state -> (debug_register, int32) fmap

  val pc_reg : core_state -> RTL.int

  type fpu_state = { fpu_data_regs : (int3, int80) fmap; fpu_status : 
                     int16; fpu_control : int16;
                     fpu_tags : (int3, int2) fmap; fpu_lastInstrPtr : 
                     int48; fpu_lastDataPtr : int48; fpu_lastOpcode : 
                     RTL.int }

  val fpu_data_regs : fpu_state -> (int3, int80) fmap

  val fpu_status : fpu_state -> int16

  val fpu_control : fpu_state -> int16

  val fpu_tags : fpu_state -> (int3, int2) fmap

  val fpu_lastInstrPtr : fpu_state -> int48

  val fpu_lastDataPtr : fpu_state -> int48

  val fpu_lastOpcode : fpu_state -> RTL.int

  type mach = { core : core_state; fpu : fpu_state }

  val core : mach -> core_state

  val fpu : mach -> fpu_state

  type mach_state = mach

  val get_bits_rng :
    Big.big_int -> RTL.int -> Big.big_int -> Big.big_int -> RTL.int

  val set_bits_rng :
    Big.big_int -> RTL.int -> Big.big_int -> Big.big_int -> RTL.int -> RTL.int

  val get_bit : Big.big_int -> RTL.int -> Big.big_int -> int1

  val set_bit : Big.big_int -> RTL.int -> Big.big_int -> bool -> RTL.int

  val get_fpu_flag_reg : fpu_flag -> fpu_state -> int1

  val get_stktop_reg : fpu_state -> int3

  val get_fpu_ctrl_flag_reg : fpu_ctrl_flag -> fpu_state -> int1

  val get_rctrl_reg : fpu_state -> int2

  val get_pctrl_reg : fpu_state -> int2

  val get_location : Big.big_int -> loc -> mach_state -> RTL.int

  val set_gp_reg : register -> int32 -> mach -> mach

  val set_seg_reg_start : segment_register -> int32 -> mach -> mach

  val set_seg_reg_limit : segment_register -> int32 -> mach -> mach

  val set_flags_reg : flag -> int1 -> mach -> mach

  val set_control_reg : control_register -> int32 -> mach -> mach

  val set_debug_reg : debug_register -> int32 -> mach -> mach

  val set_pc : RTL.int -> mach -> mach

  val set_fpu_stktop_reg : int3 -> mach -> mach

  val set_fpu_flags_reg : fpu_flag -> int1 -> mach -> mach

  val set_fpu_rctrl_reg : int2 -> mach -> mach

  val set_fpu_pctrl_reg : int2 -> mach -> mach

  val set_fpu_ctrl_reg : fpu_ctrl_flag -> int1 -> mach -> mach

  val set_fpu_lastInstrPtr_reg : int48 -> mach -> mach

  val set_fpu_lastDataPtr_reg : int48 -> mach -> mach

  val set_lastOpcode_reg : RTL.int -> mach -> mach

  val set_location : Big.big_int -> loc -> RTL.int -> mach -> mach_state

  val array_sub :
    Big.big_int -> Big.big_int -> array -> RTL.int -> mach_state -> RTL.int

  val set_fpu_datareg : int3 -> int80 -> mach -> mach

  val set_fpu_tags_reg : Word.int -> int2 -> mach -> mach

  val array_upd :
    Big.big_int -> Big.big_int -> array -> RTL.int -> RTL.int -> mach ->
    mach_state
 end

module X86_RTL :
 sig
  module AddrIndexed :
   sig
    type t = RTL.int

    val index : RTL.int -> Big.big_int

    val eq : Word.int -> Word.int -> bool
   end

  module AddrMap :
   sig
    type elt = AddrIndexed.t

    val elt_eq : AddrIndexed.t -> AddrIndexed.t -> bool

    type 'x t = 'x PMap.t

    val eq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

    val init : 'a1 -> 'a1 * 'a1 PTree.t

    val get : AddrIndexed.t -> 'a1 t -> 'a1

    val set : AddrIndexed.t -> 'a1 -> 'a1 t -> 'a1 * 'a1 PTree.t

    val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t
   end

  type pseudo_reg =
    Big.big_int
    (* singleton inductive, whose constructor was ps_reg *)

  val pseudo_reg_rect :
    Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1

  val pseudo_reg_rec :
    Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1

  type bit_vector_op =
  | Coq_add_op
  | Coq_sub_op
  | Coq_mul_op
  | Coq_divs_op
  | Coq_divu_op
  | Coq_modu_op
  | Coq_mods_op
  | Coq_and_op
  | Coq_or_op
  | Coq_xor_op
  | Coq_shl_op
  | Coq_shr_op
  | Coq_shru_op
  | Coq_ror_op
  | Coq_rol_op

  val bit_vector_op_rect :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1

  val bit_vector_op_rec :
    'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1

  type float_arith_op =
  | Coq_fadd_op
  | Coq_fsub_op
  | Coq_fmul_op
  | Coq_fdiv_op

  val float_arith_op_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> float_arith_op -> 'a1

  val float_arith_op_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> float_arith_op -> 'a1

  type test_op =
  | Coq_eq_op
  | Coq_lt_op
  | Coq_ltu_op

  val test_op_rect : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1

  val test_op_rec : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1

  type rounding_mode = mode

  type rtl_exp =
  | Coq_arith_rtl_exp of Big.big_int * bit_vector_op * rtl_exp * rtl_exp
  | Coq_test_rtl_exp of Big.big_int * test_op * rtl_exp * rtl_exp
  | Coq_if_rtl_exp of Big.big_int * rtl_exp * rtl_exp * rtl_exp
  | Coq_cast_s_rtl_exp of Big.big_int * Big.big_int * rtl_exp
  | Coq_cast_u_rtl_exp of Big.big_int * Big.big_int * rtl_exp
  | Coq_imm_rtl_exp of Big.big_int * RTL.int
  | Coq_get_loc_rtl_exp of Big.big_int * X86_MACHINE.location
  | Coq_get_ps_reg_rtl_exp of Big.big_int * pseudo_reg
  | Coq_get_array_rtl_exp of Big.big_int * Big.big_int * X86_MACHINE.array
     * rtl_exp
  | Coq_get_byte_rtl_exp of rtl_exp
  | Coq_get_random_rtl_exp of Big.big_int
  | Coq_farith_rtl_exp of Big.big_int * Big.big_int * float_arith_op
     * rtl_exp * rtl_exp * rtl_exp
  | Coq_fcast_rtl_exp of Big.big_int * Big.big_int * Big.big_int
     * Big.big_int * rtl_exp * rtl_exp

  val rtl_exp_rect :
    (Big.big_int -> bit_vector_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1)
    -> (Big.big_int -> test_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
    'a1) -> (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int ->
    RTL.int -> 'a1) -> (Big.big_int -> X86_MACHINE.location -> 'a1) ->
    (Big.big_int -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int ->
    X86_MACHINE.array -> rtl_exp -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> 'a1) -> (Big.big_int -> Big.big_int -> __ ->
    float_arith_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
    'a1) -> (Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> __
    -> __ -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> Big.big_int ->
    rtl_exp -> 'a1

  val rtl_exp_rec :
    (Big.big_int -> bit_vector_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1)
    -> (Big.big_int -> test_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
    'a1) -> (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int ->
    RTL.int -> 'a1) -> (Big.big_int -> X86_MACHINE.location -> 'a1) ->
    (Big.big_int -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int ->
    X86_MACHINE.array -> rtl_exp -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> 'a1) -> (Big.big_int -> Big.big_int -> __ ->
    float_arith_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
    'a1) -> (Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> __
    -> __ -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> Big.big_int ->
    rtl_exp -> 'a1

  type rtl_instr =
  | Coq_set_loc_rtl of Big.big_int * rtl_exp * X86_MACHINE.location
  | Coq_set_ps_reg_rtl of Big.big_int * rtl_exp * pseudo_reg
  | Coq_set_array_rtl of Big.big_int * Big.big_int * X86_MACHINE.array
     * rtl_exp * rtl_exp
  | Coq_set_byte_rtl of rtl_exp * rtl_exp
  | Coq_advance_oracle_rtl
  | Coq_if_rtl of rtl_exp * rtl_instr
  | Coq_error_rtl
  | Coq_trap_rtl

  val rtl_instr_rect :
    (Big.big_int -> rtl_exp -> X86_MACHINE.location -> 'a1) -> (Big.big_int
    -> rtl_exp -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int ->
    X86_MACHINE.array -> rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp ->
    'a1) -> 'a1 -> (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
    rtl_instr -> 'a1

  val rtl_instr_rec :
    (Big.big_int -> rtl_exp -> X86_MACHINE.location -> 'a1) -> (Big.big_int
    -> rtl_exp -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int ->
    X86_MACHINE.array -> rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp ->
    'a1) -> 'a1 -> (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 ->
    rtl_instr -> 'a1

  type oracle = { oracle_bits : (Big.big_int -> Big.big_int -> RTL.int);
                  oracle_offset : Big.big_int }

  val oracle_bits : oracle -> Big.big_int -> Big.big_int -> RTL.int

  val oracle_offset : oracle -> Big.big_int

  type pseudo_env = Big.big_int -> pseudo_reg -> RTL.int

  type rtl_state = { rtl_oracle : oracle; rtl_env : pseudo_env;
                     rtl_mach_state : X86_MACHINE.mach_state;
                     rtl_memory : int8 AddrMap.t }

  val rtl_oracle : rtl_state -> oracle

  val rtl_env : rtl_state -> pseudo_env

  val rtl_mach_state : rtl_state -> X86_MACHINE.mach_state

  val rtl_memory : rtl_state -> int8 AddrMap.t

  type 'a coq_RTL_ans =
  | Fail_ans
  | Trap_ans
  | Okay_ans of 'a

  val coq_RTL_ans_rect : 'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2

  val coq_RTL_ans_rec : 'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2

  type 't coq_RTL = rtl_state -> 't coq_RTL_ans * rtl_state

  val coq_RTL_monad : __ coq_RTL coq_Monad

  val coq_Fail : 'a1 coq_RTL

  val coq_Trap : 'a1 coq_RTL

  val empty_env : pseudo_env

  val eq_pseudo_reg : Big.big_int -> pseudo_reg -> pseudo_reg -> bool

  val update_ps_env :
    Big.big_int -> pseudo_reg -> RTL.int -> pseudo_env -> pseudo_env

  val set_loc : Big.big_int -> X86_MACHINE.location -> RTL.int -> unit coq_RTL

  val set_ps_reg : Big.big_int -> pseudo_reg -> RTL.int -> unit coq_RTL

  val set_array :
    Big.big_int -> Big.big_int -> X86_MACHINE.array -> RTL.int -> RTL.int ->
    unit coq_RTL

  val set_byte : RTL.int -> RTL.int -> unit coq_RTL

  val advance_oracle : unit coq_RTL

  val interp_arith :
    Big.big_int -> bit_vector_op -> RTL.int -> RTL.int -> RTL.int

  val interp_test : Big.big_int -> test_op -> RTL.int -> RTL.int -> RTL.int

  val dec_rounding_mode : RTL.int -> rounding_mode

  type rtl_float = binary_float

  val default_nan_pl : Big.big_int -> bool * nan_pl

  val nan_pl_conv :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> nan_pl ->
    nan_pl

  val unop_nan_pl : Big.big_int -> Big.big_int -> rtl_float -> bool * nan_pl

  val binop_nan_pl :
    Big.big_int -> Big.big_int -> rtl_float -> rtl_float -> bool * nan_pl

  val interp_farith :
    Big.big_int -> Big.big_int -> float_arith_op -> RTL.int -> RTL.int ->
    RTL.int -> RTL.int

  val cond_Zopp : bool -> Big.big_int -> Big.big_int

  val binary_float_cast :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> RTL.int ->
    rtl_float -> rtl_float

  val interp_fcast :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> RTL.int ->
    RTL.int -> RTL.int

  val interp_rtl_exp : Big.big_int -> rtl_exp -> rtl_state -> RTL.int

  val interp_rtl_exp_comp : Big.big_int -> rtl_exp -> RTL.int coq_RTL

  val get_loc : Big.big_int -> X86_MACHINE.location -> RTL.int coq_RTL

  val get_array :
    Big.big_int -> Big.big_int -> X86_MACHINE.array -> RTL.int -> RTL.int
    coq_RTL

  val get_byte : RTL.int -> RTL.int coq_RTL

  val get_random : Big.big_int -> RTL.int coq_RTL

  val interp_rtl : rtl_instr -> unit coq_RTL

  type instruction = { instr_assembly : char list; instr_rtl : rtl_instr list }

  val instr_assembly : instruction -> char list

  val instr_rtl : instruction -> rtl_instr list
 end

module X86_Compile :
 sig
  type conv_state = { c_rev_i : X86_RTL.rtl_instr list; c_next : Big.big_int }

  val c_rev_i : conv_state -> X86_RTL.rtl_instr list

  val c_next : conv_state -> Big.big_int

  type 't coq_Conv = conv_state -> 't * conv_state

  val coq_Conv_monad : __ coq_Conv coq_Monad

  val runConv : unit coq_Conv -> X86_RTL.rtl_instr list

  val coq_EMIT : X86_RTL.rtl_instr -> unit coq_Conv

  val raise_error : unit coq_Conv

  val raise_trap : unit coq_Conv

  val no_op : unit coq_Conv

  val load_int : Big.big_int -> RTL.int -> X86_RTL.rtl_exp coq_Conv

  val arith :
    Big.big_int -> X86_RTL.bit_vector_op -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val test :
    Big.big_int -> X86_RTL.test_op -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp coq_Conv

  val cast_u :
    Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val cast_s :
    Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val read_loc : Big.big_int -> X86_MACHINE.loc -> X86_RTL.rtl_exp coq_Conv

  val write_loc :
    Big.big_int -> X86_RTL.rtl_exp -> X86_MACHINE.loc -> unit coq_Conv

  val write_ps_and_fresh :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val read_byte : X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val write_byte : X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv

  val if_exp :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp coq_Conv

  val if_trap : X86_RTL.rtl_exp -> unit coq_Conv

  val if_set_loc :
    X86_RTL.rtl_exp -> Big.big_int -> X86_RTL.rtl_exp -> X86_MACHINE.location
    -> unit coq_Conv

  val choose : Big.big_int -> X86_RTL.rtl_exp coq_Conv

  val load_Z : Big.big_int -> Big.big_int -> X86_RTL.rtl_exp coq_Conv

  val load_reg : register -> X86_RTL.rtl_exp coq_Conv

  val set_reg : X86_RTL.rtl_exp -> register -> unit coq_Conv

  val get_seg_start : segment_register -> X86_RTL.rtl_exp coq_Conv

  val get_seg_limit : segment_register -> X86_RTL.rtl_exp coq_Conv

  val get_flag : X86_MACHINE.flag -> X86_RTL.rtl_exp coq_Conv

  val set_flag : X86_MACHINE.flag -> X86_RTL.rtl_exp -> unit coq_Conv

  val get_pc : X86_RTL.rtl_exp coq_Conv

  val set_pc : X86_RTL.rtl_exp -> unit coq_Conv

  val not : Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val test_neq :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    coq_Conv

  val undef_flag : X86_MACHINE.flag -> unit coq_Conv

  val scale_to_int32 : scale -> int32

  val compute_addr : address -> X86_RTL.rtl_exp coq_Conv

  val add_and_check_segment :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val lmem : segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val smem :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv

  val load_mem_n :
    segment_register -> X86_RTL.rtl_exp -> Big.big_int -> Big.big_int ->
    X86_RTL.rtl_exp coq_Conv

  val load_mem32 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val load_mem16 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val load_mem8 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val opsize : bool -> bool -> Big.big_int

  val load_mem :
    prefix -> bool -> segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    coq_Conv

  val iload_op32 : segment_register -> operand -> X86_RTL.rtl_exp coq_Conv

  val iload_op16 : segment_register -> operand -> X86_RTL.rtl_exp coq_Conv

  val iload_op8 : segment_register -> operand -> X86_RTL.rtl_exp coq_Conv

  val set_mem_n :
    segment_register -> X86_RTL.rtl_exp -> Big.big_int -> X86_RTL.rtl_exp ->
    Big.big_int -> unit coq_Conv

  val set_mem32 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv

  val set_mem16 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv

  val set_mem8 :
    segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv

  val set_mem :
    prefix -> bool -> segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    -> unit coq_Conv

  val iset_op32 :
    segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv

  val iset_op16 :
    segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv

  val iset_op8 :
    segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv

  val load_op :
    prefix -> bool -> segment_register -> operand -> X86_RTL.rtl_exp coq_Conv

  val set_op :
    prefix -> bool -> segment_register -> X86_RTL.rtl_exp -> operand -> unit
    coq_Conv

  val get_segment : prefix -> segment_register -> segment_register

  val op_contains_stack : operand -> bool

  val get_segment_op :
    prefix -> segment_register -> operand -> segment_register

  val get_segment_op2 :
    prefix -> segment_register -> operand -> operand -> segment_register

  val compute_cc : condition_type -> X86_RTL.rtl_exp coq_Conv

  val compute_parity_aux :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> Big.big_int ->
    X86_RTL.rtl_exp coq_Conv

  val compute_parity :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val conv_INC : prefix -> bool -> operand -> unit coq_Conv

  val conv_DEC : prefix -> bool -> operand -> unit coq_Conv

  val conv_ADC : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_STC : unit coq_Conv

  val conv_STD : unit coq_Conv

  val conv_CLC : unit coq_Conv

  val conv_CLD : unit coq_Conv

  val conv_CMC : unit coq_Conv

  val conv_LAHF : unit coq_Conv

  val conv_SAHF : unit coq_Conv

  val conv_ADD : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_SUB_CMP_generic :
    bool -> prefix -> bool -> operand -> operand -> operand ->
    segment_register -> segment_register -> segment_register -> unit coq_Conv

  val conv_CMP : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_SUB : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_NEG : prefix -> bool -> operand -> unit coq_Conv

  val conv_SBB : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_DIV : prefix -> bool -> operand -> unit coq_Conv

  val conv_IDIV : prefix -> bool -> operand -> unit coq_Conv

  val conv_IMUL :
    prefix -> bool -> operand -> operand option -> int32 option -> unit
    coq_Conv

  val conv_MUL : prefix -> bool -> operand -> unit coq_Conv

  val conv_shift :
    X86_RTL.bit_vector_op -> prefix -> bool -> operand -> reg_or_immed ->
    unit coq_Conv

  val conv_SHL : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_SAR : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_SHR : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_ROR : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_ROL : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_RCL : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val conv_RCR : prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv

  val size65 : Big.big_int

  val conv_SHLD :
    prefix -> operand -> register -> reg_or_immed -> unit coq_Conv

  val conv_SHRD :
    prefix -> operand -> register -> reg_or_immed -> unit coq_Conv

  val get_AH : X86_RTL.rtl_exp coq_Conv

  val set_AH : X86_RTL.rtl_exp -> unit coq_Conv

  val get_AL : X86_RTL.rtl_exp coq_Conv

  val set_AL : X86_RTL.rtl_exp -> unit coq_Conv

  val conv_AAA_AAS : X86_RTL.bit_vector_op -> unit coq_Conv

  val conv_AAD : unit coq_Conv

  val conv_AAM : unit coq_Conv

  val testcarryAdd :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp coq_Conv

  val testcarrySub :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp coq_Conv

  val conv_DAA_DAS :
    X86_RTL.bit_vector_op -> (X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv) -> unit coq_Conv

  val conv_logical_op :
    bool -> X86_RTL.bit_vector_op -> prefix -> bool -> operand -> operand ->
    unit coq_Conv

  val conv_AND : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_OR : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_XOR : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_TEST : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_NOT : prefix -> bool -> operand -> unit coq_Conv

  val conv_POP : prefix -> operand -> unit coq_Conv

  val conv_POPA : prefix -> unit coq_Conv

  val conv_PUSH : prefix -> bool -> operand -> unit coq_Conv

  val conv_PUSH_pseudo : prefix -> bool -> X86_RTL.rtl_exp -> unit coq_Conv

  val conv_PUSHA : prefix -> unit coq_Conv

  val conv_JMP :
    prefix -> bool -> bool -> operand -> selector option -> unit coq_Conv

  val conv_Jcc : prefix -> condition_type -> int32 -> unit coq_Conv

  val conv_CALL :
    prefix -> bool -> bool -> operand -> selector option -> unit coq_Conv

  val conv_RET : prefix -> bool -> int16 option -> unit coq_Conv

  val conv_LEAVE : prefix -> unit coq_Conv

  val conv_LOOP : prefix -> bool -> bool -> int8 -> unit coq_Conv

  val conv_BS_aux :
    Big.big_int -> bool -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    coq_Conv

  val conv_BS : bool -> prefix -> operand -> operand -> unit coq_Conv

  val conv_BSF : prefix -> operand -> operand -> unit coq_Conv

  val conv_BSR : prefix -> operand -> operand -> unit coq_Conv

  val get_Bit :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    coq_Conv

  val modify_Bit :
    Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp coq_Conv

  val set_Bit :
    prefix -> bool -> operand -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit
    coq_Conv

  val set_Bit_mem :
    prefix -> bool -> operand -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
    X86_RTL.rtl_exp -> unit coq_Conv

  val fbit : bool -> bool -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv

  val conv_BT : bool -> bool -> prefix -> operand -> operand -> unit coq_Conv

  val conv_BSWAP : prefix -> register -> unit coq_Conv

  val conv_CWDE : prefix -> unit coq_Conv

  val conv_CDQ : prefix -> unit coq_Conv

  val conv_MOV : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_CMOV :
    prefix -> bool -> condition_type -> operand -> operand -> unit coq_Conv

  val conv_MOV_extend :
    (Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
    coq_Conv) -> prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_MOVZX : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_MOVSX : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_XCHG : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_XADD : prefix -> bool -> operand -> operand -> unit coq_Conv

  val conv_CMPXCHG : prefix -> bool -> operand -> operand -> unit coq_Conv

  val string_op_reg_shift : register -> prefix -> bool -> unit coq_Conv

  val conv_MOVS : prefix -> bool -> unit coq_Conv

  val conv_STOS : prefix -> bool -> unit coq_Conv

  val conv_CMPS : prefix -> bool -> unit coq_Conv

  val conv_LEA : prefix -> operand -> operand -> unit coq_Conv

  val conv_HLT : prefix -> unit coq_Conv

  val conv_SETcc : prefix -> condition_type -> operand -> unit coq_Conv

  val check_prefix : prefix -> unit coq_Conv

  val instr_to_rtl : prefix -> instr -> X86_RTL.rtl_instr list
 end
