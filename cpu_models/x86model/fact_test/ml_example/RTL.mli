open BinInt
open BinPos
open Bits
open Coqlib
open Fappli_IEEE
open Fappli_IEEE_bits
open Fcore_Zaux
open Maps
open Monad
open Nat0
open PeanoNat
open ZArith_dec

type __ = Obj.t

type int = Word.int

module type MACHINE_SIG =
 sig
  type location

  type array

  val size_addr : Big.big_int

  type mach_state

  val get_location : Big.big_int -> location -> mach_state -> Word.int

  val set_location :
    Big.big_int -> location -> Word.int -> mach_state -> mach_state

  val array_sub :
    Big.big_int -> Big.big_int -> array -> Word.int -> mach_state -> Word.int

  val array_upd :
    Big.big_int -> Big.big_int -> array -> Word.int -> Word.int -> mach_state
    -> mach_state
 end

module RTL :
 functor (M:MACHINE_SIG) ->
 sig
  module AddrIndexed :
   sig
    type t = int

    val index : int -> Big.big_int

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
  | Coq_imm_rtl_exp of Big.big_int * int
  | Coq_get_loc_rtl_exp of Big.big_int * M.location
  | Coq_get_ps_reg_rtl_exp of Big.big_int * pseudo_reg
  | Coq_get_array_rtl_exp of Big.big_int * Big.big_int * M.array * rtl_exp
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
    int -> 'a1) -> (Big.big_int -> M.location -> 'a1) -> (Big.big_int ->
    pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array -> rtl_exp
    -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> 'a1) ->
    (Big.big_int -> Big.big_int -> __ -> float_arith_op -> rtl_exp -> 'a1 ->
    rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> Big.big_int
    -> Big.big_int -> Big.big_int -> __ -> __ -> rtl_exp -> 'a1 -> rtl_exp ->
    'a1 -> 'a1) -> Big.big_int -> rtl_exp -> 'a1

  val rtl_exp_rec :
    (Big.big_int -> bit_vector_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1)
    -> (Big.big_int -> test_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
    'a1) -> (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) ->
    (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int ->
    int -> 'a1) -> (Big.big_int -> M.location -> 'a1) -> (Big.big_int ->
    pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array -> rtl_exp
    -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> 'a1) ->
    (Big.big_int -> Big.big_int -> __ -> float_arith_op -> rtl_exp -> 'a1 ->
    rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> Big.big_int
    -> Big.big_int -> Big.big_int -> __ -> __ -> rtl_exp -> 'a1 -> rtl_exp ->
    'a1 -> 'a1) -> Big.big_int -> rtl_exp -> 'a1

  type rtl_instr =
  | Coq_set_loc_rtl of Big.big_int * rtl_exp * M.location
  | Coq_set_ps_reg_rtl of Big.big_int * rtl_exp * pseudo_reg
  | Coq_set_array_rtl of Big.big_int * Big.big_int * M.array * rtl_exp
     * rtl_exp
  | Coq_set_byte_rtl of rtl_exp * rtl_exp
  | Coq_advance_oracle_rtl
  | Coq_if_rtl of rtl_exp * rtl_instr
  | Coq_error_rtl
  | Coq_trap_rtl

  val rtl_instr_rect :
    (Big.big_int -> rtl_exp -> M.location -> 'a1) -> (Big.big_int -> rtl_exp
    -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array ->
    rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp -> 'a1) -> 'a1 ->
    (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> rtl_instr -> 'a1

  val rtl_instr_rec :
    (Big.big_int -> rtl_exp -> M.location -> 'a1) -> (Big.big_int -> rtl_exp
    -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array ->
    rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp -> 'a1) -> 'a1 ->
    (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> rtl_instr -> 'a1

  type oracle = { oracle_bits : (Big.big_int -> Big.big_int -> int);
                  oracle_offset : Big.big_int }

  val oracle_bits : oracle -> Big.big_int -> Big.big_int -> int

  val oracle_offset : oracle -> Big.big_int

  type pseudo_env = Big.big_int -> pseudo_reg -> int

  type rtl_state = { rtl_oracle : oracle; rtl_env : pseudo_env;
                     rtl_mach_state : M.mach_state;
                     rtl_memory : int8 AddrMap.t }

  val rtl_oracle : rtl_state -> oracle

  val rtl_env : rtl_state -> pseudo_env

  val rtl_mach_state : rtl_state -> M.mach_state

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
    Big.big_int -> pseudo_reg -> int -> pseudo_env -> pseudo_env

  val set_loc : Big.big_int -> M.location -> int -> unit coq_RTL

  val set_ps_reg : Big.big_int -> pseudo_reg -> int -> unit coq_RTL

  val set_array :
    Big.big_int -> Big.big_int -> M.array -> int -> int -> unit coq_RTL

  val set_byte : int -> int -> unit coq_RTL

  val advance_oracle : unit coq_RTL

  val interp_arith : Big.big_int -> bit_vector_op -> int -> int -> int

  val interp_test : Big.big_int -> test_op -> int -> int -> int

  val dec_rounding_mode : int -> rounding_mode

  type rtl_float = binary_float

  val default_nan_pl : Big.big_int -> bool * nan_pl

  val nan_pl_conv :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> nan_pl ->
    nan_pl

  val unop_nan_pl : Big.big_int -> Big.big_int -> rtl_float -> bool * nan_pl

  val binop_nan_pl :
    Big.big_int -> Big.big_int -> rtl_float -> rtl_float -> bool * nan_pl

  val interp_farith :
    Big.big_int -> Big.big_int -> float_arith_op -> int -> int -> int -> int

  val cond_Zopp : bool -> Big.big_int -> Big.big_int

  val binary_float_cast :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> int ->
    rtl_float -> rtl_float

  val interp_fcast :
    Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> int -> int ->
    int

  val interp_rtl_exp : Big.big_int -> rtl_exp -> rtl_state -> int

  val interp_rtl_exp_comp : Big.big_int -> rtl_exp -> int coq_RTL

  val get_loc : Big.big_int -> M.location -> int coq_RTL

  val get_array : Big.big_int -> Big.big_int -> M.array -> int -> int coq_RTL

  val get_byte : int -> int coq_RTL

  val get_random : Big.big_int -> int coq_RTL

  val interp_rtl : rtl_instr -> unit coq_RTL

  type instruction = { instr_assembly : char list; instr_rtl : rtl_instr list }

  val instr_assembly : instruction -> char list

  val instr_rtl : instruction -> rtl_instr list
 end
