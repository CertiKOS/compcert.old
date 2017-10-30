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
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

module RTL =
 functor (M:MACHINE_SIG) ->
 struct
  module AddrIndexed =
   struct
    type t = int

    (** val index : int -> Big.big_int **)

    let index i =
      ZIndexed.index i

    (** val eq : Word.int -> Word.int -> bool **)

    let eq x y =
      zeq x y
   end

  module AddrMap = IMap(AddrIndexed)

  type pseudo_reg =
    Big.big_int
    (* singleton inductive, whose constructor was ps_reg *)

  (** val pseudo_reg_rect :
      Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1 **)

  let pseudo_reg_rect _ f p =
    f p

  (** val pseudo_reg_rec :
      Big.big_int -> (Big.big_int -> 'a1) -> pseudo_reg -> 'a1 **)

  let pseudo_reg_rec _ f p =
    f p

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

  (** val bit_vector_op_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1 **)

  let bit_vector_op_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Coq_add_op -> f
  | Coq_sub_op -> f0
  | Coq_mul_op -> f1
  | Coq_divs_op -> f2
  | Coq_divu_op -> f3
  | Coq_modu_op -> f4
  | Coq_mods_op -> f5
  | Coq_and_op -> f6
  | Coq_or_op -> f7
  | Coq_xor_op -> f8
  | Coq_shl_op -> f9
  | Coq_shr_op -> f10
  | Coq_shru_op -> f11
  | Coq_ror_op -> f12
  | Coq_rol_op -> f13

  (** val bit_vector_op_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> bit_vector_op -> 'a1 **)

  let bit_vector_op_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 = function
  | Coq_add_op -> f
  | Coq_sub_op -> f0
  | Coq_mul_op -> f1
  | Coq_divs_op -> f2
  | Coq_divu_op -> f3
  | Coq_modu_op -> f4
  | Coq_mods_op -> f5
  | Coq_and_op -> f6
  | Coq_or_op -> f7
  | Coq_xor_op -> f8
  | Coq_shl_op -> f9
  | Coq_shr_op -> f10
  | Coq_shru_op -> f11
  | Coq_ror_op -> f12
  | Coq_rol_op -> f13

  type float_arith_op =
  | Coq_fadd_op
  | Coq_fsub_op
  | Coq_fmul_op
  | Coq_fdiv_op

  (** val float_arith_op_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> float_arith_op -> 'a1 **)

  let float_arith_op_rect f f0 f1 f2 = function
  | Coq_fadd_op -> f
  | Coq_fsub_op -> f0
  | Coq_fmul_op -> f1
  | Coq_fdiv_op -> f2

  (** val float_arith_op_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> float_arith_op -> 'a1 **)

  let float_arith_op_rec f f0 f1 f2 = function
  | Coq_fadd_op -> f
  | Coq_fsub_op -> f0
  | Coq_fmul_op -> f1
  | Coq_fdiv_op -> f2

  type test_op =
  | Coq_eq_op
  | Coq_lt_op
  | Coq_ltu_op

  (** val test_op_rect : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1 **)

  let test_op_rect f f0 f1 = function
  | Coq_eq_op -> f
  | Coq_lt_op -> f0
  | Coq_ltu_op -> f1

  (** val test_op_rec : 'a1 -> 'a1 -> 'a1 -> test_op -> 'a1 **)

  let test_op_rec f f0 f1 = function
  | Coq_eq_op -> f
  | Coq_lt_op -> f0
  | Coq_ltu_op -> f1

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

  (** val rtl_exp_rect :
      (Big.big_int -> bit_vector_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
      'a1) -> (Big.big_int -> test_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
      'a1) -> (Big.big_int -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp ->
      'a1 -> 'a1) -> (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) ->
      (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int
      -> int -> 'a1) -> (Big.big_int -> M.location -> 'a1) -> (Big.big_int ->
      pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array -> rtl_exp
      -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> 'a1) ->
      (Big.big_int -> Big.big_int -> __ -> float_arith_op -> rtl_exp -> 'a1
      -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int ->
      Big.big_int -> Big.big_int -> Big.big_int -> __ -> __ -> rtl_exp -> 'a1
      -> rtl_exp -> 'a1 -> 'a1) -> Big.big_int -> rtl_exp -> 'a1 **)

  let rec rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ = function
  | Coq_arith_rtl_exp (s, b, e1, e2) ->
    f s b e1 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1) e2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_test_rtl_exp (s, top, e1, e2) ->
    f0 s top e1 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1)
      e2 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_if_rtl_exp (s, cond, e1, e2) ->
    f1 s cond
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size1 cond) e1
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1) e2
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_cast_s_rtl_exp (s1, s2, e) ->
    f2 s1 s2 e (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1 e)
  | Coq_cast_u_rtl_exp (s1, s2, e) ->
    f3 s1 s2 e (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1 e)
  | Coq_imm_rtl_exp (s, i) -> f4 s i
  | Coq_get_loc_rtl_exp (s, l) -> f5 s l
  | Coq_get_ps_reg_rtl_exp (s, ps) -> f6 s ps
  | Coq_get_array_rtl_exp (l, s, a, r0) ->
    f7 l s a r0 (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 l r0)
  | Coq_get_byte_rtl_exp addr ->
    f8 addr
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 M.size_addr addr)
  | Coq_get_random_rtl_exp s -> f9 s
  | Coq_farith_rtl_exp (ew, mw, fop, rounding, x, x0) ->
    let len = add (Pos.to_nat ew) (Pos.to_nat mw) in
    f10 ew mw __ fop rounding
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size2 rounding) x
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 len x) x0
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 len x0)
  | Coq_fcast_rtl_exp (ew1, mw1, ew2, mw2, rounding, r0) ->
    f11 ew1 mw1 ew2 mw2 __ __ rounding
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size2 rounding)
      r0
      (rtl_exp_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
        (add (Pos.to_nat ew1) (Pos.to_nat mw1)) r0)

  (** val rtl_exp_rec :
      (Big.big_int -> bit_vector_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
      'a1) -> (Big.big_int -> test_op -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 ->
      'a1) -> (Big.big_int -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> rtl_exp ->
      'a1 -> 'a1) -> (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) ->
      (Big.big_int -> Big.big_int -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int
      -> int -> 'a1) -> (Big.big_int -> M.location -> 'a1) -> (Big.big_int ->
      pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array -> rtl_exp
      -> 'a1 -> 'a1) -> (rtl_exp -> 'a1 -> 'a1) -> (Big.big_int -> 'a1) ->
      (Big.big_int -> Big.big_int -> __ -> float_arith_op -> rtl_exp -> 'a1
      -> rtl_exp -> 'a1 -> rtl_exp -> 'a1 -> 'a1) -> (Big.big_int ->
      Big.big_int -> Big.big_int -> Big.big_int -> __ -> __ -> rtl_exp -> 'a1
      -> rtl_exp -> 'a1 -> 'a1) -> Big.big_int -> rtl_exp -> 'a1 **)

  let rec rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 _ = function
  | Coq_arith_rtl_exp (s, b, e1, e2) ->
    f s b e1 (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1) e2
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_test_rtl_exp (s, top, e1, e2) ->
    f0 s top e1 (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1) e2
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_if_rtl_exp (s, cond, e1, e2) ->
    f1 s cond
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size1 cond) e1
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e1) e2
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s e2)
  | Coq_cast_s_rtl_exp (s1, s2, e) ->
    f2 s1 s2 e (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1 e)
  | Coq_cast_u_rtl_exp (s1, s2, e) ->
    f3 s1 s2 e (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1 e)
  | Coq_imm_rtl_exp (s, i) -> f4 s i
  | Coq_get_loc_rtl_exp (s, l) -> f5 s l
  | Coq_get_ps_reg_rtl_exp (s, ps) -> f6 s ps
  | Coq_get_array_rtl_exp (l, s, a, r0) ->
    f7 l s a r0 (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 l r0)
  | Coq_get_byte_rtl_exp addr ->
    f8 addr
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 M.size_addr addr)
  | Coq_get_random_rtl_exp s -> f9 s
  | Coq_farith_rtl_exp (ew, mw, fop, rounding, x, x0) ->
    let len = add (Pos.to_nat ew) (Pos.to_nat mw) in
    f10 ew mw __ fop rounding
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size2 rounding) x
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 len x) x0
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 len x0)
  | Coq_fcast_rtl_exp (ew1, mw1, ew2, mw2, rounding, r0) ->
    f11 ew1 mw1 ew2 mw2 __ __ rounding
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 size2 rounding) r0
      (rtl_exp_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
        (add (Pos.to_nat ew1) (Pos.to_nat mw1)) r0)

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

  (** val rtl_instr_rect :
      (Big.big_int -> rtl_exp -> M.location -> 'a1) -> (Big.big_int ->
      rtl_exp -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array
      -> rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp -> 'a1) -> 'a1 ->
      (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> rtl_instr -> 'a1 **)

  let rec rtl_instr_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_set_loc_rtl (s, e, l) -> f s e l
  | Coq_set_ps_reg_rtl (s, e, ps) -> f0 s e ps
  | Coq_set_array_rtl (l, s, arr, e1, e2) -> f1 l s arr e1 e2
  | Coq_set_byte_rtl (e, addr) -> f2 e addr
  | Coq_advance_oracle_rtl -> f3
  | Coq_if_rtl (r0, r1) ->
    f4 r0 r1 (rtl_instr_rect f f0 f1 f2 f3 f4 f5 f6 r1)
  | Coq_error_rtl -> f5
  | Coq_trap_rtl -> f6

  (** val rtl_instr_rec :
      (Big.big_int -> rtl_exp -> M.location -> 'a1) -> (Big.big_int ->
      rtl_exp -> pseudo_reg -> 'a1) -> (Big.big_int -> Big.big_int -> M.array
      -> rtl_exp -> rtl_exp -> 'a1) -> (rtl_exp -> rtl_exp -> 'a1) -> 'a1 ->
      (rtl_exp -> rtl_instr -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> rtl_instr -> 'a1 **)

  let rec rtl_instr_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | Coq_set_loc_rtl (s, e, l) -> f s e l
  | Coq_set_ps_reg_rtl (s, e, ps) -> f0 s e ps
  | Coq_set_array_rtl (l, s, arr, e1, e2) -> f1 l s arr e1 e2
  | Coq_set_byte_rtl (e, addr) -> f2 e addr
  | Coq_advance_oracle_rtl -> f3
  | Coq_if_rtl (r0, r1) -> f4 r0 r1 (rtl_instr_rec f f0 f1 f2 f3 f4 f5 f6 r1)
  | Coq_error_rtl -> f5
  | Coq_trap_rtl -> f6

  type oracle = { oracle_bits : (Big.big_int -> Big.big_int -> int);
                  oracle_offset : Big.big_int }

  (** val oracle_bits : oracle -> Big.big_int -> Big.big_int -> int **)

  let oracle_bits o =
    o.oracle_bits

  (** val oracle_offset : oracle -> Big.big_int **)

  let oracle_offset o =
    o.oracle_offset

  type pseudo_env = Big.big_int -> pseudo_reg -> int

  type rtl_state = { rtl_oracle : oracle; rtl_env : pseudo_env;
                     rtl_mach_state : M.mach_state;
                     rtl_memory : int8 AddrMap.t }

  (** val rtl_oracle : rtl_state -> oracle **)

  let rtl_oracle r =
    r.rtl_oracle

  (** val rtl_env : rtl_state -> pseudo_env **)

  let rtl_env r =
    r.rtl_env

  (** val rtl_mach_state : rtl_state -> M.mach_state **)

  let rtl_mach_state r =
    r.rtl_mach_state

  (** val rtl_memory : rtl_state -> int8 AddrMap.t **)

  let rtl_memory r =
    r.rtl_memory

  type 'a coq_RTL_ans =
  | Fail_ans
  | Trap_ans
  | Okay_ans of 'a

  (** val coq_RTL_ans_rect :
      'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2 **)

  let coq_RTL_ans_rect f f0 f1 = function
  | Fail_ans -> f
  | Trap_ans -> f0
  | Okay_ans x -> f1 x

  (** val coq_RTL_ans_rec :
      'a2 -> 'a2 -> ('a1 -> 'a2) -> 'a1 coq_RTL_ans -> 'a2 **)

  let coq_RTL_ans_rec f f0 f1 = function
  | Fail_ans -> f
  | Trap_ans -> f0
  | Okay_ans x -> f1 x

  type 't coq_RTL = rtl_state -> 't coq_RTL_ans * rtl_state

  (** val coq_RTL_monad : __ coq_RTL coq_Monad **)

  let coq_RTL_monad =
    { coq_Return = (fun _ x rs -> ((Okay_ans x), rs)); coq_Bind =
      (fun _ _ c f rs ->
      let (r, rs') = c rs in
      (match r with
       | Okay_ans v -> f v rs'
       | x -> (x, rs'))) }

  (** val coq_Fail : 'a1 coq_RTL **)

  let coq_Fail rs =
    (Fail_ans, rs)

  (** val coq_Trap : 'a1 coq_RTL **)

  let coq_Trap rs =
    (Trap_ans, rs)

  (** val empty_env : pseudo_env **)

  let empty_env s _ =
    Word.zero s

  (** val eq_pseudo_reg : Big.big_int -> pseudo_reg -> pseudo_reg -> bool **)

  let eq_pseudo_reg _ ps1 ps2 =
    Z.eq_dec ps1 ps2

  (** val update_ps_env :
      Big.big_int -> pseudo_reg -> int -> pseudo_env -> pseudo_env **)

  let update_ps_env s ps v env s' ps' =
    let s0 = Nat.eq_dec s s' in
    if s0
    then let s1 = eq_pseudo_reg s' ps ps' in if s1 then v else env s' ps'
    else env s' ps'

  (** val set_loc : Big.big_int -> M.location -> int -> unit coq_RTL **)

  let set_loc s l v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = (rtl_env rs);
      rtl_mach_state = (M.set_location s l v (rtl_mach_state rs));
      rtl_memory = (rtl_memory rs) })

  (** val set_ps_reg : Big.big_int -> pseudo_reg -> int -> unit coq_RTL **)

  let set_ps_reg s ps v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env =
      (update_ps_env s ps v (rtl_env rs)); rtl_mach_state =
      (rtl_mach_state rs); rtl_memory = (rtl_memory rs) })

  (** val set_array :
      Big.big_int -> Big.big_int -> M.array -> int -> int -> unit coq_RTL **)

  let set_array l s a i v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = (rtl_env rs);
      rtl_mach_state = (M.array_upd l s a i v (rtl_mach_state rs));
      rtl_memory = (rtl_memory rs) })

  (** val set_byte : int -> int -> unit coq_RTL **)

  let set_byte addr v rs =
    ((Okay_ans ()), { rtl_oracle = (rtl_oracle rs); rtl_env = (rtl_env rs);
      rtl_mach_state = (rtl_mach_state rs); rtl_memory =
      (AddrMap.set addr v (rtl_memory rs)) })

  (** val advance_oracle : unit coq_RTL **)

  let advance_oracle rs =
    let o = rtl_oracle rs in
    let o' = { oracle_bits = (oracle_bits o); oracle_offset =
      (Z.add (oracle_offset o) Big.one) }
    in
    ((Okay_ans ()), { rtl_oracle = o'; rtl_env = (rtl_env rs);
    rtl_mach_state = (rtl_mach_state rs); rtl_memory = (rtl_memory rs) })

  (** val interp_arith : Big.big_int -> bit_vector_op -> int -> int -> int **)

  let interp_arith s b v1 v2 =
    match b with
    | Coq_add_op -> Word.add s v1 v2
    | Coq_sub_op -> Word.sub s v1 v2
    | Coq_mul_op -> Word.mul s v1 v2
    | Coq_divs_op -> Word.divs s v1 v2
    | Coq_divu_op -> Word.divu s v1 v2
    | Coq_modu_op -> Word.modu s v1 v2
    | Coq_mods_op -> Word.mods s v1 v2
    | Coq_and_op -> Word.coq_and s v1 v2
    | Coq_or_op -> Word.coq_or s v1 v2
    | Coq_xor_op -> Word.xor s v1 v2
    | Coq_shl_op -> Word.shl s v1 v2
    | Coq_shr_op -> Word.shr s v1 v2
    | Coq_shru_op -> Word.shru s v1 v2
    | Coq_ror_op -> Word.ror s v1 v2
    | Coq_rol_op -> Word.rol s v1 v2

  (** val interp_test : Big.big_int -> test_op -> int -> int -> int **)

  let interp_test s t0 v1 v2 =
    if match t0 with
       | Coq_eq_op -> if zeq v1 v2 then true else false
       | Coq_lt_op -> Word.lt s v1 v2
       | Coq_ltu_op -> if zlt v1 v2 then true else false
    then Word.one size1
    else Word.zero size1

  (** val dec_rounding_mode : int -> rounding_mode **)

  let dec_rounding_mode rm =
    if zeq rm (Word.repr size2 Big.zero)
    then Coq_mode_NE
    else if zeq rm (Word.repr size2 Big.one)
         then Coq_mode_DN
         else if zeq rm (Word.repr size2 (Big.double Big.one))
              then Coq_mode_UP
              else Coq_mode_ZR

  type rtl_float = binary_float

  (** val default_nan_pl : Big.big_int -> bool * nan_pl **)

  let default_nan_pl mw =
    (false,
      (iter_nat (fun x -> Big.double x) (Pos.to_nat (Pos.sub mw Big.one))
        Big.one))

  (** val nan_pl_conv :
      Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> nan_pl ->
      nan_pl **)

  let nan_pl_conv _ mw1 _ mw2 nan =
    if coq_Z_le_dec mw1 mw2
    then nan
    else let (_, pl2) = default_nan_pl mw2 in pl2

  (** val unop_nan_pl :
      Big.big_int -> Big.big_int -> rtl_float -> bool * nan_pl **)

  let unop_nan_pl _ mw = function
  | B754_nan (s, pl) -> (s, pl)
  | _ -> default_nan_pl mw

  (** val binop_nan_pl :
      Big.big_int -> Big.big_int -> rtl_float -> rtl_float -> bool * nan_pl **)

  let binop_nan_pl _ mw f1 f2 =
    match f1 with
    | B754_nan (s1, pl1) -> (s1, pl1)
    | _ ->
      (match f2 with
       | B754_nan (s2, pl2) -> (s2, pl2)
       | _ -> default_nan_pl mw)

  (** val interp_farith :
      Big.big_int -> Big.big_int -> float_arith_op -> int -> int -> int -> int **)

  let interp_farith ew mw fop rm v1 v2 =
    let prec = Z.add mw Big.one in
    let emax =
      Big.z_case
        (fun _ ->
        Big.one)
        (fun p ->
        Z.pow_pos (Big.double Big.one) p)
        (fun _ ->
        Big.zero)
        (Z.sub ew Big.one)
    in
    let bf_of_bits = binary_float_of_bits mw ew in
    let bf1 = bf_of_bits v1 in
    let bf2 = bf_of_bits v2 in
    let md = dec_rounding_mode rm in
    let pl_op = binop_nan_pl ew mw in
    let res =
      match fop with
      | Coq_fadd_op -> coq_Bplus prec emax pl_op md bf1 bf2
      | Coq_fsub_op -> coq_Bminus prec emax pl_op md bf1 bf2
      | Coq_fmul_op -> coq_Bmult prec emax pl_op md bf1 bf2
      | Coq_fdiv_op -> coq_Bdiv prec emax pl_op md bf1 bf2
    in
    Word.repr (add (Pos.to_nat ew) (Pos.to_nat mw))
      (bits_of_binary_float mw ew res)

  (** val cond_Zopp : bool -> Big.big_int -> Big.big_int **)

  let cond_Zopp b m =
    if b then Z.opp m else m

  (** val binary_float_cast :
      Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> int ->
      rtl_float -> rtl_float **)

  let binary_float_cast ew1 mw1 ew2 mw2 rm bf =
    let md = dec_rounding_mode rm in
    (match bf with
     | B754_nan (s, pl) -> B754_nan (s, (nan_pl_conv ew1 mw1 ew2 mw2 pl))
     | B754_finite (sign, mant, ep) ->
       let prec2 = Z.add mw2 Big.one in
       let emax2 =
         Big.z_case
           (fun _ ->
           Big.one)
           (fun p ->
           Z.pow_pos (Big.double Big.one) p)
           (fun _ ->
           Big.zero)
           (Z.sub ew2 Big.one)
       in
       binary_normalize prec2 emax2 md (cond_Zopp sign mant) ep true
     | x -> x)

  (** val interp_fcast :
      Big.big_int -> Big.big_int -> Big.big_int -> Big.big_int -> int -> int
      -> int **)

  let interp_fcast ew1 mw1 ew2 mw2 rm v =
    let bf_of_bits = binary_float_of_bits mw1 ew1 in
    let bf = bf_of_bits v in
    let bf' = binary_float_cast ew1 mw1 ew2 mw2 rm bf in
    Word.repr (add (Pos.to_nat ew2) (Pos.to_nat mw2))
      (bits_of_binary_float mw2 ew2 bf')

  (** val interp_rtl_exp : Big.big_int -> rtl_exp -> rtl_state -> int **)

  let rec interp_rtl_exp _ e rs =
    match e with
    | Coq_arith_rtl_exp (s, b, e1, e2) ->
      let v1 = interp_rtl_exp s e1 rs in
      let v2 = interp_rtl_exp s e2 rs in interp_arith s b v1 v2
    | Coq_test_rtl_exp (s, t0, e1, e2) ->
      let v1 = interp_rtl_exp s e1 rs in
      let v2 = interp_rtl_exp s e2 rs in interp_test s t0 v1 v2
    | Coq_if_rtl_exp (s, cd, e1, e2) ->
      let v = interp_rtl_exp size1 cd rs in
      if zeq v (Word.one size1)
      then interp_rtl_exp s e1 rs
      else interp_rtl_exp s e2 rs
    | Coq_cast_s_rtl_exp (s1, s2, e0) ->
      let v = interp_rtl_exp s1 e0 rs in Word.repr s2 (Word.signed s1 v)
    | Coq_cast_u_rtl_exp (s1, s2, e0) ->
      let v = interp_rtl_exp s1 e0 rs in Word.repr s2 v
    | Coq_imm_rtl_exp (_, v) -> v
    | Coq_get_loc_rtl_exp (s, l) -> M.get_location s l (rtl_mach_state rs)
    | Coq_get_ps_reg_rtl_exp (s, ps) -> rtl_env rs s ps
    | Coq_get_array_rtl_exp (l, s, a, e0) ->
      let i = interp_rtl_exp l e0 rs in
      M.array_sub l s a i (rtl_mach_state rs)
    | Coq_get_byte_rtl_exp addr ->
      let v = interp_rtl_exp M.size_addr addr rs in
      AddrMap.get v (rtl_memory rs)
    | Coq_get_random_rtl_exp s ->
      let oracle0 = rtl_oracle rs in
      oracle_bits oracle0 s (oracle_offset oracle0)
    | Coq_farith_rtl_exp (ew, mw, fop, rm, x, x0) ->
      let len = add (Pos.to_nat ew) (Pos.to_nat mw) in
      let v1 = interp_rtl_exp len x rs in
      let v2 = interp_rtl_exp len x0 rs in
      let vrm = interp_rtl_exp size2 rm rs in
      interp_farith ew mw fop vrm v1 v2
    | Coq_fcast_rtl_exp (ew1, mw1, ew2, mw2, rm, e0) ->
      let v = interp_rtl_exp (add (Pos.to_nat ew1) (Pos.to_nat mw1)) e0 rs in
      let vrm = interp_rtl_exp size2 rm rs in
      interp_fcast ew1 mw1 ew2 mw2 vrm v

  (** val interp_rtl_exp_comp : Big.big_int -> rtl_exp -> int coq_RTL **)

  let interp_rtl_exp_comp s e rs =
    ((Okay_ans (interp_rtl_exp s e rs)), rs)

  (** val get_loc : Big.big_int -> M.location -> int coq_RTL **)

  let get_loc s l =
    interp_rtl_exp_comp s (Coq_get_loc_rtl_exp (s, l))

  (** val get_array :
      Big.big_int -> Big.big_int -> M.array -> int -> int coq_RTL **)

  let get_array l s a i =
    interp_rtl_exp_comp s (Coq_get_array_rtl_exp (l, s, a, (Coq_imm_rtl_exp
      (l, i))))

  (** val get_byte : int -> int coq_RTL **)

  let get_byte addr =
    interp_rtl_exp_comp size8 (Coq_get_byte_rtl_exp (Coq_imm_rtl_exp
      (M.size_addr, addr)))

  (** val get_random : Big.big_int -> int coq_RTL **)

  let get_random s =
    interp_rtl_exp_comp s (Coq_get_random_rtl_exp s)

  (** val interp_rtl : rtl_instr -> unit coq_RTL **)

  let rec interp_rtl = function
  | Coq_set_loc_rtl (s, e, l) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic interp_rtl_exp_comp s e)
      (fun v -> set_loc s l v)
  | Coq_set_ps_reg_rtl (s, e, ps) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic interp_rtl_exp_comp s e)
      (fun v -> set_ps_reg s ps v)
  | Coq_set_array_rtl (l, s, a, e1, e2) ->
    coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic interp_rtl_exp_comp l e1)
      (fun i ->
      coq_Bind (Obj.magic coq_RTL_monad) (Obj.magic interp_rtl_exp_comp s e2)
        (fun v -> set_array l s a i v))
  | Coq_set_byte_rtl (e, addr) ->
    coq_Bind (Obj.magic coq_RTL_monad)
      (Obj.magic interp_rtl_exp_comp size8 e) (fun v ->
      coq_Bind (Obj.magic coq_RTL_monad)
        (Obj.magic interp_rtl_exp_comp M.size_addr addr) (fun a ->
        set_byte a v))
  | Coq_advance_oracle_rtl -> advance_oracle
  | Coq_if_rtl (r, i) ->
    coq_Bind (Obj.magic coq_RTL_monad)
      (Obj.magic interp_rtl_exp_comp size1 r) (fun v ->
      if zeq v (Word.one size1)
      then interp_rtl i
      else coq_Return (Obj.magic coq_RTL_monad) ())
  | Coq_error_rtl -> coq_Fail
  | Coq_trap_rtl -> coq_Trap

  type instruction = { instr_assembly : char list; instr_rtl : rtl_instr list }

  (** val instr_assembly : instruction -> char list **)

  let instr_assembly i =
    i.instr_assembly

  (** val instr_rtl : instruction -> rtl_instr list **)

  let instr_rtl i =
    i.instr_rtl
 end
