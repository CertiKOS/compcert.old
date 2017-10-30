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

module X86_MACHINE =
 struct
  (** val size_addr : Big.big_int **)

  let size_addr =
    size32

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

  (** val flag_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag -> 'a1 **)

  let flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | ID -> f
  | VIP -> f0
  | VIF -> f1
  | AC -> f2
  | VM -> f3
  | RF -> f4
  | NT -> f5
  | IOPL -> f6
  | OF -> f7
  | DF -> f8
  | IF_flag -> f9
  | TF -> f10
  | SF -> f11
  | ZF -> f12
  | AF -> f13
  | PF -> f14
  | CF -> f15

  (** val flag_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> flag -> 'a1 **)

  let flag_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
  | ID -> f
  | VIP -> f0
  | VIF -> f1
  | AC -> f2
  | VM -> f3
  | RF -> f4
  | NT -> f5
  | IOPL -> f6
  | OF -> f7
  | DF -> f8
  | IF_flag -> f9
  | TF -> f10
  | SF -> f11
  | ZF -> f12
  | AF -> f13
  | PF -> f14
  | CF -> f15

  (** val flag_eq_dec : flag -> flag -> bool **)

  let flag_eq_dec f1 f2 =
    match f1 with
    | ID ->
      (match f2 with
       | ID -> true
       | _ -> false)
    | VIP ->
      (match f2 with
       | VIP -> true
       | _ -> false)
    | VIF ->
      (match f2 with
       | VIF -> true
       | _ -> false)
    | AC ->
      (match f2 with
       | AC -> true
       | _ -> false)
    | VM ->
      (match f2 with
       | VM -> true
       | _ -> false)
    | RF ->
      (match f2 with
       | RF -> true
       | _ -> false)
    | NT ->
      (match f2 with
       | NT -> true
       | _ -> false)
    | IOPL ->
      (match f2 with
       | IOPL -> true
       | _ -> false)
    | OF ->
      (match f2 with
       | OF -> true
       | _ -> false)
    | DF ->
      (match f2 with
       | DF -> true
       | _ -> false)
    | IF_flag ->
      (match f2 with
       | IF_flag -> true
       | _ -> false)
    | TF ->
      (match f2 with
       | TF -> true
       | _ -> false)
    | SF ->
      (match f2 with
       | SF -> true
       | _ -> false)
    | ZF ->
      (match f2 with
       | ZF -> true
       | _ -> false)
    | AF ->
      (match f2 with
       | AF -> true
       | _ -> false)
    | PF ->
      (match f2 with
       | PF -> true
       | _ -> false)
    | CF ->
      (match f2 with
       | CF -> true
       | _ -> false)

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

  (** val fpu_flag_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> fpu_flag -> 'a1 **)

  let fpu_flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
  | F_Busy -> f
  | F_C3 -> f0
  | F_C2 -> f1
  | F_C1 -> f2
  | F_C0 -> f3
  | F_ES -> f4
  | F_SF -> f5
  | F_PE -> f6
  | F_UE -> f7
  | F_OE -> f8
  | F_ZE -> f9
  | F_DE -> f10
  | F_IE -> f11

  (** val fpu_flag_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> 'a1 -> fpu_flag -> 'a1 **)

  let fpu_flag_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
  | F_Busy -> f
  | F_C3 -> f0
  | F_C2 -> f1
  | F_C1 -> f2
  | F_C0 -> f3
  | F_ES -> f4
  | F_SF -> f5
  | F_PE -> f6
  | F_UE -> f7
  | F_OE -> f8
  | F_ZE -> f9
  | F_DE -> f10
  | F_IE -> f11

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

  (** val fpu_ctrl_flag_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> fpu_ctrl_flag -> 'a1 **)

  let fpu_ctrl_flag_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | F_Res15 -> f
  | F_Res14 -> f0
  | F_Res13 -> f1
  | F_Res7 -> f2
  | F_Res6 -> f3
  | F_IC -> f4
  | F_PM -> f5
  | F_UM -> f6
  | F_OM -> f7
  | F_ZM -> f8
  | F_DM -> f9
  | F_IM -> f10

  (** val fpu_ctrl_flag_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
      'a1 -> 'a1 -> fpu_ctrl_flag -> 'a1 **)

  let fpu_ctrl_flag_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 = function
  | F_Res15 -> f
  | F_Res14 -> f0
  | F_Res13 -> f1
  | F_Res7 -> f2
  | F_Res6 -> f3
  | F_IC -> f4
  | F_PM -> f5
  | F_UM -> f6
  | F_OM -> f7
  | F_ZM -> f8
  | F_DM -> f9
  | F_IM -> f10

  (** val size11 : Big.big_int **)

  let size11 =
    Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ Big.zero)))))))))

  (** val size48 : Big.big_int **)

  let size48 =
    Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      Big.zero))))))))))))))))))))))))))))))))))))))))))))))

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

  (** val loc_rect :
      (register -> 'a1) -> (segment_register -> 'a1) -> (segment_register ->
      'a1) -> (flag -> 'a1) -> (control_register -> 'a1) -> (debug_register
      -> 'a1) -> 'a1 -> 'a1 -> (fpu_flag -> 'a1) -> 'a1 -> 'a1 ->
      (fpu_ctrl_flag -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> Big.big_int -> loc -> 'a1 **)

  let loc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ = function
  | Coq_reg_loc x -> f x
  | Coq_seg_reg_start_loc x -> f0 x
  | Coq_seg_reg_limit_loc x -> f1 x
  | Coq_flag_loc x -> f2 x
  | Coq_control_register_loc x -> f3 x
  | Coq_debug_register_loc x -> f4 x
  | Coq_pc_loc -> f5
  | Coq_fpu_stktop_loc -> f6
  | Coq_fpu_flag_loc x -> f7 x
  | Coq_fpu_rctrl_loc -> f8
  | Coq_fpu_pctrl_loc -> f9
  | Coq_fpu_ctrl_flag_loc x -> f10 x
  | Coq_fpu_lastInstrPtr_loc -> f11
  | Coq_fpu_lastDataPtr_loc -> f12
  | Coq_fpu_lastOpcode_loc -> f13

  (** val loc_rec :
      (register -> 'a1) -> (segment_register -> 'a1) -> (segment_register ->
      'a1) -> (flag -> 'a1) -> (control_register -> 'a1) -> (debug_register
      -> 'a1) -> 'a1 -> 'a1 -> (fpu_flag -> 'a1) -> 'a1 -> 'a1 ->
      (fpu_ctrl_flag -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> Big.big_int -> loc -> 'a1 **)

  let loc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 _ = function
  | Coq_reg_loc x -> f x
  | Coq_seg_reg_start_loc x -> f0 x
  | Coq_seg_reg_limit_loc x -> f1 x
  | Coq_flag_loc x -> f2 x
  | Coq_control_register_loc x -> f3 x
  | Coq_debug_register_loc x -> f4 x
  | Coq_pc_loc -> f5
  | Coq_fpu_stktop_loc -> f6
  | Coq_fpu_flag_loc x -> f7 x
  | Coq_fpu_rctrl_loc -> f8
  | Coq_fpu_pctrl_loc -> f9
  | Coq_fpu_ctrl_flag_loc x -> f10 x
  | Coq_fpu_lastInstrPtr_loc -> f11
  | Coq_fpu_lastDataPtr_loc -> f12
  | Coq_fpu_lastOpcode_loc -> f13

  type location = loc

  type arr =
  | Coq_fpu_datareg
  | Coq_fpu_tag

  (** val arr_rect :
      'a1 -> 'a1 -> Big.big_int -> Big.big_int -> arr -> 'a1 **)

  let arr_rect f f0 _ _ = function
  | Coq_fpu_datareg -> f
  | Coq_fpu_tag -> f0

  (** val arr_rec : 'a1 -> 'a1 -> Big.big_int -> Big.big_int -> arr -> 'a1 **)

  let arr_rec f f0 _ _ = function
  | Coq_fpu_datareg -> f
  | Coq_fpu_tag -> f0

  type array = arr

  type ('a, 'b) fmap = 'a -> 'b

  (** val upd :
      ('a1 -> 'a1 -> bool) -> ('a1, 'a2) fmap -> 'a1 -> 'a2 -> ('a1, 'a2) fmap **)

  let upd eq_dec f x v y =
    if eq_dec x y then v else f y

  (** val look : ('a1, 'a2) fmap -> 'a1 -> 'a2 **)

  let look f x =
    f x

  type core_state = { gp_regs : (register, int32) fmap;
                      seg_regs_starts : (segment_register, int32) fmap;
                      seg_regs_limits : (segment_register, int32) fmap;
                      flags_reg : (flag, int1) fmap;
                      control_regs : (control_register, int32) fmap;
                      debug_regs : (debug_register, int32) fmap;
                      pc_reg : RTL.int }

  (** val gp_regs : core_state -> (register, int32) fmap **)

  let gp_regs x = x.gp_regs

  (** val seg_regs_starts : core_state -> (segment_register, int32) fmap **)

  let seg_regs_starts x = x.seg_regs_starts

  (** val seg_regs_limits : core_state -> (segment_register, int32) fmap **)

  let seg_regs_limits x = x.seg_regs_limits

  (** val flags_reg : core_state -> (flag, int1) fmap **)

  let flags_reg x = x.flags_reg

  (** val control_regs : core_state -> (control_register, int32) fmap **)

  let control_regs x = x.control_regs

  (** val debug_regs : core_state -> (debug_register, int32) fmap **)

  let debug_regs x = x.debug_regs

  (** val pc_reg : core_state -> RTL.int **)

  let pc_reg x = x.pc_reg

  type fpu_state = { fpu_data_regs : (int3, int80) fmap; fpu_status : 
                     int16; fpu_control : int16;
                     fpu_tags : (int3, int2) fmap; fpu_lastInstrPtr : 
                     int48; fpu_lastDataPtr : int48; fpu_lastOpcode : 
                     RTL.int }

  (** val fpu_data_regs : fpu_state -> (int3, int80) fmap **)

  let fpu_data_regs x = x.fpu_data_regs

  (** val fpu_status : fpu_state -> int16 **)

  let fpu_status x = x.fpu_status

  (** val fpu_control : fpu_state -> int16 **)

  let fpu_control x = x.fpu_control

  (** val fpu_tags : fpu_state -> (int3, int2) fmap **)

  let fpu_tags x = x.fpu_tags

  (** val fpu_lastInstrPtr : fpu_state -> int48 **)

  let fpu_lastInstrPtr x = x.fpu_lastInstrPtr

  (** val fpu_lastDataPtr : fpu_state -> int48 **)

  let fpu_lastDataPtr x = x.fpu_lastDataPtr

  (** val fpu_lastOpcode : fpu_state -> RTL.int **)

  let fpu_lastOpcode x = x.fpu_lastOpcode

  type mach = { core : core_state; fpu : fpu_state }

  (** val core : mach -> core_state **)

  let core x = x.core

  (** val fpu : mach -> fpu_state **)

  let fpu x = x.fpu

  type mach_state = mach

  (** val get_bits_rng :
      Big.big_int -> RTL.int -> Big.big_int -> Big.big_int -> RTL.int **)

  let get_bits_rng s i n m =
    Word.repr (sub m n) (Word.shru s i (Word.repr s (Z.of_nat n)))

  (** val set_bits_rng :
      Big.big_int -> RTL.int -> Big.big_int -> Big.big_int -> RTL.int ->
      RTL.int **)

  let set_bits_rng s i n m v =
    let highbits = Word.shru s i (Word.repr s (Z.add (Z.of_nat m) Big.one))
    in
    let lowbits = Z.modulo i (two_power_nat n) in
    Word.repr s
      (Z.add (Z.add lowbits (Z.mul v (two_power_nat n)))
        (Z.mul highbits (two_power_nat (add m (Big.succ Big.zero)))))

  (** val get_bit : Big.big_int -> RTL.int -> Big.big_int -> int1 **)

  let get_bit s i n =
    let wordsize = Big.succ s in
    if Word.bits_of_Z wordsize i n then Word.one size1 else Word.zero size1

  (** val set_bit :
      Big.big_int -> RTL.int -> Big.big_int -> bool -> RTL.int **)

  let set_bit s i n v =
    set_bits_rng s i n n (Word.bool_to_int (sub n n) v)

  (** val get_fpu_flag_reg : fpu_flag -> fpu_state -> int1 **)

  let get_fpu_flag_reg f fs =
    match f with
    | F_Busy ->
      get_bit size16 fs.fpu_status (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone Big.one)))
    | F_C3 ->
      get_bit size16 fs.fpu_status (Big.double (Big.doubleplusone
        (Big.doubleplusone Big.one)))
    | F_C2 ->
      get_bit size16 fs.fpu_status (Big.double (Big.doubleplusone (Big.double
        Big.one)))
    | F_C1 ->
      get_bit size16 fs.fpu_status (Big.doubleplusone (Big.double (Big.double
        Big.one)))
    | F_C0 ->
      get_bit size16 fs.fpu_status (Big.double (Big.double (Big.double
        Big.one)))
    | F_ES ->
      get_bit size16 fs.fpu_status (Big.doubleplusone (Big.doubleplusone
        Big.one))
    | F_SF ->
      get_bit size16 fs.fpu_status (Big.double (Big.doubleplusone Big.one))
    | F_PE ->
      get_bit size16 fs.fpu_status (Big.doubleplusone (Big.double Big.one))
    | F_UE -> get_bit size16 fs.fpu_status (Big.double (Big.double Big.one))
    | F_OE -> get_bit size16 fs.fpu_status (Big.doubleplusone Big.one)
    | F_ZE -> get_bit size16 fs.fpu_status (Big.double Big.one)
    | F_DE -> get_bit size16 fs.fpu_status Big.one
    | F_IE -> get_bit size16 fs.fpu_status Big.zero

  (** val get_stktop_reg : fpu_state -> int3 **)

  let get_stktop_reg fs =
    get_bits_rng size16 fs.fpu_status (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      Big.zero))))))))))) (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ Big.zero)))))))))))))

  (** val get_fpu_ctrl_flag_reg : fpu_ctrl_flag -> fpu_state -> int1 **)

  let get_fpu_ctrl_flag_reg f fs =
    match f with
    | F_Res15 ->
      get_bit size16 fs.fpu_control (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone Big.one)))
    | F_Res14 ->
      get_bit size16 fs.fpu_control (Big.double (Big.doubleplusone
        (Big.doubleplusone Big.one)))
    | F_Res13 ->
      get_bit size16 fs.fpu_control (Big.doubleplusone (Big.double
        (Big.doubleplusone Big.one)))
    | F_Res7 ->
      get_bit size16 fs.fpu_control (Big.doubleplusone (Big.doubleplusone
        Big.one))
    | F_Res6 ->
      get_bit size16 fs.fpu_control (Big.double (Big.doubleplusone Big.one))
    | F_IC ->
      get_bit size16 fs.fpu_control (Big.double (Big.double
        (Big.doubleplusone Big.one)))
    | F_PM ->
      get_bit size16 fs.fpu_control (Big.doubleplusone (Big.double Big.one))
    | F_UM -> get_bit size16 fs.fpu_control (Big.double (Big.double Big.one))
    | F_OM -> get_bit size16 fs.fpu_control (Big.doubleplusone Big.one)
    | F_ZM -> get_bit size16 fs.fpu_control (Big.double Big.one)
    | F_DM -> get_bit size16 fs.fpu_control Big.one
    | F_IM -> get_bit size16 fs.fpu_control Big.zero

  (** val get_rctrl_reg : fpu_state -> int2 **)

  let get_rctrl_reg fs =
    get_bits_rng size16 fs.fpu_control (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      Big.zero)))))))))) (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      Big.zero)))))))))))

  (** val get_pctrl_reg : fpu_state -> int2 **)

  let get_pctrl_reg fs =
    get_bits_rng size16 fs.fpu_control (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ Big.zero))))))))
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ Big.zero)))))))))

  (** val get_location : Big.big_int -> loc -> mach_state -> RTL.int **)

  let get_location _ l m =
    match l with
    | Coq_reg_loc r -> look m.core.gp_regs r
    | Coq_seg_reg_start_loc r -> look m.core.seg_regs_starts r
    | Coq_seg_reg_limit_loc r -> look m.core.seg_regs_limits r
    | Coq_flag_loc f -> look m.core.flags_reg f
    | Coq_control_register_loc r -> look m.core.control_regs r
    | Coq_debug_register_loc r -> look m.core.debug_regs r
    | Coq_pc_loc -> m.core.pc_reg
    | Coq_fpu_stktop_loc -> get_stktop_reg m.fpu
    | Coq_fpu_flag_loc f -> get_fpu_flag_reg f m.fpu
    | Coq_fpu_ctrl_flag_loc f -> get_fpu_ctrl_flag_reg f m.fpu
    | Coq_fpu_lastInstrPtr_loc -> m.fpu.fpu_lastInstrPtr
    | Coq_fpu_lastDataPtr_loc -> m.fpu.fpu_lastDataPtr
    | Coq_fpu_lastOpcode_loc -> m.fpu.fpu_lastOpcode
    | _ -> get_rctrl_reg m.fpu

  (** val set_gp_reg : register -> int32 -> mach -> mach **)

  let set_gp_reg r v m =
    { core = { gp_regs = (fun y ->
      if register_eq_dec r y then v else m.core.gp_regs y); seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = m.core.seg_regs_limits;
      flags_reg = m.core.flags_reg; control_regs = m.core.control_regs;
      debug_regs = m.core.debug_regs; pc_reg = m.core.pc_reg }; fpu = m.fpu }

  (** val set_seg_reg_start : segment_register -> int32 -> mach -> mach **)

  let set_seg_reg_start r v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts = (fun y ->
      if segment_register_eq_dec r y then v else m.core.seg_regs_starts y);
      seg_regs_limits = m.core.seg_regs_limits; flags_reg = m.core.flags_reg;
      control_regs = m.core.control_regs; debug_regs = m.core.debug_regs;
      pc_reg = m.core.pc_reg }; fpu = m.fpu }

  (** val set_seg_reg_limit : segment_register -> int32 -> mach -> mach **)

  let set_seg_reg_limit r v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = (fun y ->
      if segment_register_eq_dec r y then v else m.core.seg_regs_limits y);
      flags_reg = m.core.flags_reg; control_regs = m.core.control_regs;
      debug_regs = m.core.debug_regs; pc_reg = m.core.pc_reg }; fpu = m.fpu }

  (** val set_flags_reg : flag -> int1 -> mach -> mach **)

  let set_flags_reg r v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = m.core.seg_regs_limits;
      flags_reg = (fun y ->
      if flag_eq_dec r y then v else m.core.flags_reg y); control_regs =
      m.core.control_regs; debug_regs = m.core.debug_regs; pc_reg =
      m.core.pc_reg }; fpu = m.fpu }

  (** val set_control_reg : control_register -> int32 -> mach -> mach **)

  let set_control_reg r v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = m.core.seg_regs_limits;
      flags_reg = m.core.flags_reg; control_regs = (fun y ->
      if control_register_eq_dec r y then v else m.core.control_regs y);
      debug_regs = m.core.debug_regs; pc_reg = m.core.pc_reg }; fpu = m.fpu }

  (** val set_debug_reg : debug_register -> int32 -> mach -> mach **)

  let set_debug_reg r v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = m.core.seg_regs_limits;
      flags_reg = m.core.flags_reg; control_regs = m.core.control_regs;
      debug_regs = (fun y ->
      if debug_register_eq_dec r y then v else m.core.debug_regs y); pc_reg =
      m.core.pc_reg }; fpu = m.fpu }

  (** val set_pc : RTL.int -> mach -> mach **)

  let set_pc v m =
    { core = { gp_regs = m.core.gp_regs; seg_regs_starts =
      m.core.seg_regs_starts; seg_regs_limits = m.core.seg_regs_limits;
      flags_reg = m.core.flags_reg; control_regs = m.core.control_regs;
      debug_regs = m.core.debug_regs; pc_reg = v }; fpu = m.fpu }

  (** val set_fpu_stktop_reg : int3 -> mach -> mach **)

  let set_fpu_stktop_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status =
      (set_bits_rng size16 m.fpu.fpu_status (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ Big.zero))))))))))) (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ Big.zero))))))))))))) v); fpu_control =
      m.fpu.fpu_control; fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr =
      m.fpu.fpu_lastInstrPtr; fpu_lastDataPtr = m.fpu.fpu_lastDataPtr;
      fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_fpu_flags_reg : fpu_flag -> int1 -> mach -> mach **)

  let set_fpu_flags_reg f v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status =
      (let old_status = m.fpu.fpu_status in
       let b = negb (if zeq v (Word.zero size1) then true else false) in
       (match f with
        | F_Busy ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero))))))))))))))) b
        | F_C3 ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))) b
        | F_C2 ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero)))))))))) b
        | F_C1 ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero))))))))) b
        | F_C0 ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))) b
        | F_ES ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ Big.zero))))))) b
        | F_SF ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))) b
        | F_PE ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ Big.zero))))) b
        | F_UE ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero)))) b
        | F_OE ->
          set_bit size16 old_status (Big.succ (Big.succ (Big.succ Big.zero)))
            b
        | F_ZE -> set_bit size16 old_status (Big.succ (Big.succ Big.zero)) b
        | F_DE -> set_bit size16 old_status (Big.succ Big.zero) b
        | F_IE -> set_bit size16 old_status Big.zero b)); fpu_control =
      m.fpu.fpu_control; fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr =
      m.fpu.fpu_lastInstrPtr; fpu_lastDataPtr = m.fpu.fpu_lastDataPtr;
      fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_fpu_rctrl_reg : int2 -> mach -> mach **)

  let set_fpu_rctrl_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control =
      (set_bits_rng size16 m.fpu.fpu_control (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        Big.zero)))))))))) (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        Big.zero))))))))))) v); fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr =
      m.fpu.fpu_lastInstrPtr; fpu_lastDataPtr = m.fpu.fpu_lastDataPtr;
      fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_fpu_pctrl_reg : int2 -> mach -> mach **)

  let set_fpu_pctrl_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control =
      (set_bits_rng size16 m.fpu.fpu_control (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ Big.zero))))))))
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ Big.zero))))))))) v); fpu_tags = m.fpu.fpu_tags;
      fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr; fpu_lastDataPtr =
      m.fpu.fpu_lastDataPtr; fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_fpu_ctrl_reg : fpu_ctrl_flag -> int1 -> mach -> mach **)

  let set_fpu_ctrl_reg f v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control =
      (let old_ctrl = m.fpu.fpu_control in
       let b = negb (if zeq v (Word.zero size1) then true else false) in
       (match f with
        | F_Res15 ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero))))))))))))))) b
        | F_Res14 ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))) b
        | F_Res13 ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ Big.zero))))))))))))) b
        | F_Res7 ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ Big.zero))))))) b
        | F_Res6 ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))) b
        | F_IC ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ Big.zero)))))))))))) b
        | F_PM ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ Big.zero))))) b
        | F_UM ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ (Big.succ
            Big.zero)))) b
        | F_OM ->
          set_bit size16 old_ctrl (Big.succ (Big.succ (Big.succ Big.zero))) b
        | F_ZM -> set_bit size16 old_ctrl (Big.succ (Big.succ Big.zero)) b
        | F_DM -> set_bit size16 old_ctrl (Big.succ Big.zero) b
        | F_IM -> set_bit size16 old_ctrl Big.zero b)); fpu_tags =
      m.fpu.fpu_tags; fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr;
      fpu_lastDataPtr = m.fpu.fpu_lastDataPtr; fpu_lastOpcode =
      m.fpu.fpu_lastOpcode } }

  (** val set_fpu_lastInstrPtr_reg : int48 -> mach -> mach **)

  let set_fpu_lastInstrPtr_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control = m.fpu.fpu_control;
      fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr = v; fpu_lastDataPtr =
      m.fpu.fpu_lastDataPtr; fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_fpu_lastDataPtr_reg : int48 -> mach -> mach **)

  let set_fpu_lastDataPtr_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control = m.fpu.fpu_control;
      fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr;
      fpu_lastDataPtr = v; fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val set_lastOpcode_reg : RTL.int -> mach -> mach **)

  let set_lastOpcode_reg v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control = m.fpu.fpu_control;
      fpu_tags = m.fpu.fpu_tags; fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr;
      fpu_lastDataPtr = m.fpu.fpu_lastDataPtr; fpu_lastOpcode = v } }

  (** val set_location :
      Big.big_int -> loc -> RTL.int -> mach -> mach_state **)

  let set_location _ l v m =
    match l with
    | Coq_reg_loc r -> set_gp_reg r v m
    | Coq_seg_reg_start_loc r -> set_seg_reg_start r v m
    | Coq_seg_reg_limit_loc r -> set_seg_reg_limit r v m
    | Coq_flag_loc f -> set_flags_reg f v m
    | Coq_control_register_loc r -> set_control_reg r v m
    | Coq_debug_register_loc r -> set_debug_reg r v m
    | Coq_pc_loc -> set_pc v m
    | Coq_fpu_stktop_loc -> set_fpu_stktop_reg v m
    | Coq_fpu_flag_loc f -> set_fpu_flags_reg f v m
    | Coq_fpu_rctrl_loc -> set_fpu_rctrl_reg v m
    | Coq_fpu_pctrl_loc -> set_fpu_pctrl_reg v m
    | Coq_fpu_ctrl_flag_loc f -> set_fpu_ctrl_reg f v m
    | Coq_fpu_lastInstrPtr_loc -> set_fpu_lastInstrPtr_reg v m
    | Coq_fpu_lastDataPtr_loc -> set_fpu_lastDataPtr_reg v m
    | Coq_fpu_lastOpcode_loc -> set_lastOpcode_reg v m

  (** val array_sub :
      Big.big_int -> Big.big_int -> array -> RTL.int -> mach_state -> RTL.int **)

  let array_sub _ _ a i m =
    match a with
    | Coq_fpu_datareg -> look m.fpu.fpu_data_regs i
    | Coq_fpu_tag -> look m.fpu.fpu_tags i

  (** val set_fpu_datareg : int3 -> int80 -> mach -> mach **)

  let set_fpu_datareg r v m =
    { core = m.core; fpu = { fpu_data_regs = (fun y ->
      if zeq r y then v else m.fpu.fpu_data_regs y); fpu_status =
      m.fpu.fpu_status; fpu_control = m.fpu.fpu_control; fpu_tags =
      m.fpu.fpu_tags; fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr;
      fpu_lastDataPtr = m.fpu.fpu_lastDataPtr; fpu_lastOpcode =
      m.fpu.fpu_lastOpcode } }

  (** val set_fpu_tags_reg : Word.int -> int2 -> mach -> mach **)

  let set_fpu_tags_reg r v m =
    { core = m.core; fpu = { fpu_data_regs = m.fpu.fpu_data_regs;
      fpu_status = m.fpu.fpu_status; fpu_control = m.fpu.fpu_control;
      fpu_tags = (fun y -> if zeq r y then v else m.fpu.fpu_tags y);
      fpu_lastInstrPtr = m.fpu.fpu_lastInstrPtr; fpu_lastDataPtr =
      m.fpu.fpu_lastDataPtr; fpu_lastOpcode = m.fpu.fpu_lastOpcode } }

  (** val array_upd :
      Big.big_int -> Big.big_int -> array -> RTL.int -> RTL.int -> mach ->
      mach_state **)

  let array_upd _ _ a i v m =
    match a with
    | Coq_fpu_datareg -> set_fpu_datareg i v m
    | Coq_fpu_tag -> set_fpu_tags_reg i v m
 end

module X86_RTL = RTL.RTL(X86_MACHINE)

module X86_Compile =
 struct
  type conv_state = { c_rev_i : X86_RTL.rtl_instr list; c_next : Big.big_int }

  (** val c_rev_i : conv_state -> X86_RTL.rtl_instr list **)

  let c_rev_i x = x.c_rev_i

  (** val c_next : conv_state -> Big.big_int **)

  let c_next x = x.c_next

  type 't coq_Conv = conv_state -> 't * conv_state

  (** val coq_Conv_monad : __ coq_Conv coq_Monad **)

  let coq_Conv_monad =
    { coq_Return = (fun _ x s -> (x, s)); coq_Bind = (fun _ _ c f s ->
      let (v, s') = c s in f v s') }

  (** val runConv : unit coq_Conv -> X86_RTL.rtl_instr list **)

  let runConv c =
    let (_, c') = c { c_rev_i = []; c_next = Big.zero } in rev c'.c_rev_i

  (** val coq_EMIT : X86_RTL.rtl_instr -> unit coq_Conv **)

  let coq_EMIT i s =
    ((), { c_rev_i = (i :: s.c_rev_i); c_next = s.c_next })

  (** val raise_error : unit coq_Conv **)

  let raise_error =
    coq_EMIT X86_RTL.Coq_error_rtl

  (** val raise_trap : unit coq_Conv **)

  let raise_trap =
    coq_EMIT X86_RTL.Coq_trap_rtl

  (** val no_op : unit coq_Conv **)

  let no_op =
    coq_Return (Obj.magic coq_Conv_monad) ()

  (** val load_int : Big.big_int -> RTL.int -> X86_RTL.rtl_exp coq_Conv **)

  let load_int s i =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_imm_rtl_exp (s, i))

  (** val arith :
      Big.big_int -> X86_RTL.bit_vector_op -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let arith s b e1 e2 =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_arith_rtl_exp (s, b,
      e1, e2))

  (** val test :
      Big.big_int -> X86_RTL.test_op -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let test s t0 e1 e2 =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_test_rtl_exp (s, t0,
      e1, e2))

  (** val cast_u :
      Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
      coq_Conv **)

  let cast_u s1 s2 e =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_cast_u_rtl_exp (s1,
      s2, e))

  (** val cast_s :
      Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
      coq_Conv **)

  let cast_s s1 s2 e =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_cast_s_rtl_exp (s1,
      s2, e))

  (** val read_loc :
      Big.big_int -> X86_MACHINE.loc -> X86_RTL.rtl_exp coq_Conv **)

  let read_loc s l =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_get_loc_rtl_exp (s,
      l))

  (** val write_loc :
      Big.big_int -> X86_RTL.rtl_exp -> X86_MACHINE.loc -> unit coq_Conv **)

  let write_loc s e l =
    coq_EMIT (X86_RTL.Coq_set_loc_rtl (s, e, l))

  (** val write_ps_and_fresh :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let write_ps_and_fresh s e ts =
    let r = ts.c_next in
    let ts' = { c_rev_i = ((X86_RTL.Coq_set_ps_reg_rtl (s, e,
      r)) :: ts.c_rev_i); c_next = (Z.add r Big.one) }
    in
    ((X86_RTL.Coq_get_ps_reg_rtl_exp (s, r)), ts')

  (** val read_byte : X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let read_byte a =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_get_byte_rtl_exp a)

  (** val write_byte : X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let write_byte v a =
    coq_EMIT (X86_RTL.Coq_set_byte_rtl (v, a))

  (** val if_exp :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let if_exp s g e1 e2 =
    coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_if_rtl_exp (s, g, e1,
      e2))

  (** val if_trap : X86_RTL.rtl_exp -> unit coq_Conv **)

  let if_trap g =
    coq_EMIT (X86_RTL.Coq_if_rtl (g, X86_RTL.Coq_trap_rtl))

  (** val if_set_loc :
      X86_RTL.rtl_exp -> Big.big_int -> X86_RTL.rtl_exp ->
      X86_MACHINE.location -> unit coq_Conv **)

  let if_set_loc cond s e l =
    coq_EMIT (X86_RTL.Coq_if_rtl (cond, (X86_RTL.Coq_set_loc_rtl (s, e, l))))

  (** val choose : Big.big_int -> X86_RTL.rtl_exp coq_Conv **)

  let choose s =
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic coq_EMIT X86_RTL.Coq_advance_oracle_rtl) (fun _ ->
      coq_Return (Obj.magic coq_Conv_monad) (X86_RTL.Coq_get_random_rtl_exp
        s))

  (** val load_Z : Big.big_int -> Big.big_int -> X86_RTL.rtl_exp coq_Conv **)

  let load_Z s z =
    load_int s (Word.repr s z)

  (** val load_reg : register -> X86_RTL.rtl_exp coq_Conv **)

  let load_reg r =
    read_loc size32 (X86_MACHINE.Coq_reg_loc r)

  (** val set_reg : X86_RTL.rtl_exp -> register -> unit coq_Conv **)

  let set_reg p r =
    write_loc size32 p (X86_MACHINE.Coq_reg_loc r)

  (** val get_seg_start : segment_register -> X86_RTL.rtl_exp coq_Conv **)

  let get_seg_start s =
    read_loc size32 (X86_MACHINE.Coq_seg_reg_start_loc s)

  (** val get_seg_limit : segment_register -> X86_RTL.rtl_exp coq_Conv **)

  let get_seg_limit s =
    read_loc size32 (X86_MACHINE.Coq_seg_reg_limit_loc s)

  (** val get_flag : X86_MACHINE.flag -> X86_RTL.rtl_exp coq_Conv **)

  let get_flag fl =
    read_loc size1 (X86_MACHINE.Coq_flag_loc fl)

  (** val set_flag : X86_MACHINE.flag -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_flag fl r =
    write_loc size1 r (X86_MACHINE.Coq_flag_loc fl)

  (** val get_pc : X86_RTL.rtl_exp coq_Conv **)

  let get_pc =
    read_loc size32 X86_MACHINE.Coq_pc_loc

  (** val set_pc : X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_pc v =
    write_loc size32 v X86_MACHINE.Coq_pc_loc

  (** val not : Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let not s p =
    coq_Bind (Obj.magic coq_Conv_monad) (load_Z s (Word.max_unsigned s))
      (fun mask -> arith s X86_RTL.Coq_xor_op p mask)

  (** val test_neq :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
      coq_Conv **)

  let test_neq s e1 e2 =
    coq_Bind (Obj.magic coq_Conv_monad) (test s X86_RTL.Coq_eq_op e1 e2)
      (fun test_eq -> not size1 test_eq)

  (** val undef_flag : X86_MACHINE.flag -> unit coq_Conv **)

  let undef_flag f =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic choose size1) (fun v ->
      set_flag f v)

  (** val scale_to_int32 : scale -> int32 **)

  let scale_to_int32 s =
    Word.repr size32
      (match s with
       | Scale1 -> Big.one
       | Scale2 -> (Big.double Big.one)
       | Scale4 -> (Big.double (Big.double Big.one))
       | Scale8 -> (Big.double (Big.double (Big.double Big.one))))

  (** val compute_addr : address -> X86_RTL.rtl_exp coq_Conv **)

  let compute_addr a =
    let disp = a.addrDisp in
    (match a.addrBase with
     | Some r1 ->
       (match a.addrIndex with
        | Some p ->
          let (s, r2) = p in
          coq_Bind (Obj.magic coq_Conv_monad) (load_reg r1) (fun b ->
            coq_Bind (Obj.magic coq_Conv_monad) (load_reg r2) (fun i ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (load_int size32 (scale_to_int32 s)) (fun s0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (arith size32 X86_RTL.Coq_mul_op i s0) (fun p0 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (arith size32 X86_RTL.Coq_add_op b p0) (fun p1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (load_int size32 disp) (fun disp0 ->
                      arith size32 X86_RTL.Coq_add_op p1 disp0))))))
        | None ->
          coq_Bind (Obj.magic coq_Conv_monad) (load_reg r1) (fun p1 ->
            coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 disp)
              (fun p2 -> arith size32 X86_RTL.Coq_add_op p1 p2)))
     | None ->
       (match a.addrIndex with
        | Some p ->
          let (s, r) = p in
          coq_Bind (Obj.magic coq_Conv_monad) (load_reg r) (fun i ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (load_int size32 (scale_to_int32 s)) (fun s0 ->
              coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 disp)
                (fun disp0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (arith size32 X86_RTL.Coq_mul_op i s0) (fun p0 ->
                  arith size32 X86_RTL.Coq_add_op disp0 p0))))
        | None -> load_int size32 disp))

  (** val add_and_check_segment :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let add_and_check_segment seg a =
    coq_Bind (Obj.magic coq_Conv_monad) (get_seg_start seg) (fun start ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_seg_limit seg) (fun limit ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (test size32 X86_RTL.Coq_ltu_op limit a) (fun guard ->
          coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic if_trap guard)
            (fun _ -> arith size32 X86_RTL.Coq_add_op start a))))

  (** val lmem :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let lmem seg a =
    coq_Bind (Obj.magic coq_Conv_monad) (add_and_check_segment seg a)
      (fun p -> read_byte p)

  (** val smem :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let smem seg v a =
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic add_and_check_segment seg a) (fun p -> write_byte v p)

  (** val load_mem_n :
      segment_register -> X86_RTL.rtl_exp -> Big.big_int -> Big.big_int ->
      X86_RTL.rtl_exp coq_Conv **)

  let rec load_mem_n seg addr sz nbytes_minus_one =
    Big.nat_case
      (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (lmem seg addr) (fun b ->
        cast_u size8 sz b))
      (fun n ->
      coq_Bind (Obj.magic coq_Conv_monad) (lmem seg addr) (fun b0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (cast_u size8 sz b0) (fun b0' ->
          coq_Bind (Obj.magic coq_Conv_monad) (load_Z size32 Big.one)
            (fun one0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (arith size32 X86_RTL.Coq_add_op addr one0) (fun newaddr ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (load_mem_n seg newaddr sz n) (fun rec0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (load_Z sz (Big.double (Big.double (Big.double Big.one))))
                  (fun eight ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (arith sz X86_RTL.Coq_shl_op rec0 eight) (fun rec' ->
                    arith sz X86_RTL.Coq_or_op b0' rec'))))))))
      nbytes_minus_one

  (** val load_mem32 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let load_mem32 seg addr =
    load_mem_n seg addr size32 (Big.succ (Big.succ (Big.succ Big.zero)))

  (** val load_mem16 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let load_mem16 seg addr =
    load_mem_n seg addr size16 (Big.succ Big.zero)

  (** val load_mem8 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let load_mem8 seg addr =
    load_mem_n seg addr size8 Big.zero

  (** val opsize : bool -> bool -> Big.big_int **)

  let opsize override w =
    if override
    then if w then size16 else size8
    else if w then size32 else size8

  (** val load_mem :
      prefix -> bool -> segment_register -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let load_mem p w seg op =
    if p.op_override
    then if w then load_mem16 seg op else load_mem8 seg op
    else if w then load_mem32 seg op else load_mem8 seg op

  (** val iload_op32 :
      segment_register -> operand -> X86_RTL.rtl_exp coq_Conv **)

  let iload_op32 seg = function
  | Imm_op i -> load_int size32 i
  | Reg_op r -> load_reg r
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (compute_addr a) (fun p1 ->
      load_mem32 seg p1)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 off) (fun p1 ->
      load_mem32 seg p1)

  (** val iload_op16 :
      segment_register -> operand -> X86_RTL.rtl_exp coq_Conv **)

  let iload_op16 seg = function
  | Imm_op i ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 i) (fun tmp ->
      cast_u size32 size16 tmp)
  | Reg_op r ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_reg r) (fun tmp ->
      cast_u size32 size16 tmp)
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (compute_addr a) (fun p1 ->
      load_mem16 seg p1)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 off) (fun p1 ->
      load_mem16 seg p1)

  (** val iload_op8 :
      segment_register -> operand -> X86_RTL.rtl_exp coq_Conv **)

  let iload_op8 seg = function
  | Imm_op i ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 i) (fun tmp ->
      cast_u size32 size8 tmp)
  | Reg_op r ->
    coq_Bind (Obj.magic coq_Conv_monad)
      (load_reg
        (match r with
         | ESP -> EAX
         | EBP -> ECX
         | ESI -> EDX
         | EDI -> EBX
         | x -> x)) (fun tmp ->
      match r with
      | EAX -> cast_u size32 size8 tmp
      | ECX -> cast_u size32 size8 tmp
      | EDX -> cast_u size32 size8 tmp
      | EBX -> cast_u size32 size8 tmp
      | _ ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (load_Z size32 (Big.double (Big.double (Big.double Big.one))))
          (fun eight ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (arith size32 X86_RTL.Coq_shru_op tmp eight) (fun tmp2 ->
            cast_u size32 size8 tmp2)))
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (compute_addr a) (fun p1 ->
      load_mem8 seg p1)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (load_int size32 off) (fun p1 ->
      load_mem8 seg p1)

  (** val set_mem_n :
      segment_register -> X86_RTL.rtl_exp -> Big.big_int -> X86_RTL.rtl_exp
      -> Big.big_int -> unit coq_Conv **)

  let rec set_mem_n seg addr sz v nbytes_minus_one =
    Big.nat_case
      (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic cast_u sz size8 v)
        (fun b0 -> smem seg b0 addr))
      (fun n ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic cast_u sz size8 v)
        (fun b0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (smem seg b0 addr) (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z size32 Big.one) (fun one0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size32 X86_RTL.Coq_add_op addr one0)
              (fun newaddr ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic load_Z sz (Big.double (Big.double (Big.double
                  Big.one)))) (fun eight ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith sz X86_RTL.Coq_shru_op v eight)
                  (fun newv -> set_mem_n seg newaddr sz newv n)))))))
      nbytes_minus_one

  (** val set_mem32 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_mem32 seg v a =
    set_mem_n seg a size32 v (Big.succ (Big.succ (Big.succ Big.zero)))

  (** val set_mem16 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_mem16 seg v a =
    set_mem_n seg a size16 v (Big.succ Big.zero)

  (** val set_mem8 :
      segment_register -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_mem8 seg v a =
    set_mem_n seg a size8 v Big.zero

  (** val set_mem :
      prefix -> bool -> segment_register -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_mem p w seg =
    if p.op_override
    then if w then set_mem16 seg else set_mem8 seg
    else if w then set_mem32 seg else set_mem8 seg

  (** val iset_op32 :
      segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv **)

  let iset_op32 seg p = function
  | Imm_op _ -> raise_error
  | Reg_op r -> set_reg p r
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_addr a)
      (fun addr -> set_mem32 seg p addr)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_int size32 off)
      (fun addr -> set_mem32 seg p addr)

  (** val iset_op16 :
      segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv **)

  let iset_op16 seg p = function
  | Imm_op _ -> raise_error
  | Reg_op r ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg r) (fun tmp ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_int size32 (Word.mone size32)) (fun mask ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size32 (Big.double (Big.double (Big.double
            (Big.double Big.one))))) (fun sixteen ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_shl_op mask sixteen)
            (fun mask2 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size32 X86_RTL.Coq_and_op mask2 tmp)
              (fun tmp2 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic cast_u size16 size32 p) (fun p32 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size32 X86_RTL.Coq_or_op tmp2 p32)
                  (fun tmp3 -> set_reg tmp3 r)))))))
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_addr a)
      (fun addr -> set_mem16 seg p addr)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_int size32 off)
      (fun addr -> set_mem16 seg p addr)

  (** val iset_op8 :
      segment_register -> X86_RTL.rtl_exp -> operand -> unit coq_Conv **)

  let iset_op8 seg p = function
  | Imm_op _ -> raise_error
  | Reg_op r ->
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_reg
        (match r with
         | ESP -> EAX
         | EBP -> ECX
         | ESI -> EDX
         | EDI -> EBX
         | x -> x)) (fun tmp0 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z size32
          (match r with
           | EAX -> Big.zero
           | ECX -> Big.zero
           | EDX -> Big.zero
           | EBX -> Big.zero
           | _ -> (Big.double (Big.double (Big.double Big.one)))))
        (fun shift ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_int size32 (Word.mone size32)) (fun mone0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z size32 (Big.doubleplusone (Big.doubleplusone
              (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
              (Big.doubleplusone (Big.doubleplusone Big.one))))))))
            (fun mask0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size32 X86_RTL.Coq_shl_op mask0 shift)
              (fun mask1 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic arith size32 X86_RTL.Coq_xor_op mask1 mone0)
                (fun mask2 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size32 X86_RTL.Coq_and_op tmp0 mask2)
                  (fun tmp1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic cast_u size8 size32 p) (fun pext ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith size32 X86_RTL.Coq_shl_op pext shift)
                      (fun pext_shift ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size32 X86_RTL.Coq_or_op tmp1
                          pext_shift) (fun res ->
                        set_reg res
                          (match r with
                           | ESP -> EAX
                           | EBP -> ECX
                           | ESI -> EDX
                           | EDI -> EBX
                           | x -> x)))))))))))
  | Address_op a ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_addr a)
      (fun addr -> set_mem8 seg p addr)
  | Offset_op off ->
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_int size32 off)
      (fun addr -> set_mem8 seg p addr)

  (** val load_op :
      prefix -> bool -> segment_register -> operand -> X86_RTL.rtl_exp
      coq_Conv **)

  let load_op p w seg op =
    if p.op_override
    then if w then iload_op16 seg op else iload_op8 seg op
    else if w then iload_op32 seg op else iload_op8 seg op

  (** val set_op :
      prefix -> bool -> segment_register -> X86_RTL.rtl_exp -> operand ->
      unit coq_Conv **)

  let set_op p w seg =
    if p.op_override
    then if w then iset_op16 seg else iset_op8 seg
    else if w then iset_op32 seg else iset_op8 seg

  (** val get_segment : prefix -> segment_register -> segment_register **)

  let get_segment p def =
    match p.seg_override with
    | Some s -> s
    | None -> def

  (** val op_contains_stack : operand -> bool **)

  let op_contains_stack = function
  | Address_op a ->
    (match a.addrBase with
     | Some r ->
       (match r with
        | ESP -> true
        | EBP -> true
        | _ -> false)
     | None -> false)
  | _ -> false

  (** val get_segment_op :
      prefix -> segment_register -> operand -> segment_register **)

  let get_segment_op p def op =
    match p.seg_override with
    | Some s -> s
    | None -> if op_contains_stack op then SS else def

  (** val get_segment_op2 :
      prefix -> segment_register -> operand -> operand -> segment_register **)

  let get_segment_op2 p def op1 op2 =
    match p.seg_override with
    | Some s -> s
    | None ->
      let b = op_contains_stack op1 in
      let b0 = op_contains_stack op2 in
      if b then SS else if b0 then SS else def

  (** val compute_cc : condition_type -> X86_RTL.rtl_exp coq_Conv **)

  let compute_cc = function
  | O_ct -> get_flag X86_MACHINE.OF
  | NO_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.OF) (fun p ->
      not size1 p)
  | B_ct -> get_flag X86_MACHINE.CF
  | NB_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.CF) (fun p ->
      not size1 p)
  | E_ct -> get_flag X86_MACHINE.ZF
  | NE_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.ZF) (fun p ->
      not size1 p)
  | BE_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.CF) (fun cf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.ZF)
        (fun zf -> arith size1 X86_RTL.Coq_or_op cf zf))
  | NBE_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.CF) (fun cf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.ZF)
        (fun zf ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (arith size1 X86_RTL.Coq_or_op cf zf) (fun p -> not size1 p)))
  | S_ct -> get_flag X86_MACHINE.SF
  | NS_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.SF) (fun p ->
      not size1 p)
  | P_ct -> get_flag X86_MACHINE.PF
  | NP_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.PF) (fun p ->
      not size1 p)
  | L_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.SF) (fun sf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.OF)
        (fun of0 -> arith size1 X86_RTL.Coq_xor_op sf of0))
  | NL_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.SF) (fun sf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.OF)
        (fun of0 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (arith size1 X86_RTL.Coq_xor_op sf of0) (fun p -> not size1 p)))
  | LE_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.ZF) (fun zf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.OF)
        (fun of0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.SF)
          (fun sf ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (arith size1 X86_RTL.Coq_xor_op of0 sf) (fun p ->
            arith size1 X86_RTL.Coq_or_op zf p))))
  | NLE_ct ->
    coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.ZF) (fun zf ->
      coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.OF)
        (fun of0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (get_flag X86_MACHINE.SF)
          (fun sf ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (arith size1 X86_RTL.Coq_xor_op of0 sf) (fun p0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (arith size1 X86_RTL.Coq_or_op zf p0) (fun p1 -> not size1 p1)))))

  (** val compute_parity_aux :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> Big.big_int ->
      X86_RTL.rtl_exp coq_Conv **)

  let rec compute_parity_aux s op1 op2 n =
    Big.nat_case
      (fun _ ->
      load_Z size1 Big.zero)
      (fun m ->
      coq_Bind (Obj.magic coq_Conv_monad) (compute_parity_aux s op1 op2 m)
        (fun op3 ->
        coq_Bind (Obj.magic coq_Conv_monad) (load_Z s (Z.of_nat m))
          (fun sf ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (arith s X86_RTL.Coq_shru_op op1 sf) (fun op4 ->
            coq_Bind (Obj.magic coq_Conv_monad) (cast_u s size1 op4)
              (fun r -> arith size1 X86_RTL.Coq_xor_op r op3)))))
      n

  (** val compute_parity :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let compute_parity s op =
    coq_Bind (Obj.magic coq_Conv_monad) (load_Z size1 Big.zero) (fun r1 ->
      coq_Bind (Obj.magic coq_Conv_monad) (load_Z size1 Big.one) (fun one0 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (compute_parity_aux s op r1 (Big.succ (Big.succ (Big.succ (Big.succ
            (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))
          (fun p -> arith size1 X86_RTL.Coq_xor_op p one0)))

  (** val conv_INC : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_INC pre w op =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op) (fun p0 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z (opsize pre.op_override w) Big.one) (fun p1 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith (opsize pre.op_override w) X86_RTL.Coq_add_op p0
            p1) (fun p2 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z (opsize pre.op_override w) Big.zero)
            (fun zero0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_lt_op p2
                p0) (fun ofp ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_eq_op
                  p2 zero0) (fun zfp ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test (opsize pre.op_override w)
                    X86_RTL.Coq_lt_op p2 zero0) (fun sfp ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic compute_parity (opsize pre.op_override w) p2)
                    (fun pfp ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic cast_u (opsize pre.op_override w) size4 p0)
                      (fun n0 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic load_Z size4 Big.one) (fun n1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic arith size4 X86_RTL.Coq_add_op n0 n1)
                          (fun n2 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic test size4 X86_RTL.Coq_ltu_op n2 n0)
                            (fun afp ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (set_flag X86_MACHINE.OF ofp) (fun _ ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (set_flag X86_MACHINE.ZF zfp) (fun _ ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (set_flag X86_MACHINE.SF sfp) (fun _ ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (set_flag X86_MACHINE.PF pfp) (fun _ ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (set_flag X86_MACHINE.AF afp) (fun _ ->
                                      set0 seg p2 op)))))))))))))))))

  (** val conv_DEC : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_DEC pre w op =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op) (fun p0 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z (opsize pre.op_override w) Big.one) (fun p1 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith (opsize pre.op_override w) X86_RTL.Coq_sub_op p0
            p1) (fun p2 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z (opsize pre.op_override w) Big.zero)
            (fun zero0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_lt_op p0
                p2) (fun ofp ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_eq_op
                  p2 zero0) (fun zfp ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test (opsize pre.op_override w)
                    X86_RTL.Coq_lt_op p2 zero0) (fun sfp ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic compute_parity (opsize pre.op_override w) p2)
                    (fun pfp ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic cast_u (opsize pre.op_override w) size4 p0)
                      (fun n0 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic load_Z size4 Big.one) (fun n1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic arith size4 X86_RTL.Coq_sub_op n0 n1)
                          (fun n2 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic test size4 X86_RTL.Coq_ltu_op n0 n2)
                            (fun afp ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (set_flag X86_MACHINE.OF ofp) (fun _ ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (set_flag X86_MACHINE.ZF zfp) (fun _ ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (set_flag X86_MACHINE.SF sfp) (fun _ ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (set_flag X86_MACHINE.PF pfp) (fun _ ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (set_flag X86_MACHINE.AF afp) (fun _ ->
                                      set0 seg p2 op)))))))))))))))))

  (** val conv_ADC : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_ADC pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z (opsize pre.op_override w) Big.zero) (fun zero0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
        (fun up ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
          (fun p0 ->
          coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
            (fun p1 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic get_flag X86_MACHINE.CF) (fun cf0 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic write_ps_and_fresh size1 cf0) (fun old_cf ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic cast_u size1 (opsize pre.op_override w) old_cf)
                  (fun cfext ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic arith (opsize pre.op_override w)
                      X86_RTL.Coq_add_op p0 p1) (fun p2' ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith (opsize pre.op_override w)
                        X86_RTL.Coq_add_op p2' cfext) (fun p2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic test (opsize pre.op_override w)
                          X86_RTL.Coq_lt_op p0 zero0) (fun b0 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic test (opsize pre.op_override w)
                            X86_RTL.Coq_lt_op p1 zero0) (fun b1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic test (opsize pre.op_override w)
                              X86_RTL.Coq_lt_op p2 zero0) (fun b2 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith size1 X86_RTL.Coq_xor_op b0
                                b1) (fun b3 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size1 X86_RTL.Coq_xor_op up
                                  b3) (fun b4 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith size1 X86_RTL.Coq_xor_op
                                    b0 b2) (fun b5 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size1 X86_RTL.Coq_and_op
                                      b4 b5) (fun ofp ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test
                                        (opsize pre.op_override w)
                                        X86_RTL.Coq_ltu_op p2' p0) (fun b6 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic test
                                          (opsize pre.op_override w)
                                          X86_RTL.Coq_ltu_op p2' p1)
                                        (fun b7 ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic test
                                            (opsize pre.op_override w)
                                            X86_RTL.Coq_ltu_op p2 p2')
                                          (fun b8 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic test
                                              (opsize pre.op_override w)
                                              X86_RTL.Coq_ltu_op p2 cfext)
                                            (fun b9 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic arith size1
                                                X86_RTL.Coq_or_op b6 b7)
                                              (fun b10 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic arith size1
                                                  X86_RTL.Coq_or_op b8 b9)
                                                (fun b11 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic arith size1
                                                    X86_RTL.Coq_or_op b10
                                                    b11) (fun cfp ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic test
                                                      (opsize pre.op_override
                                                        w) X86_RTL.Coq_eq_op
                                                      p2 zero0) (fun zfp ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic test
                                                        (opsize
                                                          pre.op_override w)
                                                        X86_RTL.Coq_lt_op p2
                                                        zero0) (fun sfp ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic
                                                          compute_parity
                                                          (opsize
                                                            pre.op_override
                                                            w) p2)
                                                        (fun pfp ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic cast_u
                                                            (opsize
                                                              pre.op_override
                                                              w) size4 p0)
                                                          (fun n0 ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic cast_u
                                                              (opsize
                                                                pre.op_override
                                                                w) size4 p1)
                                                            (fun n1 ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                cast_u size1
                                                                size4 old_cf)
                                                              (fun cf4 ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  arith size4
                                                                  X86_RTL.Coq_add_op
                                                                  n0 n1)
                                                                (fun n2 ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    arith
                                                                    size4
                                                                    X86_RTL.Coq_add_op
                                                                    n2 cf4)
                                                                  (fun n3 ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    test
                                                                    size4
                                                                    X86_RTL.Coq_ltu_op
                                                                    n3 n0)
                                                                    (fun b12 ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    test
                                                                    size4
                                                                    X86_RTL.Coq_ltu_op
                                                                    n3 n1)
                                                                    (fun b13 ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    arith
                                                                    size1
                                                                    X86_RTL.Coq_or_op
                                                                    b12 b13)
                                                                    (fun afp ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.OF
                                                                    ofp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.CF
                                                                    cfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.ZF
                                                                    zfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.SF
                                                                    sfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.PF
                                                                    pfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.AF
                                                                    afp)
                                                                    (fun _ ->
                                                                    set0 seg
                                                                    p2 op1))))))))))))))))))))))))))))))))))))))))

  (** val conv_STC : unit coq_Conv **)

  let conv_STC =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
      (fun one0 -> set_flag X86_MACHINE.CF one0)

  (** val conv_STD : unit coq_Conv **)

  let conv_STD =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
      (fun one0 -> set_flag X86_MACHINE.DF one0)

  (** val conv_CLC : unit coq_Conv **)

  let conv_CLC =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.zero)
      (fun zero0 -> set_flag X86_MACHINE.CF zero0)

  (** val conv_CLD : unit coq_Conv **)

  let conv_CLD =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.zero)
      (fun zero0 -> set_flag X86_MACHINE.DF zero0)

  (** val conv_CMC : unit coq_Conv **)

  let conv_CMC =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.zero)
      (fun zero0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_flag X86_MACHINE.CF)
        (fun p1 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic test size1 X86_RTL.Coq_eq_op zero0 p1) (fun p0 ->
          set_flag X86_MACHINE.CF p0)))

  (** val conv_LAHF : unit coq_Conv **)

  let conv_LAHF =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size8 Big.zero)
      (fun dst ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_flag X86_MACHINE.SF)
        (fun fl ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
            Big.one))) (fun pos ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic cast_u size1 size8 fl) (fun byt ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size8 X86_RTL.Coq_shl_op byt pos) (fun tmp ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic arith size8 X86_RTL.Coq_or_op dst tmp)
                (fun dst0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic get_flag X86_MACHINE.ZF) (fun fl0 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load_Z size8 (Big.double (Big.doubleplusone
                      Big.one))) (fun pos0 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic cast_u size1 size8 fl0) (fun byt0 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size8 X86_RTL.Coq_shl_op byt0 pos0)
                        (fun tmp0 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic arith size8 X86_RTL.Coq_or_op dst0 tmp0)
                          (fun dst1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic get_flag X86_MACHINE.AF) (fun fl1 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic load_Z size8 (Big.double (Big.double
                                Big.one))) (fun pos1 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic cast_u size1 size8 fl1)
                                (fun byt1 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith size8 X86_RTL.Coq_shl_op
                                    byt1 pos1) (fun tmp1 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size8 X86_RTL.Coq_or_op
                                      dst1 tmp1) (fun dst2 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic get_flag X86_MACHINE.PF)
                                      (fun fl2 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic load_Z size8 (Big.double
                                          Big.one)) (fun pos2 ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u size1 size8 fl2)
                                          (fun byt2 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size8
                                              X86_RTL.Coq_shl_op byt2 pos2)
                                            (fun tmp2 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic arith size8
                                                X86_RTL.Coq_or_op dst2 tmp2)
                                              (fun dst3 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic get_flag
                                                  X86_MACHINE.CF) (fun fl3 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic load_Z size8
                                                    Big.zero) (fun pos3 ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic cast_u size1
                                                      size8 fl3) (fun byt3 ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic arith size8
                                                        X86_RTL.Coq_shl_op
                                                        byt3 pos3)
                                                      (fun tmp3 ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          size8
                                                          X86_RTL.Coq_or_op
                                                          dst3 tmp3)
                                                        (fun dst4 ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic load_Z
                                                            size8 Big.one)
                                                          (fun fl4 ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic load_Z
                                                              size8 Big.one)
                                                            (fun pos4 ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                cast_u size8
                                                                size8 fl4)
                                                              (fun byt4 ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  arith size8
                                                                  X86_RTL.Coq_shl_op
                                                                  byt4 pos4)
                                                                (fun tmp4 ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    arith
                                                                    size8
                                                                    X86_RTL.Coq_or_op
                                                                    dst4
                                                                    tmp4)
                                                                  (fun dst5 ->
                                                                  iset_op8 DS
                                                                    dst5
                                                                    (Reg_op
                                                                    ESP))))))))))))))))))))))))))))))))

  (** val conv_SAHF : unit coq_Conv **)

  let conv_SAHF =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size8 Big.one)
      (fun one0 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic iload_op8 DS (Reg_op ESP)) (fun ah ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
            Big.one))) (fun pos ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size8 X86_RTL.Coq_shr_op ah pos) (fun tmp ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size8 X86_RTL.Coq_and_op tmp one0)
              (fun tmp0 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test size8 X86_RTL.Coq_eq_op one0 tmp0)
                (fun sfp ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic load_Z size8 (Big.double (Big.doubleplusone
                    Big.one))) (fun pos0 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic arith size8 X86_RTL.Coq_shr_op ah pos0)
                    (fun tmp1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith size8 X86_RTL.Coq_and_op tmp1 one0)
                      (fun tmp2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic test size8 X86_RTL.Coq_eq_op one0 tmp2)
                        (fun zfp ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic load_Z size8 (Big.double (Big.double
                            Big.one))) (fun pos1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith size8 X86_RTL.Coq_shr_op ah
                              pos1) (fun tmp3 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith size8 X86_RTL.Coq_and_op tmp3
                                one0) (fun tmp4 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic test size8 X86_RTL.Coq_eq_op one0
                                  tmp4) (fun afp ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic load_Z size8 (Big.double
                                    Big.one)) (fun pos2 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size8 X86_RTL.Coq_shr_op
                                      ah pos2) (fun tmp5 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size8
                                        X86_RTL.Coq_and_op tmp5 one0)
                                      (fun tmp6 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic test size8
                                          X86_RTL.Coq_eq_op one0 tmp6)
                                        (fun pfp ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic load_Z size8 Big.zero)
                                          (fun pos3 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size8
                                              X86_RTL.Coq_shr_op ah pos3)
                                            (fun tmp7 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic arith size8
                                                X86_RTL.Coq_and_op tmp7 one0)
                                              (fun tmp8 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size8
                                                  X86_RTL.Coq_eq_op one0
                                                  tmp8) (fun cfp ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (set_flag X86_MACHINE.SF
                                                    sfp) (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (set_flag X86_MACHINE.ZF
                                                      zfp) (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (set_flag
                                                        X86_MACHINE.AF afp)
                                                      (fun _ ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (set_flag
                                                          X86_MACHINE.PF pfp)
                                                        (fun _ ->
                                                        set_flag
                                                          X86_MACHINE.CF cfp))))))))))))))))))))))))))

  (** val conv_ADD : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_ADD pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z (opsize pre.op_override w) Big.zero) (fun zero0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
        (fun up ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
          (fun p0 ->
          coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
            (fun p1 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith (opsize pre.op_override w) X86_RTL.Coq_add_op
                p0 p1) (fun p2 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_lt_op
                  p0 zero0) (fun b0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test (opsize pre.op_override w)
                    X86_RTL.Coq_lt_op p1 zero0) (fun b1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic test (opsize pre.op_override w)
                      X86_RTL.Coq_lt_op p2 zero0) (fun b2 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith size1 X86_RTL.Coq_xor_op b0 b1)
                      (fun b3 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size1 X86_RTL.Coq_xor_op up b3)
                        (fun b4 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic arith size1 X86_RTL.Coq_xor_op b0 b2)
                          (fun b5 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith size1 X86_RTL.Coq_and_op b4 b5)
                            (fun ofp ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic test (opsize pre.op_override w)
                                X86_RTL.Coq_ltu_op p2 p0) (fun b6 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic test (opsize pre.op_override w)
                                  X86_RTL.Coq_ltu_op p2 p1) (fun b7 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith size1 X86_RTL.Coq_or_op b6
                                    b7) (fun cfp ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic test
                                      (opsize pre.op_override w)
                                      X86_RTL.Coq_eq_op p2 zero0) (fun zfp ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test
                                        (opsize pre.op_override w)
                                        X86_RTL.Coq_lt_op p2 zero0)
                                      (fun sfp ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic compute_parity
                                          (opsize pre.op_override w) p2)
                                        (fun pfp ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u
                                            (opsize pre.op_override w) size4
                                            p0) (fun n0 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic cast_u
                                              (opsize pre.op_override w)
                                              size4 p1) (fun n1 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic arith size4
                                                X86_RTL.Coq_add_op n0 n1)
                                              (fun n2 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size4
                                                  X86_RTL.Coq_ltu_op n2 n0)
                                                (fun b8 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size4
                                                    X86_RTL.Coq_ltu_op n2 n1)
                                                  (fun b9 ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic arith size1
                                                      X86_RTL.Coq_or_op b8
                                                      b9) (fun afp ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (set_flag
                                                        X86_MACHINE.OF ofp)
                                                      (fun _ ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (set_flag
                                                          X86_MACHINE.CF cfp)
                                                        (fun _ ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (set_flag
                                                            X86_MACHINE.ZF
                                                            zfp) (fun _ ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (set_flag
                                                              X86_MACHINE.SF
                                                              sfp) (fun _ ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (set_flag
                                                                X86_MACHINE.PF
                                                                pfp)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (set_flag
                                                                  X86_MACHINE.AF
                                                                  afp)
                                                                (fun _ ->
                                                                set0 seg p2
                                                                  op1))))))))))))))))))))))))))))))

  (** val conv_SUB_CMP_generic :
      bool -> prefix -> bool -> operand -> operand -> operand ->
      segment_register -> segment_register -> segment_register -> unit
      coq_Conv **)

  let conv_SUB_CMP_generic e pre w dest op1 op2 segdest seg1 seg2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z (opsize pre.op_override w) Big.zero) (fun zero0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
        (fun one0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg1 op1)
          (fun p0 ->
          coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg2 op2)
            (fun p1 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith (opsize pre.op_override w) X86_RTL.Coq_sub_op
                p0 p1) (fun p2 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_lt_op
                  p0 zero0) (fun b0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test (opsize pre.op_override w)
                    X86_RTL.Coq_lt_op p1 zero0) (fun b1' ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic arith size1 X86_RTL.Coq_xor_op b1' one0)
                    (fun b1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic test (opsize pre.op_override w)
                        X86_RTL.Coq_lt_op p2 zero0) (fun b2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size1 X86_RTL.Coq_xor_op b0 b1)
                        (fun b3 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic arith size1 X86_RTL.Coq_xor_op b3 one0)
                          (fun b4 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith size1 X86_RTL.Coq_xor_op b0 b2)
                            (fun b5 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith size1 X86_RTL.Coq_and_op b4
                                b5) (fun ofp ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic test (opsize pre.op_override w)
                                  X86_RTL.Coq_ltu_op p0 p1) (fun cfp ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic test (opsize pre.op_override w)
                                    X86_RTL.Coq_eq_op p2 zero0) (fun zfp ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic test
                                      (opsize pre.op_override w)
                                      X86_RTL.Coq_lt_op p2 zero0) (fun sfp ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic compute_parity
                                        (opsize pre.op_override w) p2)
                                      (fun pfp ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_u
                                          (opsize pre.op_override w) size4
                                          p0) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u
                                            (opsize pre.op_override w) size4
                                            p1) (fun _ ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic test
                                              (opsize pre.op_override w)
                                              X86_RTL.Coq_ltu_op p0 p1)
                                            (fun afp ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (set_flag X86_MACHINE.OF ofp)
                                              (fun _ ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (set_flag X86_MACHINE.CF cfp)
                                                (fun _ ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (set_flag X86_MACHINE.ZF
                                                    zfp) (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (set_flag X86_MACHINE.SF
                                                      sfp) (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (set_flag
                                                        X86_MACHINE.PF pfp)
                                                      (fun _ ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (set_flag
                                                          X86_MACHINE.AF afp)
                                                        (fun _ ->
                                                        if e
                                                        then set0 segdest p2
                                                               dest
                                                        else no_op))))))))))))))))))))))))))

  (** val conv_CMP : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_CMP pre w op1 op2 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    conv_SUB_CMP_generic false pre w op1 op1 op2 seg seg seg

  (** val conv_SUB : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_SUB pre w op1 op2 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    conv_SUB_CMP_generic true pre w op1 op1 op2 seg seg seg

  (** val conv_NEG : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_NEG pre w op1 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    conv_SUB_CMP_generic true pre w op1 (Imm_op (Word.zero size32)) op1 seg
      seg seg

  (** val conv_SBB : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_SBB pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z (opsize pre.op_override w) Big.zero) (fun zero0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
        (fun one0 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic get_flag X86_MACHINE.CF) (fun cf0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic write_ps_and_fresh size1 cf0) (fun old_cf ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic cast_u size1 (opsize pre.op_override w) old_cf)
              (fun old_cf_ext ->
              coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
                (fun p0 ->
                coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
                  (fun p1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic arith (opsize pre.op_override w)
                      X86_RTL.Coq_sub_op p0 p1) (fun p1' ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith (opsize pre.op_override w)
                        X86_RTL.Coq_sub_op p1' old_cf_ext) (fun p2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic test (opsize pre.op_override w)
                          X86_RTL.Coq_lt_op p0 zero0) (fun b0 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic test (opsize pre.op_override w)
                            X86_RTL.Coq_lt_op p1 zero0) (fun b1' ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith size1 X86_RTL.Coq_xor_op b1'
                              one0) (fun b1 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic test (opsize pre.op_override w)
                                X86_RTL.Coq_lt_op p2 zero0) (fun b2 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size1 X86_RTL.Coq_xor_op b0
                                  b1) (fun b3 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith size1 X86_RTL.Coq_xor_op
                                    b3 one0) (fun b4 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size1 X86_RTL.Coq_xor_op
                                      b0 b2) (fun b5 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size1
                                        X86_RTL.Coq_and_op b4 b5) (fun ofp ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic test
                                          (opsize pre.op_override w)
                                          X86_RTL.Coq_ltu_op p0 p1)
                                        (fun b6 ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic test
                                            (opsize pre.op_override w)
                                            X86_RTL.Coq_ltu_op p1'
                                            old_cf_ext) (fun b7 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size1
                                              X86_RTL.Coq_or_op b6 b7)
                                            (fun cfp ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic test
                                                (opsize pre.op_override w)
                                                X86_RTL.Coq_eq_op p2 zero0)
                                              (fun zfp ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test
                                                  (opsize pre.op_override w)
                                                  X86_RTL.Coq_lt_op p2 zero0)
                                                (fun sfp ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic compute_parity
                                                    (opsize pre.op_override
                                                      w) p2) (fun pfp ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic cast_u
                                                      (opsize pre.op_override
                                                        w) size4 p0)
                                                    (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_u
                                                        (opsize
                                                          pre.op_override w)
                                                        size4 p1) (fun _ ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic test
                                                          (opsize
                                                            pre.op_override
                                                            w)
                                                          X86_RTL.Coq_ltu_op
                                                          p0 p1) (fun b0' ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic test
                                                            (opsize
                                                              pre.op_override
                                                              w)
                                                            X86_RTL.Coq_eq_op
                                                            p0 p1)
                                                          (fun b0'' ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic arith
                                                              size1
                                                              X86_RTL.Coq_or_op
                                                              b0' b0'')
                                                            (fun afp ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (set_flag
                                                                X86_MACHINE.OF
                                                                ofp)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (set_flag
                                                                  X86_MACHINE.CF
                                                                  cfp)
                                                                (fun _ ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (set_flag
                                                                    X86_MACHINE.ZF
                                                                    zfp)
                                                                  (fun _ ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.SF
                                                                    sfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.PF
                                                                    pfp)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set_flag
                                                                    X86_MACHINE.AF
                                                                    afp)
                                                                    (fun _ ->
                                                                    set0 seg
                                                                    p2 op1))))))))))))))))))))))))))))))))))

  (** val conv_DIV : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_DIV pre w op =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.CF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
                (fun _ ->
                if pre.op_override
                then if w
                     then coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend_lower ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op16 seg (Reg_op EDX))
                                (fun dividend_upper ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u size16 size32
                                    dividend_upper) (fun dividend0 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size32 (Big.double
                                      (Big.double (Big.double (Big.double
                                      Big.one))))) (fun sixteen ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size32
                                        X86_RTL.Coq_shl_op dividend0 sixteen)
                                      (fun dividend1 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_u size16 size32
                                          dividend_lower)
                                        (fun dividend_lower_ext ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith size32
                                            X86_RTL.Coq_or_op dividend1
                                            dividend_lower_ext)
                                          (fun dividend ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic iload_op16 seg op)
                                            (fun op_val ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic write_ps_and_fresh
                                                size16 op_val)
                                              (fun divisor ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size16
                                                  Big.zero) (fun zero0 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size16
                                                    X86_RTL.Coq_eq_op zero0
                                                    divisor)
                                                  (fun divide_by_zero ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (if_trap divide_by_zero)
                                                    (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_u
                                                        size16 size32
                                                        divisor)
                                                      (fun divisor_ext ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          size32
                                                          X86_RTL.Coq_divu_op
                                                          dividend
                                                          divisor_ext)
                                                        (fun quotient ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic load_Z
                                                            size32
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            Big.one))))))))))))))))
                                                          (fun max_quotient ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic test
                                                              size32
                                                              X86_RTL.Coq_ltu_op
                                                              max_quotient
                                                              quotient)
                                                            (fun div_error ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (if_trap
                                                                div_error)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  arith
                                                                  size32
                                                                  X86_RTL.Coq_modu_op
                                                                  dividend
                                                                  divisor_ext)
                                                                (fun remainder ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    cast_u
                                                                    size32
                                                                    size16
                                                                    quotient)
                                                                  (fun quotient_trunc ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_u
                                                                    size32
                                                                    size16
                                                                    remainder)
                                                                    (fun remainder_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (iset_op16
                                                                    seg
                                                                    quotient_trunc
                                                                    (Reg_op
                                                                    EAX))
                                                                    (fun _ ->
                                                                    iset_op16
                                                                    seg
                                                                    remainder_trunc
                                                                    (Reg_op
                                                                    EDX)))))))))))))))))))))))
                     else coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op8 seg op) (fun op_val ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic write_ps_and_fresh size8 op_val)
                                  (fun divisor ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size8 Big.zero)
                                    (fun zero0 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test size8 X86_RTL.Coq_eq_op
                                        zero0 divisor) (fun divide_by_zero ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (if_trap divide_by_zero) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u size8 size16
                                            divisor) (fun divisor_ext ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size16
                                              X86_RTL.Coq_divu_op dividend
                                              divisor_ext) (fun quotient ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size16
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                Big.one))))))))
                                              (fun max_quotient ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size16
                                                  X86_RTL.Coq_ltu_op
                                                  max_quotient quotient)
                                                (fun div_error ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (if_trap div_error)
                                                  (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic arith size16
                                                      X86_RTL.Coq_modu_op
                                                      dividend divisor_ext)
                                                    (fun remainder ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_u
                                                        size16 size8
                                                        quotient)
                                                      (fun quotient_trunc ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic cast_u
                                                          size16 size8
                                                          remainder)
                                                        (fun remainder_trunc ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (iset_op8 seg
                                                            quotient_trunc
                                                            (Reg_op EAX))
                                                          (fun _ ->
                                                          iset_op8 seg
                                                            remainder_trunc
                                                            (Reg_op ESP)))))))))))))))))
                else if w
                     then coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op32 seg (Reg_op EAX))
                            (fun oe ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size32 oe)
                              (fun dividend_lower ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op32 seg (Reg_op EDX))
                                (fun dividend_upper ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u size32 (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ
                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    dividend_upper) (fun dividend0 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ
                                      Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      (Big.double (Big.double (Big.double
                                      (Big.double (Big.double Big.one))))))
                                    (fun thirtytwo ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ
                                        Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        X86_RTL.Coq_shl_op dividend0
                                        thirtytwo) (fun dividend1 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_u size32 (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ
                                          Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          dividend_lower)
                                        (fun dividend_lower_ext ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ
                                            Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            X86_RTL.Coq_or_op dividend1
                                            dividend_lower_ext)
                                          (fun dividend ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic iload_op32 seg op)
                                            (fun op_val ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic write_ps_and_fresh
                                                size32 op_val)
                                              (fun divisor ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size32
                                                  Big.zero) (fun zero0 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size32
                                                    X86_RTL.Coq_eq_op zero0
                                                    divisor)
                                                  (fun divide_by_zero ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (if_trap divide_by_zero)
                                                    (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_u
                                                        size32 (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        divisor)
                                                      (fun divisor_ext ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ
                                                          Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          X86_RTL.Coq_divu_op
                                                          dividend
                                                          divisor_ext)
                                                        (fun quotient ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic load_Z
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            Big.one))))))))))))))))))))))))))))))))
                                                          (fun max_quotient ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic test
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              X86_RTL.Coq_ltu_op
                                                              max_quotient
                                                              quotient)
                                                            (fun div_error ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (if_trap
                                                                div_error)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  arith
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  X86_RTL.Coq_modu_op
                                                                  dividend
                                                                  divisor_ext)
                                                                (fun remainder ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    cast_u
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    quotient)
                                                                  (fun quotient_trunc ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_u
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    remainder)
                                                                    (fun remainder_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (iset_op32
                                                                    seg
                                                                    quotient_trunc
                                                                    (Reg_op
                                                                    EAX))
                                                                    (fun _ ->
                                                                    iset_op32
                                                                    seg
                                                                    remainder_trunc
                                                                    (Reg_op
                                                                    EDX)))))))))))))))))))))))
                     else coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op8 seg op) (fun op_val ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic write_ps_and_fresh size8 op_val)
                                  (fun divisor ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size8 Big.zero)
                                    (fun zero0 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test size8 X86_RTL.Coq_eq_op
                                        zero0 divisor) (fun divide_by_zero ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (if_trap divide_by_zero) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u size8 size16
                                            divisor) (fun divisor_ext ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size16
                                              X86_RTL.Coq_divu_op dividend
                                              divisor_ext) (fun quotient ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size16
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                Big.one))))))))
                                              (fun max_quotient ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size16
                                                  X86_RTL.Coq_ltu_op
                                                  max_quotient quotient)
                                                (fun div_error ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (if_trap div_error)
                                                  (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic arith size16
                                                      X86_RTL.Coq_modu_op
                                                      dividend divisor_ext)
                                                    (fun remainder ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_u
                                                        size16 size8
                                                        quotient)
                                                      (fun quotient_trunc ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic cast_u
                                                          size16 size8
                                                          remainder)
                                                        (fun remainder_trunc ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (iset_op8 seg
                                                            quotient_trunc
                                                            (Reg_op EAX))
                                                          (fun _ ->
                                                          iset_op8 seg
                                                            remainder_trunc
                                                            (Reg_op ESP)))))))))))))))))))))))

  (** val conv_IDIV : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_IDIV pre w op =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.CF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
                (fun _ ->
                if pre.op_override
                then if w
                     then coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend_lower ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op16 seg (Reg_op EDX))
                                (fun dividend_upper ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_s size16 size32
                                    dividend_upper) (fun dividend0 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size32 (Big.double
                                      (Big.double (Big.double (Big.double
                                      Big.one))))) (fun sixteen ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size32
                                        X86_RTL.Coq_shl_op dividend0 sixteen)
                                      (fun dividend1 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_s size16 size32
                                          dividend_lower)
                                        (fun dividend_lower_ext ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith size32
                                            X86_RTL.Coq_or_op dividend1
                                            dividend_lower_ext)
                                          (fun dividend ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic iload_op16 seg op)
                                            (fun op_val ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic write_ps_and_fresh
                                                size16 op_val)
                                              (fun divisor ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size16
                                                  Big.zero) (fun zero0 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size16
                                                    X86_RTL.Coq_eq_op zero0
                                                    divisor)
                                                  (fun divide_by_zero ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (if_trap divide_by_zero)
                                                    (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_s
                                                        size16 size32
                                                        divisor)
                                                      (fun divisor_ext ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          size32
                                                          X86_RTL.Coq_divs_op
                                                          dividend
                                                          divisor_ext)
                                                        (fun quotient ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic load_Z
                                                            size32
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            Big.one)))))))))))))))
                                                          (fun max_quotient ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic load_Z
                                                              size32 (Big.opp
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              Big.one)))))))))))))))))
                                                            (fun min_quotient ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic test
                                                                size32
                                                                X86_RTL.Coq_lt_op
                                                                max_quotient
                                                                quotient)
                                                              (fun div_error0 ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  test size32
                                                                  X86_RTL.Coq_lt_op
                                                                  quotient
                                                                  min_quotient)
                                                                (fun div_error1 ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    arith
                                                                    size1
                                                                    X86_RTL.Coq_or_op
                                                                    div_error0
                                                                    div_error1)
                                                                  (fun div_error ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_trap
                                                                    div_error)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    arith
                                                                    size32
                                                                    X86_RTL.Coq_mods_op
                                                                    dividend
                                                                    divisor_ext)
                                                                    (fun remainder ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_s
                                                                    size32
                                                                    size16
                                                                    quotient)
                                                                    (fun quotient_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_s
                                                                    size32
                                                                    size16
                                                                    remainder)
                                                                    (fun remainder_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (iset_op16
                                                                    seg
                                                                    quotient_trunc
                                                                    (Reg_op
                                                                    EAX))
                                                                    (fun _ ->
                                                                    iset_op16
                                                                    seg
                                                                    remainder_trunc
                                                                    (Reg_op
                                                                    EDX))))))))))))))))))))))))))
                     else coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op8 seg op) (fun op_val ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic write_ps_and_fresh size8 op_val)
                                  (fun divisor ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size8 Big.zero)
                                    (fun zero0 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test size8 X86_RTL.Coq_eq_op
                                        zero0 divisor) (fun divide_by_zero ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (if_trap divide_by_zero) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_s size8 size16
                                            divisor) (fun divisor_ext ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size16
                                              X86_RTL.Coq_divs_op dividend
                                              divisor_ext) (fun quotient ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size16
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                Big.one)))))))
                                              (fun max_quotient ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size16
                                                  (Big.opp (Big.double
                                                  (Big.double (Big.double
                                                  (Big.double (Big.double
                                                  (Big.double (Big.double
                                                  Big.one)))))))))
                                                (fun min_quotient ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size16
                                                    X86_RTL.Coq_lt_op
                                                    max_quotient quotient)
                                                  (fun div_error0 ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic test size16
                                                      X86_RTL.Coq_lt_op
                                                      quotient min_quotient)
                                                    (fun div_error1 ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic arith size1
                                                        X86_RTL.Coq_or_op
                                                        div_error0
                                                        div_error1)
                                                      (fun div_error ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (if_trap div_error)
                                                        (fun _ ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic arith
                                                            size16
                                                            X86_RTL.Coq_mods_op
                                                            dividend
                                                            divisor_ext)
                                                          (fun remainder ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic cast_s
                                                              size16 size8
                                                              quotient)
                                                            (fun quotient_trunc ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                cast_s size16
                                                                size8
                                                                remainder)
                                                              (fun remainder_trunc ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (iset_op8 seg
                                                                  quotient_trunc
                                                                  (Reg_op
                                                                  EAX))
                                                                (fun _ ->
                                                                iset_op8 seg
                                                                  remainder_trunc
                                                                  (Reg_op
                                                                  ESP))))))))))))))))))))
                else if w
                     then coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op32 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size32 eax)
                              (fun dividend_lower ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op32 seg (Reg_op EDX))
                                (fun dividend_upper ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_s size32 (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ
                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    dividend_upper) (fun dividend0 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ
                                      Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      (Big.double (Big.double (Big.double
                                      (Big.double (Big.double Big.one))))))
                                    (fun thirtytwo ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ
                                        Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        X86_RTL.Coq_shl_op dividend0
                                        thirtytwo) (fun dividend1 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_s size32 (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ
                                          Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          dividend_lower)
                                        (fun dividend_lower_ext ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ
                                            Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            X86_RTL.Coq_or_op dividend1
                                            dividend_lower_ext)
                                          (fun dividend ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic iload_op32 seg op)
                                            (fun op_val ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic write_ps_and_fresh
                                                size32 op_val)
                                              (fun divisor ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size32
                                                  Big.zero) (fun zero0 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size32
                                                    X86_RTL.Coq_eq_op zero0
                                                    divisor)
                                                  (fun divide_by_zero ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (if_trap divide_by_zero)
                                                    (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic cast_s
                                                        size32 (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        (Big.succ (Big.succ
                                                        Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                        divisor)
                                                      (fun divisor_ext ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ (Big.succ
                                                          (Big.succ
                                                          Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                          X86_RTL.Coq_divs_op
                                                          dividend
                                                          divisor_ext)
                                                        (fun quotient ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic load_Z
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            (Big.succ
                                                            Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            (Big.doubleplusone
                                                            Big.one)))))))))))))))))))))))))))))))
                                                          (fun max_quotient ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic load_Z
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              (Big.succ
                                                              Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                              (Big.opp
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              (Big.double
                                                              Big.one)))))))))))))))))))))))))))))))))
                                                            (fun min_quotient ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic test
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                (Big.succ
                                                                Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                X86_RTL.Coq_lt_op
                                                                max_quotient
                                                                quotient)
                                                              (fun div_error0 ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  test
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  (Big.succ
                                                                  Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                  X86_RTL.Coq_lt_op
                                                                  quotient
                                                                  min_quotient)
                                                                (fun div_error1 ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    arith
                                                                    size1
                                                                    X86_RTL.Coq_or_op
                                                                    div_error0
                                                                    div_error1)
                                                                  (fun div_error ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_trap
                                                                    div_error)
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    arith
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    X86_RTL.Coq_mods_op
                                                                    dividend
                                                                    divisor_ext)
                                                                    (fun remainder ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_s
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    quotient)
                                                                    (fun quotient_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    cast_s
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    (Big.succ
                                                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                                    size32
                                                                    remainder)
                                                                    (fun remainder_trunc ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (iset_op32
                                                                    seg
                                                                    quotient_trunc
                                                                    (Reg_op
                                                                    EAX))
                                                                    (fun _ ->
                                                                    iset_op32
                                                                    seg
                                                                    remainder_trunc
                                                                    (Reg_op
                                                                    EDX))))))))))))))))))))))))))
                     else coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun dividend ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic iload_op8 seg op) (fun op_val ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic write_ps_and_fresh size8 op_val)
                                  (fun divisor ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size8 Big.zero)
                                    (fun zero0 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic test size8 X86_RTL.Coq_eq_op
                                        zero0 divisor) (fun divide_by_zero ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (if_trap divide_by_zero) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_s size8 size16
                                            divisor) (fun divisor_ext ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size16
                                              X86_RTL.Coq_divs_op dividend
                                              divisor_ext) (fun quotient ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size16
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                (Big.doubleplusone
                                                Big.one)))))))
                                              (fun max_quotient ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size16
                                                  (Big.opp (Big.double
                                                  (Big.double (Big.double
                                                  (Big.double (Big.double
                                                  (Big.double (Big.double
                                                  Big.one)))))))))
                                                (fun min_quotient ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size16
                                                    X86_RTL.Coq_lt_op
                                                    max_quotient quotient)
                                                  (fun div_error0 ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic test size16
                                                      X86_RTL.Coq_lt_op
                                                      quotient min_quotient)
                                                    (fun div_error1 ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic arith size1
                                                        X86_RTL.Coq_or_op
                                                        div_error0
                                                        div_error1)
                                                      (fun div_error ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (if_trap div_error)
                                                        (fun _ ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic arith
                                                            size16
                                                            X86_RTL.Coq_mods_op
                                                            dividend
                                                            divisor_ext)
                                                          (fun remainder ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic cast_s
                                                              size16 size8
                                                              quotient)
                                                            (fun quotient_trunc ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                cast_s size16
                                                                size8
                                                                remainder)
                                                              (fun remainder_trunc ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (iset_op8 seg
                                                                  quotient_trunc
                                                                  (Reg_op
                                                                  EAX))
                                                                (fun _ ->
                                                                iset_op8 seg
                                                                  remainder_trunc
                                                                  (Reg_op
                                                                  ESP))))))))))))))))))))))))))

  (** val conv_IMUL :
      prefix -> bool -> operand -> operand option -> int32 option -> unit
      coq_Conv **)

  let conv_IMUL pre w op1 opopt2 iopt =
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
            (fun _ ->
            match opopt2 with
            | Some op2 ->
              (match iopt with
               | Some imm3 ->
                 let load = load_op pre w in
                 let set0 = set_op pre w in
                 let seg =
                   match pre.seg_override with
                   | Some s -> s
                   | None ->
                     let b = op_contains_stack op1 in
                     let b0 = op_contains_stack op2 in
                     if b then SS else if b0 then SS else DS
                 in
                 coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
                   (fun p1 ->
                   coq_Bind (Obj.magic coq_Conv_monad)
                     (Obj.magic load_int size32 imm3) (fun p2' ->
                     coq_Bind (Obj.magic coq_Conv_monad)
                       (Obj.magic cast_u size32 (opsize pre.op_override w)
                         p2') (fun p2 ->
                       coq_Bind (Obj.magic coq_Conv_monad)
                         (Obj.magic cast_s (opsize pre.op_override w)
                           (sub
                             (mul (Big.succ (Big.succ Big.zero))
                               (add (opsize pre.op_override w) (Big.succ
                                 Big.zero))) (Big.succ Big.zero)) p1)
                         (fun p1ext ->
                         coq_Bind (Obj.magic coq_Conv_monad)
                           (Obj.magic cast_s (opsize pre.op_override w)
                             (sub
                               (mul (Big.succ (Big.succ Big.zero))
                                 (add (opsize pre.op_override w) (Big.succ
                                   Big.zero))) (Big.succ Big.zero)) p2)
                           (fun p2ext ->
                           coq_Bind (Obj.magic coq_Conv_monad)
                             (Obj.magic arith
                               (sub
                                 (mul (Big.succ (Big.succ Big.zero))
                                   (add (opsize pre.op_override w) (Big.succ
                                     Big.zero))) (Big.succ Big.zero))
                               X86_RTL.Coq_mul_op p1ext p2ext) (fun res ->
                             coq_Bind (Obj.magic coq_Conv_monad)
                               (Obj.magic cast_s
                                 (sub
                                   (mul (Big.succ (Big.succ Big.zero))
                                     (add (opsize pre.op_override w)
                                       (Big.succ Big.zero))) (Big.succ
                                   Big.zero)) (opsize pre.op_override w) res)
                               (fun lowerhalf ->
                               coq_Bind (Obj.magic coq_Conv_monad)
                                 (Obj.magic cast_s (opsize pre.op_override w)
                                   (sub
                                     (mul (Big.succ (Big.succ Big.zero))
                                       (add (opsize pre.op_override w)
                                         (Big.succ Big.zero))) (Big.succ
                                     Big.zero)) lowerhalf) (fun reextend ->
                                 coq_Bind (Obj.magic coq_Conv_monad)
                                   (Obj.magic test
                                     (sub
                                       (mul (Big.succ (Big.succ Big.zero))
                                         (add (opsize pre.op_override w)
                                           (Big.succ Big.zero))) (Big.succ
                                       Big.zero)) X86_RTL.Coq_eq_op reextend
                                     res) (fun b0 ->
                                   coq_Bind (Obj.magic coq_Conv_monad)
                                     (Obj.magic not size1 b0) (fun flag0 ->
                                     coq_Bind (Obj.magic coq_Conv_monad)
                                       (set_flag X86_MACHINE.CF flag0)
                                       (fun _ ->
                                       coq_Bind (Obj.magic coq_Conv_monad)
                                         (set_flag X86_MACHINE.OF flag0)
                                         (fun _ -> set0 seg lowerhalf op1))))))))))))
               | None ->
                 let load = load_op pre w in
                 let set0 = set_op pre w in
                 let seg =
                   match pre.seg_override with
                   | Some s -> s
                   | None ->
                     let b = op_contains_stack op1 in
                     let b0 = op_contains_stack op2 in
                     if b then SS else if b0 then SS else DS
                 in
                 coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
                   (fun p1 ->
                   coq_Bind (Obj.magic coq_Conv_monad)
                     (Obj.magic load seg op2) (fun p2 ->
                     coq_Bind (Obj.magic coq_Conv_monad)
                       (Obj.magic cast_s (opsize pre.op_override w)
                         (sub
                           (mul (Big.succ (Big.succ Big.zero))
                             (add (opsize pre.op_override w) (Big.succ
                               Big.zero))) (Big.succ Big.zero)) p1)
                       (fun p1ext ->
                       coq_Bind (Obj.magic coq_Conv_monad)
                         (Obj.magic cast_s (opsize pre.op_override w)
                           (sub
                             (mul (Big.succ (Big.succ Big.zero))
                               (add (opsize pre.op_override w) (Big.succ
                                 Big.zero))) (Big.succ Big.zero)) p2)
                         (fun p2ext ->
                         coq_Bind (Obj.magic coq_Conv_monad)
                           (Obj.magic arith
                             (sub
                               (mul (Big.succ (Big.succ Big.zero))
                                 (add (opsize pre.op_override w) (Big.succ
                                   Big.zero))) (Big.succ Big.zero))
                             X86_RTL.Coq_mul_op p1ext p2ext) (fun res ->
                           coq_Bind (Obj.magic coq_Conv_monad)
                             (Obj.magic cast_s
                               (sub
                                 (mul (Big.succ (Big.succ Big.zero))
                                   (add (opsize pre.op_override w) (Big.succ
                                     Big.zero))) (Big.succ Big.zero))
                               (opsize pre.op_override w) res)
                             (fun lowerhalf ->
                             coq_Bind (Obj.magic coq_Conv_monad)
                               (Obj.magic cast_s (opsize pre.op_override w)
                                 (sub
                                   (mul (Big.succ (Big.succ Big.zero))
                                     (add (opsize pre.op_override w)
                                       (Big.succ Big.zero))) (Big.succ
                                   Big.zero)) lowerhalf) (fun reextend ->
                               coq_Bind (Obj.magic coq_Conv_monad)
                                 (Obj.magic test
                                   (sub
                                     (mul (Big.succ (Big.succ Big.zero))
                                       (add (opsize pre.op_override w)
                                         (Big.succ Big.zero))) (Big.succ
                                     Big.zero)) X86_RTL.Coq_eq_op reextend
                                   res) (fun b0 ->
                                 coq_Bind (Obj.magic coq_Conv_monad)
                                   (Obj.magic not size1 b0) (fun flag0 ->
                                   coq_Bind (Obj.magic coq_Conv_monad)
                                     (set_flag X86_MACHINE.CF flag0)
                                     (fun _ ->
                                     coq_Bind (Obj.magic coq_Conv_monad)
                                       (set_flag X86_MACHINE.OF flag0)
                                       (fun _ -> set0 seg lowerhalf op1))))))))))))
            | None ->
              let load = load_op pre w in
              let seg =
                match pre.seg_override with
                | Some s -> s
                | None -> if op_contains_stack op1 then SS else DS
              in
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic load seg (Reg_op EAX)) (fun eax ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic write_ps_and_fresh (opsize pre.op_override w)
                    eax) (fun p1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load seg op1) (fun op1_val ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic write_ps_and_fresh
                        (opsize pre.op_override w) op1_val) (fun p2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic cast_s (opsize pre.op_override w)
                          (sub
                            (mul (Big.succ (Big.succ Big.zero))
                              (add (opsize pre.op_override w) (Big.succ
                                Big.zero))) (Big.succ Big.zero)) p1)
                        (fun p1ext ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic cast_s (opsize pre.op_override w)
                            (sub
                              (mul (Big.succ (Big.succ Big.zero))
                                (add (opsize pre.op_override w) (Big.succ
                                  Big.zero))) (Big.succ Big.zero)) p2)
                          (fun p2ext ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith
                              (sub
                                (mul (Big.succ (Big.succ Big.zero))
                                  (add (opsize pre.op_override w) (Big.succ
                                    Big.zero))) (Big.succ Big.zero))
                              X86_RTL.Coq_mul_op p1ext p2ext) (fun res ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_s
                                (sub
                                  (mul (Big.succ (Big.succ Big.zero))
                                    (add (opsize pre.op_override w) (Big.succ
                                      Big.zero))) (Big.succ Big.zero))
                                (opsize pre.op_override w) res)
                              (fun lowerhalf ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic load_Z
                                  (sub
                                    (mul (Big.succ (Big.succ Big.zero))
                                      (add (opsize pre.op_override w)
                                        (Big.succ Big.zero))) (Big.succ
                                    Big.zero))
                                  (Z.of_nat
                                    (add (opsize pre.op_override w) (Big.succ
                                      Big.zero)))) (fun shift ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith
                                    (sub
                                      (mul (Big.succ (Big.succ Big.zero))
                                        (add (opsize pre.op_override w)
                                          (Big.succ Big.zero))) (Big.succ
                                      Big.zero)) X86_RTL.Coq_shr_op res
                                    shift) (fun res_shifted ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic cast_s
                                      (sub
                                        (mul (Big.succ (Big.succ Big.zero))
                                          (add (opsize pre.op_override w)
                                            (Big.succ Big.zero))) (Big.succ
                                        Big.zero)) (opsize pre.op_override w)
                                      res_shifted) (fun upperhalf ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic load_Z
                                        (opsize pre.op_override w) Big.zero)
                                      (fun zero0 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic load_Z
                                          (opsize pre.op_override w)
                                          (Word.max_unsigned
                                            (opsize pre.op_override w)))
                                        (fun max ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic test
                                            (opsize pre.op_override w)
                                            X86_RTL.Coq_eq_op upperhalf
                                            zero0) (fun b0 ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic test
                                              (opsize pre.op_override w)
                                              X86_RTL.Coq_eq_op upperhalf
                                              max) (fun b1 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic test
                                                (opsize pre.op_override w)
                                                X86_RTL.Coq_lt_op lowerhalf
                                                zero0) (fun b2 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic arith size1
                                                  X86_RTL.Coq_or_op b0 b1)
                                                (fun b3 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic not size1 b3)
                                                  (fun b4 ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic arith size1
                                                      X86_RTL.Coq_and_op b0
                                                      b2) (fun b5 ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic not size1
                                                        b2) (fun b6 ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          size1
                                                          X86_RTL.Coq_and_op
                                                          b1 b6) (fun b7 ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic arith
                                                            size1
                                                            X86_RTL.Coq_or_op
                                                            b4 b5) (fun b8 ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic arith
                                                              size1
                                                              X86_RTL.Coq_or_op
                                                              b7 b8)
                                                            (fun flag0 ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (set_flag
                                                                X86_MACHINE.CF
                                                                flag0)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (set_flag
                                                                  X86_MACHINE.OF
                                                                  flag0)
                                                                (fun _ ->
                                                                if w
                                                                then 
                                                                  let set0 =
                                                                    set_op
                                                                    pre w
                                                                  in
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (set0 seg
                                                                    lowerhalf
                                                                    (Reg_op
                                                                    EAX))
                                                                    (fun _ ->
                                                                    set0 seg
                                                                    upperhalf
                                                                    (Reg_op
                                                                    EDX))
                                                                else 
                                                                  iset_op16
                                                                    seg res
                                                                    (Reg_op
                                                                    EAX))))))))))))))))))))))))))))))

  (** val conv_MUL : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_MUL pre w op =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
            (fun _ ->
            if pre.op_override
            then if w
                 then coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic iload_op16 seg op) (fun op_val ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic write_ps_and_fresh size16 op_val)
                          (fun p1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op16 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size16 eax)
                              (fun p2 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic cast_u size16 size32 p1)
                                (fun p1ext ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u size16 size32 p2)
                                  (fun p2ext ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size32
                                      X86_RTL.Coq_mul_op p1ext p2ext)
                                    (fun res ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic cast_u size32 size16 res)
                                      (fun res_lower ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic load_Z size32 (Big.double
                                          (Big.double (Big.double (Big.double
                                          Big.one))))) (fun sixteen ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith size32
                                            X86_RTL.Coq_shru_op res sixteen)
                                          (fun res_shifted ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic cast_u size32 size16
                                              res_shifted) (fun res_upper ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size16
                                                Big.zero) (fun zero0 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size16
                                                  X86_RTL.Coq_ltu_op zero0
                                                  res_upper) (fun cf_test ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (set_flag X86_MACHINE.CF
                                                    cf_test) (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (set_flag X86_MACHINE.OF
                                                      cf_test) (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (iset_op16 seg
                                                        res_lower (Reg_op
                                                        EAX)) (fun _ ->
                                                      iset_op16 seg res_upper
                                                        (Reg_op EDX)))))))))))))))))
                 else coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic iload_op8 seg op) (fun p1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic iload_op8 seg (Reg_op EAX)) (fun p2 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic cast_u size8 size16 p1) (fun p1ext ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_u size8 size16 p2)
                              (fun p2ext ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size16 X86_RTL.Coq_mul_op
                                  p1ext p2ext) (fun res ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic load_Z size16 (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    Big.one)))))))) (fun max ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic test size16 X86_RTL.Coq_ltu_op
                                      max res) (fun cf_test ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (set_flag X86_MACHINE.CF cf_test)
                                      (fun _ ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (set_flag X86_MACHINE.OF cf_test)
                                        (fun _ ->
                                        iset_op16 seg res (Reg_op EAX))))))))))
            else if w
                 then coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic iload_op32 seg op) (fun op_val ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic write_ps_and_fresh size32 op_val)
                          (fun p1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic iload_op32 seg (Reg_op EAX))
                            (fun eax ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic write_ps_and_fresh size32 eax)
                              (fun p2 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic cast_u size32 (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ (Big.succ (Big.succ (Big.succ
                                  (Big.succ
                                  Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                  p1) (fun p1ext ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u size32 (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ (Big.succ (Big.succ
                                    (Big.succ (Big.succ
                                    Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                    p2) (fun p2ext ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ (Big.succ (Big.succ (Big.succ
                                      (Big.succ
                                      Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      X86_RTL.Coq_mul_op p1ext p2ext)
                                    (fun res ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic cast_u (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ (Big.succ (Big.succ
                                        (Big.succ
                                        Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        size32 res) (fun res_lower ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic load_Z (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ (Big.succ (Big.succ
                                          (Big.succ
                                          Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          (Big.double (Big.double (Big.double
                                          (Big.double (Big.double
                                          Big.one)))))) (fun thirtytwo ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ (Big.succ
                                            (Big.succ (Big.succ
                                            Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                            X86_RTL.Coq_shru_op res
                                            thirtytwo) (fun res_shifted ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic cast_u (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ (Big.succ
                                              (Big.succ (Big.succ
                                              Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              size32 res_shifted)
                                            (fun res_upper ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size32
                                                Big.zero) (fun zero0 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size32
                                                  X86_RTL.Coq_ltu_op zero0
                                                  res_upper) (fun cf_test ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (set_flag X86_MACHINE.CF
                                                    cf_test) (fun _ ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (set_flag X86_MACHINE.OF
                                                      cf_test) (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (iset_op32 seg
                                                        res_lower (Reg_op
                                                        EAX)) (fun _ ->
                                                      iset_op32 seg res_upper
                                                        (Reg_op EDX)))))))))))))))))
                 else coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic iload_op8 seg op) (fun p1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic iload_op8 seg (Reg_op EAX)) (fun p2 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic cast_u size8 size16 p1) (fun p1ext ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_u size8 size16 p2)
                              (fun p2ext ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size16 X86_RTL.Coq_mul_op
                                  p1ext p2ext) (fun res ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic load_Z size16 (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    (Big.doubleplusone (Big.doubleplusone
                                    Big.one)))))))) (fun max ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic test size16 X86_RTL.Coq_ltu_op
                                      max res) (fun cf_test ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (set_flag X86_MACHINE.CF cf_test)
                                      (fun _ ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (set_flag X86_MACHINE.OF cf_test)
                                        (fun _ ->
                                        iset_op16 seg res (Reg_op EAX))))))))))))))

  (** val conv_shift :
      X86_RTL.bit_vector_op -> prefix -> bool -> operand -> reg_or_immed ->
      unit coq_Conv **)

  let conv_shift shift pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.CF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
                (fun _ ->
                coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
                  (fun p1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (match op2 with
                     | Reg_ri r -> Obj.magic iload_op8 seg (Reg_op r)
                     | Imm_ri i -> Obj.magic load_int size8 i) (fun p2 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic load_Z size8 (Big.doubleplusone
                        (Big.doubleplusone (Big.doubleplusone
                        (Big.doubleplusone Big.one))))) (fun mask ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size8 X86_RTL.Coq_and_op p2 mask)
                        (fun p3 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic cast_u size8 (opsize pre.op_override w)
                            p3) (fun p2cast ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith (opsize pre.op_override w) shift
                              p1 p2cast) (fun p4 -> set0 seg p4 op1))))))))))))

  (** val conv_SHL :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_SHL pre w op1 op2 =
    conv_shift X86_RTL.Coq_shl_op pre w op1 op2

  (** val conv_SAR :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_SAR pre w op1 op2 =
    conv_shift X86_RTL.Coq_shr_op pre w op1 op2

  (** val conv_SHR :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_SHR pre w op1 op2 =
    conv_shift X86_RTL.Coq_shru_op pre w op1 op2

  (** val conv_ROR :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_ROR pre w op1 op2 =
    conv_shift X86_RTL.Coq_ror_op pre w op1 op2

  (** val conv_ROL :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_ROL pre w op1 op2 =
    conv_shift X86_RTL.Coq_rol_op pre w op1 op2

  (** val conv_RCL :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_RCL pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1) (fun p1 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (match op2 with
         | Reg_ri r -> Obj.magic iload_op8 seg (Reg_op r)
         | Imm_ri i -> Obj.magic load_int size8 i) (fun p2 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
            (Big.doubleplusone (Big.doubleplusone Big.one))))) (fun mask ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size8 X86_RTL.Coq_and_op p2 mask) (fun p3 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Big.nat_case
                 (fun _ ->
                 no_op)
                 (fun n ->
                 Big.nat_case
                   (fun _ ->
                   no_op)
                   (fun n0 ->
                   Big.nat_case
                     (fun _ ->
                     no_op)
                     (fun n1 ->
                     Big.nat_case
                       (fun _ ->
                       no_op)
                       (fun n2 ->
                       Big.nat_case
                         (fun _ ->
                         no_op)
                         (fun n3 ->
                         Big.nat_case
                           (fun _ ->
                           no_op)
                           (fun n4 ->
                           Big.nat_case
                             (fun _ ->
                             no_op)
                             (fun n5 ->
                             Big.nat_case
                               (fun _ ->
                               coq_Bind (Obj.magic coq_Conv_monad)
                                 (Obj.magic load_Z size8 (Big.doubleplusone
                                   (Big.double (Big.double Big.one))))
                                 (fun modmask ->
                                 coq_Bind (Obj.magic coq_Conv_monad)
                                   (Obj.magic arith size8 X86_RTL.Coq_modu_op
                                     p3 modmask) (fun _ -> no_op)))
                               (fun n6 ->
                               Big.nat_case
                                 (fun _ ->
                                 no_op)
                                 (fun n7 ->
                                 Big.nat_case
                                   (fun _ ->
                                   no_op)
                                   (fun n8 ->
                                   Big.nat_case
                                     (fun _ ->
                                     no_op)
                                     (fun n9 ->
                                     Big.nat_case
                                       (fun _ ->
                                       no_op)
                                       (fun n10 ->
                                       Big.nat_case
                                         (fun _ ->
                                         no_op)
                                         (fun n11 ->
                                         Big.nat_case
                                           (fun _ ->
                                           no_op)
                                           (fun n12 ->
                                           Big.nat_case
                                             (fun _ ->
                                             no_op)
                                             (fun n13 ->
                                             Big.nat_case
                                               (fun _ ->
                                               coq_Bind
                                                 (Obj.magic coq_Conv_monad)
                                                 (Obj.magic load_Z size8
                                                   (Big.doubleplusone
                                                   (Big.double (Big.double
                                                   (Big.double Big.one)))))
                                                 (fun modmask ->
                                                 coq_Bind
                                                   (Obj.magic coq_Conv_monad)
                                                   (Obj.magic arith size8
                                                     X86_RTL.Coq_modu_op p3
                                                     modmask) (fun _ ->
                                                   no_op)))
                                               (fun _ ->
                                               no_op)
                                               n13)
                                             n12)
                                           n11)
                                         n10)
                                       n9)
                                     n8)
                                   n7)
                                 n6)
                               n5)
                             n4)
                           n3)
                         n2)
                       n1)
                     n0)
                   n)
                 (opsize pre.op_override w)) (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic cast_u size8
                  (add (opsize pre.op_override w) (Big.succ Big.zero)) p3)
                (fun p2cast ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic cast_u (opsize pre.op_override w)
                    (add (opsize pre.op_override w) (Big.succ Big.zero)) p1)
                  (fun tmp ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic get_flag X86_MACHINE.CF) (fun cf0 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic write_ps_and_fresh size1 cf0) (fun cf ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic cast_u size1
                          (add (opsize pre.op_override w) (Big.succ
                            Big.zero)) cf) (fun cf1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic load_Z
                            (add (opsize pre.op_override w) (Big.succ
                              Big.zero))
                            (Z.of_nat
                              (add (opsize pre.op_override w) (Big.succ
                                Big.zero)))) (fun tt ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith
                              (add (opsize pre.op_override w) (Big.succ
                                Big.zero)) X86_RTL.Coq_shl_op cf1 tt)
                            (fun cf2 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith
                                (add (opsize pre.op_override w) (Big.succ
                                  Big.zero)) X86_RTL.Coq_or_op tmp cf2)
                              (fun tmp0 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith
                                  (add (opsize pre.op_override w) (Big.succ
                                    Big.zero)) X86_RTL.Coq_rol_op tmp0
                                  p2cast) (fun tmp1 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u
                                    (add (opsize pre.op_override w) (Big.succ
                                      Big.zero)) (opsize pre.op_override w)
                                    tmp1) (fun p4 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith
                                      (add (opsize pre.op_override w)
                                        (Big.succ Big.zero))
                                      X86_RTL.Coq_shr_op tmp1 tt) (fun cf3 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic cast_u
                                        (add (opsize pre.op_override w)
                                          (Big.succ Big.zero)) size1 cf3)
                                      (fun cf4 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (undef_flag X86_MACHINE.OF) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (set_flag X86_MACHINE.CF cf4)
                                          (fun _ -> set0 seg p4 op1)))))))))))))))))))

  (** val conv_RCR :
      prefix -> bool -> operand -> reg_or_immed -> unit coq_Conv **)

  let conv_RCR pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1) (fun p1 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (match op2 with
         | Reg_ri r -> Obj.magic iload_op8 seg (Reg_op r)
         | Imm_ri i -> Obj.magic load_int size8 i) (fun p2 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
            (Big.doubleplusone (Big.doubleplusone Big.one))))) (fun mask ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size8 X86_RTL.Coq_and_op p2 mask) (fun p3 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Big.nat_case
                 (fun _ ->
                 no_op)
                 (fun n ->
                 Big.nat_case
                   (fun _ ->
                   no_op)
                   (fun n0 ->
                   Big.nat_case
                     (fun _ ->
                     no_op)
                     (fun n1 ->
                     Big.nat_case
                       (fun _ ->
                       no_op)
                       (fun n2 ->
                       Big.nat_case
                         (fun _ ->
                         no_op)
                         (fun n3 ->
                         Big.nat_case
                           (fun _ ->
                           no_op)
                           (fun n4 ->
                           Big.nat_case
                             (fun _ ->
                             no_op)
                             (fun n5 ->
                             Big.nat_case
                               (fun _ ->
                               coq_Bind (Obj.magic coq_Conv_monad)
                                 (Obj.magic load_Z size8 (Big.doubleplusone
                                   (Big.double (Big.double Big.one))))
                                 (fun modmask ->
                                 coq_Bind (Obj.magic coq_Conv_monad)
                                   (Obj.magic arith size8 X86_RTL.Coq_modu_op
                                     p3 modmask) (fun _ -> no_op)))
                               (fun n6 ->
                               Big.nat_case
                                 (fun _ ->
                                 no_op)
                                 (fun n7 ->
                                 Big.nat_case
                                   (fun _ ->
                                   no_op)
                                   (fun n8 ->
                                   Big.nat_case
                                     (fun _ ->
                                     no_op)
                                     (fun n9 ->
                                     Big.nat_case
                                       (fun _ ->
                                       no_op)
                                       (fun n10 ->
                                       Big.nat_case
                                         (fun _ ->
                                         no_op)
                                         (fun n11 ->
                                         Big.nat_case
                                           (fun _ ->
                                           no_op)
                                           (fun n12 ->
                                           Big.nat_case
                                             (fun _ ->
                                             no_op)
                                             (fun n13 ->
                                             Big.nat_case
                                               (fun _ ->
                                               coq_Bind
                                                 (Obj.magic coq_Conv_monad)
                                                 (Obj.magic load_Z size8
                                                   (Big.doubleplusone
                                                   (Big.double (Big.double
                                                   (Big.double Big.one)))))
                                                 (fun modmask ->
                                                 coq_Bind
                                                   (Obj.magic coq_Conv_monad)
                                                   (Obj.magic arith size8
                                                     X86_RTL.Coq_modu_op p3
                                                     modmask) (fun _ ->
                                                   no_op)))
                                               (fun _ ->
                                               no_op)
                                               n13)
                                             n12)
                                           n11)
                                         n10)
                                       n9)
                                     n8)
                                   n7)
                                 n6)
                               n5)
                             n4)
                           n3)
                         n2)
                       n1)
                     n0)
                   n)
                 (opsize pre.op_override w)) (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic cast_u size8
                  (add (opsize pre.op_override w) (Big.succ Big.zero)) p3)
                (fun p2cast ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic load_Z
                    (add (opsize pre.op_override w) (Big.succ Big.zero))
                    Big.one) (fun oneshift ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic cast_u (opsize pre.op_override w)
                      (add (opsize pre.op_override w) (Big.succ Big.zero))
                      p1) (fun tmp ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith
                        (add (opsize pre.op_override w) (Big.succ Big.zero))
                        X86_RTL.Coq_shl_op tmp oneshift) (fun tmp0 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic get_flag X86_MACHINE.CF) (fun cf0 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic write_ps_and_fresh size1 cf0) (fun cf ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic cast_u size1
                              (add (opsize pre.op_override w) (Big.succ
                                Big.zero)) cf) (fun cf1 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith
                                (add (opsize pre.op_override w) (Big.succ
                                  Big.zero)) X86_RTL.Coq_or_op tmp0 cf1)
                              (fun tmp1 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith
                                  (add (opsize pre.op_override w) (Big.succ
                                    Big.zero)) X86_RTL.Coq_ror_op tmp1
                                  p2cast) (fun tmp2 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u
                                    (add (opsize pre.op_override w) (Big.succ
                                      Big.zero)) size1 tmp2) (fun cf2 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith
                                      (add (opsize pre.op_override w)
                                        (Big.succ Big.zero))
                                      X86_RTL.Coq_shr_op tmp2 oneshift)
                                    (fun p4 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic cast_u
                                        (add (opsize pre.op_override w)
                                          (Big.succ Big.zero))
                                        (opsize pre.op_override w) p4)
                                      (fun p5 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (undef_flag X86_MACHINE.OF) (fun _ ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (set_flag X86_MACHINE.CF cf2)
                                          (fun _ -> set0 seg p5 op1)))))))))))))))))))

  (** val size65 : Big.big_int **)

  let size65 =
    Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ
      Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val conv_SHLD :
      prefix -> operand -> register -> reg_or_immed -> unit coq_Conv **)

  let conv_SHLD pre op1 r ri =
    let load = load_op pre true in
    let set0 = set_op pre true in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (match ri with
       | Reg_ri r0 -> Obj.magic iload_op8 seg (Reg_op r0)
       | Imm_ri i -> Obj.magic load_int size8 i) (fun count ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z size8 (Big.double (Big.double (Big.double
          (Big.double (Big.double Big.one)))))) (fun thirtytwo ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith size8 X86_RTL.Coq_modu_op count thirtytwo)
          (fun count0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (if pre.op_override
             then Obj.magic load_Z size8 (Big.double (Big.double (Big.double
                    (Big.double Big.one))))
             else Obj.magic load_Z size8 (Big.double (Big.double (Big.double
                    (Big.double (Big.double Big.one)))))) (fun opsize0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size8 Big.zero) (fun zero0 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test_neq size8 count0 zero0)
                (fun count_not_zero ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test size8 X86_RTL.Coq_ltu_op opsize0 count0)
                  (fun count_gt_opsize ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load seg op1) (fun p1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic load seg (Reg_op r)) (fun p2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic cast_u size8 size65 opsize0)
                        (fun shiftup ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic cast_u (opsize pre.op_override true)
                            size65 p1) (fun wide_p1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith size65 X86_RTL.Coq_shl_op
                              wide_p1 shiftup) (fun wide_p2 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_u (opsize pre.op_override true)
                                size65 p2) (fun wide_p3 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size65 X86_RTL.Coq_or_op
                                  wide_p2 wide_p3) (fun combined ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic cast_u size8 size65 count0)
                                  (fun wide_count ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size65
                                      X86_RTL.Coq_shl_op combined wide_count)
                                    (fun shifted ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size65
                                        X86_RTL.Coq_shru_op shifted shiftup)
                                      (fun shifted0 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_u size65
                                          (opsize pre.op_override true)
                                          shifted0) (fun res ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith size65
                                            X86_RTL.Coq_shru_op shifted0
                                            shiftup) (fun shifted_out ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic cast_u size65 size1
                                              shifted_out) (fun cf ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic load_Z size8
                                                Big.one) (fun one0 ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic test size8
                                                  X86_RTL.Coq_eq_op count0
                                                  one0) (fun count_is_one ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic load_Z
                                                    (opsize pre.op_override
                                                      true) Big.zero)
                                                  (fun pzero ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic test
                                                      (opsize pre.op_override
                                                        true)
                                                      X86_RTL.Coq_lt_op p1
                                                      pzero) (fun b0 ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic test
                                                        (opsize
                                                          pre.op_override
                                                          true)
                                                        X86_RTL.Coq_lt_op res
                                                        pzero) (fun b1 ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic arith
                                                          size1
                                                          X86_RTL.Coq_xor_op
                                                          b0 b1) (fun of0 ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic test
                                                            (opsize
                                                              pre.op_override
                                                              true)
                                                            X86_RTL.Coq_eq_op
                                                            res pzero)
                                                          (fun zf ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic
                                                              compute_parity
                                                              (opsize
                                                                pre.op_override
                                                                true) res)
                                                            (fun pf ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                choose size1)
                                                              (fun undef_cf ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  if_exp
                                                                  size1
                                                                  count_gt_opsize
                                                                  undef_cf
                                                                  cf)
                                                                (fun new_cf ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_cf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.CF))
                                                                  (fun _ ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_of ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_is_one
                                                                    of0
                                                                    undef_of)
                                                                    (fun new_of ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_of
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.OF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_sf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_sf
                                                                    b1)
                                                                    (fun new_sf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_sf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.SF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_zf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_zf
                                                                    zf)
                                                                    (fun new_zf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_zf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.ZF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_pf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_pf
                                                                    pf)
                                                                    (fun new_pf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_pf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.PF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_af ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    undef_af
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.AF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    (opsize
                                                                    pre.op_override
                                                                    true))
                                                                    (fun undef_res ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    (opsize
                                                                    pre.op_override
                                                                    true)
                                                                    count_gt_opsize
                                                                    undef_res
                                                                    res)
                                                                    (fun newres ->
                                                                    set0 seg
                                                                    newres
                                                                    op1)))))))))))))))))))))))))))))))))))))))))))))))

  (** val conv_SHRD :
      prefix -> operand -> register -> reg_or_immed -> unit coq_Conv **)

  let conv_SHRD pre op1 r ri =
    let load = load_op pre true in
    let set0 = set_op pre true in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (match ri with
       | Reg_ri r0 -> Obj.magic iload_op8 seg (Reg_op r0)
       | Imm_ri i -> Obj.magic load_int size8 i) (fun count ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z size8 (Big.double (Big.double (Big.double
          (Big.double (Big.double Big.one)))))) (fun thirtytwo ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith size8 X86_RTL.Coq_modu_op count thirtytwo)
          (fun count0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (if pre.op_override
             then Obj.magic load_Z size8 (Big.double (Big.double (Big.double
                    (Big.double Big.one))))
             else Obj.magic load_Z size8 (Big.double (Big.double (Big.double
                    (Big.double (Big.double Big.one)))))) (fun opsize0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size8 Big.zero) (fun zero0 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test_neq size8 count0 zero0)
                (fun count_not_zero ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic test size8 X86_RTL.Coq_ltu_op opsize0 count0)
                  (fun count_gt_opsize ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load seg op1) (fun p1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic load seg (Reg_op r)) (fun p2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic cast_u (opsize pre.op_override true)
                          size65 p1) (fun wide_p1 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic cast_u size8 size65 opsize0)
                          (fun shiftup ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic cast_u (opsize pre.op_override true)
                              size65 p2) (fun wide_p2 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith size65 X86_RTL.Coq_shl_op
                                wide_p2 shiftup) (fun wide_p3 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size65 X86_RTL.Coq_or_op
                                  wide_p1 wide_p3) (fun combined ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic load_Z size65 Big.one)
                                  (fun one0 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size65
                                      X86_RTL.Coq_shl_op combined one0)
                                    (fun combined' ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic cast_u size8 size65 count0)
                                      (fun wide_count ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic arith size65
                                          X86_RTL.Coq_shru_op combined'
                                          wide_count) (fun shifted ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic cast_u size65 size1
                                            shifted) (fun cf ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size65
                                              X86_RTL.Coq_shru_op shifted
                                              one0) (fun res' ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic cast_u size65
                                                (opsize pre.op_override true)
                                                res') (fun res ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic load_Z size8
                                                  Big.one) (fun one_8 ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic test size8
                                                    X86_RTL.Coq_eq_op count0
                                                    one_8)
                                                  (fun count_isone ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic load_Z
                                                      (opsize pre.op_override
                                                        true) Big.zero)
                                                    (fun pzero ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic test
                                                        (opsize
                                                          pre.op_override
                                                          true)
                                                        X86_RTL.Coq_lt_op p1
                                                        pzero) (fun b0 ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic test
                                                          (opsize
                                                            pre.op_override
                                                            true)
                                                          X86_RTL.Coq_lt_op
                                                          res pzero)
                                                        (fun b1 ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (Obj.magic arith
                                                            size1
                                                            X86_RTL.Coq_xor_op
                                                            b0 b1)
                                                          (fun of0 ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (Obj.magic test
                                                              (opsize
                                                                pre.op_override
                                                                true)
                                                              X86_RTL.Coq_eq_op
                                                              res pzero)
                                                            (fun zf ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (Obj.magic
                                                                compute_parity
                                                                (opsize
                                                                  pre.op_override
                                                                  true) res)
                                                              (fun pf ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (Obj.magic
                                                                  choose
                                                                  size1)
                                                                (fun undef_cf ->
                                                                coq_Bind
                                                                  (Obj.magic
                                                                    coq_Conv_monad)
                                                                  (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_cf
                                                                    cf)
                                                                  (fun new_cf ->
                                                                  coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_cf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.CF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_of ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_isone
                                                                    of0
                                                                    undef_of)
                                                                    (fun new_of ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_of
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.OF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_sf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_sf
                                                                    b1)
                                                                    (fun new_sf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_sf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.SF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_zf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_zf
                                                                    zf)
                                                                    (fun new_zf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_zf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.ZF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_pf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    size1
                                                                    count_gt_opsize
                                                                    undef_pf
                                                                    pf)
                                                                    (fun new_pf ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    new_pf
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.PF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    size1)
                                                                    (fun undef_af ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (if_set_loc
                                                                    count_not_zero
                                                                    size1
                                                                    undef_af
                                                                    (X86_MACHINE.Coq_flag_loc
                                                                    X86_MACHINE.AF))
                                                                    (fun _ ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    choose
                                                                    (opsize
                                                                    pre.op_override
                                                                    true))
                                                                    (fun undef_res ->
                                                                    coq_Bind
                                                                    (Obj.magic
                                                                    coq_Conv_monad)
                                                                    (Obj.magic
                                                                    if_exp
                                                                    (opsize
                                                                    pre.op_override
                                                                    true)
                                                                    count_gt_opsize
                                                                    undef_res
                                                                    res)
                                                                    (fun newres ->
                                                                    set0 seg
                                                                    newres
                                                                    op1))))))))))))))))))))))))))))))))))))))))))))))))

  (** val get_AH : X86_RTL.rtl_exp coq_Conv **)

  let get_AH =
    iload_op8 DS (Reg_op ESP)

  (** val set_AH : X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_AH v =
    iset_op8 DS v (Reg_op ESP)

  (** val get_AL : X86_RTL.rtl_exp coq_Conv **)

  let get_AL =
    iload_op8 DS (Reg_op EAX)

  (** val set_AL : X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_AL v =
    iset_op8 DS v (Reg_op EAX)

  (** val conv_AAA_AAS : X86_RTL.bit_vector_op -> unit coq_Conv **)

  let conv_AAA_AAS op1 =
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z size8 (Big.doubleplusone (Big.double (Big.double
        Big.one)))) (fun pnine ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
          (Big.doubleplusone Big.one)))) (fun p0Fmask ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic get_flag X86_MACHINE.AF) (fun af_val ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic write_ps_and_fresh size1 af_val) (fun paf ->
            coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_AL) (fun al ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic write_ps_and_fresh size8 al) (fun pal ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size8 X86_RTL.Coq_and_op pal p0Fmask)
                  (fun digit1 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic test size8 X86_RTL.Coq_lt_op pnine digit1)
                    (fun cond1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith size1 X86_RTL.Coq_or_op cond1 paf)
                      (fun cond ->
                      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_AH)
                        (fun ah ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic write_ps_and_fresh size8 ah) (fun pah ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic load_Z size1 Big.zero) (fun pfalse ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith size8 X86_RTL.Coq_and_op pal
                                p0Fmask) (fun v_al0 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic load_Z size8 (Big.double
                                  (Big.doubleplusone Big.one))) (fun psix ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic load_Z size8 Big.one)
                                  (fun pone ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic load_Z size1 Big.one)
                                    (fun ptrue ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size8 op1 pal psix)
                                      (fun pal_c ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic arith size8
                                          X86_RTL.Coq_and_op pal_c p0Fmask)
                                        (fun pal_cmask ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic if_exp size8 cond
                                            pal_cmask v_al0) (fun v_al ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic arith size8 op1 pah
                                              pone) (fun pah_c ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic if_exp size8 cond
                                                pah_c pah) (fun v_ah ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic if_exp size1 cond
                                                  ptrue pfalse) (fun v_af ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic if_exp size1
                                                    cond ptrue pfalse)
                                                  (fun v_cf ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (set_flag X86_MACHINE.AF
                                                      v_af) (fun _ ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (set_flag
                                                        X86_MACHINE.CF v_cf)
                                                      (fun _ ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (undef_flag
                                                          X86_MACHINE.OF)
                                                        (fun _ ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (undef_flag
                                                            X86_MACHINE.SF)
                                                          (fun _ ->
                                                          coq_Bind
                                                            (Obj.magic
                                                              coq_Conv_monad)
                                                            (undef_flag
                                                              X86_MACHINE.ZF)
                                                            (fun _ ->
                                                            coq_Bind
                                                              (Obj.magic
                                                                coq_Conv_monad)
                                                              (undef_flag
                                                                X86_MACHINE.PF)
                                                              (fun _ ->
                                                              coq_Bind
                                                                (Obj.magic
                                                                  coq_Conv_monad)
                                                                (set_AL v_al)
                                                                (fun _ ->
                                                                set_AH v_ah))))))))))))))))))))))))))))))

  (** val conv_AAD : unit coq_Conv **)

  let conv_AAD =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_AL) (fun pal ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_AH) (fun pah ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size8 (Big.double (Big.doubleplusone (Big.double
            Big.one)))) (fun pten ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z size8 (Big.doubleplusone (Big.doubleplusone
              (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
              (Big.doubleplusone (Big.doubleplusone Big.one))))))))
            (fun pFF ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size8 Big.zero) (fun pzero ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic arith size8 X86_RTL.Coq_mul_op pah pten)
                (fun tensval ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size8 X86_RTL.Coq_add_op pal tensval)
                  (fun pal_c ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic arith size8 X86_RTL.Coq_and_op pal_c pFF)
                    (fun pal_cmask ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic test size8 X86_RTL.Coq_eq_op pal_cmask
                        pzero) (fun zfp ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (set_flag X86_MACHINE.ZF zfp) (fun _ ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic test size8 X86_RTL.Coq_lt_op pal_cmask
                            pzero) (fun sfp ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (set_flag X86_MACHINE.SF sfp) (fun _ ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic compute_parity size8 pal_cmask)
                              (fun pfp ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (set_flag X86_MACHINE.PF pfp) (fun _ ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (undef_flag X86_MACHINE.OF) (fun _ ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (undef_flag X86_MACHINE.AF) (fun _ ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (undef_flag X86_MACHINE.CF) (fun _ ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (set_AL pal_cmask) (fun _ ->
                                        set_AH pzero))))))))))))))))))

  (** val conv_AAM : unit coq_Conv **)

  let conv_AAM =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_AL) (fun pal ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z size8 (Big.double (Big.doubleplusone (Big.double
          Big.one)))) (fun pten ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith size8 X86_RTL.Coq_divu_op pal pten) (fun digit1 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size8 X86_RTL.Coq_modu_op pal pten)
            (fun digit2 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size8 Big.zero) (fun pzero ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test size8 X86_RTL.Coq_eq_op digit2 pzero)
                (fun b0 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (set_flag X86_MACHINE.ZF b0) (fun _ ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic test size8 X86_RTL.Coq_lt_op digit2 pzero)
                    (fun b1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (set_flag X86_MACHINE.SF b1) (fun _ ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic compute_parity size8 digit2) (fun b2 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (set_flag X86_MACHINE.PF b2) (fun _ ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (undef_flag X86_MACHINE.OF) (fun _ ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (undef_flag X86_MACHINE.AF) (fun _ ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (undef_flag X86_MACHINE.CF) (fun _ ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (set_AH digit1) (fun _ -> set_AL digit2)))))))))))))))

  (** val testcarryAdd :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let testcarryAdd s p1 p2 p3 =
    coq_Bind (Obj.magic coq_Conv_monad) (test s X86_RTL.Coq_ltu_op p3 p1)
      (fun b0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (test s X86_RTL.Coq_ltu_op p3 p2)
        (fun b1 -> arith size1 X86_RTL.Coq_or_op b0 b1))

  (** val testcarrySub :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let testcarrySub s p1 p2 _ =
    test s X86_RTL.Coq_ltu_op p1 p2

  (** val conv_DAA_DAS :
      X86_RTL.bit_vector_op -> (X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv) -> unit coq_Conv **)

  let conv_DAA_DAS _ _ =
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.CF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.ZF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF)
                (fun _ ->
                coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic choose size8)
                  (fun pal -> set_AL pal)))))))

  (** val conv_logical_op :
      bool -> X86_RTL.bit_vector_op -> prefix -> bool -> operand -> operand
      -> unit coq_Conv **)

  let conv_logical_op do_effect b pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b0 = op_contains_stack op1 in
        let b1 = op_contains_stack op2 in
        if b0 then SS else if b1 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1) (fun p0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2) (fun p1 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith (opsize pre.op_override w) b p0 p1) (fun p2 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic load_Z (opsize pre.op_override w) Big.zero)
            (fun zero0 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_eq_op
                zero0 p2) (fun zfp ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test (opsize pre.op_override w) X86_RTL.Coq_lt_op
                  p2 zero0) (fun sfp ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic compute_parity (opsize pre.op_override w) p2)
                  (fun pfp ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load_Z size1 Big.zero) (fun zero1 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (set_flag X86_MACHINE.OF zero1) (fun _ ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (set_flag X86_MACHINE.CF zero1) (fun _ ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (set_flag X86_MACHINE.ZF zfp) (fun _ ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (set_flag X86_MACHINE.SF sfp) (fun _ ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (set_flag X86_MACHINE.PF pfp) (fun _ ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (undef_flag X86_MACHINE.AF) (fun _ ->
                                if do_effect then set0 seg p2 op1 else no_op))))))))))))))

  (** val conv_AND : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_AND p w op1 op2 =
    conv_logical_op true X86_RTL.Coq_and_op p w op1 op2

  (** val conv_OR : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_OR p w op1 op2 =
    conv_logical_op true X86_RTL.Coq_or_op p w op1 op2

  (** val conv_XOR : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_XOR p w op1 op2 =
    conv_logical_op true X86_RTL.Coq_xor_op p w op1 op2

  (** val conv_TEST :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_TEST p w op1 op2 =
    conv_logical_op false X86_RTL.Coq_and_op p w op1 op2

  (** val conv_NOT : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_NOT pre w op =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op) (fun p0 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic load_Z (opsize pre.op_override w)
          (Word.max_unsigned size32)) (fun max_unsigned0 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith (opsize pre.op_override w) X86_RTL.Coq_xor_op p0
            max_unsigned0) (fun p1 -> set0 seg p1 op)))

  (** val conv_POP : prefix -> operand -> unit coq_Conv **)

  let conv_POP pre op =
    let seg = SS in
    let set0 = set_op pre true seg in
    let loadmem = load_mem pre true seg in
    let espoffset =
      if pre.op_override
      then (Big.double Big.one)
      else (Big.double (Big.double Big.one))
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
      (fun oldesp ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic loadmem oldesp)
        (fun value ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size32 espoffset) (fun offset ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_add_op oldesp offset)
            (fun newesp ->
            coq_Bind (Obj.magic coq_Conv_monad) (set0 value op) (fun _ ->
              set_reg newesp ESP)))))

  (** val conv_POPA : prefix -> unit coq_Conv **)

  let conv_POPA pre =
    let espoffset =
      if pre.op_override
      then (Big.double Big.one)
      else (Big.double (Big.double Big.one))
    in
    let poprtl = fun r -> conv_POP pre (Reg_op r) in
    coq_Bind (Obj.magic coq_Conv_monad) (poprtl EDI) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (poprtl ESI) (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (poprtl EBP) (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
            (fun oldesp ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size32 espoffset) (fun offset ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic arith size32 X86_RTL.Coq_add_op oldesp offset)
                (fun newesp ->
                coq_Bind (Obj.magic coq_Conv_monad) (set_reg newesp ESP)
                  (fun _ ->
                  coq_Bind (Obj.magic coq_Conv_monad) (poprtl EBX) (fun _ ->
                    coq_Bind (Obj.magic coq_Conv_monad) (poprtl EDX)
                      (fun _ ->
                      coq_Bind (Obj.magic coq_Conv_monad) (poprtl ECX)
                        (fun _ -> poprtl EAX))))))))))

  (** val conv_PUSH : prefix -> bool -> operand -> unit coq_Conv **)

  let conv_PUSH pre _ op =
    let seg = SS in
    let load = load_op pre true seg in
    let setmem = set_mem pre true seg in
    let espoffset =
      if pre.op_override
      then (Big.double Big.one)
      else (Big.double (Big.double Big.one))
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load op) (fun p0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
        (fun oldesp ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size32 espoffset) (fun offset ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_sub_op oldesp offset)
            (fun newesp ->
            coq_Bind (Obj.magic coq_Conv_monad) (setmem p0 newesp) (fun _ ->
              set_reg newesp ESP)))))

  (** val conv_PUSH_pseudo :
      prefix -> bool -> X86_RTL.rtl_exp -> unit coq_Conv **)

  let conv_PUSH_pseudo pre w pr =
    let seg = SS in
    let setmem = set_mem pre w seg in
    let espoffset =
      if pre.op_override
      then if w then (Big.double Big.one) else Big.one
      else if w then (Big.double (Big.double Big.one)) else Big.one
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
      (fun oldesp ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size32 espoffset)
        (fun offset ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic arith size32 X86_RTL.Coq_sub_op oldesp offset)
          (fun newesp ->
          coq_Bind (Obj.magic coq_Conv_monad) (setmem pr newesp) (fun _ ->
            set_reg newesp ESP))))

  (** val conv_PUSHA : prefix -> unit coq_Conv **)

  let conv_PUSHA pre =
    let load = load_op pre true SS in
    let pushrtl = fun r -> conv_PUSH pre true (Reg_op r) in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load (Reg_op ESP))
      (fun oldesp ->
      coq_Bind (Obj.magic coq_Conv_monad) (pushrtl EAX) (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (pushrtl ECX) (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (pushrtl EDX) (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (pushrtl EBX) (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (conv_PUSH_pseudo pre true oldesp) (fun _ ->
                coq_Bind (Obj.magic coq_Conv_monad) (pushrtl EBP) (fun _ ->
                  coq_Bind (Obj.magic coq_Conv_monad) (pushrtl ESI) (fun _ ->
                    pushrtl EDI))))))))

  (** val conv_JMP :
      prefix -> bool -> bool -> operand -> selector option -> unit coq_Conv **)

  let conv_JMP pre near absolute op _ =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    if near
    then coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic iload_op32 seg op)
           (fun disp ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (if absolute
              then Obj.magic load_Z size32 Big.zero
              else Obj.magic get_pc) (fun base ->
             coq_Bind (Obj.magic coq_Conv_monad)
               (Obj.magic arith size32 X86_RTL.Coq_add_op base disp)
               (fun newpc -> set_pc newpc)))
    else raise_error

  (** val conv_Jcc : prefix -> condition_type -> int32 -> unit coq_Conv **)

  let conv_Jcc _ ct disp =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_cc ct)
      (fun guard ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_pc) (fun oldpc ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_int size32 disp)
          (fun pdisp ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_add_op oldpc pdisp)
            (fun newpc ->
            if_set_loc guard size32 newpc X86_MACHINE.Coq_pc_loc))))

  (** val conv_CALL :
      prefix -> bool -> bool -> operand -> selector option -> unit coq_Conv **)

  let conv_CALL pre near absolute op sel =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_pc) (fun oldpc ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
        (fun oldesp ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic load_Z size32 (Big.double (Big.double Big.one)))
          (fun four ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_sub_op oldesp four)
            (fun newesp ->
            coq_Bind (Obj.magic coq_Conv_monad) (set_mem32 SS oldpc newesp)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (set_reg newesp ESP)
                (fun _ -> conv_JMP pre near absolute op sel))))))

  (** val conv_RET : prefix -> bool -> int16 option -> unit coq_Conv **)

  let conv_RET _ same_segment disp =
    if same_segment
    then coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ESP)
           (fun oldesp ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (Obj.magic load_mem32 SS oldesp) (fun value ->
             coq_Bind (Obj.magic coq_Conv_monad)
               (Obj.magic load_Z size32 (Big.double (Big.double Big.one)))
               (fun four ->
               coq_Bind (Obj.magic coq_Conv_monad)
                 (Obj.magic arith size32 X86_RTL.Coq_add_op oldesp four)
                 (fun newesp ->
                 coq_Bind (Obj.magic coq_Conv_monad) (set_pc value) (fun _ ->
                   match disp with
                   | Some imm ->
                     coq_Bind (Obj.magic coq_Conv_monad)
                       (Obj.magic load_int size16 imm) (fun imm0 ->
                       coq_Bind (Obj.magic coq_Conv_monad)
                         (Obj.magic cast_u size16 size32 imm0) (fun imm1 ->
                         coq_Bind (Obj.magic coq_Conv_monad)
                           (Obj.magic arith size32 X86_RTL.Coq_add_op newesp
                             imm1) (fun newesp2 -> set_reg newesp2 ESP)))
                   | None -> set_reg newesp ESP)))))
    else raise_error

  (** val conv_LEAVE : prefix -> unit coq_Conv **)

  let conv_LEAVE pre =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg EBP)
      (fun ebp_val ->
      coq_Bind (Obj.magic coq_Conv_monad) (set_reg ebp_val ESP) (fun _ ->
        conv_POP pre (Reg_op EBP)))

  (** val conv_LOOP : prefix -> bool -> bool -> int8 -> unit coq_Conv **)

  let conv_LOOP pre flagged testz disp =
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size1 Big.one)
      (fun ptrue ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg ECX) (fun p0 ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_Z size32 Big.one)
          (fun p1 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_sub_op p0 p1) (fun p2 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic load_Z size32 Big.zero) (fun pzero ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic test size32 X86_RTL.Coq_eq_op p2 pzero)
                (fun pcz ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size1 X86_RTL.Coq_xor_op pcz ptrue)
                  (fun pcnz ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic get_flag X86_MACHINE.ZF) (fun pzf ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic arith size1 X86_RTL.Coq_xor_op pzf ptrue)
                      (fun pnzf ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (if flagged
                         then if testz
                              then Obj.magic arith size1 X86_RTL.Coq_and_op
                                     pzf pcnz
                              else Obj.magic arith size1 X86_RTL.Coq_and_op
                                     pnzf pcnz
                         else Obj.magic arith size1 X86_RTL.Coq_or_op pcnz
                                pcnz) (fun bcond ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic get_pc) (fun eip0 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic load_int size8 disp) (fun doffset0 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_s size8 size32 doffset0)
                              (fun doffset1 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size32 X86_RTL.Coq_add_op
                                  eip0 doffset1) (fun eip1 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (if pre.op_override
                                   then Obj.magic load_Z size32 (Big.double
                                          (Big.double (Big.double (Big.double
                                          (Big.double (Big.double (Big.double
                                          (Big.double (Big.double (Big.double
                                          (Big.double (Big.double (Big.double
                                          (Big.double (Big.double (Big.double
                                          Big.one))))))))))))))))
                                   else Obj.magic load_Z size32
                                          (Z.opp Big.one)) (fun eipmask ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size32
                                      X86_RTL.Coq_and_op eip1 eipmask)
                                    (fun eip2 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (if_set_loc bcond size32 eip2
                                        X86_MACHINE.Coq_pc_loc) (fun _ ->
                                      set_reg p2 ECX)))))))))))))))))

  (** val conv_BS_aux :
      Big.big_int -> bool -> Big.big_int -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let rec conv_BS_aux s d n op =
    let curr_int =
      if d
      then Word.repr s (Z.of_nat (sub s n))
      else Word.repr s (Z.of_nat n)
    in
    (Big.nat_case
       (fun _ ->
       load_int s curr_int)
       (fun n' ->
       coq_Bind (Obj.magic coq_Conv_monad) (load_int s curr_int)
         (fun bcount ->
         coq_Bind (Obj.magic coq_Conv_monad) (conv_BS_aux s d n' op)
           (fun rec0 ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (arith s X86_RTL.Coq_shru_op op bcount) (fun ps ->
             coq_Bind (Obj.magic coq_Conv_monad) (cast_u s size1 ps)
               (fun curr_bit ->
               coq_Bind (Obj.magic coq_Conv_monad) (load_int s curr_int)
                 (fun rec1 -> if_exp s curr_bit rec1 rec0))))))
       n)

  (** val conv_BS : bool -> prefix -> operand -> operand -> unit coq_Conv **)

  let conv_BS d pre op1 op2 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    let load = load_op pre true in
    let set0 = set_op pre true in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.CF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
              (fun _ ->
              coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1)
                (fun _ ->
                coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
                  (fun src ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load_Z (opsize pre.op_override true) Big.zero)
                    (fun zero0 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic test (opsize pre.op_override true)
                        X86_RTL.Coq_eq_op src zero0) (fun zf ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic conv_BS_aux (opsize pre.op_override true)
                          d (opsize pre.op_override true) src) (fun res0 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic choose (opsize pre.op_override true))
                          (fun res1 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic if_exp (opsize pre.op_override true)
                              zf res1 res0) (fun res ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (set_flag X86_MACHINE.ZF zf) (fun _ ->
                              set0 seg res op1)))))))))))))

  (** val conv_BSF : prefix -> operand -> operand -> unit coq_Conv **)

  let conv_BSF pre op1 op2 =
    conv_BS true pre op1 op2

  (** val conv_BSR : prefix -> operand -> operand -> unit coq_Conv **)

  let conv_BSR pre op1 op2 =
    conv_BS false pre op1 op2

  (** val get_Bit :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
      coq_Conv **)

  let get_Bit s pb poff =
    coq_Bind (Obj.magic coq_Conv_monad) (load_Z s Big.one) (fun omask ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (arith s X86_RTL.Coq_shr_op pb poff) (fun shr_pb ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (arith s X86_RTL.Coq_and_op shr_pb omask) (fun mask_pb ->
          cast_u s size1 mask_pb)))

  (** val modify_Bit :
      Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp coq_Conv **)

  let modify_Bit s value poff bitval =
    coq_Bind (Obj.magic coq_Conv_monad) (load_Z s Big.one) (fun obit ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (arith s X86_RTL.Coq_shl_op obit poff) (fun one_shifted ->
        coq_Bind (Obj.magic coq_Conv_monad) (not s one_shifted)
          (fun inv_one_shifted ->
          coq_Bind (Obj.magic coq_Conv_monad) (cast_u size1 s bitval)
            (fun bitvalword ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (arith s X86_RTL.Coq_shl_op bitvalword poff)
              (fun bit_shifted ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (arith s X86_RTL.Coq_and_op value inv_one_shifted)
                (fun newval -> arith s X86_RTL.Coq_or_op newval bit_shifted))))))

  (** val set_Bit :
      prefix -> bool -> operand -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp -> unit
      coq_Conv **)

  let set_Bit pre w op poff bitval =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    let load = load_op pre w seg in
    let set0 = set_op pre w seg in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load op) (fun value ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic modify_Bit (opsize pre.op_override w) value poff bitval)
        (fun newvalue -> set0 newvalue op))

  (** val set_Bit_mem :
      prefix -> bool -> operand -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp ->
      X86_RTL.rtl_exp -> unit coq_Conv **)

  let set_Bit_mem pre w op addr poff bitval =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    let load = load_mem pre w seg in
    let set0 = set_mem pre w seg in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load addr) (fun value ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic modify_Bit (opsize pre.op_override w) value poff bitval)
        (fun newvalue -> set0 newvalue addr))

  (** val fbit :
      bool -> bool -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp coq_Conv **)

  let fbit param1 param2 v =
    if param1
    then if param2 then load_Z size1 Big.one else load_Z size1 Big.zero
    else if param2
         then coq_Return (Obj.magic coq_Conv_monad) v
         else not size1 v

  (** val conv_BT :
      bool -> bool -> prefix -> operand -> operand -> unit coq_Conv **)

  let conv_BT param1 param2 pre op1 regimm =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    let load = load_op pre true seg in
    let lmem0 = load_mem pre true seg in
    let opsz = opsize pre.op_override true in
    coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.OF) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.SF)
        (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.AF)
          (fun _ ->
          coq_Bind (Obj.magic coq_Conv_monad) (undef_flag X86_MACHINE.PF)
            (fun _ ->
            coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load regimm)
              (fun pi ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic load_Z opsz (Z.add (Z.of_nat opsz) Big.one))
                (fun popsz ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (match regimm with
                   | Imm_op _ ->
                     Obj.magic arith (opsize pre.op_override true)
                       X86_RTL.Coq_modu_op pi popsz
                   | _ -> coq_Return (Obj.magic coq_Conv_monad) pi)
                  (fun rawoffset ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic load_Z size32
                      (Z.div (Z.of_nat (add opsz (Big.succ Big.zero)))
                        (Big.double (Big.double (Big.double Big.one)))))
                    (fun popsz_bytes ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic load_Z opsz Big.zero) (fun pzero ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic load_Z size32 (Big.opp Big.one))
                        (fun pneg1 ->
                        let btmem = fun psaddr ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic arith (opsize pre.op_override true)
                              X86_RTL.Coq_mods_op rawoffset popsz)
                            (fun bitoffset ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic arith (opsize pre.op_override true)
                                X86_RTL.Coq_divs_op rawoffset popsz)
                              (fun wordoffset' ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic cast_s
                                  (opsize pre.op_override true) size32
                                  wordoffset') (fun wordoffset ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic test
                                    (opsize pre.op_override true)
                                    X86_RTL.Coq_lt_op bitoffset pzero)
                                  (fun isneg ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith opsz X86_RTL.Coq_add_op
                                      popsz bitoffset) (fun negbitoffset ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size32
                                        X86_RTL.Coq_add_op pneg1 wordoffset)
                                      (fun negwordoffset ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic cast_u opsz
                                          (opsize pre.op_override true)
                                          negbitoffset) (fun nbitoffset1 ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic if_exp
                                            (opsize pre.op_override true)
                                            isneg nbitoffset1 bitoffset)
                                          (fun nbitoffset ->
                                          coq_Bind (Obj.magic coq_Conv_monad)
                                            (Obj.magic cast_u size32 size32
                                              negwordoffset)
                                            (fun nwordoffset1 ->
                                            coq_Bind
                                              (Obj.magic coq_Conv_monad)
                                              (Obj.magic if_exp size32 isneg
                                                nwordoffset1 wordoffset)
                                              (fun nwordoffset ->
                                              coq_Bind
                                                (Obj.magic coq_Conv_monad)
                                                (Obj.magic arith size32
                                                  X86_RTL.Coq_mul_op
                                                  nwordoffset popsz_bytes)
                                                (fun newaddrdelta ->
                                                coq_Bind
                                                  (Obj.magic coq_Conv_monad)
                                                  (Obj.magic arith size32
                                                    X86_RTL.Coq_add_op
                                                    newaddrdelta psaddr)
                                                  (fun newaddr ->
                                                  coq_Bind
                                                    (Obj.magic
                                                      coq_Conv_monad)
                                                    (Obj.magic lmem0 newaddr)
                                                    (fun value ->
                                                    coq_Bind
                                                      (Obj.magic
                                                        coq_Conv_monad)
                                                      (Obj.magic get_Bit
                                                        (opsize
                                                          pre.op_override
                                                          true) value
                                                        nbitoffset)
                                                      (fun bt ->
                                                      coq_Bind
                                                        (Obj.magic
                                                          coq_Conv_monad)
                                                        (Obj.magic fbit
                                                          param1 param2 bt)
                                                        (fun newbt ->
                                                        coq_Bind
                                                          (Obj.magic
                                                            coq_Conv_monad)
                                                          (set_flag
                                                            X86_MACHINE.CF
                                                            bt) (fun _ ->
                                                          set_Bit_mem pre
                                                            true op1 newaddr
                                                            nbitoffset newbt))))))))))))))))
                        in
                        (match op1 with
                         | Imm_op _ -> raise_error
                         | Reg_op r1 ->
                           coq_Bind (Obj.magic coq_Conv_monad)
                             (Obj.magic load (Reg_op r1)) (fun value ->
                             coq_Bind (Obj.magic coq_Conv_monad)
                               (Obj.magic arith (opsize pre.op_override true)
                                 X86_RTL.Coq_modu_op rawoffset popsz)
                               (fun bitoffset ->
                               coq_Bind (Obj.magic coq_Conv_monad)
                                 (Obj.magic get_Bit
                                   (opsize pre.op_override true) value
                                   bitoffset) (fun bt ->
                                 coq_Bind (Obj.magic coq_Conv_monad)
                                   (Obj.magic fbit param1 param2 bt)
                                   (fun newbt ->
                                   coq_Bind (Obj.magic coq_Conv_monad)
                                     (set_flag X86_MACHINE.CF bt) (fun _ ->
                                     set_Bit pre true op1 bitoffset newbt)))))
                         | Address_op a ->
                           coq_Bind (Obj.magic coq_Conv_monad)
                             (Obj.magic compute_addr a) (fun psaddr ->
                             btmem psaddr)
                         | Offset_op ioff ->
                           coq_Bind (Obj.magic coq_Conv_monad)
                             (Obj.magic load_int size32 ioff) (fun psaddr ->
                             btmem psaddr))))))))))))

  (** val conv_BSWAP : prefix -> register -> unit coq_Conv **)

  let conv_BSWAP _ r =
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z size32 (Big.double (Big.double (Big.double
        Big.one)))) (fun eight ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load_reg r) (fun ps0 ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic cast_u size32 size8 ps0) (fun b0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic arith size32 X86_RTL.Coq_shru_op ps0 eight)
            (fun ps1 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic cast_u size32 size8 ps1) (fun b1 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic cast_u size8 size32 b1) (fun w1 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic arith size32 X86_RTL.Coq_shru_op ps1 eight)
                  (fun ps2 ->
                  coq_Bind (Obj.magic coq_Conv_monad)
                    (Obj.magic cast_u size32 size8 ps2) (fun b2 ->
                    coq_Bind (Obj.magic coq_Conv_monad)
                      (Obj.magic cast_u size8 size32 b2) (fun w2 ->
                      coq_Bind (Obj.magic coq_Conv_monad)
                        (Obj.magic arith size32 X86_RTL.Coq_shru_op ps2
                          eight) (fun ps3 ->
                        coq_Bind (Obj.magic coq_Conv_monad)
                          (Obj.magic cast_u size32 size8 ps3) (fun b3 ->
                          coq_Bind (Obj.magic coq_Conv_monad)
                            (Obj.magic cast_u size8 size32 b3) (fun w3 ->
                            coq_Bind (Obj.magic coq_Conv_monad)
                              (Obj.magic cast_u size8 size32 b0) (fun res0 ->
                              coq_Bind (Obj.magic coq_Conv_monad)
                                (Obj.magic arith size32 X86_RTL.Coq_shl_op
                                  res0 eight) (fun res1 ->
                                coq_Bind (Obj.magic coq_Conv_monad)
                                  (Obj.magic arith size32 X86_RTL.Coq_add_op
                                    res1 w1) (fun res2 ->
                                  coq_Bind (Obj.magic coq_Conv_monad)
                                    (Obj.magic arith size32
                                      X86_RTL.Coq_shl_op res2 eight)
                                    (fun res3 ->
                                    coq_Bind (Obj.magic coq_Conv_monad)
                                      (Obj.magic arith size32
                                        X86_RTL.Coq_add_op res3 w2)
                                      (fun res4 ->
                                      coq_Bind (Obj.magic coq_Conv_monad)
                                        (Obj.magic arith size32
                                          X86_RTL.Coq_shl_op res4 eight)
                                        (fun res5 ->
                                        coq_Bind (Obj.magic coq_Conv_monad)
                                          (Obj.magic arith size32
                                            X86_RTL.Coq_add_op res5 w3)
                                          (fun res6 -> set_reg res6 r)))))))))))))))))))

  (** val conv_CWDE : prefix -> unit coq_Conv **)

  let conv_CWDE pre =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> DS
    in
    if pre.op_override
    then coq_Bind (Obj.magic coq_Conv_monad)
           (Obj.magic iload_op8 seg (Reg_op EAX)) (fun p1 ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (Obj.magic cast_s size8 size16 p1) (fun p2 ->
             iset_op16 seg p2 (Reg_op EAX)))
    else coq_Bind (Obj.magic coq_Conv_monad)
           (Obj.magic iload_op16 seg (Reg_op EAX)) (fun p1 ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (Obj.magic cast_s size16 size32 p1) (fun p2 ->
             iset_op32 seg p2 (Reg_op EAX)))

  (** val conv_CDQ : prefix -> unit coq_Conv **)

  let conv_CDQ pre =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> DS
    in
    if pre.op_override
    then coq_Bind (Obj.magic coq_Conv_monad)
           (Obj.magic iload_op16 seg (Reg_op EAX)) (fun p1 ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (Obj.magic cast_s size16 size32 p1) (fun p2 ->
             coq_Bind (Obj.magic coq_Conv_monad)
               (Obj.magic cast_s size32 size16 p2) (fun p2_bottom ->
               coq_Bind (Obj.magic coq_Conv_monad)
                 (Obj.magic load_Z size32 (Big.double (Big.double (Big.double
                   (Big.double Big.one))))) (fun sixteen ->
                 coq_Bind (Obj.magic coq_Conv_monad)
                   (Obj.magic arith size32 X86_RTL.Coq_shr_op p2 sixteen)
                   (fun p2_top0 ->
                   coq_Bind (Obj.magic coq_Conv_monad)
                     (Obj.magic cast_s size32 size16 p2_top0) (fun p2_top ->
                     coq_Bind (Obj.magic coq_Conv_monad)
                       (iset_op16 seg p2_top (Reg_op EDX)) (fun _ ->
                       iset_op16 seg p2_bottom (Reg_op EAX))))))))
    else coq_Bind (Obj.magic coq_Conv_monad)
           (Obj.magic iload_op32 seg (Reg_op EAX)) (fun p1 ->
           coq_Bind (Obj.magic coq_Conv_monad)
             (Obj.magic cast_s size32 (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
               Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
               p1) (fun p2 ->
             coq_Bind (Obj.magic coq_Conv_monad)
               (Obj.magic cast_s (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                 Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                 size32 p2) (fun p2_bottom ->
               coq_Bind (Obj.magic coq_Conv_monad)
                 (Obj.magic load_Z (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                   (Big.succ (Big.succ (Big.succ (Big.succ
                   Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                   (Big.double (Big.double (Big.double (Big.double
                   (Big.double Big.one)))))) (fun thirtytwo ->
                 coq_Bind (Obj.magic coq_Conv_monad)
                   (Obj.magic arith (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                     (Big.succ (Big.succ (Big.succ (Big.succ
                     Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                     X86_RTL.Coq_shr_op p2 thirtytwo) (fun p2_top0 ->
                   coq_Bind (Obj.magic coq_Conv_monad)
                     (Obj.magic cast_s (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
                       Big.zero)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                       size32 p2_top0) (fun p2_top ->
                     coq_Bind (Obj.magic coq_Conv_monad)
                       (iset_op32 seg p2_top (Reg_op EDX)) (fun _ ->
                       iset_op32 seg p2_bottom (Reg_op EAX))))))))

  (** val conv_MOV : prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_MOV pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2) (fun res ->
      set0 seg res op1)

  (** val conv_CMOV :
      prefix -> bool -> condition_type -> operand -> operand -> unit coq_Conv **)

  let conv_CMOV pre w cc op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1) (fun tmp0 ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
        (fun src ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_cc cc)
          (fun cc0 ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic cast_u (opsize pre.op_override w)
              (opsize pre.op_override w) src) (fun tmp1 ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic if_exp (opsize pre.op_override w) cc0 tmp1 tmp0)
              (fun tmp -> set0 seg tmp op1)))))

  (** val conv_MOV_extend :
      (Big.big_int -> Big.big_int -> X86_RTL.rtl_exp -> X86_RTL.rtl_exp
      coq_Conv) -> prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_MOV_extend extend_op pre w op1 op2 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    if pre.op_override
    then if w
         then coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic iload_op16 seg op2) (fun p1 ->
                iset_op16 seg p1 op1)
         else coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic iload_op8 seg op2) (fun p1 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic extend_op size8 size16 p1) (fun p2 ->
                  iset_op16 seg p2 op1))
    else if w
         then coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic iload_op16 seg op2) (fun p1 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic extend_op size16 size32 p1) (fun p2 ->
                  iset_op32 seg p2 op1))
         else coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic iload_op8 seg op2) (fun p1 ->
                coq_Bind (Obj.magic coq_Conv_monad)
                  (Obj.magic extend_op size8 size32 p1) (fun p2 ->
                  iset_op32 seg p2 op1))

  (** val conv_MOVZX :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_MOVZX pre w op1 op2 =
    conv_MOV_extend cast_u pre w op1 op2

  (** val conv_MOVSX :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_MOVSX pre w op1 op2 =
    conv_MOV_extend cast_s pre w op1 op2

  (** val conv_XCHG :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_XCHG pre w op1 op2 =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None ->
        let b = op_contains_stack op1 in
        let b0 = op_contains_stack op2 in
        if b then SS else if b0 then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op1) (fun p1 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic write_ps_and_fresh (opsize pre.op_override w) p1)
        (fun sp1 ->
        coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load seg op2)
          (fun p2 ->
          coq_Bind (Obj.magic coq_Conv_monad) (set0 seg p2 op1) (fun _ ->
            set0 seg sp1 op2))))

  (** val conv_XADD :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_XADD pre w op1 op2 =
    coq_Bind (Obj.magic coq_Conv_monad) (conv_XCHG pre w op1 op2) (fun _ ->
      conv_ADD pre w op1 op2)

  (** val conv_CMPXCHG :
      prefix -> bool -> operand -> operand -> unit coq_Conv **)

  let conv_CMPXCHG pre w op1 op2 =
    coq_Bind (Obj.magic coq_Conv_monad) (conv_CMP pre w (Reg_op EAX) op1)
      (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (conv_CMOV pre w E_ct op1 op2)
        (fun _ -> conv_CMOV pre w NE_ct (Reg_op EAX) op1))

  (** val string_op_reg_shift :
      register -> prefix -> bool -> unit coq_Conv **)

  let string_op_reg_shift reg pre w =
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load_Z size32
        (if pre.op_override
         then if w then (Big.double Big.one) else Big.one
         else if w then (Big.double (Big.double Big.one)) else Big.one))
      (fun offset ->
      coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic get_flag X86_MACHINE.DF)
        (fun df ->
        coq_Bind (Obj.magic coq_Conv_monad)
          (Obj.magic iload_op32 DS (Reg_op reg)) (fun tmp ->
          coq_Bind (Obj.magic coq_Conv_monad)
            (Obj.magic write_ps_and_fresh size32 tmp) (fun old_reg ->
            coq_Bind (Obj.magic coq_Conv_monad)
              (Obj.magic arith size32 X86_RTL.Coq_add_op old_reg offset)
              (fun new_reg1 ->
              coq_Bind (Obj.magic coq_Conv_monad)
                (Obj.magic arith size32 X86_RTL.Coq_sub_op old_reg offset)
                (fun new_reg2 ->
                coq_Bind (Obj.magic coq_Conv_monad) (set_reg new_reg1 reg)
                  (fun _ ->
                  if_set_loc df size32 new_reg2 (X86_MACHINE.Coq_reg_loc reg))))))))

  (** val conv_MOVS : prefix -> bool -> unit coq_Conv **)

  let conv_MOVS pre w =
    let load = load_op pre w in
    let set0 = set_op pre w in
    let seg_load =
      match pre.seg_override with
      | Some s -> s
      | None -> DS
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (Obj.magic load seg_load (Address_op { addrDisp = (Word.zero size32);
        addrBase = (Some ESI); addrIndex = None })) (fun p1 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (set0 ES p1 (Address_op { addrDisp = (Word.zero size32); addrBase =
          (Some EDI); addrIndex = None })) (fun _ ->
        coq_Bind (Obj.magic coq_Conv_monad) (string_op_reg_shift EDI pre w)
          (fun _ -> string_op_reg_shift ESI pre w)))

  (** val conv_STOS : prefix -> bool -> unit coq_Conv **)

  let conv_STOS pre w =
    let load = load_op pre w in
    let set0 = set_op pre w in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic load DS (Reg_op EAX))
      (fun p1 ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (set0 ES p1 (Address_op { addrDisp = (Word.zero size32); addrBase =
          (Some EDI); addrIndex = None })) (fun _ ->
        string_op_reg_shift EDI pre w))

  (** val conv_CMPS : prefix -> bool -> unit coq_Conv **)

  let conv_CMPS pre w =
    let seg1 =
      match pre.seg_override with
      | Some s -> s
      | None -> DS
    in
    let op1 = Address_op { addrDisp = (Word.zero size32); addrBase = (Some
      ESI); addrIndex = None }
    in
    let op2 = Address_op { addrDisp = (Word.zero size32); addrBase = (Some
      EDI); addrIndex = None }
    in
    coq_Bind (Obj.magic coq_Conv_monad)
      (conv_SUB_CMP_generic false pre w op1 op2 op2 seg1 seg1 ES) (fun _ ->
      coq_Bind (Obj.magic coq_Conv_monad) (string_op_reg_shift EDI pre w)
        (fun _ -> string_op_reg_shift ESI pre w))

  (** val conv_LEA : prefix -> operand -> operand -> unit coq_Conv **)

  let conv_LEA pre op1 op2 =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op1 then SS else DS
    in
    (match op2 with
     | Address_op a ->
       coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_addr a)
         (fun r -> iset_op32 seg r op1)
     | _ -> raise_error)

  (** val conv_HLT : prefix -> unit coq_Conv **)

  let conv_HLT _ =
    raise_trap

  (** val conv_SETcc :
      prefix -> condition_type -> operand -> unit coq_Conv **)

  let conv_SETcc pre ct op =
    let seg =
      match pre.seg_override with
      | Some s -> s
      | None -> if op_contains_stack op then SS else DS
    in
    coq_Bind (Obj.magic coq_Conv_monad) (Obj.magic compute_cc ct)
      (fun ccval ->
      coq_Bind (Obj.magic coq_Conv_monad)
        (Obj.magic cast_u size1 size8 ccval) (fun ccext ->
        iset_op8 seg ccext op))

  (** val check_prefix : prefix -> unit coq_Conv **)

  let check_prefix p =
    if p.addr_override then raise_error else no_op

  (** val instr_to_rtl : prefix -> instr -> X86_RTL.rtl_instr list **)

  let instr_to_rtl pre i =
    runConv
      (coq_Bind (Obj.magic coq_Conv_monad) (check_prefix pre) (fun _ ->
        match i with
        | AAA -> conv_AAA_AAS X86_RTL.Coq_add_op
        | AAD -> conv_AAD
        | AAM -> conv_AAM
        | AAS -> conv_AAA_AAS X86_RTL.Coq_sub_op
        | ADC (w, op1, op2) -> conv_ADC pre w op1 op2
        | ADD (w, op1, op2) -> conv_ADD pre w op1 op2
        | AND (w, op1, op2) -> conv_AND pre w op1 op2
        | BOUND (_, _) -> raise_trap
        | BSF (op1, op2) -> conv_BSF pre op1 op2
        | BSR (op1, op2) -> conv_BSR pre op1 op2
        | BSWAP r -> conv_BSWAP pre r
        | BT (op1, op2) -> conv_BT false true pre op1 op2
        | BTC (op1, op2) -> conv_BT false false pre op1 op2
        | BTR (op1, op2) -> conv_BT true false pre op1 op2
        | BTS (op1, op2) -> conv_BT true true pre op1 op2
        | CALL (near, abs, op1, sel) -> conv_CALL pre near abs op1 sel
        | CDQ -> conv_CDQ pre
        | CLC -> conv_CLC
        | CLD -> conv_CLD
        | CLI -> raise_trap
        | CLTS -> raise_trap
        | CMC -> conv_CMC
        | CMOVcc (ct, op1, op2) -> conv_CMOV pre true ct op1 op2
        | CMP (w, op1, op2) -> conv_CMP pre w op1 op2
        | CMPS w -> conv_CMPS pre w
        | CMPXCHG (w, op1, op2) -> conv_CMPXCHG pre w op1 op2
        | CPUID -> raise_trap
        | CWDE -> conv_CWDE pre
        | DAA -> conv_DAA_DAS X86_RTL.Coq_add_op (testcarryAdd size8)
        | DAS ->
          conv_DAA_DAS X86_RTL.Coq_sub_op (fun p1 p2 _ ->
            test size8 X86_RTL.Coq_ltu_op p1 p2)
        | DEC (w, op1) -> conv_DEC pre w op1
        | DIV (w, op) -> conv_DIV pre w op
        | HLT -> raise_trap
        | IDIV (w, op) -> conv_IDIV pre w op
        | IMUL (w, op1, op2, i0) -> conv_IMUL pre w op1 op2 i0
        | INC (w, op1) -> conv_INC pre w op1
        | Jcc (ct, disp) -> conv_Jcc pre ct disp
        | JMP (near, abs, op1, sel) -> conv_JMP pre near abs op1 sel
        | LAHF -> conv_LAHF
        | LAR (_, _) -> raise_trap
        | LEA (op1, op2) -> conv_LEA pre op1 op2
        | LEAVE -> conv_LEAVE pre
        | LGS (_, _) -> raise_trap
        | LOOP disp -> conv_LOOP pre false false disp
        | LOOPZ disp -> conv_LOOP pre true true disp
        | LOOPNZ disp -> conv_LOOP pre true false disp
        | MOV (w, op1, op2) -> conv_MOV pre w op1 op2
        | MOVCR (_, _, _) -> raise_trap
        | MOVDR (_, _, _) -> raise_trap
        | MOVSR (_, _, _) -> raise_trap
        | MOVBE (_, _) -> raise_trap
        | MOVS w -> conv_MOVS pre w
        | MOVSX (w, op1, op2) -> conv_MOVSX pre w op1 op2
        | MOVZX (w, op1, op2) -> conv_MOVZX pre w op1 op2
        | MUL (w, op) -> conv_MUL pre w op
        | NEG (w, op1) -> conv_NEG pre w op1
        | NOP _ -> coq_Return (Obj.magic coq_Conv_monad) ()
        | NOT (w, op1) -> conv_NOT pre w op1
        | OR (w, op1, op2) -> conv_OR pre w op1 op2
        | POP op -> conv_POP pre op
        | POPA -> conv_POPA pre
        | POPF -> raise_trap
        | PUSH (w, op) -> conv_PUSH pre w op
        | PUSHSR _ -> raise_trap
        | PUSHA -> conv_PUSHA pre
        | PUSHF -> raise_trap
        | RCL (w, op1, op2) -> conv_RCL pre w op1 op2
        | RCR (w, op1, op2) -> conv_RCR pre w op1 op2
        | RDMSR -> raise_trap
        | RDPMC -> raise_trap
        | RDTSC -> raise_trap
        | RDTSCP -> raise_trap
        | RET (ss, disp) -> conv_RET pre ss disp
        | ROL (w, op1, op2) -> conv_ROL pre w op1 op2
        | ROR (w, op1, op2) -> conv_ROR pre w op1 op2
        | RSM -> raise_trap
        | SAHF -> conv_SAHF
        | SAR (w, op1, op2) -> conv_SAR pre w op1 op2
        | SBB (w, op1, op2) -> conv_SBB pre w op1 op2
        | SCAS _ -> raise_trap
        | SETcc (ct, op) -> conv_SETcc pre ct op
        | SGDT _ -> raise_trap
        | SHL (w, op1, op2) -> conv_SHL pre w op1 op2
        | SHLD (op1, op2, ri) -> conv_SHLD pre op1 op2 ri
        | SHR (w, op1, op2) -> conv_SHR pre w op1 op2
        | SHRD (op1, op2, ri) -> conv_SHRD pre op1 op2 ri
        | SIDT _ -> raise_trap
        | SLDT _ -> raise_trap
        | SMSW _ -> raise_trap
        | STC -> conv_STC
        | STD -> conv_STD
        | STI -> raise_trap
        | STOS w -> conv_STOS pre w
        | STR _ -> raise_trap
        | SUB (w, op1, op2) -> conv_SUB pre w op1 op2
        | TEST (w, op1, op2) -> conv_TEST pre w op1 op2
        | WBINVD -> raise_trap
        | XADD (w, op1, op2) -> conv_XADD pre w op1 op2
        | XCHG (w, op1, op2) -> conv_XCHG pre w op1 op2
        | XOR (w, op1, op2) -> conv_XOR pre w op1 op2
        | _ -> raise_error))
 end
