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

(** val coq_EncodingMonad : __ coq_Enc coq_Monad **)

let coq_EncodingMonad =
  { coq_Return = (fun _ x -> Some x); coq_Bind = (fun _ _ c f ->
    match c with
    | Some v -> f v
    | None -> None) }

(** val invalid : 'a1 coq_Enc **)

let invalid =
  None

(** val bits_to_bytes : bool list -> int8 list coq_Enc **)

let bits_to_bytes lbits =
  let to_bytes =
    let rec to_bytes lbits0 n acc res =
      match lbits0 with
      | [] ->
        if Nat.eqb n (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
             (Big.succ (Big.succ Big.zero)))))))
        then coq_Return coq_EncodingMonad res
        else invalid
      | b :: lbits' ->
        let acc' =
          if b
          then Word.add size8 (Word.shl size8 acc (Word.one size8))
                 (Word.one size8)
          else Word.shl size8 acc (Word.one size8)
        in
        if Nat.eqb n Big.zero
        then to_bytes lbits' (Big.succ (Big.succ (Big.succ (Big.succ
               (Big.succ (Big.succ (Big.succ Big.zero)))))))
               (Word.zero size8) (acc' :: res)
        else to_bytes lbits' (Nat.pred n) acc' res
    in to_bytes
  in
  coq_Bind (Obj.magic coq_EncodingMonad)
    (Obj.magic to_bytes lbits (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ Big.zero))))))) (Word.zero size8) [])
    (fun lbytes -> coq_Return (Obj.magic coq_EncodingMonad) (rev lbytes))

(** val x86_encode : prefix -> instr -> int8 list coq_Enc **)

let x86_encode pre ins =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (Obj.magic pretty_print instr_bigrammar (pre, ins)) (fun lbits ->
    bits_to_bytes lbits)

(** val s2bl : char list -> bool list **)

let rec s2bl = function
| [] -> []
| a::s0 -> (if (=) a '0' then false else true) :: (s2bl s0)

(** val enc_reg : register -> bool list **)

let enc_reg = function
| EAX -> s2bl ('0'::('0'::('0'::[])))
| ECX -> s2bl ('0'::('0'::('1'::[])))
| EDX -> s2bl ('0'::('1'::('0'::[])))
| EBX -> s2bl ('0'::('1'::('1'::[])))
| ESP -> s2bl ('1'::('0'::('0'::[])))
| EBP -> s2bl ('1'::('0'::('1'::[])))
| ESI -> s2bl ('1'::('1'::('0'::[])))
| EDI -> s2bl ('1'::('1'::('1'::[])))

(** val enc_debug_reg : debug_register -> bool list **)

let enc_debug_reg = function
| DR0 -> s2bl ('0'::('0'::('0'::[])))
| DR1 -> s2bl ('0'::('0'::('1'::[])))
| DR2 -> s2bl ('0'::('1'::('0'::[])))
| DR3 -> s2bl ('0'::('1'::('1'::[])))
| DR6 -> s2bl ('1'::('1'::('0'::[])))
| DR7 -> s2bl ('1'::('1'::('1'::[])))

(** val enc_control_reg : control_register -> bool list **)

let enc_control_reg = function
| CR0 -> s2bl ('0'::('0'::('0'::[])))
| CR2 -> s2bl ('0'::('1'::('0'::[])))
| CR3 -> s2bl ('0'::('1'::('1'::[])))
| CR4 -> s2bl ('1'::('0'::('0'::[])))

(** val sreg3_2_reg : segment_register -> register **)

let sreg3_2_reg = function
| ES -> EAX
| CS -> ECX
| SS -> EDX
| DS -> EBX
| FS -> ESP
| GS -> EBP

(** val enc_condition_type : condition_type -> bool list **)

let enc_condition_type = function
| O_ct -> s2bl ('0'::('0'::('0'::('0'::[]))))
| NO_ct -> s2bl ('0'::('0'::('0'::('1'::[]))))
| B_ct -> s2bl ('0'::('0'::('1'::('0'::[]))))
| NB_ct -> s2bl ('0'::('0'::('1'::('1'::[]))))
| E_ct -> s2bl ('0'::('1'::('0'::('0'::[]))))
| NE_ct -> s2bl ('0'::('1'::('0'::('1'::[]))))
| BE_ct -> s2bl ('0'::('1'::('1'::('0'::[]))))
| NBE_ct -> s2bl ('0'::('1'::('1'::('1'::[]))))
| S_ct -> s2bl ('1'::('0'::('0'::('0'::[]))))
| NS_ct -> s2bl ('1'::('0'::('0'::('1'::[]))))
| P_ct -> s2bl ('1'::('0'::('1'::('0'::[]))))
| NP_ct -> s2bl ('1'::('0'::('1'::('1'::[]))))
| L_ct -> s2bl ('1'::('1'::('0'::('0'::[]))))
| NL_ct -> s2bl ('1'::('1'::('0'::('1'::[]))))
| LE_ct -> s2bl ('1'::('1'::('1'::('0'::[]))))
| NLE_ct -> s2bl ('1'::('1'::('1'::('1'::[]))))

(** val enc_scale : scale -> bool list **)

let enc_scale = function
| Scale1 -> s2bl ('0'::('0'::[]))
| Scale2 -> s2bl ('0'::('1'::[]))
| Scale4 -> s2bl ('1'::('0'::[]))
| Scale8 -> s2bl ('1'::('1'::[]))

(** val enc_SIB :
    register -> (scale * register) option -> bool list coq_Enc **)

let enc_SIB bs idxopt =
  match bs with
  | ESP ->
    (match idxopt with
     | Some p ->
       let (sc, idx) = p in
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match idx with
          | ESP -> invalid
          | _ ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (enc_scale sc) (enc_reg idx))) (fun si ->
         coq_Return (Obj.magic coq_EncodingMonad) (app si (enc_reg bs)))
     | None ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app (s2bl ('0'::('0'::[])))
           (app (s2bl ('1'::('0'::('0'::[]))))
             (s2bl ('1'::('0'::('0'::[])))))))
  | _ ->
    (match idxopt with
     | Some p ->
       let (sc, idx) = p in
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match idx with
          | ESP -> invalid
          | _ ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (enc_scale sc) (enc_reg idx))) (fun si ->
         coq_Return (Obj.magic coq_EncodingMonad) (app si (enc_reg bs)))
     | None -> invalid)

(** val int_explode : Big.big_int -> Word.int -> Big.big_int -> bool list **)

let int_explode sz i n =
  let bs = Word.bits_of_Z (Big.succ sz) i in
  let rec int_explode_aux n0 =
    Big.nat_case
      (fun _ ->
      [])
      (fun m ->
      (bs (Z.of_nat m)) :: (int_explode_aux m))
      n0
  in int_explode_aux n

(** val enc_byte : int8 -> bool list **)

let enc_byte i =
  int_explode size8 i (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ Big.zero))))))))

(** val repr_in_signed : Big.big_int -> Big.big_int -> Word.int -> bool **)

let repr_in_signed n1 n2 w =
  (&&) (proj_sumbool (zle (Word.min_signed n2) (Word.signed n1 w)))
    (proj_sumbool (zle (Word.signed n1 w) (Word.max_signed n2)))

(** val repr_in_signed_byte : int32 -> bool **)

let repr_in_signed_byte w =
  repr_in_signed (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))) (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ Big.zero))))))) w

(** val repr_in_signed_halfword : int32 -> bool **)

let repr_in_signed_halfword w =
  repr_in_signed (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))) (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))
    w

(** val enc_byte_i32 : int32 -> bool list coq_Enc **)

let enc_byte_i32 i =
  if repr_in_signed_byte i
  then coq_Return (Obj.magic coq_EncodingMonad)
         (int_explode size32 i (Big.succ (Big.succ (Big.succ (Big.succ
           (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))
  else invalid

(** val enc_halfword : int16 -> bool list **)

let enc_halfword i =
  let b0 =
    Word.coq_and size16
      (Word.shru size16 i
        (Word.repr size16 (Big.double (Big.double (Big.double Big.one)))))
      (Word.repr size16 (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone Big.one))))))))
  in
  let b1 =
    Word.coq_and size16 i
      (Word.repr size16 (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone Big.one))))))))
  in
  let hw =
    Word.coq_or size16
      (Word.shl size16 b1
        (Word.repr size16 (Big.double (Big.double (Big.double Big.one))))) b0
  in
  int_explode size16 hw (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))))

(** val enc_halfword_i32 : int32 -> bool list coq_Enc **)

let enc_halfword_i32 i =
  if repr_in_signed_halfword i
  then let b0 =
         Word.coq_and size32
           (Word.shru size32 i
             (Word.repr size32 (Big.double (Big.double (Big.double
               Big.one)))))
           (Word.repr size32 (Big.doubleplusone (Big.doubleplusone
             (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
             (Big.doubleplusone (Big.doubleplusone Big.one))))))))
       in
       let b1 =
         Word.coq_and size32 i
           (Word.repr size32 (Big.doubleplusone (Big.doubleplusone
             (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
             (Big.doubleplusone (Big.doubleplusone Big.one))))))))
       in
       let hw =
         Word.coq_or size32
           (Word.shl size32 b1
             (Word.repr size32 (Big.double (Big.double (Big.double
               Big.one))))) b0
       in
       coq_Return (Obj.magic coq_EncodingMonad)
         (int_explode size32 hw (Big.succ (Big.succ (Big.succ (Big.succ
           (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
           (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
           Big.zero)))))))))))))))))
  else invalid

(** val enc_word : Big.big_int -> Word.int -> bool list **)

let enc_word sz i =
  let b3 =
    Word.coq_and sz i
      (Word.repr sz (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone Big.one))))))))
  in
  let b2 =
    Word.coq_and sz
      (Word.shru sz i
        (Word.repr sz (Big.double (Big.double (Big.double Big.one)))))
      (Word.repr sz (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone Big.one))))))))
  in
  let b1 =
    Word.coq_and sz
      (Word.shru sz i
        (Word.repr sz (Big.double (Big.double (Big.double (Big.double
          Big.one))))))
      (Word.repr sz (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
        (Big.doubleplusone Big.one))))))))
  in
  let b0 =
    Word.shru sz i
      (Word.repr sz (Big.double (Big.double (Big.double (Big.doubleplusone
        Big.one)))))
  in
  let w1 =
    Word.shl sz b1
      (Word.repr sz (Big.double (Big.double (Big.double Big.one))))
  in
  let w2 =
    Word.shl sz b2
      (Word.repr sz (Big.double (Big.double (Big.double (Big.double
        Big.one)))))
  in
  let w3 =
    Word.shl sz b3
      (Word.repr sz (Big.double (Big.double (Big.double (Big.doubleplusone
        Big.one)))))
  in
  let hw = Word.coq_or sz w3 (Word.coq_or sz w2 (Word.coq_or sz w1 b0)) in
  int_explode sz hw (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))))

(** val enc_address : bool list -> address -> bool list coq_Enc **)

let enc_address opb addr =
  let { addrDisp = disp; addrBase = addrBase0; addrIndex = idxopt } = addr in
  (match addrBase0 with
   | Some bs ->
     let enc_r_or_m =
       match bs with
       | ESP ->
         coq_Bind coq_EncodingMonad (Obj.magic enc_SIB bs idxopt) (fun l ->
           coq_Return coq_EncodingMonad
             (app (s2bl ('1'::('0'::('0'::[])))) l))
       | _ ->
         (match idxopt with
          | Some _ ->
            coq_Bind coq_EncodingMonad (Obj.magic enc_SIB bs idxopt)
              (fun l ->
              coq_Return coq_EncodingMonad
                (app (s2bl ('1'::('0'::('0'::[])))) l))
          | None -> coq_Return coq_EncodingMonad (enc_reg bs))
     in
     coq_Bind (Obj.magic coq_EncodingMonad) (Obj.magic enc_r_or_m)
       (fun r_or_m ->
       let enc_disp_idxopt =
         if repr_in_signed_byte disp
         then coq_Bind coq_EncodingMonad (Obj.magic enc_byte_i32 disp)
                (fun d ->
                coq_Return coq_EncodingMonad
                  (app (s2bl ('0'::('1'::[]))) (app opb (app r_or_m d))))
         else coq_Return coq_EncodingMonad
                (app (s2bl ('1'::('0'::[])))
                  (app opb (app r_or_m (enc_word size32 disp))))
       in
       (match bs with
        | EBP -> Obj.magic enc_disp_idxopt
        | _ ->
          if zeq disp (Word.zero size32)
          then coq_Return (Obj.magic coq_EncodingMonad)
                 (app (s2bl ('0'::('0'::[]))) (app opb r_or_m))
          else Obj.magic enc_disp_idxopt))
   | None ->
     (match idxopt with
      | Some p ->
        let (sc, idx) = p in
        coq_Bind (Obj.magic coq_EncodingMonad)
          (match idx with
           | ESP -> invalid
           | _ ->
             coq_Return (Obj.magic coq_EncodingMonad)
               (app (enc_scale sc) (enc_reg idx))) (fun si ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('0'::('0'::[])))
              (app opb
                (app (s2bl ('1'::('0'::('0'::[]))))
                  (app si
                    (app (s2bl ('1'::('0'::('1'::[]))))
                      (enc_word size32 disp)))))))
      | None ->
        coq_Return (Obj.magic coq_EncodingMonad)
          (app (s2bl ('0'::('0'::[])))
            (app opb
              (app (s2bl ('1'::('0'::('1'::[])))) (enc_word size32 disp))))))

(** val enc_modrm_gen : bool list -> operand -> bool list coq_Enc **)

let enc_modrm_gen opb = function
| Reg_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[]))) (app opb (enc_reg r2)))
| Address_op addr -> enc_address opb addr
| _ -> invalid

(** val enc_modrm_2 : char list -> operand -> bool list coq_Enc **)

let enc_modrm_2 bs op2 =
  enc_modrm_gen (s2bl bs) op2

(** val enc_imm : bool -> bool -> int32 -> bool list coq_Enc **)

let enc_imm op_override0 w i1 =
  if op_override0
  then if w then enc_halfword_i32 i1 else enc_byte_i32 i1
  else if w
       then coq_Return (Obj.magic coq_EncodingMonad) (enc_word size32 i1)
       else enc_byte_i32 i1

(** val enc_bit : bool -> bool list **)

let enc_bit = function
| true -> s2bl ('1'::[])
| false -> s2bl ('0'::[])

(** val enc_dbit : bool -> bool list **)

let enc_dbit d =
  d :: []

(** val enc_logic_or_arith :
    char list -> char list -> bool -> bool -> operand -> operand -> bool list
    coq_Enc **)

let enc_logic_or_arith lb1 lb2 op_override0 w op1 op2 =
  match op1 with
  | Reg_op r1 ->
    (match r1 with
     | EAX ->
       (match op2 with
        | Imm_op i1 ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i1)
            (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl lb1)
                (app (s2bl ('1'::('0'::[]))) (app (enc_bit w) l1))))
        | Offset_op _ -> invalid
        | _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op1 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op2
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl lb1)
                (app (s2bl ('0'::[]))
                  (app (enc_dbit true) (app (enc_bit w) l1))))))
     | _ ->
       (match op2 with
        | Imm_op i1 ->
          if op_override0
          then if w
               then coq_Bind (Obj.magic coq_EncodingMonad)
                      (enc_modrm_2 lb2 op1) (fun l1 ->
                      if repr_in_signed_byte i1
                      then coq_Bind (Obj.magic coq_EncodingMonad)
                             (enc_byte_i32 i1) (fun l_i1 ->
                             coq_Return (Obj.magic coq_EncodingMonad)
                               (app
                                 (s2bl
                                   ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                                 (app l1 l_i1)))
                      else coq_Bind (Obj.magic coq_EncodingMonad)
                             (enc_halfword_i32 i1) (fun l_i1 ->
                             coq_Return (Obj.magic coq_EncodingMonad)
                               (app
                                 (s2bl
                                   ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                                 (app l1 l_i1))))
               else coq_Bind (Obj.magic coq_EncodingMonad)
                      (enc_modrm_2 lb2 op1) (fun l1 ->
                      coq_Bind (Obj.magic coq_EncodingMonad)
                        (enc_byte_i32 i1) (fun l_i1 ->
                        coq_Return (Obj.magic coq_EncodingMonad)
                          (app
                            (s2bl
                              ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                            (app l1 l_i1))))
          else if w
               then coq_Bind (Obj.magic coq_EncodingMonad)
                      (enc_modrm_2 lb2 op1) (fun l1 ->
                      if repr_in_signed_byte i1
                      then coq_Bind (Obj.magic coq_EncodingMonad)
                             (enc_byte_i32 i1) (fun l_i1 ->
                             coq_Return (Obj.magic coq_EncodingMonad)
                               (app
                                 (s2bl
                                   ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                                 (app l1 l_i1)))
                      else coq_Return (Obj.magic coq_EncodingMonad)
                             (app
                               (s2bl
                                 ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                               (app l1 (enc_word size32 i1))))
               else coq_Bind (Obj.magic coq_EncodingMonad)
                      (enc_modrm_2 lb2 op1) (fun l1 ->
                      coq_Bind (Obj.magic coq_EncodingMonad)
                        (enc_byte_i32 i1) (fun l_i1 ->
                        coq_Return (Obj.magic coq_EncodingMonad)
                          (app
                            (s2bl
                              ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                            (app l1 l_i1))))
        | Offset_op _ -> invalid
        | _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op1 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op2
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl lb1)
                (app (s2bl ('0'::[]))
                  (app (enc_dbit true) (app (enc_bit w) l1)))))))
  | Address_op _ ->
    (match op2 with
     | Imm_op i1 ->
       if op_override0
       then if w
            then coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   if repr_in_signed_byte i1
                   then coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_byte_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                              (app l1 l_i1)))
                   else coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_halfword_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                              (app l1 l_i1))))
            else coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 i1)
                     (fun l_i1 ->
                     coq_Return (Obj.magic coq_EncodingMonad)
                       (app
                         (s2bl
                           ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                         (app l1 l_i1))))
       else if w
            then coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   if repr_in_signed_byte i1
                   then coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_byte_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                              (app l1 l_i1)))
                   else coq_Return (Obj.magic coq_EncodingMonad)
                          (app
                            (s2bl
                              ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                            (app l1 (enc_word size32 i1))))
            else coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 i1)
                     (fun l_i1 ->
                     coq_Return (Obj.magic coq_EncodingMonad)
                       (app
                         (s2bl
                           ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                         (app l1 l_i1))))
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app (s2bl lb1)
             (app (s2bl ('0'::[]))
               (app (enc_dbit false) (app (enc_bit w) l1)))))
     | _ -> invalid)
  | _ ->
    (match op2 with
     | Imm_op i1 ->
       if op_override0
       then if w
            then coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   if repr_in_signed_byte i1
                   then coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_byte_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                              (app l1 l_i1)))
                   else coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_halfword_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                              (app l1 l_i1))))
            else coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 i1)
                     (fun l_i1 ->
                     coq_Return (Obj.magic coq_EncodingMonad)
                       (app
                         (s2bl
                           ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                         (app l1 l_i1))))
       else if w
            then coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   if repr_in_signed_byte i1
                   then coq_Bind (Obj.magic coq_EncodingMonad)
                          (enc_byte_i32 i1) (fun l_i1 ->
                          coq_Return (Obj.magic coq_EncodingMonad)
                            (app
                              (s2bl
                                ('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))
                              (app l1 l_i1)))
                   else coq_Return (Obj.magic coq_EncodingMonad)
                          (app
                            (s2bl
                              ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))
                            (app l1 (enc_word size32 i1))))
            else coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb2 op1)
                   (fun l1 ->
                   coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 i1)
                     (fun l_i1 ->
                     coq_Return (Obj.magic coq_EncodingMonad)
                       (app
                         (s2bl
                           ('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))
                         (app l1 l_i1))))
     | _ -> invalid)

(** val enc_BitScan : operand -> operand -> bool list -> bool list coq_Enc **)

let enc_BitScan op1 op2 lb =
  match op1 with
  | Reg_op r1 ->
    (match op2 with
     | Reg_op r2 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app lb
           (app (s2bl ('1'::('1'::[]))) (app (enc_reg r1) (enc_reg r2))))
     | _ -> invalid)
  | Address_op _ ->
    (match op2 with
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad) (app lb l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_bit_test :
    char list -> char list -> operand -> operand -> bool list coq_Enc **)

let enc_bit_test lb1 lb2 op1 op2 = match op2 with
| Imm_op i1 ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb1 op1) (fun l1 ->
    coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm false false i1)
      (fun l_i1 ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl
            ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))))
          (app l1 l_i1))))
| _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op2 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::[])))))))))
        (app (s2bl ('1'::('0'::('1'::[]))))
          (app (s2bl lb2) (app (s2bl ('0'::('1'::('1'::[])))) l1)))))

(** val enc_div_mul : bool -> operand -> char list -> bool list coq_Enc **)

let enc_div_mul w op1 lb =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_2 lb op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
        (app (enc_bit w) l1)))

(** val enc_Rotate :
    bool -> operand -> reg_or_immed -> register -> bool list coq_Enc **)

let enc_Rotate w op1 ri r =
  match ri with
  | Reg_ri r0 ->
    (match r0 with
     | ECX ->
       coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
         (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app (s2bl ('1'::('1'::('0'::('1'::('0'::('0'::('1'::[]))))))))
             (app (enc_bit w) l1)))
     | _ -> invalid)
  | Imm_ri i1 ->
    coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
      (fun l1 ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app (s2bl ('1'::('1'::('0'::('0'::('0'::('0'::('0'::[]))))))))
          (app (enc_bit w) (app l1 (enc_byte i1)))))

(** val enc_op_bool : bool -> bool list **)

let enc_op_bool = function
| true -> s2bl ('0'::[])
| false -> s2bl ('1'::[])

(** val enc_AAA : bool list coq_Enc **)

let enc_AAA =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))

(** val enc_AAD : bool list coq_Enc **)

let enc_AAD =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_AAM : bool list coq_Enc **)

let enc_AAM =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_AAS : bool list coq_Enc **)

let enc_AAS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))

(** val enc_ADC : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_ADC =
  enc_logic_or_arith ('0'::('0'::('0'::('1'::('0'::[])))))
    ('0'::('1'::('0'::[])))

(** val enc_ADD : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_ADD =
  enc_logic_or_arith ('0'::('0'::('0'::('0'::('0'::[])))))
    ('0'::('0'::('0'::[])))

(** val enc_AND : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_AND =
  enc_logic_or_arith ('0'::('0'::('1'::('0'::('0'::[])))))
    ('1'::('0'::('0'::[])))

(** val enc_ARPL : operand -> operand -> bool list coq_Enc **)

let enc_ARPL op1 op2 =
  match op1 with
  | Reg_op r1 ->
    (match op2 with
     | Reg_op r2 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::[])))))))))))
           (app (enc_reg r1) (enc_reg r2)))
     | Address_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::[])))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_BOUND : operand -> operand -> bool list coq_Enc **)

let enc_BOUND op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('0'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::[])))))))))
        l1))

(** val enc_BSF : operand -> operand -> bool list coq_Enc **)

let enc_BSF op1 op2 =
  enc_BitScan op1 op2
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))))

(** val enc_BSR : operand -> operand -> bool list coq_Enc **)

let enc_BSR op1 op2 =
  enc_BitScan op1 op2
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::[])))))))))))))))))

(** val enc_BSWAP : register -> bool list coq_Enc **)

let enc_BSWAP r =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::[]))))))))))))))
      (enc_reg r))

(** val enc_BT : operand -> operand -> bool list coq_Enc **)

let enc_BT =
  enc_bit_test ('1'::('0'::('0'::[]))) ('0'::('0'::[]))

(** val enc_BTC : operand -> operand -> bool list coq_Enc **)

let enc_BTC =
  enc_bit_test ('1'::('1'::('1'::[]))) ('1'::('1'::[]))

(** val enc_BTR : operand -> operand -> bool list coq_Enc **)

let enc_BTR =
  enc_bit_test ('1'::('1'::('0'::[]))) ('1'::('0'::[]))

(** val enc_BTS : operand -> operand -> bool list coq_Enc **)

let enc_BTS =
  enc_bit_test ('1'::('0'::('1'::[]))) ('0'::('1'::[]))

(** val enc_CALL :
    bool -> bool -> operand -> selector option -> bool list coq_Enc **)

let enc_CALL near absolute op1 sel =
  if near
  then if absolute
       then (match sel with
             | Some _ -> invalid
             | None ->
               coq_Bind (Obj.magic coq_EncodingMonad)
                 (enc_modrm_2 ('0'::('1'::('0'::[]))) op1) (fun l1 ->
                 coq_Return (Obj.magic coq_EncodingMonad)
                   (app
                     (s2bl
                       ('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
                     l1)))
       else (match sel with
             | Some _ -> invalid
             | None ->
               (match op1 with
                | Imm_op i1 ->
                  coq_Return (Obj.magic coq_EncodingMonad)
                    (app
                      (s2bl
                        ('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))
                      (enc_word size32 i1))
                | _ -> invalid))
  else if absolute
       then (match sel with
             | Some sel0 ->
               (match op1 with
                | Imm_op i1 ->
                  coq_Return (Obj.magic coq_EncodingMonad)
                    (app
                      (s2bl
                        ('1'::('0'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
                      (app (enc_word size32 i1) (enc_halfword sel0)))
                | _ -> invalid)
             | None ->
               coq_Bind (Obj.magic coq_EncodingMonad)
                 (enc_modrm_2 ('0'::('1'::('1'::[]))) op1) (fun l1 ->
                 coq_Return (Obj.magic coq_EncodingMonad)
                   (app
                     (s2bl
                       ('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
                     l1)))
       else invalid

(** val enc_CDQ : bool list coq_Enc **)

let enc_CDQ =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))

(** val enc_CLC : bool list coq_Enc **)

let enc_CLC =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))

(** val enc_CLD : bool list coq_Enc **)

let enc_CLD =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::[])))))))))

(** val enc_CLI : bool list coq_Enc **)

let enc_CLI =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::[])))))))))

(** val enc_CLTS : bool list coq_Enc **)

let enc_CLTS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::('0'::[])))))))))))))))))

(** val enc_CMC : bool list coq_Enc **)

let enc_CMC =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::[])))))))))

(** val enc_CMOVcc :
    condition_type -> operand -> operand -> bool list coq_Enc **)

let enc_CMOVcc ct op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))
        (app (enc_condition_type ct) l1)))

(** val enc_CMP : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_CMP =
  enc_logic_or_arith ('0'::('0'::('1'::('1'::('1'::[])))))
    ('1'::('1'::('1'::[])))

(** val enc_CMPS : bool -> bool list coq_Enc **)

let enc_CMPS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('0'::('1'::('0'::('0'::('1'::('1'::[]))))))))
      (enc_bit w))

(** val enc_CMPXCHG : bool -> operand -> operand -> bool list coq_Enc **)

let enc_CMPXCHG w op1 op2 =
  match op1 with
  | Reg_op r1 ->
    (match op2 with
     | Reg_op r2 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[]))))))))))))))))
           (app (enc_bit w)
             (app (s2bl ('1'::('1'::[]))) (app (enc_reg r2) (enc_reg r1)))))
     | _ -> invalid)
  | Address_op _ ->
    (match op2 with
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[]))))))))))))))))
             (app (enc_bit w) l1)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CPUID : bool list coq_Enc **)

let enc_CPUID =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_CWDE : bool list coq_Enc **)

let enc_CWDE =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))

(** val enc_DAA : bool list coq_Enc **)

let enc_DAA =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('1'::('0'::('0'::('1'::('1'::('1'::[])))))))))

(** val enc_DAS : bool list coq_Enc **)

let enc_DAS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))

(** val enc_DEC : bool -> operand -> bool list coq_Enc **)

let enc_DEC w op1 = match op1 with
| Reg_op r ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))
      (app (enc_bit w)
        (app (s2bl ('1'::('1'::('0'::('0'::('1'::[])))))) (enc_reg r))))
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ECX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))
        (app (enc_bit w) l1)))
| _ -> invalid

(** val enc_DIV : bool -> operand -> bool list coq_Enc **)

let enc_DIV w op1 =
  enc_div_mul w op1 ('1'::('1'::('0'::[])))

(** val enc_HLT : bool list coq_Enc **)

let enc_HLT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))

(** val enc_IDIV : bool -> operand -> bool list coq_Enc **)

let enc_IDIV w op1 =
  enc_div_mul w op1 ('1'::('1'::('1'::[])))

(** val enc_IMUL :
    bool -> bool -> operand -> operand option -> int32 option -> bool list
    coq_Enc **)

let enc_IMUL op_override0 w op1 opopt iopt =
  match opopt with
  | Some op2 ->
    (match iopt with
     | Some imm3 ->
       if repr_in_signed_byte imm3
       then coq_Bind (Obj.magic coq_EncodingMonad)
              (match op1 with
               | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
               | _ -> invalid) (fun l1 ->
              coq_Bind (Obj.magic coq_EncodingMonad)
                (enc_imm op_override0 false imm3) (fun l_imm3 ->
                coq_Return (Obj.magic coq_EncodingMonad)
                  (app
                    (s2bl
                      ('0'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::[])))))))))
                    (app l1 l_imm3))))
       else coq_Bind (Obj.magic coq_EncodingMonad)
              (match op1 with
               | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
               | _ -> invalid) (fun l1 ->
              coq_Bind (Obj.magic coq_EncodingMonad)
                (enc_imm op_override0 true imm3) (fun l_imm3 ->
                coq_Return (Obj.magic coq_EncodingMonad)
                  (app
                    (s2bl
                      ('0'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::[])))))))))
                    (app l1 l_imm3))))
     | None ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1)))
  | None ->
    (match iopt with
     | Some _ -> invalid
     | None ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (enc_modrm_2 ('1'::('0'::('1'::[]))) op1) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
             (app (enc_bit w) l1))))

(** val enc_IN : bool -> port_number option -> bool list coq_Enc **)

let enc_IN w = function
| Some imm8 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('1'::('0'::[]))))))))
      (app (enc_bit w) (enc_byte imm8)))
| None ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('1'::('1'::('0'::[]))))))))
      (enc_bit w))

(** val enc_INC : bool -> operand -> bool list coq_Enc **)

let enc_INC w op1 = match op1 with
| Reg_op r ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))
      (app (enc_bit w)
        (app (s2bl ('1'::('1'::('0'::('0'::('0'::[])))))) (enc_reg r))))
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EAX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))
        (app (enc_bit w) l1)))
| _ -> invalid

(** val enc_INS : bool -> bool list coq_Enc **)

let enc_INS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('0'::('1'::('1'::('0'::('1'::('1'::('0'::[]))))))))
      (enc_bit w))

(** val enc_INT : bool list coq_Enc **)

let enc_INT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::[])))))))))

(** val enc_INTn : interrupt_type -> bool list coq_Enc **)

let enc_INTn it =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('0'::('0'::('1'::('1'::('0'::('1'::[])))))))))
      (enc_byte it))

(** val enc_INTO : bool list coq_Enc **)

let enc_INTO =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::[])))))))))

(** val enc_INVD : bool list coq_Enc **)

let enc_INVD =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_INVLPG : operand -> bool list coq_Enc **)

let enc_INVLPG op1 = match op1 with
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EDI in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_IRET : bool list coq_Enc **)

let enc_IRET =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::[])))))))))

(** val enc_Jcc : condition_type -> int32 -> bool list coq_Enc **)

let enc_Jcc ct disp =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))
      (app (enc_condition_type ct) (enc_word size32 disp)))

(** val enc_JCXZ : int8 -> bool list coq_Enc **)

let enc_JCXZ b =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::[])))))))))
      (enc_byte b))

(** val enc_JMP :
    bool -> bool -> operand -> selector option -> bool list coq_Enc **)

let enc_JMP near absolute op1 sel =
  if near
  then if absolute
       then (match sel with
             | Some _ -> invalid
             | None ->
               coq_Bind (Obj.magic coq_EncodingMonad)
                 (enc_modrm_2 ('1'::('0'::('0'::[]))) op1) (fun l1 ->
                 coq_Return (Obj.magic coq_EncodingMonad)
                   (app
                     (s2bl
                       ('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
                     l1)))
       else (match sel with
             | Some _ -> invalid
             | None ->
               (match op1 with
                | Imm_op i1 ->
                  if repr_in_signed_byte i1
                  then coq_Bind (Obj.magic coq_EncodingMonad)
                         (enc_byte_i32 i1) (fun l_i1 ->
                         coq_Return (Obj.magic coq_EncodingMonad)
                           (app
                             (s2bl
                               ('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::[])))))))))
                             l_i1))
                  else coq_Return (Obj.magic coq_EncodingMonad)
                         (app
                           (s2bl
                             ('1'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::[])))))))))
                           (enc_word size32 i1))
                | _ -> invalid))
  else if absolute
       then (match sel with
             | Some sel0 ->
               (match op1 with
                | Imm_op i1 ->
                  coq_Return (Obj.magic coq_EncodingMonad)
                    (app
                      (s2bl
                        ('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))
                      (app (enc_word size32 i1) (enc_halfword sel0)))
                | _ -> invalid)
             | None ->
               coq_Bind (Obj.magic coq_EncodingMonad)
                 (enc_modrm_2 ('1'::('0'::('1'::[]))) op1) (fun l1 ->
                 coq_Return (Obj.magic coq_EncodingMonad)
                   (app
                     (s2bl
                       ('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
                     l1)))
       else invalid

(** val enc_LAHF : bool list coq_Enc **)

let enc_LAHF =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))

(** val enc_LAR : operand -> operand -> bool list coq_Enc **)

let enc_LAR op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::[])))))))))))))))))
        l1))

(** val enc_LDS : operand -> operand -> bool list coq_Enc **)

let enc_LDS op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::[])))))))))
        l1))

(** val enc_LEA : operand -> operand -> bool list coq_Enc **)

let enc_LEA op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('0'::('0'::('0'::('1'::('1'::('0'::('1'::[])))))))))
        l1))

(** val enc_LEAVE : bool list coq_Enc **)

let enc_LEAVE =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('0'::('0'::('1'::('0'::('0'::('1'::[])))))))))

(** val enc_LES : operand -> operand -> bool list coq_Enc **)

let enc_LES op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::[])))))))))
        l1))

(** val enc_LFS : operand -> operand -> bool list coq_Enc **)

let enc_LFS op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::('0'::[]))))))))))))))))
        l1))

(** val enc_LGDT : operand -> bool list coq_Enc **)

let enc_LGDT op1 = match op1 with
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EDX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_LGS : operand -> operand -> bool list coq_Enc **)

let enc_LGS op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))
        l1))

(** val enc_LIDT : operand -> bool list coq_Enc **)

let enc_LIDT op1 = match op1 with
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EBX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_LLDT : operand -> bool list coq_Enc **)

let enc_LLDT op1 = match op1 with
| Reg_op r1 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::('0'::('1'::('0'::[]))))))))))))))))))))))
      (enc_reg r1))
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EDX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[]))))))))))))))))
        l1))
| _ -> invalid

(** val enc_LMSW : operand -> bool list coq_Enc **)

let enc_LMSW op1 = match op1 with
| Reg_op r1 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::[]))))))))))))))))))))))
      (enc_reg r1))
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ESI in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[]))))))))))))))))
        l1))
| _ -> invalid

(** val enc_LODS : bool -> bool list coq_Enc **)

let enc_LODS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('0'::('1'::('0'::('1'::('1'::('0'::[]))))))))
      (enc_bit w))

(** val enc_LOOP : int8 -> bool list coq_Enc **)

let enc_LOOP disp =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::[])))))))))
      (enc_byte disp))

(** val enc_LOOPNZ : int8 -> bool list coq_Enc **)

let enc_LOOPNZ disp =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))
      (enc_byte disp))

(** val enc_LOOPZ : int8 -> bool list coq_Enc **)

let enc_LOOPZ disp =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::[])))))))))
      (enc_byte disp))

(** val enc_LSL : operand -> operand -> bool list coq_Enc **)

let enc_LSL op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::[])))))))))))))))))
        l1))

(** val enc_LSS : operand -> operand -> bool list coq_Enc **)

let enc_LSS op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))
        l1))

(** val enc_LTR : operand -> bool list coq_Enc **)

let enc_LTR op1 = match op1 with
| Reg_op r1 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::('0'::('1'::('1'::[]))))))))))))))))))))))
      (enc_reg r1))
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EBX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[]))))))))))))))))
        l1))
| _ -> invalid

(** val enc_MOV : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_MOV op_override0 w op1 op2 =
  match op1 with
  | Imm_op _ -> invalid
  | Reg_op r1 ->
    (match r1 with
     | EAX ->
       (match op2 with
        | Imm_op i1 ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i1)
            (fun l_i1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('1'::('1'::[])))))
                (app (enc_bit w) (app (enc_reg r1) l_i1))))
        | Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('1'::('0'::('0'::[]))))))))
                (app (enc_bit w) l1)))
        | Address_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op1 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op2
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('1'::('0'::('1'::[]))))))))
                (app (enc_bit w) l1)))
        | Offset_op o1 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('1'::('0'::('1'::('0'::('0'::('0'::('0'::[]))))))))
              (app (enc_bit w) (enc_word size32 o1))))
     | _ ->
       (match op2 with
        | Imm_op i1 ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i1)
            (fun l_i1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('1'::('1'::[])))))
                (app (enc_bit w) (app (enc_reg r1) l_i1))))
        | Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('1'::('0'::('0'::[]))))))))
                (app (enc_bit w) l1)))
        | Address_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op1 with
             | Reg_op r2 -> enc_modrm_gen (enc_reg r2) op2
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('1'::('0'::('1'::[]))))))))
                (app (enc_bit w) l1)))
        | Offset_op _ -> invalid))
  | Address_op _ ->
    (match op2 with
     | Imm_op i1 ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (enc_modrm_2 ('0'::('0'::('0'::[]))) op1) (fun l1 ->
         coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i1)
           (fun l_i1 ->
           coq_Return (Obj.magic coq_EncodingMonad)
             (app (s2bl ('1'::('1'::('0'::('0'::('0'::('1'::('1'::[]))))))))
               (app (enc_bit w) (app l1 l_i1)))))
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app (s2bl ('1'::('0'::('0'::('0'::('1'::('0'::('0'::[]))))))))
             (app (enc_bit w) l1)))
     | _ -> invalid)
  | Offset_op o1 ->
    (match op2 with
     | Reg_op r ->
       (match r with
        | EAX ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('1'::('0'::('1'::('0'::('0'::('0'::('1'::[]))))))))
              (app (enc_bit w) (enc_word size32 o1)))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_MOVBE : operand -> operand -> bool list coq_Enc **)

let enc_MOVBE op1 op2 =
  match op1 with
  | Reg_op _ ->
    (match op2 with
     | Address_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | Address_op _ ->
    (match op2 with
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVCR :
    bool -> control_register -> register -> bool list coq_Enc **)

let enc_MOVCR direction cr r =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))
      (app (enc_bit direction)
        (app (s2bl ('0'::('1'::('1'::[]))))
          (app (enc_control_reg cr) (enc_reg r)))))

(** val enc_MOVDR :
    bool -> debug_register -> register -> bool list coq_Enc **)

let enc_MOVDR direction dr r =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app
      (s2bl
        ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))
      (app (enc_bit direction)
        (app (s2bl ('1'::('1'::('1'::[]))))
          (app (enc_debug_reg dr) (enc_reg r)))))

(** val enc_MOVS : bool -> bool list coq_Enc **)

let enc_MOVS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('0'::('1'::('0'::('0'::('1'::('0'::[]))))))))
      (enc_bit w))

(** val enc_MOVSR :
    bool -> segment_register -> operand -> bool list coq_Enc **)

let enc_MOVSR direction sr op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = sreg3_2_reg sr in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('0'::('0'::('0'::('1'::('1'::[])))))))
        (app (enc_bit direction) (app (s2bl ('0'::[])) l1))))

(** val enc_MOVSX : bool -> operand -> operand -> bool list coq_Enc **)

let enc_MOVSX w op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[]))))))))))))))))
        (app (enc_bit w) l1)))

(** val enc_MOVZX : bool -> operand -> operand -> bool list coq_Enc **)

let enc_MOVZX w op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op1 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op2
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[]))))))))))))))))
        (app (enc_bit w) l1)))

(** val enc_MUL : bool -> operand -> bool list coq_Enc **)

let enc_MUL w op1 =
  enc_div_mul w op1 ('1'::('0'::('0'::[])))

(** val enc_NEG : bool -> operand -> bool list coq_Enc **)

let enc_NEG w op =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EBX in enc_modrm_gen (enc_reg r1) op) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
        (app (enc_bit w) l1)))

(** val enc_NOP : operand -> bool list coq_Enc **)

let enc_NOP op =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EAX in enc_modrm_gen (enc_reg r1) op) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))
        l1))

(** val enc_NOT : bool -> operand -> bool list coq_Enc **)

let enc_NOT w op =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EDX in enc_modrm_gen (enc_reg r1) op) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
        (app (enc_bit w) l1)))

(** val enc_OR : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_OR =
  enc_logic_or_arith ('0'::('0'::('0'::('0'::('1'::[])))))
    ('0'::('0'::('1'::[])))

(** val enc_OUT : bool -> port_number option -> bool list coq_Enc **)

let enc_OUT w = function
| Some p0 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('0'::('1'::('1'::[]))))))))
      (app (enc_bit w) (enc_byte p0)))
| None ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('1'::('0'::('1'::('1'::('1'::[]))))))))
      (enc_bit w))

(** val enc_OUTS : bool -> bool list coq_Enc **)

let enc_OUTS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('0'::('1'::('1'::('0'::('1'::('1'::('1'::[]))))))))
      (enc_bit w))

(** val enc_POP : operand -> bool list coq_Enc **)

let enc_POP op1 = match op1 with
| Reg_op r1 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('0'::('1'::('0'::('1'::('1'::[])))))) (enc_reg r1))
| _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_modrm_2 ('0'::('0'::('0'::[]))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::[])))))))))
        l1))

(** val enc_POPA : bool list coq_Enc **)

let enc_POPA =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::[])))))))))

(** val enc_POPF : bool list coq_Enc **)

let enc_POPF =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))

(** val enc_POPSR : segment_register -> bool list coq_Enc **)

let enc_POPSR = function
| ES ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::[])))))))))
| CS -> invalid
| SS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('1'::('0'::('1'::('1'::('1'::[])))))))))
| DS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
| FS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
| GS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_PUSH : bool -> operand -> bool list coq_Enc **)

let enc_PUSH w op1 =
  if w
  then (match op1 with
        | Imm_op i1 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app
              (s2bl
                ('0'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))
              (enc_word size32 i1))
        | Reg_op r1 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('0'::('1'::('0'::('1'::('0'::[])))))) (enc_reg r1))
        | Address_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_modrm_2 ('1'::('1'::('0'::[]))) op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))
                l1))
        | Offset_op _ -> invalid)
  else (match op1 with
        | Imm_op i1 ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm false false i1)
            (fun l_i1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))
                l_i1))
        | _ -> invalid)

(** val enc_PUSHA : bool list coq_Enc **)

let enc_PUSHA =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))

(** val enc_PUSHF : bool list coq_Enc **)

let enc_PUSHF =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))

(** val enc_PUSHSR : segment_register -> bool list coq_Enc **)

let enc_PUSHSR = function
| ES ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('0'::('0'::('1'::('1'::('0'::[])))))))))
| CS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('0'::[])))))))))
| SS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::[])))))))))
| DS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))
| FS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
| GS ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_RCL : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_RCL w op1 ri =
  enc_Rotate w op1 ri EDX

(** val enc_RCR : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_RCR w op1 ri =
  enc_Rotate w op1 ri EBX

(** val enc_RDMSR : bool list coq_Enc **)

let enc_RDMSR =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_RDPMC : bool list coq_Enc **)

let enc_RDPMC =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_RDTSC : bool list coq_Enc **)

let enc_RDTSC =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_RDTSCP : bool list coq_Enc **)

let enc_RDTSCP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))))))))))))

(** val enc_RET : bool -> int16 option -> bool list coq_Enc **)

let enc_RET same_segment = function
| Some disp0 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('0'::('0'::[])))))
      (app (enc_op_bool same_segment)
        (app (s2bl ('0'::('1'::('0'::[])))) (enc_halfword disp0))))
| None ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::('0'::('0'::[])))))
      (app (enc_op_bool same_segment) (s2bl ('0'::('1'::('1'::[]))))))

(** val enc_ROL : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_ROL w op1 ri =
  enc_Rotate w op1 ri EAX

(** val enc_ROR : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_ROR w op1 ri =
  enc_Rotate w op1 ri ECX

(** val enc_RSM : bool list coq_Enc **)

let enc_RSM =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_SAHF : bool list coq_Enc **)

let enc_SAHF =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))

(** val enc_SAR : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_SAR w op1 ri =
  enc_Rotate w op1 ri EDI

(** val enc_SBB : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_SBB =
  enc_logic_or_arith ('0'::('0'::('0'::('1'::('1'::[])))))
    ('0'::('1'::('1'::[])))

(** val enc_SCAS : bool -> bool list coq_Enc **)

let enc_SCAS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('0'::('1'::('0'::('1'::('1'::('1'::[]))))))))
      (enc_bit w))

(** val enc_SETcc : condition_type -> operand -> bool list coq_Enc **)

let enc_SETcc ct op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EAX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))
        (app (enc_condition_type ct) l1)))

(** val enc_SGDT : operand -> bool list coq_Enc **)

let enc_SGDT op1 = match op1 with
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EAX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_SHL : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_SHL w op1 ri =
  enc_Rotate w op1 ri ESP

(** val enc_SHLD :
    operand -> register -> reg_or_immed -> bool list coq_Enc **)

let enc_SHLD op1 r = function
| Reg_ri r0 ->
  (match r0 with
   | ECX ->
     coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
       (fun l1 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::('0'::('1'::[])))))))))))))))))
           l1))
   | _ -> invalid)
| Imm_ri i1 ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
    (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::('0'::('0'::[])))))))))))))))))
        (app l1 (enc_byte i1))))

(** val enc_SHR : bool -> operand -> reg_or_immed -> bool list coq_Enc **)

let enc_SHR w op1 ri =
  enc_Rotate w op1 ri EBP

(** val enc_SHRD :
    operand -> register -> reg_or_immed -> bool list coq_Enc **)

let enc_SHRD op1 r = function
| Reg_ri r0 ->
  (match r0 with
   | ECX ->
     coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
       (fun l1 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::[])))))))))))))))))
           l1))
   | _ -> invalid)
| Imm_ri i1 ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_modrm_gen (enc_reg r) op1)
    (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::[])))))))))))))))))
        (app l1 (enc_byte i1))))

(** val enc_SIDT : operand -> bool list coq_Enc **)

let enc_SIDT op1 = match op1 with
| Address_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ECX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_SLDT : operand -> bool list coq_Enc **)

let enc_SLDT op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EAX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
        l1))

(** val enc_SMSW : operand -> bool list coq_Enc **)

let enc_SMSW op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ESP in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))
        l1))

(** val enc_STC : bool list coq_Enc **)

let enc_STC =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::[])))))))))

(** val enc_STD : bool list coq_Enc **)

let enc_STD =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::[])))))))))

(** val enc_STI : bool list coq_Enc **)

let enc_STI =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))

(** val enc_STOS : bool -> bool list coq_Enc **)

let enc_STOS w =
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('0'::('1'::('0'::('1'::('0'::('1'::[]))))))))
      (enc_bit w))

(** val enc_STR : operand -> bool list coq_Enc **)

let enc_STR op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ECX in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
        l1))

(** val enc_SUB : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_SUB =
  enc_logic_or_arith ('0'::('0'::('1'::('0'::('1'::[])))))
    ('1'::('0'::('1'::[])))

(** val enc_TEST : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_TEST op_override0 w op1 op2 =
  match op1 with
  | Imm_op i ->
    (match op2 with
     | Imm_op i0 ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (enc_modrm_2 ('0'::('0'::('0'::[]))) op1) (fun l1 ->
         coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i0)
           (fun l_i ->
           coq_Return (Obj.magic coq_EncodingMonad)
             (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
               (app (enc_bit w) (app l1 l_i)))))
     | Reg_op r ->
       (match r with
        | EAX ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i)
            (fun l_i ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('1'::('0'::('1'::('0'::('0'::[]))))))))
                (app (enc_bit w) l_i)))
        | _ -> invalid)
     | _ -> invalid)
  | Reg_op r ->
    (match r with
     | EAX ->
       (match op2 with
        | Imm_op i ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i)
            (fun l_i ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('1'::('0'::('1'::('0'::('0'::[]))))))))
                (app (enc_bit w) l_i)))
        | _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_modrm_gen (enc_reg r) op2) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('0'::('1'::('0'::[]))))))))
                (app (enc_bit w) l1))))
     | _ ->
       (match op2 with
        | Imm_op i ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_modrm_2 ('0'::('0'::('0'::[]))) op1) (fun l1 ->
            coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i)
              (fun l_i ->
              coq_Return (Obj.magic coq_EncodingMonad)
                (app
                  (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
                  (app (enc_bit w) (app l1 l_i)))))
        | _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_modrm_gen (enc_reg r) op2) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('0'::('0'::('0'::('0'::('1'::('0'::[]))))))))
                (app (enc_bit w) l1)))))
  | _ ->
    (match op2 with
     | Imm_op i ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (enc_modrm_2 ('0'::('0'::('0'::[]))) op1) (fun l1 ->
         coq_Bind (Obj.magic coq_EncodingMonad) (enc_imm op_override0 w i)
           (fun l_i ->
           coq_Return (Obj.magic coq_EncodingMonad)
             (app (s2bl ('1'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))
               (app (enc_bit w) (app l1 l_i)))))
     | _ -> invalid)

(** val enc_UD2 : bool list coq_Enc **)

let enc_UD2 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('F'::('F'::('F'::('F'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_VERR : operand -> bool list coq_Enc **)

let enc_VERR op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = ESP in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
        l1))

(** val enc_VERW : operand -> bool list coq_Enc **)

let enc_VERW op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (let r1 = EBP in enc_modrm_gen (enc_reg r1) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
        l1))

(** val enc_WBINVD : bool list coq_Enc **)

let enc_WBINVD =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_WRMSR : bool list coq_Enc **)

let enc_WRMSR =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_XADD : bool -> operand -> operand -> bool list coq_Enc **)

let enc_XADD w op1 op2 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (match op2 with
     | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
     | _ -> invalid) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[]))))))))))))))))
        (app (enc_bit w) l1)))

(** val enc_XCHG : bool -> operand -> operand -> bool list coq_Enc **)

let enc_XCHG w op1 op2 =
  match op1 with
  | Reg_op r1 ->
    (match r1 with
     | EAX ->
       (match op2 with
        | Reg_op r2 ->
          if w
          then coq_Return (Obj.magic coq_EncodingMonad)
                 (app (s2bl ('1'::('0'::('0'::('1'::('0'::[]))))))
                   (enc_reg r2))
          else coq_Return (Obj.magic coq_EncodingMonad)
                 (app
                   (s2bl ('1'::('0'::('0'::('0'::('0'::('1'::('1'::[]))))))))
                   (app (enc_bit w)
                     (app (s2bl ('1'::('1'::[])))
                       (app (enc_reg r2) (enc_reg EAX)))))
        | _ -> invalid)
     | _ ->
       (match op2 with
        | Reg_op r2 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('1'::('0'::('0'::('0'::('0'::('1'::('1'::[]))))))))
              (app (enc_bit w)
                (app (s2bl ('1'::('1'::[]))) (app (enc_reg r2) (enc_reg r1)))))
        | _ -> invalid))
  | Address_op _ ->
    (match op2 with
     | Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | Reg_op r1 -> enc_modrm_gen (enc_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app (s2bl ('1'::('0'::('0'::('0'::('0'::('1'::('1'::[]))))))))
             (app (enc_bit w) l1)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_XLAT : bool list coq_Enc **)

let enc_XLAT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::[])))))))))

(** val enc_XOR : bool -> bool -> operand -> operand -> bool list coq_Enc **)

let enc_XOR =
  enc_logic_or_arith ('0'::('0'::('1'::('1'::('0'::[])))))
    ('1'::('1'::('0'::[])))

(** val enc_mmx_reg : mmx_register -> bool list **)

let enc_mmx_reg r =
  int_explode size3 r (Big.succ (Big.succ (Big.succ Big.zero)))

(** val enc_fp_modrm : bool list -> fp_operand -> bool list coq_Enc **)

let enc_fp_modrm opb = function
| FPS_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[])))
      (app opb
        (int_explode size3 r2 (Big.succ (Big.succ (Big.succ Big.zero))))))
| FPM16_op addr -> enc_address opb addr
| FPM32_op addr -> enc_address opb addr
| FPM64_op addr -> enc_address opb addr
| FPM80_op addr -> enc_address opb addr

(** val enc_comhelper :
    bool list -> fp_operand -> bool list -> bool list coq_Enc **)

let enc_comhelper opb op2 lb =
  match op2 with
  | FPS_op i1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::('1'::[])))))))))))))
        (app lb
          (int_explode size3 i1 (Big.succ (Big.succ (Big.succ Big.zero))))))
  | FPM32_op _ ->
    coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_modrm opb op2) (fun l1 ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))
          l1))
  | FPM64_op _ ->
    coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_modrm opb op2) (fun l1 ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))
          l1))
  | _ -> invalid

(** val enc_fp_int3 : fp_operand -> bool list coq_Enc **)

let enc_fp_int3 = function
| FPS_op i1 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (int_explode size3 i1 (Big.succ (Big.succ (Big.succ Big.zero))))
| _ -> invalid

(** val enc_fp_arith :
    bool -> bool list -> bool list -> bool -> fp_operand -> bool list coq_Enc **)

let enc_fp_arith m lb opb zerod op =
  if zerod
  then (match op with
        | FPS_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op) (fun l1 ->
            let bm = if m then false else true in
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))
                (app (s2bl ('1'::('1'::('1'::[])))) (app lb (bm :: l1)))))
        | FPM32_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_modrm opb op)
            (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))
                l1))
        | FPM64_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_modrm opb op)
            (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))
                l1))
        | _ -> invalid)
  else (match op with
        | FPS_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))
                (app (s2bl ('1'::('1'::('1'::[])))) (app lb (m :: l1)))))
        | _ -> invalid)

(** val enc_F2XM1 : bool list coq_Enc **)

let enc_F2XM1 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FABS : bool list coq_Enc **)

let enc_FABS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_FADD : bool -> fp_operand -> bool list coq_Enc **)

let enc_FADD d op1 =
  if d
  then (match op1 with
        | FPS_op i1 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('1'::('1'::('0'::('1'::('1'::[]))))))
              (app (enc_bit d)
                (app
                  (s2bl ('0'::('0'::('1'::('1'::('0'::('0'::('0'::[]))))))))
                  (int_explode size3 i1 (Big.succ (Big.succ (Big.succ
                    Big.zero)))))))
        | FPM32_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))
                l1))
        | FPM64_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))
                l1))
        | _ -> invalid)
  else (match op1 with
        | FPS_op i1 ->
          coq_Return (Obj.magic coq_EncodingMonad)
            (app (s2bl ('1'::('1'::('0'::('1'::('1'::[]))))))
              (app (enc_bit d)
                (app
                  (s2bl ('0'::('0'::('1'::('1'::('0'::('0'::('0'::[]))))))))
                  (int_explode size3 i1 (Big.succ (Big.succ (Big.succ
                    Big.zero)))))))
        | _ -> invalid)

(** val enc_FADDP : fp_operand -> bool list coq_Enc **)

let enc_FADDP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[]))))))))))))))
        l1))

(** val enc_FBLD : fp_operand -> bool list coq_Enc **)

let enc_FBLD op1 = match op1 with
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FBSTP : fp_operand -> bool list coq_Enc **)

let enc_FBSTP op1 = match op1 with
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FCHS : bool list coq_Enc **)

let enc_FCHS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FCMOVcc : fp_condition_type -> fp_operand -> bool list coq_Enc **)

let enc_FCMOVcc fct op1 = match op1 with
| FPS_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    match fct with
    | B_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('0'::('0'::[])))))) l1))
    | E_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('0'::('1'::[])))))) l1))
    | BE_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('1'::('0'::[])))))) l1))
    | U_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('1'::('1'::[])))))) l1))
    | NB_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('0'::('0'::[])))))) l1))
    | NE_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('0'::('1'::[])))))) l1))
    | NBE_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('1'::('0'::[])))))) l1))
    | NU_fct ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
          (app (s2bl ('1'::('1'::('0'::('1'::('1'::[])))))) l1)))
| _ -> invalid

(** val enc_FCOM : fp_operand -> bool list coq_Enc **)

let enc_FCOM op1 =
  enc_comhelper (s2bl ('0'::('1'::('0'::[])))) op1 (s2bl ('0'::[]))

(** val enc_FCOMP : fp_operand -> bool list coq_Enc **)

let enc_FCOMP op1 =
  enc_comhelper (s2bl ('0'::('1'::('1'::[])))) op1 (s2bl ('1'::[]))

(** val enc_FCOMPP : bool list coq_Enc **)

let enc_FCOMPP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_FCOMIP : fp_operand -> bool list coq_Enc **)

let enc_FCOMIP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::[]))))))))))))))
        l1))

(** val enc_FCOS : bool list coq_Enc **)

let enc_FCOS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))

(** val enc_FDECSTP : bool list coq_Enc **)

let enc_FDECSTP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))))

(** val enc_FDIV : bool -> fp_operand -> bool list coq_Enc **)

let enc_FDIV =
  enc_fp_arith true (s2bl ('1'::[])) (s2bl ('1'::('1'::('0'::[]))))

(** val enc_FDIVP : fp_operand -> bool list coq_Enc **)

let enc_FDIVP fp1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 fp1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[]))))))))))))))
        l1))

(** val enc_FDIVR : bool -> fp_operand -> bool list coq_Enc **)

let enc_FDIVR =
  enc_fp_arith false (s2bl ('1'::[])) (s2bl ('1'::('1'::('1'::[]))))

(** val enc_FDIVRP : fp_operand -> bool list coq_Enc **)

let enc_FDIVRP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::[]))))))))))))))
        l1))

(** val enc_FFREE : fp_operand -> bool list coq_Enc **)

let enc_FFREE op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::('0'::[]))))))))))))))
        l1))

(** val enc_FI_instrs : char list -> fp_operand -> bool list coq_Enc **)

let enc_FI_instrs s op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_modrm (s2bl s) op1)
    (fun l1 ->
    match op1 with
    | FPM16_op _ ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))
          l1)
    | FPM32_op _ ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))
          l1)
    | _ -> invalid)

(** val enc_FIADD : fp_operand -> bool list coq_Enc **)

let enc_FIADD =
  enc_FI_instrs ('0'::('0'::('0'::[])))

(** val enc_FICOM : fp_operand -> bool list coq_Enc **)

let enc_FICOM =
  enc_FI_instrs ('0'::('1'::('0'::[])))

(** val enc_FICOMP : fp_operand -> bool list coq_Enc **)

let enc_FICOMP =
  enc_FI_instrs ('0'::('1'::('1'::[])))

(** val enc_FIDIV : fp_operand -> bool list coq_Enc **)

let enc_FIDIV =
  enc_FI_instrs ('1'::('1'::('0'::[])))

(** val enc_FIDIVR : fp_operand -> bool list coq_Enc **)

let enc_FIDIVR =
  enc_FI_instrs ('1'::('1'::('1'::[])))

(** val enc_FILD : fp_operand -> bool list coq_Enc **)

let enc_FILD op1 = match op1 with
| FPM16_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
        l1))
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FIMUL : fp_operand -> bool list coq_Enc **)

let enc_FIMUL =
  enc_FI_instrs ('0'::('0'::('1'::[])))

(** val enc_FINCSTP : bool list coq_Enc **)

let enc_FINCSTP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))

(** val enc_FIST : fp_operand -> bool list coq_Enc **)

let enc_FIST op1 =
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('0'::[])))) op1) (fun l1 ->
    match op1 with
    | FPM16_op _ ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
          l1)
    | FPM32_op _ ->
      coq_Return (Obj.magic coq_EncodingMonad)
        (app
          (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
          l1)
    | _ -> invalid)

(** val enc_FISTP : fp_operand -> bool list coq_Enc **)

let enc_FISTP op1 = match op1 with
| FPM16_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
        l1))
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FISUB : fp_operand -> bool list coq_Enc **)

let enc_FISUB =
  enc_FI_instrs ('1'::('0'::('0'::[])))

(** val enc_FISUBR : fp_operand -> bool list coq_Enc **)

let enc_FISUBR =
  enc_FI_instrs ('1'::('0'::('1'::[])))

(** val enc_FLD : fp_operand -> bool list coq_Enc **)

let enc_FLD op1 = match op1 with
| FPS_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::('0'::('0'::[]))))))))))))))
        l1))
| FPM16_op _ -> invalid
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))
        l1))
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| FPM80_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
        l1))

(** val enc_FLD1 : bool list coq_Enc **)

let enc_FLD1 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FLDCW : fp_operand -> bool list coq_Enc **)

let enc_FLDCW op1 = match op1 with
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FLDENV : fp_operand -> bool list coq_Enc **)

let enc_FLDENV op1 = match op1 with
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FLDL2E : bool list coq_Enc **)

let enc_FLDL2E =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_FLDL2T : bool list coq_Enc **)

let enc_FLDL2T =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_FLDLG2 : bool list coq_Enc **)

let enc_FLDLG2 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::[])))))))))))))))))

(** val enc_FLDLN2 : bool list coq_Enc **)

let enc_FLDLN2 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::[])))))))))))))))))

(** val enc_FLDPI : bool list coq_Enc **)

let enc_FLDPI =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_FLDZ : bool list coq_Enc **)

let enc_FLDZ =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))

(** val enc_FMUL : bool -> fp_operand -> bool list coq_Enc **)

let enc_FMUL d op1 =
  if d
  then (match op1 with
        | FPS_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('1'::('0'::('1'::('1'::[]))))))
                (app (enc_bit d)
                  (app
                    (s2bl
                      ('0'::('0'::('1'::('1'::('0'::('0'::('1'::[]))))))))
                    l1))))
        | FPM32_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_fp_modrm (s2bl ('0'::('0'::('1'::[])))) op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))
                l1))
        | FPM64_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (enc_fp_modrm (s2bl ('0'::('0'::('1'::[])))) op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))
                l1))
        | _ -> invalid)
  else (match op1 with
        | FPS_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app (s2bl ('1'::('1'::('0'::('1'::('1'::[]))))))
                (app (enc_bit d)
                  (app
                    (s2bl
                      ('0'::('0'::('1'::('1'::('0'::('0'::('1'::[]))))))))
                    l1))))
        | _ -> invalid)

(** val enc_FMULP : fp_operand -> bool list coq_Enc **)

let enc_FMULP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FNCLEX : bool list coq_Enc **)

let enc_FNCLEX =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_FNINIT : bool list coq_Enc **)

let enc_FNINIT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_FNSAVE : fp_operand -> bool list coq_Enc **)

let enc_FNSAVE op1 = match op1 with
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FNSTSW : fp_operand option -> bool list coq_Enc **)

let enc_FNSTSW = function
| Some op2 ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('1'::('1'::[])))) op2) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| None ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FNOP : bool list coq_Enc **)

let enc_FNOP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FPATAN : bool list coq_Enc **)

let enc_FPATAN =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_FPREM : bool list coq_Enc **)

let enc_FPREM =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))

(** val enc_FPREM1 : bool list coq_Enc **)

let enc_FPREM1 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))

(** val enc_FPTAN : bool list coq_Enc **)

let enc_FPTAN =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_FRNDINT : bool list coq_Enc **)

let enc_FRNDINT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))))

(** val enc_FRSTOR : fp_operand -> bool list coq_Enc **)

let enc_FRSTOR op1 = match op1 with
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FSCALE : bool list coq_Enc **)

let enc_FSCALE =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::[])))))))))))))))))

(** val enc_FSIN : bool list coq_Enc **)

let enc_FSIN =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))))

(** val enc_FSINCOS : bool list coq_Enc **)

let enc_FSINCOS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))

(** val enc_FSQRT : bool list coq_Enc **)

let enc_FSQRT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))))

(** val enc_FST : fp_operand -> bool list coq_Enc **)

let enc_FST op1 = match op1 with
| FPS_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('0'::[]))))))))))))))
        l1))
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))
        l1))
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| _ -> invalid

(** val enc_FSTP : fp_operand -> bool list coq_Enc **)

let enc_FSTP op1 = match op1 with
| FPS_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::[]))))))))))))))
        l1))
| FPM16_op _ -> invalid
| FPM32_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))
        l1))
| FPM64_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))
        l1))
| FPM80_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_fp_modrm (s2bl ('1'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app (s2bl ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))
        l1))

(** val enc_FSUB : bool -> fp_operand -> bool list coq_Enc **)

let enc_FSUB =
  enc_fp_arith true (s2bl ('0'::[])) (s2bl ('1'::('0'::('0'::[]))))

(** val enc_FSUBP : fp_operand -> bool list coq_Enc **)

let enc_FSUBP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FSUBR : bool -> fp_operand -> bool list coq_Enc **)

let enc_FSUBR =
  enc_fp_arith false (s2bl ('0'::[])) (s2bl ('1'::('0'::('1'::[]))))

(** val enc_FSUBRP : fp_operand -> bool list coq_Enc **)

let enc_FSUBRP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[]))))))))))))))
        l1))

(** val enc_FTST : bool list coq_Enc **)

let enc_FTST =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('0'::[])))))))))))))))))

(** val enc_FUCOM : fp_operand -> bool list coq_Enc **)

let enc_FUCOM op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::[]))))))))))))))
        l1))

(** val enc_FUCOMI : fp_operand -> bool list coq_Enc **)

let enc_FUCOMI op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FUCOMIP : fp_operand -> bool list coq_Enc **)

let enc_FUCOMIP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FUCOMP : fp_operand -> bool list coq_Enc **)

let enc_FUCOMP op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FUCOMPP : bool list coq_Enc **)

let enc_FUCOMPP =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_FWAIT : bool list coq_Enc **)

let enc_FWAIT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl ('1'::('0'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))

(** val enc_FXAM : bool list coq_Enc **)

let enc_FXAM =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::[])))))))))))))))))

(** val enc_FXCH : fp_operand -> bool list coq_Enc **)

let enc_FXCH op1 =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_fp_int3 op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('0'::('0'::('1'::[]))))))))))))))
        l1))

(** val enc_FXTRACT : bool list coq_Enc **)

let enc_FXTRACT =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))))

(** val enc_FYL2X : bool list coq_Enc **)

let enc_FYL2X =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_FYL2XP1 : bool list coq_Enc **)

let enc_FYL2XP1 =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))))

(** val enc_mmx_modrm_gen : bool list -> mmx_operand -> bool list coq_Enc **)

let enc_mmx_modrm_gen mmx_reg = function
| MMX_Addr_op addr -> enc_address mmx_reg addr
| MMX_Reg_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[]))) (app mmx_reg (enc_mmx_reg r2)))
| _ -> invalid

(** val enc_gg : mmx_granularity -> bool list **)

let enc_gg = function
| MMX_8 -> s2bl ('0'::('0'::[]))
| MMX_16 -> s2bl ('0'::('1'::[]))
| MMX_32 -> s2bl ('1'::('0'::[]))
| MMX_64 -> s2bl ('1'::('1'::[]))

(** val enc_EMMS : bool list coq_Enc **)

let enc_EMMS =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))

(** val enc_MOVD : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_MOVD op1 op2 =
  match op1 with
  | GP_Reg_op r ->
    (match op2 with
     | MMX_Reg_op m ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_reg r) (enc_mmx_reg m)))
     | _ -> invalid)
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | MMX_Reg_op m ->
    (match op2 with
     | GP_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_mmx_reg m) (enc_reg r)))
     | MMX_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | MMX_Imm_op _ -> invalid

(** val enc_MOVQ : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_MOVQ op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | MMX_Reg_op _ ->
    (match op2 with
     | MMX_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PACKSSDW : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PACKSSDW op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PACKSSWB : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PACKSSWB op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PACKUSWB : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PACKUSWB op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PADD :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PADD gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PADDS :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PADDS gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_16 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PADDUS :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PADDUS gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_16 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PAND : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PAND op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PANDN : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PANDN op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PCMPEQ :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PCMPEQ gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PCMPGT :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PCMPGT gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PMADDWD : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PMADDWD op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMULHUW : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PMULHUW op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMULHW : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PMULHW op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMULLW : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PMULLW op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_POR : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_POR op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSLL :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSLL gg op1 op2 =
  match gg with
  | MMX_16 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | MMX_Reg_op r ->
       (match op2 with
        | MMX_Imm_op imm ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 imm)
            (fun l_imm ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg)
                  (app (s2bl ('1'::('1'::('1'::('1'::('0'::[]))))))
                    (app (enc_mmx_reg r) l_imm)))))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PSRA :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSRA gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | MMX_Reg_op r ->
       (match op2 with
        | MMX_Imm_op imm ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 imm)
            (fun l_imm ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg)
                  (app (s2bl ('1'::('1'::('1'::('1'::('0'::[]))))))
                    (app (enc_mmx_reg r) l_imm)))))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_32 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | MMX_Reg_op r ->
       (match op2 with
        | MMX_Imm_op imm ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 imm)
            (fun l_imm ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg)
                  (app (s2bl ('1'::('1'::('1'::('1'::('0'::[]))))))
                    (app (enc_mmx_reg r) l_imm)))))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSRL :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSRL gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | MMX_Reg_op r ->
       (match op2 with
        | MMX_Imm_op imm ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 imm)
            (fun l_imm ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg)
                  (app (s2bl ('1'::('1'::('1'::('1'::('0'::[]))))))
                    (app (enc_mmx_reg r) l_imm)))))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_32 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) (app (s2bl ('1'::('1'::[]))) l1))))
        | _ -> invalid)
     | MMX_Reg_op r ->
       (match op2 with
        | MMX_Imm_op imm ->
          coq_Bind (Obj.magic coq_EncodingMonad) (enc_byte_i32 imm)
            (fun l_imm ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg)
                  (app (s2bl ('1'::('1'::('1'::('1'::('0'::[]))))))
                    (app (enc_mmx_reg r) l_imm)))))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSUB :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSUB gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PSUBS :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSUBS gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_16 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSUBUS :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PSUBUS gg op1 op2 =
  match gg with
  | MMX_8 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | MMX_16 ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)
  | _ -> invalid

(** val enc_PUNPCKH :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PUNPCKH gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PUNPCKL :
    mmx_granularity -> mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PUNPCKL gg op1 op2 =
  match gg with
  | MMX_64 -> invalid
  | _ ->
    (match op1 with
     | MMX_Addr_op _ ->
       (match op2 with
        | MMX_Reg_op _ ->
          coq_Bind (Obj.magic coq_EncodingMonad)
            (match op2 with
             | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
             | _ -> invalid) (fun l1 ->
            coq_Return (Obj.magic coq_EncodingMonad)
              (app
                (s2bl
                  ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))
                (app (enc_gg gg) l1)))
        | _ -> invalid)
     | _ -> invalid)

(** val enc_PXOR : mmx_operand -> mmx_operand -> bool list coq_Enc **)

let enc_PXOR op1 op2 =
  match op1 with
  | MMX_Addr_op _ ->
    (match op2 with
     | MMX_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | MMX_Reg_op r1 -> enc_mmx_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_xmm_r : sse_register -> bool list **)

let enc_xmm_r r =
  int_explode size3 r (Big.succ (Big.succ (Big.succ Big.zero)))

(** val enc_xmm_modrm_gen : bool list -> sse_operand -> bool list coq_Enc **)

let enc_xmm_modrm_gen xmm_reg = function
| SSE_XMM_Reg_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[]))) (app xmm_reg (enc_xmm_r r2)))
| SSE_Addr_op addr -> enc_address xmm_reg addr
| _ -> invalid

(** val enc_mm_modrm_gen : bool list -> sse_operand -> bool list coq_Enc **)

let enc_mm_modrm_gen mm_reg = function
| SSE_MM_Reg_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[]))) (app mm_reg (enc_mmx_reg r2)))
| SSE_Addr_op addr -> enc_address mm_reg addr
| _ -> invalid

(** val enc_ext_op_modrm_sse :
    bool list -> sse_operand -> bool list coq_Enc **)

let enc_ext_op_modrm_sse opb = function
| SSE_XMM_Reg_op r2 ->
  coq_Return (Obj.magic coq_EncodingMonad)
    (app (s2bl ('1'::('1'::[]))) (app opb (enc_xmm_r r2)))
| SSE_Addr_op addr -> enc_address opb addr
| _ -> invalid

(** val enc_ADDPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_ADDPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_ADDSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_ADDSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_ANDNPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_ANDNPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_ANDPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_ANDPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CMPPS :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_CMPPS op1 op2 imm =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))))
             (app l1 (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CMPSS :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_CMPSS op1 op2 imm =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::[])))))))))))))))))))))))))
             (app l1 (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_COMISS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_COMISS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTPI2PS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTPI2PS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTPS2PI : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTPS2PI op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op r ->
    (match op2 with
     | SSE_MM_Reg_op r0 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))))
           (app (enc_xmm_r r) (enc_mmx_reg r0)))
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTSI2SS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTSI2SS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op r ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_Addr_op addr -> enc_address (enc_xmm_r r) addr
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))))))))))
             l1))
     | SSE_GP_Reg_op r0 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('1'::[])))))))))))))))))))))))))))
           (app (enc_xmm_r r) (enc_reg r0)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTSS2SI : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTSS2SI op1 op2 =
  match op1 with
  | SSE_GP_Reg_op r ->
    (match op2 with
     | SSE_XMM_Reg_op r0 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))))))))))))
           (app (enc_reg r) (enc_xmm_r r0)))
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_Addr_op addr -> enc_address (enc_reg r) addr
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTTPS2PI : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTTPS2PI op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_CVTTSS2SI : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_CVTTSS2SI op1 op2 =
  match op1 with
  | SSE_GP_Reg_op r ->
    (match op2 with
     | SSE_XMM_Reg_op r0 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))))))))))))
           (app (enc_reg r) (enc_xmm_r r0)))
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_Addr_op addr -> enc_address (enc_reg r) addr
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_DIVPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_DIVPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_DIVSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_DIVSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_LDMXCSR : sse_operand -> bool list coq_Enc **)

let enc_LDMXCSR op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_MAXPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MAXPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MAXSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MAXSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MINPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MINPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MINSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MINSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVAPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVAPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_XMM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVHLPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVHLPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op a ->
    (match op2 with
     | SSE_XMM_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_xmm_r a) (enc_xmm_r r)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVHPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVHPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_XMM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVLHPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVLHPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op a ->
    (match op2 with
     | SSE_XMM_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_xmm_r a) (enc_xmm_r r)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVLPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVLPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_XMM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVMSKPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVMSKPS op1 op2 =
  match op1 with
  | SSE_GP_Reg_op a ->
    (match op2 with
     | SSE_XMM_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_reg a) (enc_xmm_r r)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_XMM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVUPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVUPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_XMM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MULPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MULPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MULSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MULSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_ORPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_ORPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_RCPPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_RCPPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_RCPSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_RCPSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_RSQRTPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_RSQRTPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_RSQRTSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_RSQRTSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('1'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_SHUFPS :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_SHUFPS op1 op2 imm =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::[])))))))))))))))))
             (app l1 (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_SQRTPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_SQRTPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_SQRTSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_SQRTSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('1'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_STMXCSR : sse_operand -> bool list coq_Enc **)

let enc_STMXCSR op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_SUBPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_SUBPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_SUBSS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_SUBSS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::[])))))))))))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_UCOMISS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_UCOMISS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_UNPCKHPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_UNPCKHPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_UNPCKLPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_UNPCKLPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_XORPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_XORPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PAVGB : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PAVGB op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | SSE_Addr_op _ ->
    (match op2 with
     | SSE_MM_Reg_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op1
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PEXTRW :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_PEXTRW op1 op2 imm =
  match op1 with
  | SSE_GP_Reg_op r ->
    (match op2 with
     | SSE_MM_Reg_op mx ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('1'::('1'::('1'::[])))))))))))))))))))
           (app (enc_reg r) (app (enc_mmx_reg mx) (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PINSRW :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_PINSRW op1 op2 imm =
  match op1 with
  | SSE_MM_Reg_op mm ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op2 with
          | SSE_Addr_op addr -> enc_address (enc_mmx_reg mm) addr
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::[])))))))))))))))))
             (app l1 (enc_byte imm))))
     | SSE_GP_Reg_op r32 ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('1'::('1'::[])))))))))))))))))))
           (app (enc_mmx_reg mm) (app (enc_reg r32) (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMAXSW : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PMAXSW op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMAXUB : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PMAXUB op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMINSW : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PMINSW op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMINUB : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PMINUB op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PMOVMSKB : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PMOVMSKB op1 op2 =
  match op1 with
  | SSE_GP_Reg_op a ->
    (match op2 with
     | SSE_MM_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))))
           (app (enc_reg a) (enc_mmx_reg r)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSADBW : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_PSADBW op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('0'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PSHUFW :
    sse_operand -> sse_operand -> int8 -> bool list coq_Enc **)

let enc_PSHUFW op1 op2 imm =
  match op1 with
  | SSE_GP_Reg_op r ->
    (match op2 with
     | SSE_MM_Reg_op mx ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::[])))))))))))))))))
           (app (enc_reg r) (app (enc_mmx_reg mx) (enc_byte imm))))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MASKMOVQ : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MASKMOVQ op1 op2 =
  match op1 with
  | SSE_MM_Reg_op a ->
    (match op2 with
     | SSE_MM_Reg_op r ->
       coq_Return (Obj.magic coq_EncodingMonad)
         (app
           (s2bl
             ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::[])))))))))))))))))))
           (app (enc_mmx_reg a) (enc_mmx_reg r)))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVNTPS : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVNTPS op1 op2 =
  match op1 with
  | SSE_XMM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_XMM_Reg_op r1 -> enc_xmm_modrm_gen (enc_xmm_r r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_MOVNTQ : sse_operand -> sse_operand -> bool list coq_Enc **)

let enc_MOVNTQ op1 op2 =
  match op1 with
  | SSE_MM_Reg_op _ ->
    (match op2 with
     | SSE_Addr_op _ ->
       coq_Bind (Obj.magic coq_EncodingMonad)
         (match op1 with
          | SSE_MM_Reg_op r1 -> enc_mm_modrm_gen (enc_mmx_reg r1) op2
          | _ -> invalid) (fun l1 ->
         coq_Return (Obj.magic coq_EncodingMonad)
           (app
             (s2bl
               ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::[])))))))))))))))))
             l1))
     | _ -> invalid)
  | _ -> invalid

(** val enc_PREFETCHT0 : sse_operand -> bool list coq_Enc **)

let enc_PREFETCHT0 op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('0'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_PREFETCHT1 : sse_operand -> bool list coq_Enc **)

let enc_PREFETCHT1 op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('1'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_PREFETCHT2 : sse_operand -> bool list coq_Enc **)

let enc_PREFETCHT2 op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('1'::('1'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_PREFETCHNTA : sse_operand -> bool list coq_Enc **)

let enc_PREFETCHNTA op1 = match op1 with
| SSE_Addr_op _ ->
  coq_Bind (Obj.magic coq_EncodingMonad)
    (enc_ext_op_modrm_sse (s2bl ('0'::('0'::('0'::[])))) op1) (fun l1 ->
    coq_Return (Obj.magic coq_EncodingMonad)
      (app
        (s2bl
          ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))
        l1))
| _ -> invalid

(** val enc_SFENCE : bool list coq_Enc **)

let enc_SFENCE =
  coq_Return (Obj.magic coq_EncodingMonad)
    (s2bl
      ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::[])))))))))))))))))))))))))

(** val enc_prefix : prefix -> bool list coq_Enc **)

let enc_prefix pre =
  let lr =
    match pre.lock_rep with
    | Some l ->
      (match l with
       | Coq_lock ->
         s2bl ('1'::('1'::('1'::('1'::('0'::('0'::('0'::('0'::[]))))))))
       | Coq_rep ->
         s2bl ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::[]))))))))
       | Coq_repn ->
         s2bl ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::[])))))))))
    | None -> s2bl []
  in
  let so =
    match pre.seg_override with
    | Some s ->
      (match s with
       | ES ->
         s2bl ('0'::('0'::('1'::('0'::('0'::('1'::('1'::('0'::[]))))))))
       | CS ->
         s2bl ('0'::('0'::('1'::('0'::('1'::('1'::('1'::('0'::[]))))))))
       | SS ->
         s2bl ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('0'::[]))))))))
       | DS ->
         s2bl ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('0'::[]))))))))
       | FS ->
         s2bl ('0'::('1'::('1'::('0'::('0'::('1'::('0'::('0'::[]))))))))
       | GS ->
         s2bl ('0'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::[])))))))))
    | None -> s2bl []
  in
  let oo =
    if pre.op_override
    then s2bl ('0'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::[]))))))))
    else s2bl []
  in
  let ao =
    if pre.addr_override
    then s2bl ('0'::('1'::('1'::('0'::('0'::('1'::('1'::('1'::[]))))))))
    else s2bl []
  in
  coq_Return (Obj.magic coq_EncodingMonad) (app lr (app so (app oo ao)))

(** val check_pre_rep : prefix -> bool **)

let check_pre_rep pre =
  let { lock_rep = lr; seg_override = _; op_override = _; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some l ->
     (match l with
      | Coq_rep -> if addr_o then false else true
      | _ -> false)
   | None -> if addr_o then false else true)

(** val check_pre_rep_or_repn : prefix -> bool **)

let check_pre_rep_or_repn pre =
  let { lock_rep = lr; seg_override = _; op_override = _; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some l ->
     (match l with
      | Coq_lock -> false
      | _ -> if addr_o then false else true)
   | None -> if addr_o then false else true)

(** val check_pre_lock_with_op_override : prefix -> bool **)

let check_pre_lock_with_op_override pre =
  let { lock_rep = lr; seg_override = _; op_override = op_o; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some l ->
     (match l with
      | Coq_lock -> if op_o then if addr_o then false else true else false
      | _ -> false)
   | None -> if addr_o then false else true)

(** val check_pre_lock_no_op_override : prefix -> bool **)

let check_pre_lock_no_op_override pre =
  let { lock_rep = lr; seg_override = _; op_override = op_o; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some l ->
     (match l with
      | Coq_lock -> if op_o then false else if addr_o then false else true
      | _ -> false)
   | None -> if op_o then false else if addr_o then false else true)

(** val check_pre_seg_with_op_override : prefix -> bool **)

let check_pre_seg_with_op_override pre =
  let { lock_rep = lr; seg_override = _; op_override = op_o; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some _ -> false
   | None -> if op_o then if addr_o then false else true else false)

(** val check_pre_seg_op_override : prefix -> bool **)

let check_pre_seg_op_override pre =
  let { lock_rep = lr; seg_override = _; op_override = _; addr_override =
    addr_o } = pre
  in
  (match lr with
   | Some _ -> false
   | None -> if addr_o then false else true)

(** val check_pre_seg_override : prefix -> bool **)

let check_pre_seg_override pre =
  let { lock_rep = lr; seg_override = seg; op_override = op_o;
    addr_override = addr_o } = pre
  in
  (match lr with
   | Some _ -> false
   | None ->
     (match seg with
      | Some _ -> if op_o then false else if addr_o then false else true
      | None -> false))

(** val check_empty_prefix : prefix -> bool **)

let check_empty_prefix pre =
  let { lock_rep = lr; seg_override = seg; op_override = op_o;
    addr_override = addr_o } = pre
  in
  (match lr with
   | Some _ -> false
   | None ->
     (match seg with
      | Some _ -> false
      | None -> if op_o then false else if addr_o then false else true))

(** val enc_rep_instr : prefix -> instr -> bool list coq_Enc **)

let enc_rep_instr pre i =
  if check_pre_rep pre
  then (match i with
        | INS w -> enc_INS w
        | LODS w -> enc_LODS w
        | MOVS w -> enc_MOVS w
        | OUTS w -> enc_OUTS w
        | RET (ss, disp) -> enc_RET ss disp
        | STOS w -> enc_STOS w
        | _ -> invalid)
  else invalid

(** val enc_lock_with_op_override_instr :
    prefix -> instr -> bool list coq_Enc **)

let enc_lock_with_op_override_instr pre i =
  if check_pre_lock_with_op_override pre
  then (match i with
        | ADC (w, op1, op2) -> enc_ADC pre.op_override w op1 op2
        | ADD (w, op1, op2) -> enc_ADD pre.op_override w op1 op2
        | AND (w, op1, op2) -> enc_AND pre.op_override w op1 op2
        | DEC (w, op1) -> enc_DEC w op1
        | INC (w, op1) -> enc_INC w op1
        | NEG (w, op1) -> enc_NEG w op1
        | NOT (w, op1) -> enc_NOT w op1
        | OR (w, op1, op2) -> enc_OR pre.op_override w op1 op2
        | SBB (w, op1, op2) -> enc_SBB pre.op_override w op1 op2
        | SUB (w, op1, op2) -> enc_SUB pre.op_override w op1 op2
        | XCHG (w, op1, op2) -> enc_XCHG w op1 op2
        | XOR (w, op1, op2) -> enc_XOR pre.op_override w op1 op2
        | _ -> invalid)
  else invalid

(** val enc_lock_no_op_override_instr :
    prefix -> instr -> bool list coq_Enc **)

let enc_lock_no_op_override_instr pre i =
  if check_pre_lock_no_op_override pre
  then (match i with
        | ADC (w, op1, op2) -> enc_ADC pre.op_override w op1 op2
        | ADD (w, op1, op2) -> enc_ADD pre.op_override w op1 op2
        | AND (w, op1, op2) -> enc_AND pre.op_override w op1 op2
        | BTC (op1, op2) -> enc_BTC op1 op2
        | BTR (op1, op2) -> enc_BTR op1 op2
        | BTS (op1, op2) -> enc_BTS op1 op2
        | CMPXCHG (w, op1, op2) -> enc_CMPXCHG w op1 op2
        | DEC (w, op1) -> enc_DEC w op1
        | INC (w, op1) -> enc_INC w op1
        | NEG (w, op1) -> enc_NEG w op1
        | NOT (w, op1) -> enc_NOT w op1
        | OR (w, op1, op2) -> enc_OR pre.op_override w op1 op2
        | SBB (w, op1, op2) -> enc_SBB pre.op_override w op1 op2
        | SUB (w, op1, op2) -> enc_SUB pre.op_override w op1 op2
        | XADD (w, op1, op2) -> enc_XADD w op1 op2
        | XCHG (w, op1, op2) -> enc_XCHG w op1 op2
        | XOR (w, op1, op2) -> enc_XOR pre.op_override w op1 op2
        | _ -> invalid)
  else invalid

(** val enc_seg_with_op_override_instr :
    prefix -> instr -> bool list coq_Enc **)

let enc_seg_with_op_override_instr pre i =
  if check_pre_seg_with_op_override pre
  then (match i with
        | CMP (w, op1, op2) -> enc_CMP pre.op_override w op1 op2
        | IMUL (w, op1, opopt, iopt) ->
          enc_IMUL pre.op_override w op1 opopt iopt
        | MOV (w, op1, op2) -> enc_MOV pre.op_override w op1 op2
        | TEST (w, op1, op2) -> enc_TEST pre.op_override w op1 op2
        | _ -> invalid)
  else invalid

(** val enc_seg_op_override_instr : prefix -> instr -> bool list coq_Enc **)

let enc_seg_op_override_instr pre i =
  if check_pre_seg_op_override pre
  then (match i with
        | CDQ -> enc_CDQ
        | CMOVcc (ct, op1, op2) -> enc_CMOVcc ct op1 op2
        | CWDE -> enc_CWDE
        | DIV (w, op1) -> enc_DIV w op1
        | IDIV (w, op1) -> enc_IDIV w op1
        | MOVSX (w, op1, op2) -> enc_MOVSX w op1 op2
        | MOVZX (w, op1, op2) -> enc_MOVZX w op1 op2
        | MUL (w, op1) -> enc_MUL w op1
        | NOP opopt -> enc_NOP opopt
        | ROL (w, op1, ri) -> enc_ROL w op1 ri
        | ROR (w, op1, ri) -> enc_ROR w op1 ri
        | SAR (w, op1, ri) -> enc_SAR w op1 ri
        | SHL (w, op1, ri) -> enc_SHL w op1 ri
        | SHLD (w, op1, ri) -> enc_SHLD w op1 ri
        | SHR (w, op1, ri) -> enc_SHR w op1 ri
        | SHRD (w, op1, ri) -> enc_SHRD w op1 ri
        | _ -> invalid)
  else invalid

(** val enc_seg_override_instr : prefix -> instr -> bool list coq_Enc **)

let enc_seg_override_instr pre i =
  if check_pre_seg_override pre
  then (match i with
        | AAA -> enc_AAA
        | AAD -> enc_AAD
        | AAM -> enc_AAM
        | AAS -> enc_AAS
        | ARPL (op1, op2) -> enc_ARPL op1 op2
        | BOUND (op1, op2) -> enc_BOUND op1 op2
        | BSF (op1, op2) -> enc_BSF op1 op2
        | BSR (op1, op2) -> enc_BSR op1 op2
        | BSWAP r -> enc_BSWAP r
        | BT (op1, op2) -> enc_BT op1 op2
        | CALL (near, abs, op1, sel) -> enc_CALL near abs op1 sel
        | CLC -> enc_CLC
        | CLD -> enc_CLD
        | CLI -> enc_CLI
        | CLTS -> enc_CLTS
        | CMC -> enc_CMC
        | CMP (w, op1, op2) -> enc_CMP pre.op_override w op1 op2
        | CPUID -> enc_CPUID
        | DAA -> enc_DAA
        | DAS -> enc_DAS
        | F2XM1 -> enc_F2XM1
        | FABS -> enc_FABS
        | FADD (d, op1) -> enc_FADD d op1
        | FADDP op1 -> enc_FADDP op1
        | FBLD op1 -> enc_FBLD op1
        | FBSTP op1 -> enc_FBSTP op1
        | FCHS -> enc_FCHS
        | FCMOVcc (fct, op1) -> enc_FCMOVcc fct op1
        | FCOM op1 -> enc_FCOM op1
        | FCOMP op1 -> enc_FCOMP op1
        | FCOMPP -> enc_FCOMPP
        | FCOMIP op1 -> enc_FCOMIP op1
        | FCOS -> enc_FCOS
        | FDECSTP -> enc_FDECSTP
        | FDIV (op1, op2) -> enc_FDIV op1 op2
        | FDIVP op1 -> enc_FDIVP op1
        | FDIVR (op1, op2) -> enc_FDIVR op1 op2
        | FDIVRP op1 -> enc_FDIVRP op1
        | FFREE op1 -> enc_FFREE op1
        | FIADD op1 -> enc_FIADD op1
        | FICOM op1 -> enc_FICOM op1
        | FICOMP op1 -> enc_FICOMP op1
        | FIDIV op1 -> enc_FIDIV op1
        | FIDIVR op1 -> enc_FIDIVR op1
        | FILD op1 -> enc_FILD op1
        | FIMUL op1 -> enc_FIMUL op1
        | FINCSTP -> enc_FINCSTP
        | FIST op1 -> enc_FIST op1
        | FISTP op1 -> enc_FISTP op1
        | FISUB op1 -> enc_FISUB op1
        | FISUBR op1 -> enc_FISUBR op1
        | FLD op1 -> enc_FLD op1
        | FLD1 -> enc_FLD1
        | FLDCW op1 -> enc_FLDCW op1
        | FLDENV op1 -> enc_FLDENV op1
        | FLDL2E -> enc_FLDL2E
        | FLDL2T -> enc_FLDL2T
        | FLDLG2 -> enc_FLDLG2
        | FLDLN2 -> enc_FLDLN2
        | FLDPI -> enc_FLDPI
        | FLDZ -> enc_FLDZ
        | FMUL (d, op1) -> enc_FMUL d op1
        | FMULP op1 -> enc_FMULP op1
        | FNCLEX -> enc_FNCLEX
        | FNINIT -> enc_FNINIT
        | FNOP -> enc_FNOP
        | FNSAVE op1 -> enc_FNSAVE op1
        | FNSTSW op1 -> enc_FNSTSW op1
        | FPATAN -> enc_FPATAN
        | FPREM -> enc_FPREM
        | FPREM1 -> enc_FPREM1
        | FPTAN -> enc_FPTAN
        | FRNDINT -> enc_FRNDINT
        | FRSTOR op1 -> enc_FRSTOR op1
        | FSCALE -> enc_FSCALE
        | FSIN -> enc_FSIN
        | FSINCOS -> enc_FSINCOS
        | FSQRT -> enc_FSQRT
        | FST op1 -> enc_FST op1
        | FSTP op1 -> enc_FSTP op1
        | FSUB (op1, op2) -> enc_FSUB op1 op2
        | FSUBP op1 -> enc_FSUBP op1
        | FSUBR (op1, op2) -> enc_FSUBR op1 op2
        | FSUBRP op1 -> enc_FSUBRP op1
        | FTST -> enc_FTST
        | FUCOM op1 -> enc_FUCOM op1
        | FUCOMP op1 -> enc_FUCOMP op1
        | FUCOMPP -> enc_FUCOMPP
        | FUCOMI op1 -> enc_FUCOMI op1
        | FUCOMIP op1 -> enc_FUCOMIP op1
        | FXAM -> enc_FXAM
        | FXCH op1 -> enc_FXCH op1
        | FXTRACT -> enc_FXTRACT
        | FYL2X -> enc_FYL2X
        | FYL2XP1 -> enc_FYL2XP1
        | FWAIT -> enc_FWAIT
        | EMMS -> enc_EMMS
        | MOVD (op1, op2) -> enc_MOVD op1 op2
        | MOVQ (op1, op2) -> enc_MOVQ op1 op2
        | PACKSSDW (op1, op2) -> enc_PACKSSDW op1 op2
        | PACKSSWB (op1, op2) -> enc_PACKSSWB op1 op2
        | PACKUSWB (op1, op2) -> enc_PACKUSWB op1 op2
        | PADD (gg, op1, op2) -> enc_PADD gg op1 op2
        | PADDS (gg, op1, op2) -> enc_PADDS gg op1 op2
        | PADDUS (gg, op1, op2) -> enc_PADDUS gg op1 op2
        | PAND (op1, op2) -> enc_PAND op1 op2
        | PANDN (op1, op2) -> enc_PANDN op1 op2
        | PCMPEQ (gg, op1, op2) -> enc_PCMPEQ gg op1 op2
        | PCMPGT (gg, op1, op2) -> enc_PCMPGT gg op1 op2
        | PMADDWD (op1, op2) -> enc_PMADDWD op1 op2
        | PMULHUW (op1, op2) -> enc_PMULHUW op1 op2
        | PMULHW (op1, op2) -> enc_PMULHW op1 op2
        | PMULLW (op1, op2) -> enc_PMULLW op1 op2
        | POR (op1, op2) -> enc_POR op1 op2
        | PSLL (gg, op1, op2) -> enc_PSLL gg op1 op2
        | PSRA (gg, op1, op2) -> enc_PSRA gg op1 op2
        | PSRL (gg, op1, op2) -> enc_PSRL gg op1 op2
        | PSUB (gg, op1, op2) -> enc_PSUB gg op1 op2
        | PSUBS (gg, op1, op2) -> enc_PSUBS gg op1 op2
        | PSUBUS (gg, op1, op2) -> enc_PSUBUS gg op1 op2
        | PUNPCKH (gg, op1, op2) -> enc_PUNPCKH gg op1 op2
        | PUNPCKL (gg, op1, op2) -> enc_PUNPCKL gg op1 op2
        | PXOR (op1, op2) -> enc_PXOR op1 op2
        | ADDPS (op1, op2) -> enc_ADDPS op1 op2
        | ADDSS (op1, op2) -> enc_ADDSS op1 op2
        | ANDNPS (op1, op2) -> enc_ANDNPS op1 op2
        | ANDPS (op1, op2) -> enc_ANDPS op1 op2
        | CMPPS (op1, op2, imm) -> enc_CMPPS op1 op2 imm
        | CMPSS (op1, op2, imm) -> enc_CMPSS op1 op2 imm
        | COMISS (op1, op2) -> enc_COMISS op1 op2
        | CVTPI2PS (op1, op2) -> enc_CVTPI2PS op1 op2
        | CVTPS2PI (op1, op2) -> enc_CVTPS2PI op1 op2
        | CVTSI2SS (op1, op2) -> enc_CVTSI2SS op1 op2
        | CVTSS2SI (op1, op2) -> enc_CVTSS2SI op1 op2
        | CVTTPS2PI (op1, op2) -> enc_CVTTPS2PI op1 op2
        | CVTTSS2SI (op1, op2) -> enc_CVTTSS2SI op1 op2
        | DIVPS (op1, op2) -> enc_DIVPS op1 op2
        | DIVSS (op1, op2) -> enc_DIVSS op1 op2
        | LDMXCSR op1 -> enc_LDMXCSR op1
        | MAXPS (op1, op2) -> enc_MAXPS op1 op2
        | MAXSS (op1, op2) -> enc_MAXSS op1 op2
        | MINPS (op1, op2) -> enc_MINPS op1 op2
        | MINSS (op1, op2) -> enc_MINSS op1 op2
        | MOVAPS (op1, op2) -> enc_MOVAPS op1 op2
        | MOVHLPS (op1, op2) -> enc_MOVHLPS op1 op2
        | MOVHPS (op1, op2) -> enc_MOVHPS op1 op2
        | MOVLHPS (op1, op2) -> enc_MOVLHPS op1 op2
        | MOVLPS (op1, op2) -> enc_MOVLPS op1 op2
        | MOVMSKPS (op1, op2) -> enc_MOVMSKPS op1 op2
        | MOVSS (op1, op2) -> enc_MOVSS op1 op2
        | MOVUPS (op1, op2) -> enc_MOVUPS op1 op2
        | MULPS (op1, op2) -> enc_MULPS op1 op2
        | MULSS (op1, op2) -> enc_MULSS op1 op2
        | ORPS (op1, op2) -> enc_ORPS op1 op2
        | RCPPS (op1, op2) -> enc_RCPPS op1 op2
        | RCPSS (op1, op2) -> enc_RCPSS op1 op2
        | RSQRTPS (op1, op2) -> enc_RSQRTPS op1 op2
        | RSQRTSS (op1, op2) -> enc_RSQRTSS op1 op2
        | SHUFPS (op1, op2, imm) -> enc_SHUFPS op1 op2 imm
        | SQRTPS (op1, op2) -> enc_SQRTPS op1 op2
        | SQRTSS (op1, op2) -> enc_SQRTSS op1 op2
        | STMXCSR op1 -> enc_STMXCSR op1
        | SUBPS (op1, op2) -> enc_SUBPS op1 op2
        | SUBSS (op1, op2) -> enc_SUBSS op1 op2
        | UCOMISS (op1, op2) -> enc_UCOMISS op1 op2
        | UNPCKHPS (op1, op2) -> enc_UNPCKHPS op1 op2
        | UNPCKLPS (op1, op2) -> enc_UNPCKLPS op1 op2
        | XORPS (op1, op2) -> enc_XORPS op1 op2
        | PAVGB (op1, op2) -> enc_PAVGB op1 op2
        | PEXTRW (op1, op2, imm) -> enc_PEXTRW op1 op2 imm
        | PINSRW (op1, op2, imm) -> enc_PINSRW op1 op2 imm
        | PMAXSW (op1, op2) -> enc_PMAXSW op1 op2
        | PMAXUB (op1, op2) -> enc_PMAXUB op1 op2
        | PMINSW (op1, op2) -> enc_PMINSW op1 op2
        | PMINUB (op1, op2) -> enc_PMINUB op1 op2
        | PMOVMSKB (op1, op2) -> enc_PMOVMSKB op1 op2
        | PSADBW (op1, op2) -> enc_PSADBW op1 op2
        | PSHUFW (op1, op2, imm) -> enc_PSHUFW op1 op2 imm
        | MASKMOVQ (op1, op2) -> enc_MASKMOVQ op1 op2
        | MOVNTPS (op1, op2) -> enc_MOVNTPS op1 op2
        | MOVNTQ (op1, op2) -> enc_MOVNTQ op1 op2
        | PREFETCHT0 op1 -> enc_PREFETCHT0 op1
        | PREFETCHT1 op1 -> enc_PREFETCHT1 op1
        | PREFETCHT2 op1 -> enc_PREFETCHT2 op1
        | PREFETCHNTA op1 -> enc_PREFETCHNTA op1
        | SFENCE -> enc_SFENCE
        | HLT -> enc_HLT
        | IMUL (w, op1, opopt, iopt) ->
          enc_IMUL pre.op_override w op1 opopt iopt
        | IN (w, p) -> enc_IN w p
        | INTn it -> enc_INTn it
        | INT -> enc_INT
        | INTO -> enc_INTO
        | INVD -> enc_INVD
        | INVLPG op1 -> enc_INVLPG op1
        | IRET -> enc_IRET
        | Jcc (ct, disp) -> enc_Jcc ct disp
        | JCXZ b -> enc_JCXZ b
        | JMP (near, absolute, op1, sel) -> enc_JMP near absolute op1 sel
        | LAHF -> enc_LAHF
        | LAR (op1, op2) -> enc_LAR op1 op2
        | LDS (op1, op2) -> enc_LDS op1 op2
        | LEA (op1, op2) -> enc_LEA op1 op2
        | LEAVE -> enc_LEAVE
        | LES (op1, op2) -> enc_LES op1 op2
        | LFS (op1, op2) -> enc_LFS op1 op2
        | LGDT op1 -> enc_LGDT op1
        | LGS (op1, op2) -> enc_LGS op1 op2
        | LIDT op1 -> enc_LIDT op1
        | LLDT op1 -> enc_LLDT op1
        | LMSW op1 -> enc_LMSW op1
        | LOOP disp -> enc_LOOP disp
        | LOOPZ disp -> enc_LOOPZ disp
        | LOOPNZ disp -> enc_LOOPNZ disp
        | LSL (op1, op2) -> enc_LSL op1 op2
        | LSS (op1, op2) -> enc_LSS op1 op2
        | LTR op1 -> enc_LTR op1
        | MOV (w, op1, op2) -> enc_MOV pre.op_override w op1 op2
        | MOVCR (d, cr, r) -> enc_MOVCR d cr r
        | MOVDR (d, dr, r) -> enc_MOVDR d dr r
        | MOVSR (d, sr, op1) -> enc_MOVSR d sr op1
        | MOVBE (op1, op2) -> enc_MOVBE op1 op2
        | OUT (w, p) -> enc_OUT w p
        | POP op1 -> enc_POP op1
        | POPSR sr -> enc_POPSR sr
        | POPA -> enc_POPA
        | POPF -> enc_POPF
        | PUSH (w, op1) -> enc_PUSH w op1
        | PUSHSR sr -> enc_PUSHSR sr
        | PUSHA -> enc_PUSHA
        | PUSHF -> enc_PUSHF
        | RCL (w, op1, ri) -> enc_RCL w op1 ri
        | RCR (w, op1, ri) -> enc_RCR w op1 ri
        | RDMSR -> enc_RDMSR
        | RDPMC -> enc_RDPMC
        | RDTSC -> enc_RDTSC
        | RDTSCP -> enc_RDTSCP
        | RSM -> enc_RSM
        | SAHF -> enc_SAHF
        | SETcc (ct, op1) -> enc_SETcc ct op1
        | SGDT op1 -> enc_SGDT op1
        | SIDT op1 -> enc_SIDT op1
        | SLDT op1 -> enc_SLDT op1
        | SMSW op1 -> enc_SMSW op1
        | STC -> enc_STC
        | STD -> enc_STD
        | STI -> enc_STI
        | STR op1 -> enc_STR op1
        | TEST (w, op1, op2) -> enc_TEST pre.op_override w op1 op2
        | UD2 -> enc_UD2
        | VERR op1 -> enc_VERR op1
        | VERW op1 -> enc_VERW op1
        | WBINVD -> enc_WBINVD
        | WRMSR -> enc_WRMSR
        | XLAT -> enc_XLAT
        | _ -> invalid)
  else invalid

(** val enc_all_instr : prefix -> instr -> bool list coq_Enc **)

let enc_all_instr pre = function
| AAA -> enc_AAA
| AAD -> enc_AAD
| AAM -> enc_AAM
| AAS -> enc_AAS
| ADC (w, op1, op2) -> enc_ADC pre.op_override w op1 op2
| ADD (w, op1, op2) -> enc_ADD pre.op_override w op1 op2
| AND (w, op1, op2) -> enc_AND pre.op_override w op1 op2
| ARPL (op1, op2) -> enc_ARPL op1 op2
| BOUND (op1, op2) -> enc_BOUND op1 op2
| BSF (op1, op2) -> enc_BSF op1 op2
| BSR (op1, op2) -> enc_BSR op1 op2
| BSWAP r -> enc_BSWAP r
| BT (op1, op2) -> enc_BT op1 op2
| BTC (op1, op2) -> enc_BTC op1 op2
| BTR (op1, op2) -> enc_BTR op1 op2
| BTS (op1, op2) -> enc_BTS op1 op2
| CALL (near, abs, op1, sel) -> enc_CALL near abs op1 sel
| CDQ -> enc_CDQ
| CLC -> enc_CLC
| CLD -> enc_CLD
| CLI -> enc_CLI
| CLTS -> enc_CLTS
| CMC -> enc_CMC
| CMOVcc (ct, op1, op2) -> enc_CMOVcc ct op1 op2
| CMP (w, op1, op2) -> enc_CMP pre.op_override w op1 op2
| CMPS w -> enc_CMPS w
| CMPXCHG (w, op1, op2) -> enc_CMPXCHG w op1 op2
| CPUID -> enc_CPUID
| CWDE -> enc_CWDE
| DAA -> enc_DAA
| DAS -> enc_DAS
| DEC (w, op1) -> enc_DEC w op1
| DIV (w, op1) -> enc_DIV w op1
| F2XM1 -> enc_F2XM1
| FABS -> enc_FABS
| FADD (d, op1) -> enc_FADD d op1
| FADDP op1 -> enc_FADDP op1
| FBLD op1 -> enc_FBLD op1
| FBSTP op1 -> enc_FBSTP op1
| FCHS -> enc_FCHS
| FCMOVcc (fct, op1) -> enc_FCMOVcc fct op1
| FCOM op1 -> enc_FCOM op1
| FCOMP op1 -> enc_FCOMP op1
| FCOMPP -> enc_FCOMPP
| FCOMIP op1 -> enc_FCOMIP op1
| FCOS -> enc_FCOS
| FDECSTP -> enc_FDECSTP
| FDIV (op1, op2) -> enc_FDIV op1 op2
| FDIVP op1 -> enc_FDIVP op1
| FDIVR (op1, op2) -> enc_FDIVR op1 op2
| FDIVRP op1 -> enc_FDIVRP op1
| FFREE op1 -> enc_FFREE op1
| FIADD op1 -> enc_FIADD op1
| FICOM op1 -> enc_FICOM op1
| FICOMP op1 -> enc_FICOMP op1
| FIDIV op1 -> enc_FIDIV op1
| FIDIVR op1 -> enc_FIDIVR op1
| FILD op1 -> enc_FILD op1
| FIMUL op1 -> enc_FIMUL op1
| FINCSTP -> enc_FINCSTP
| FIST op1 -> enc_FIST op1
| FISTP op1 -> enc_FISTP op1
| FISUB op1 -> enc_FISUB op1
| FISUBR op1 -> enc_FISUBR op1
| FLD op1 -> enc_FLD op1
| FLD1 -> enc_FLD1
| FLDCW op1 -> enc_FLDCW op1
| FLDENV op1 -> enc_FLDENV op1
| FLDL2E -> enc_FLDL2E
| FLDL2T -> enc_FLDL2T
| FLDLG2 -> enc_FLDLG2
| FLDLN2 -> enc_FLDLN2
| FLDPI -> enc_FLDPI
| FLDZ -> enc_FLDZ
| FMUL (d, op1) -> enc_FMUL d op1
| FMULP op1 -> enc_FMULP op1
| FNCLEX -> enc_FNCLEX
| FNINIT -> enc_FNINIT
| FNOP -> enc_FNOP
| FNSAVE op1 -> enc_FNSAVE op1
| FNSTSW op1 -> enc_FNSTSW op1
| FPATAN -> enc_FPATAN
| FPREM -> enc_FPREM
| FPREM1 -> enc_FPREM1
| FPTAN -> enc_FPTAN
| FRNDINT -> enc_FRNDINT
| FRSTOR op1 -> enc_FRSTOR op1
| FSCALE -> enc_FSCALE
| FSIN -> enc_FSIN
| FSINCOS -> enc_FSINCOS
| FSQRT -> enc_FSQRT
| FST op1 -> enc_FST op1
| FSTP op1 -> enc_FSTP op1
| FSUB (op1, op2) -> enc_FSUB op1 op2
| FSUBP op1 -> enc_FSUBP op1
| FSUBR (op1, op2) -> enc_FSUBR op1 op2
| FSUBRP op1 -> enc_FSUBRP op1
| FTST -> enc_FTST
| FUCOM op1 -> enc_FUCOM op1
| FUCOMP op1 -> enc_FUCOMP op1
| FUCOMPP -> enc_FUCOMPP
| FUCOMI op1 -> enc_FUCOMI op1
| FUCOMIP op1 -> enc_FUCOMIP op1
| FXAM -> enc_FXAM
| FXCH op1 -> enc_FXCH op1
| FXTRACT -> enc_FXTRACT
| FYL2X -> enc_FYL2X
| FYL2XP1 -> enc_FYL2XP1
| FWAIT -> enc_FWAIT
| EMMS -> enc_EMMS
| MOVD (op1, op2) -> enc_MOVD op1 op2
| MOVQ (op1, op2) -> enc_MOVQ op1 op2
| PACKSSDW (op1, op2) -> enc_PACKSSDW op1 op2
| PACKSSWB (op1, op2) -> enc_PACKSSWB op1 op2
| PACKUSWB (op1, op2) -> enc_PACKUSWB op1 op2
| PADD (gg, op1, op2) -> enc_PADD gg op1 op2
| PADDS (gg, op1, op2) -> enc_PADDS gg op1 op2
| PADDUS (gg, op1, op2) -> enc_PADDUS gg op1 op2
| PAND (op1, op2) -> enc_PAND op1 op2
| PANDN (op1, op2) -> enc_PANDN op1 op2
| PCMPEQ (gg, op1, op2) -> enc_PCMPEQ gg op1 op2
| PCMPGT (gg, op1, op2) -> enc_PCMPGT gg op1 op2
| PMADDWD (op1, op2) -> enc_PMADDWD op1 op2
| PMULHUW (op1, op2) -> enc_PMULHUW op1 op2
| PMULHW (op1, op2) -> enc_PMULHW op1 op2
| PMULLW (op1, op2) -> enc_PMULLW op1 op2
| POR (op1, op2) -> enc_POR op1 op2
| PSLL (gg, op1, op2) -> enc_PSLL gg op1 op2
| PSRA (gg, op1, op2) -> enc_PSRA gg op1 op2
| PSRL (gg, op1, op2) -> enc_PSRL gg op1 op2
| PSUB (gg, op1, op2) -> enc_PSUB gg op1 op2
| PSUBS (gg, op1, op2) -> enc_PSUBS gg op1 op2
| PSUBUS (gg, op1, op2) -> enc_PSUBUS gg op1 op2
| PUNPCKH (gg, op1, op2) -> enc_PUNPCKH gg op1 op2
| PUNPCKL (gg, op1, op2) -> enc_PUNPCKL gg op1 op2
| PXOR (op1, op2) -> enc_PXOR op1 op2
| ADDPS (op1, op2) -> enc_ADDPS op1 op2
| ADDSS (op1, op2) -> enc_ADDSS op1 op2
| ANDNPS (op1, op2) -> enc_ANDNPS op1 op2
| ANDPS (op1, op2) -> enc_ANDPS op1 op2
| CMPPS (op1, op2, imm) -> enc_CMPPS op1 op2 imm
| CMPSS (op1, op2, imm) -> enc_CMPSS op1 op2 imm
| COMISS (op1, op2) -> enc_COMISS op1 op2
| CVTPI2PS (op1, op2) -> enc_CVTPI2PS op1 op2
| CVTPS2PI (op1, op2) -> enc_CVTPS2PI op1 op2
| CVTSI2SS (op1, op2) -> enc_CVTSI2SS op1 op2
| CVTSS2SI (op1, op2) -> enc_CVTSS2SI op1 op2
| CVTTPS2PI (op1, op2) -> enc_CVTTPS2PI op1 op2
| CVTTSS2SI (op1, op2) -> enc_CVTTSS2SI op1 op2
| DIVPS (op1, op2) -> enc_DIVPS op1 op2
| DIVSS (op1, op2) -> enc_DIVSS op1 op2
| LDMXCSR op1 -> enc_LDMXCSR op1
| MAXPS (op1, op2) -> enc_MAXPS op1 op2
| MAXSS (op1, op2) -> enc_MAXSS op1 op2
| MINPS (op1, op2) -> enc_MINPS op1 op2
| MINSS (op1, op2) -> enc_MINSS op1 op2
| MOVAPS (op1, op2) -> enc_MOVAPS op1 op2
| MOVHLPS (op1, op2) -> enc_MOVHLPS op1 op2
| MOVHPS (op1, op2) -> enc_MOVHPS op1 op2
| MOVLHPS (op1, op2) -> enc_MOVLHPS op1 op2
| MOVLPS (op1, op2) -> enc_MOVLPS op1 op2
| MOVMSKPS (op1, op2) -> enc_MOVMSKPS op1 op2
| MOVSS (op1, op2) -> enc_MOVSS op1 op2
| MOVUPS (op1, op2) -> enc_MOVUPS op1 op2
| MULPS (op1, op2) -> enc_MULPS op1 op2
| MULSS (op1, op2) -> enc_MULSS op1 op2
| ORPS (op1, op2) -> enc_ORPS op1 op2
| RCPPS (op1, op2) -> enc_RCPPS op1 op2
| RCPSS (op1, op2) -> enc_RCPSS op1 op2
| RSQRTPS (op1, op2) -> enc_RSQRTPS op1 op2
| RSQRTSS (op1, op2) -> enc_RSQRTSS op1 op2
| SHUFPS (op1, op2, imm) -> enc_SHUFPS op1 op2 imm
| SQRTPS (op1, op2) -> enc_SQRTPS op1 op2
| SQRTSS (op1, op2) -> enc_SQRTSS op1 op2
| STMXCSR op1 -> enc_STMXCSR op1
| SUBPS (op1, op2) -> enc_SUBPS op1 op2
| SUBSS (op1, op2) -> enc_SUBSS op1 op2
| UCOMISS (op1, op2) -> enc_UCOMISS op1 op2
| UNPCKHPS (op1, op2) -> enc_UNPCKHPS op1 op2
| UNPCKLPS (op1, op2) -> enc_UNPCKLPS op1 op2
| XORPS (op1, op2) -> enc_XORPS op1 op2
| PAVGB (op1, op2) -> enc_PAVGB op1 op2
| PEXTRW (op1, op2, imm) -> enc_PEXTRW op1 op2 imm
| PINSRW (op1, op2, imm) -> enc_PINSRW op1 op2 imm
| PMAXSW (op1, op2) -> enc_PMAXSW op1 op2
| PMAXUB (op1, op2) -> enc_PMAXUB op1 op2
| PMINSW (op1, op2) -> enc_PMINSW op1 op2
| PMINUB (op1, op2) -> enc_PMINUB op1 op2
| PMOVMSKB (op1, op2) -> enc_PMOVMSKB op1 op2
| PSADBW (op1, op2) -> enc_PSADBW op1 op2
| PSHUFW (op1, op2, imm) -> enc_PSHUFW op1 op2 imm
| MASKMOVQ (op1, op2) -> enc_MASKMOVQ op1 op2
| MOVNTPS (op1, op2) -> enc_MOVNTPS op1 op2
| MOVNTQ (op1, op2) -> enc_MOVNTQ op1 op2
| PREFETCHT0 op1 -> enc_PREFETCHT0 op1
| PREFETCHT1 op1 -> enc_PREFETCHT1 op1
| PREFETCHT2 op1 -> enc_PREFETCHT2 op1
| PREFETCHNTA op1 -> enc_PREFETCHNTA op1
| SFENCE -> enc_SFENCE
| HLT -> enc_HLT
| IDIV (w, op1) -> enc_IDIV w op1
| IMUL (w, op1, opopt, iopt) -> enc_IMUL pre.op_override w op1 opopt iopt
| IN (w, p) -> enc_IN w p
| INC (w, op1) -> enc_INC w op1
| INS w -> enc_INS w
| INTn it -> enc_INTn it
| INT -> enc_INT
| INTO -> enc_INTO
| INVD -> enc_INVD
| INVLPG op1 -> enc_INVLPG op1
| IRET -> enc_IRET
| Jcc (ct, disp) -> enc_Jcc ct disp
| JCXZ b -> enc_JCXZ b
| JMP (near, absolute, op1, sel) -> enc_JMP near absolute op1 sel
| LAHF -> enc_LAHF
| LAR (op1, op2) -> enc_LAR op1 op2
| LDS (op1, op2) -> enc_LDS op1 op2
| LEA (op1, op2) -> enc_LEA op1 op2
| LEAVE -> enc_LEAVE
| LES (op1, op2) -> enc_LES op1 op2
| LFS (op1, op2) -> enc_LFS op1 op2
| LGDT op1 -> enc_LGDT op1
| LGS (op1, op2) -> enc_LGS op1 op2
| LIDT op1 -> enc_LIDT op1
| LLDT op1 -> enc_LLDT op1
| LMSW op1 -> enc_LMSW op1
| LODS w -> enc_LODS w
| LOOP disp -> enc_LOOP disp
| LOOPZ disp -> enc_LOOPZ disp
| LOOPNZ disp -> enc_LOOPNZ disp
| LSL (op1, op2) -> enc_LSL op1 op2
| LSS (op1, op2) -> enc_LSS op1 op2
| LTR op1 -> enc_LTR op1
| MOV (w, op1, op2) -> enc_MOV pre.op_override w op1 op2
| MOVCR (d, cr, r) -> enc_MOVCR d cr r
| MOVDR (d, dr, r) -> enc_MOVDR d dr r
| MOVSR (d, sr, op1) -> enc_MOVSR d sr op1
| MOVBE (op1, op2) -> enc_MOVBE op1 op2
| MOVS w -> enc_MOVS w
| MOVSX (w, op1, op2) -> enc_MOVSX w op1 op2
| MOVZX (w, op1, op2) -> enc_MOVZX w op1 op2
| MUL (w, op1) -> enc_MUL w op1
| NEG (w, op1) -> enc_NEG w op1
| NOP opopt -> enc_NOP opopt
| NOT (w, op1) -> enc_NOT w op1
| OR (w, op1, op2) -> enc_OR pre.op_override w op1 op2
| OUT (w, p) -> enc_OUT w p
| OUTS w -> enc_OUTS w
| POP op1 -> enc_POP op1
| POPSR sr -> enc_POPSR sr
| POPA -> enc_POPA
| POPF -> enc_POPF
| PUSH (w, op1) -> enc_PUSH w op1
| PUSHSR sr -> enc_PUSHSR sr
| PUSHA -> enc_PUSHA
| PUSHF -> enc_PUSHF
| RCL (w, op1, ri) -> enc_RCL w op1 ri
| RCR (w, op1, ri) -> enc_RCR w op1 ri
| RDMSR -> enc_RDMSR
| RDPMC -> enc_RDPMC
| RDTSC -> enc_RDTSC
| RDTSCP -> enc_RDTSCP
| RET (ss, disp) -> enc_RET ss disp
| ROL (w, op1, ri) -> enc_ROL w op1 ri
| ROR (w, op1, ri) -> enc_ROR w op1 ri
| RSM -> enc_RSM
| SAHF -> enc_SAHF
| SAR (w, op1, ri) -> enc_SAR w op1 ri
| SBB (w, op1, op2) -> enc_SBB pre.op_override w op1 op2
| SCAS w -> enc_SCAS w
| SETcc (ct, op1) -> enc_SETcc ct op1
| SGDT op1 -> enc_SGDT op1
| SHL (w, op1, ri) -> enc_SHL w op1 ri
| SHLD (op1, r, ri) -> enc_SHLD op1 r ri
| SHR (w, op1, ri) -> enc_SHR w op1 ri
| SHRD (op1, r, ri) -> enc_SHRD op1 r ri
| SIDT op1 -> enc_SIDT op1
| SLDT op1 -> enc_SLDT op1
| SMSW op1 -> enc_SMSW op1
| STC -> enc_STC
| STD -> enc_STD
| STI -> enc_STI
| STOS w -> enc_STOS w
| STR op1 -> enc_STR op1
| SUB (w, op1, op2) -> enc_SUB pre.op_override w op1 op2
| TEST (w, op1, op2) -> enc_TEST pre.op_override w op1 op2
| UD2 -> enc_UD2
| VERR op1 -> enc_VERR op1
| VERW op1 -> enc_VERW op1
| WBINVD -> enc_WBINVD
| WRMSR -> enc_WRMSR
| XADD (w, op1, op2) -> enc_XADD w op1 op2
| XCHG (w, op1, op2) -> enc_XCHG w op1 op2
| XLAT -> enc_XLAT
| XOR (w, op1, op2) -> enc_XOR pre.op_override w op1 op2
| _ -> invalid

(** val enc_instr : prefix -> instr -> bool list coq_Enc **)

let enc_instr pre i =
  if check_empty_prefix pre
  then enc_all_instr pre i
  else (match i with
        | ADC (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | ADD (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | AND (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | BTC (_, _) -> enc_lock_no_op_override_instr pre i
        | BTR (_, _) -> enc_lock_no_op_override_instr pre i
        | BTS (_, _) -> enc_lock_no_op_override_instr pre i
        | CDQ -> enc_seg_op_override_instr pre i
        | CMOVcc (_, _, _) -> enc_seg_op_override_instr pre i
        | CMP (_, _, _) ->
          if pre.op_override
          then enc_seg_with_op_override_instr pre i
          else enc_seg_override_instr pre i
        | CMPS _ ->
          if check_pre_rep_or_repn pre
          then (match i with
                | CMPS w -> enc_CMPS w
                | SCAS w -> enc_SCAS w
                | _ -> invalid)
          else invalid
        | CMPXCHG (_, _, _) -> enc_lock_no_op_override_instr pre i
        | CWDE -> enc_seg_op_override_instr pre i
        | DEC (_, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | DIV (_, _) -> enc_seg_op_override_instr pre i
        | IDIV (_, _) -> enc_seg_op_override_instr pre i
        | IMUL (_, _, _, _) ->
          if pre.op_override
          then enc_seg_with_op_override_instr pre i
          else enc_seg_override_instr pre i
        | INC (_, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | INS _ -> enc_rep_instr pre i
        | LODS _ -> enc_rep_instr pre i
        | MOV (_, _, _) ->
          if pre.op_override
          then enc_seg_with_op_override_instr pre i
          else enc_seg_override_instr pre i
        | MOVS _ -> enc_rep_instr pre i
        | MOVSX (_, _, _) -> enc_seg_op_override_instr pre i
        | MOVZX (_, _, _) -> enc_seg_op_override_instr pre i
        | MUL (_, _) -> enc_seg_op_override_instr pre i
        | NEG (_, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | NOP _ -> enc_seg_op_override_instr pre i
        | NOT (_, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | OR (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | OUTS _ -> enc_rep_instr pre i
        | RET (_, _) -> enc_rep_instr pre i
        | ROL (_, _, _) -> enc_seg_op_override_instr pre i
        | ROR (_, _, _) -> enc_seg_op_override_instr pre i
        | SAR (_, _, _) -> enc_seg_op_override_instr pre i
        | SBB (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | SCAS _ ->
          if check_pre_rep_or_repn pre
          then (match i with
                | CMPS w -> enc_CMPS w
                | SCAS w -> enc_SCAS w
                | _ -> invalid)
          else invalid
        | SHL (_, _, _) -> enc_seg_op_override_instr pre i
        | SHLD (_, _, _) -> enc_seg_op_override_instr pre i
        | SHR (_, _, _) -> enc_seg_op_override_instr pre i
        | SHRD (_, _, _) -> enc_seg_op_override_instr pre i
        | STOS _ -> enc_rep_instr pre i
        | SUB (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | TEST (_, _, _) ->
          if pre.op_override
          then enc_seg_with_op_override_instr pre i
          else enc_seg_override_instr pre i
        | XADD (_, _, _) -> enc_lock_no_op_override_instr pre i
        | XCHG (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | XOR (_, _, _) ->
          if pre.op_override
          then enc_lock_with_op_override_instr pre i
          else enc_lock_no_op_override_instr pre i
        | _ -> enc_seg_override_instr pre i)

(** val enc_pre_instr : prefix -> instr -> bool list coq_Enc **)

let enc_pre_instr pre ins =
  coq_Bind (Obj.magic coq_EncodingMonad) (enc_prefix pre) (fun l1 ->
    coq_Bind (Obj.magic coq_EncodingMonad) (enc_instr pre ins) (fun l2 ->
      coq_Return (Obj.magic coq_EncodingMonad) (app l1 l2)))

(** val enc_pre_instr_bytes : prefix -> instr -> int8 list coq_Enc **)

let enc_pre_instr_bytes pre ins =
  coq_Bind (Obj.magic coq_EncodingMonad) (Obj.magic enc_pre_instr pre ins)
    (fun lbits -> bits_to_bytes lbits)
