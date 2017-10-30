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

(** val sig_of_bitsn : Big.big_int -> interp -> Big.big_int -> bool **)

let rec sig_of_bitsn n x =
  Big.nat_case
    (fun _ _ ->
    false)
    (fun n' ->
    let f' = sig_of_bitsn n' (snd (Obj.magic x)) in
    (fun x0 -> if zeq x0 (Z.of_nat n') then fst (Obj.magic x) else f' x0))
    n

(** val bitsn_of_sig : Big.big_int -> (Big.big_int -> bool) -> interp **)

let rec bitsn_of_sig n f =
  Big.nat_case
    (fun _ ->
    Obj.magic ())
    (fun n' ->
    Obj.magic ((f (Z.of_nat n')), (bitsn_of_sig n' f)))
    n

(** val int_of_bitsn : Big.big_int -> interp -> interp **)

let int_of_bitsn n v =
  Obj.magic Word.coq_Z_of_bits n (sig_of_bitsn n v)

(** val bitsn_of_int : Big.big_int -> interp -> interp option **)

let bitsn_of_int n i =
  if zle Big.zero (Obj.magic i)
  then if zlt (Obj.magic i) (two_power_nat n)
       then Some (bitsn_of_sig n (Word.bits_of_Z n (Obj.magic i)))
       else None
  else None

(** val intn_of_sig : Big.big_int -> (Big.big_int -> bool) -> Word.int **)

let intn_of_sig n f =
  Word.coq_Z_of_bits (Big.succ n) f

(** val sig_of_intn : Big.big_int -> Word.int -> Big.big_int -> bool **)

let sig_of_intn n i =
  Word.bits_of_Z (Big.succ n) i

(** val intn_of_bitsn : Big.big_int -> interp -> Word.int **)

let intn_of_bitsn n bs =
  intn_of_sig n (sig_of_bitsn (Big.succ n) bs)

(** val bitsn_of_intn : Big.big_int -> Word.int -> interp **)

let bitsn_of_intn n v =
  bitsn_of_sig (Big.succ n) (sig_of_intn n v)

(** val register_to_Z : register -> Big.big_int **)

let register_to_Z = function
| EAX -> Big.zero
| ECX -> Big.one
| EDX -> (Big.double Big.one)
| EBX -> (Big.doubleplusone Big.one)
| ESP -> (Big.double (Big.double Big.one))
| EBP -> (Big.doubleplusone (Big.double Big.one))
| ESI -> (Big.double (Big.doubleplusone Big.one))
| EDI -> (Big.doubleplusone (Big.doubleplusone Big.one))

(** val condition_type_to_Z : condition_type -> Big.big_int **)

let condition_type_to_Z = function
| O_ct -> Big.zero
| NO_ct -> Big.one
| B_ct -> (Big.double Big.one)
| NB_ct -> (Big.doubleplusone Big.one)
| E_ct -> (Big.double (Big.double Big.one))
| NE_ct -> (Big.doubleplusone (Big.double Big.one))
| BE_ct -> (Big.double (Big.doubleplusone Big.one))
| NBE_ct -> (Big.doubleplusone (Big.doubleplusone Big.one))
| S_ct -> (Big.double (Big.double (Big.double Big.one)))
| NS_ct -> (Big.doubleplusone (Big.double (Big.double Big.one)))
| P_ct -> (Big.double (Big.doubleplusone (Big.double Big.one)))
| NP_ct -> (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))
| L_ct -> (Big.double (Big.double (Big.doubleplusone Big.one)))
| NL_ct -> (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))
| LE_ct -> (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))
| NLE_ct ->
  (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))

(** val scale_to_Z : scale -> Big.big_int **)

let scale_to_Z = function
| Scale1 -> Big.zero
| Scale2 -> Big.one
| Scale4 -> (Big.double Big.one)
| Scale8 -> (Big.doubleplusone Big.one)

(** val repr_in_signed_dec :
    Big.big_int -> Big.big_int -> Word.int -> bool **)

let repr_in_signed_dec n1 n2 w =
  if coq_Z_le_dec (Word.signed n1 w) (Word.max_signed n2)
  then coq_Z_le_dec (Word.min_signed n2) (Word.signed n1 w)
  else false

(** val repr_in_signed_byte_dec : int32 -> bool **)

let repr_in_signed_byte_dec w =
  repr_in_signed_dec size32 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ Big.zero))))))) w

(** val repr_in_signed_halfword_dec : int32 -> bool **)

let repr_in_signed_halfword_dec w =
  repr_in_signed_dec size32 (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))) w

(** val sign_shrink32_8 : Word.int -> Word.int **)

let sign_shrink32_8 =
  sign_extend (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))) (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))

(** val sign_shrink32_16 : Word.int -> Word.int **)

let sign_shrink32_16 =
  sign_extend (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero))))))))))))))))))))))))))))))) (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))))))))))))

(** val zero_shrink32_8 : Word.int -> Word.int **)

let zero_shrink32_8 w =
  Word.repr (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ Big.zero))))))) w

(** val repr_in_unsigned_byte_dec : int32 -> bool **)

let repr_in_unsigned_byte_dec w =
  coq_Z_le_dec w
    (Word.max_unsigned (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ Big.zero))))))))

(** val bit : bool -> bigrammar **)

let bit b =
  Char b

(** val anybit : bigrammar **)

let anybit =
  Any

(** val bits : char list -> bigrammar **)

let rec bits = function
| [] -> empty
| c::s' -> seq (bit (if (=) c '0' then false else true)) (bits s')

(** val tuples_of_string : char list -> interp **)

let rec tuples_of_string = function
| [] -> Obj.magic ()
| a::s' ->
  Obj.magic ((if (=) a '0' then false else true), (tuples_of_string s'))

(** val bitsmatch : char list -> bigrammar **)

let bitsmatch s =
  map (bits s) ((fun _ -> Obj.magic ()), (fun _ -> Some
    (tuples_of_string s)))

(** val bitsleft : char list -> bigrammar -> bigrammar **)

let bitsleft s p =
  map (seq (bitsmatch s) p) ((Obj.magic snd), (fun v -> Some
    (Obj.magic ((), v))))

(** val field' : Big.big_int -> bigrammar **)

let rec field' n =
  Big.nat_case
    (fun _ ->
    empty)
    (fun n0 ->
    seq anybit (field' n0))
    n

(** val field : Big.big_int -> bigrammar **)

let field n =
  map (field' n) ((int_of_bitsn n), (bitsn_of_int n))

(** val reg : bigrammar **)

let reg =
  map (field (Big.succ (Big.succ (Big.succ Big.zero))))
    ((Obj.magic coq_Z_to_register), (fun r -> Some
    (Obj.magic register_to_Z r)))

(** val int_n : Big.big_int -> bigrammar **)

let int_n n =
  map (field (Big.succ n)) ((Obj.magic Word.repr n), (fun b -> Some
    (Obj.magic b)))

(** val intn_cat :
    Big.big_int -> Big.big_int -> Word.int -> Word.int -> Word.int **)

let intn_cat n m b1 b2 =
  let sig1 = sig_of_intn n b1 in
  let sig2 = sig_of_intn m b2 in
  intn_of_sig (add (add n m) (Big.succ Big.zero))
    (Word.sig_cat (Big.succ m) sig1 sig2)

(** val intn_split1 : Big.big_int -> Big.big_int -> Word.int -> Word.int **)

let intn_split1 n m b =
  intn_of_sig n
    (Word.sig_split1 (Big.succ m)
      (sig_of_intn (add (add n m) (Big.succ Big.zero)) b))

(** val intn_split2 : Big.big_int -> Big.big_int -> Word.int -> Word.int **)

let intn_split2 n m b =
  intn_of_sig m (fun i ->
    if zlt i (Z.of_nat (Big.succ m))
    then sig_of_intn (add (add n m) (Big.succ Big.zero)) b i
    else false)

(** val intn_cat_little :
    Big.big_int -> Big.big_int -> bigrammar -> bigrammar -> bigrammar **)

let intn_cat_little n m p1 p2 =
  map (seq p1 p2) ((fun bs ->
    Obj.magic intn_cat m n (snd (Obj.magic bs)) (fst (Obj.magic bs))),
    (fun b -> Some
    (Obj.magic ((intn_split2 m n (Obj.magic b)),
      (intn_split1 m n (Obj.magic b))))))

(** val byte : bigrammar **)

let byte =
  int_n (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    Big.zero)))))))

(** val halfword : bigrammar **)

let halfword =
  intn_cat_little (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ Big.zero))))))) (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ (Big.succ Big.zero))))))) byte byte

(** val word : bigrammar **)

let word =
  intn_cat_little
    (add
      (add (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ Big.zero))))))) (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
        (Big.succ (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))))
      (Big.succ Big.zero)) (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
    (Big.succ (Big.succ Big.zero)))))))
    (intn_cat_little (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      (Big.succ (Big.succ (Big.succ Big.zero))))))))))))))) (Big.succ
      (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ (Big.succ
      Big.zero))))))) halfword byte) byte

(** val tttn : bigrammar **)

let tttn =
  map (field (Big.succ (Big.succ (Big.succ (Big.succ Big.zero)))))
    ((Obj.magic coq_Z_to_condition_type), (fun ct -> Some
    (Obj.magic condition_type_to_Z ct)))

(** val control_reg_b : bigrammar **)

let control_reg_b =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsmatch ('0'::('0'::('0'::[])))), (fun _ -> Obj.magic CR0))), (BLeaf
    (Big.one, (bitsmatch ('0'::('1'::('0'::[])))), (fun _ ->
    Obj.magic CR2))))), (BNode ((Big.double Big.one), (BLeaf ((Big.double
    Big.one), (bitsmatch ('0'::('1'::('1'::[])))), (fun _ ->
    Obj.magic CR3))), (BLeaf ((Big.doubleplusone Big.one),
    (bitsmatch ('1'::('0'::('0'::[])))), (fun _ -> Obj.magic CR4))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | CR0 -> inv_case_some case0 (Obj.magic ())
    | CR2 -> inv_case_some case1 (Obj.magic ())
    | CR3 -> inv_case_some case2 (Obj.magic ())
    | CR4 -> inv_case_some case3 (Obj.magic ())))

(** val debug_reg_b : bigrammar **)

let debug_reg_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero, (bitsmatch ('0'::('0'::('0'::[])))), (fun _ ->
    Obj.magic DR0))), (BLeaf (Big.one, (bitsmatch ('0'::('0'::('1'::[])))),
    (fun _ -> Obj.magic DR1))))), (BLeaf ((Big.double Big.one),
    (bitsmatch ('0'::('1'::('0'::[])))), (fun _ -> Obj.magic DR2))))), (BNode
    ((Big.double (Big.double Big.one)), (BNode ((Big.doubleplusone Big.one),
    (BLeaf ((Big.doubleplusone Big.one), (bitsmatch ('0'::('1'::('1'::[])))),
    (fun _ -> Obj.magic DR3))), (BLeaf ((Big.double (Big.double Big.one)),
    (bitsmatch ('1'::('1'::('0'::[])))), (fun _ -> Obj.magic DR6))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)),
    (bitsmatch ('1'::('1'::('1'::[])))), (fun _ -> Obj.magic DR7))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree (MLTree MLeaf)) in
  let case4 = MRTree (MLTree (MRTree MLeaf)) in
  let case5 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | DR0 -> inv_case_some case0 (Obj.magic ())
    | DR1 -> inv_case_some case1 (Obj.magic ())
    | DR2 -> inv_case_some case2 (Obj.magic ())
    | DR3 -> inv_case_some case3 (Obj.magic ())
    | DR6 -> inv_case_some case4 (Obj.magic ())
    | DR7 -> inv_case_some case5 (Obj.magic ())))

(** val segment_reg_b : bigrammar **)

let segment_reg_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero, (bitsmatch ('0'::('0'::('0'::[])))), (fun _ ->
    Obj.magic ES))), (BLeaf (Big.one, (bitsmatch ('0'::('0'::('1'::[])))),
    (fun _ -> Obj.magic CS))))), (BLeaf ((Big.double Big.one),
    (bitsmatch ('0'::('1'::('0'::[])))), (fun _ -> Obj.magic SS))))), (BNode
    ((Big.double (Big.double Big.one)), (BNode ((Big.doubleplusone Big.one),
    (BLeaf ((Big.doubleplusone Big.one), (bitsmatch ('0'::('1'::('1'::[])))),
    (fun _ -> Obj.magic DS))), (BLeaf ((Big.double (Big.double Big.one)),
    (bitsmatch ('1'::('0'::('0'::[])))), (fun _ -> Obj.magic FS))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)),
    (bitsmatch ('1'::('0'::('1'::[])))), (fun _ -> Obj.magic GS))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree (MLTree MLeaf)) in
  let case4 = MRTree (MLTree (MRTree MLeaf)) in
  let case5 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | ES -> inv_case_some case0 (Obj.magic ())
    | CS -> inv_case_some case1 (Obj.magic ())
    | SS -> inv_case_some case2 (Obj.magic ())
    | DS -> inv_case_some case3 (Obj.magic ())
    | FS -> inv_case_some case4 (Obj.magic ())
    | GS -> inv_case_some case5 (Obj.magic ())))

(** val field_intn : Big.big_int -> bigrammar **)

let field_intn n =
  map (field' (Big.succ n)) ((Obj.magic intn_of_bitsn n), (fun i -> Some
    (bitsn_of_intn n (Obj.magic i))))

(** val fpu_reg : bigrammar **)

let fpu_reg =
  field_intn (Big.succ (Big.succ Big.zero))

(** val mmx_reg : bigrammar **)

let mmx_reg =
  field_intn (Big.succ (Big.succ Big.zero))

(** val sse_reg : bigrammar **)

let sse_reg =
  field_intn (Big.succ (Big.succ Big.zero))

(** val scale_b : bigrammar **)

let scale_b =
  map (field (Big.succ (Big.succ Big.zero))) ((Obj.magic coq_Z_to_scale),
    (fun s -> Some (Obj.magic scale_to_Z s)))

(** val reg_no_esp : bigrammar **)

let reg_no_esp =
  let gt = BNode ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode
    (Big.zero, (BLeaf (Big.zero, (bitsmatch ('0'::('0'::('0'::[])))),
    (fun _ -> Obj.magic EAX))), (BLeaf (Big.one,
    (bitsmatch ('0'::('0'::('1'::[])))), (fun _ -> Obj.magic ECX))))), (BNode
    ((Big.double Big.one), (BLeaf ((Big.double Big.one),
    (bitsmatch ('0'::('1'::('0'::[])))), (fun _ -> Obj.magic EDX))), (BLeaf
    ((Big.doubleplusone Big.one), (bitsmatch ('0'::('1'::('1'::[])))),
    (fun _ -> Obj.magic EBX))))))), (BNode ((Big.doubleplusone (Big.double
    Big.one)), (BNode ((Big.double (Big.double Big.one)), (BLeaf ((Big.double
    (Big.double Big.one)), (bitsmatch ('1'::('0'::('1'::[])))), (fun _ ->
    Obj.magic EBP))), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    (bitsmatch ('1'::('1'::('0'::[])))), (fun _ -> Obj.magic ESI))))), (BLeaf
    ((Big.double (Big.doubleplusone Big.one)),
    (bitsmatch ('1'::('1'::('1'::[])))), (fun _ -> Obj.magic EDI))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree (MLTree MLeaf)) in
  let case3 = MLTree (MRTree (MRTree MLeaf)) in
  let case4 = MRTree (MLTree (MLTree MLeaf)) in
  let case5 = MRTree (MLTree (MRTree MLeaf)) in
  let case6 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun r ->
    match Obj.magic r with
    | EAX -> inv_case_some case0 (Obj.magic ())
    | ECX -> inv_case_some case1 (Obj.magic ())
    | EDX -> inv_case_some case2 (Obj.magic ())
    | EBX -> inv_case_some case3 (Obj.magic ())
    | ESP -> None
    | EBP -> inv_case_some case4 (Obj.magic ())
    | ESI -> inv_case_some case5 (Obj.magic ())
    | EDI -> inv_case_some case6 (Obj.magic ())))

(** val reg_no_ebp : bigrammar **)

let reg_no_ebp =
  map
    (alt
      (alt (bitsmatch ('0'::('0'::('0'::[]))))
        (alt (bitsmatch ('0'::('0'::('1'::[]))))
          (bitsmatch ('0'::('1'::('0'::[]))))))
      (alt
        (alt (bitsmatch ('0'::('1'::('1'::[]))))
          (bitsmatch ('1'::('0'::('0'::[])))))
        (alt (bitsmatch ('1'::('1'::('0'::[]))))
          (bitsmatch ('1'::('1'::('1'::[]))))))) ((fun s ->
    match Obj.magic s with
    | Coq_inl y ->
      (match y with
       | Coq_inl _ -> Obj.magic EAX
       | Coq_inr y0 ->
         (match y0 with
          | Coq_inl _ -> Obj.magic ECX
          | Coq_inr _ -> Obj.magic EDX))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         (match y0 with
          | Coq_inl _ -> Obj.magic EBX
          | Coq_inr _ -> Obj.magic ESP)
       | Coq_inr y0 ->
         (match y0 with
          | Coq_inl _ -> Obj.magic ESI
          | Coq_inr _ -> Obj.magic EDI))), (fun r ->
    match Obj.magic r with
    | EAX -> Some (Obj.magic (Coq_inl (Coq_inl ())))
    | ECX -> Some (Obj.magic (Coq_inl (Coq_inr (Coq_inl ()))))
    | EDX -> Some (Obj.magic (Coq_inl (Coq_inr (Coq_inr ()))))
    | EBX -> Some (Obj.magic (Coq_inr (Coq_inl (Coq_inl ()))))
    | ESP -> Some (Obj.magic (Coq_inr (Coq_inl (Coq_inr ()))))
    | EBP -> None
    | ESI -> Some (Obj.magic (Coq_inr (Coq_inr (Coq_inl ()))))
    | EDI -> Some (Obj.magic (Coq_inr (Coq_inr (Coq_inr ()))))))

(** val reg_no_esp_ebp : bigrammar **)

let reg_no_esp_ebp =
  map
    (alt
      (alt (bitsmatch ('0'::('0'::('0'::[]))))
        (alt (bitsmatch ('0'::('0'::('1'::[]))))
          (bitsmatch ('0'::('1'::('0'::[]))))))
      (alt (bitsmatch ('0'::('1'::('1'::[]))))
        (alt (bitsmatch ('1'::('1'::('0'::[]))))
          (bitsmatch ('1'::('1'::('1'::[]))))))) ((fun u ->
    match Obj.magic u with
    | Coq_inl y ->
      (match y with
       | Coq_inl _ -> Obj.magic EAX
       | Coq_inr y0 ->
         (match y0 with
          | Coq_inl _ -> Obj.magic ECX
          | Coq_inr _ -> Obj.magic EDX))
    | Coq_inr y ->
      (match y with
       | Coq_inl _ -> Obj.magic EBX
       | Coq_inr y0 ->
         (match y0 with
          | Coq_inl _ -> Obj.magic ESI
          | Coq_inr _ -> Obj.magic EDI))), (fun r ->
    match Obj.magic r with
    | EAX -> Some (Obj.magic (Coq_inl (Coq_inl ())))
    | ECX -> Some (Obj.magic (Coq_inl (Coq_inr (Coq_inl ()))))
    | EDX -> Some (Obj.magic (Coq_inl (Coq_inr (Coq_inr ()))))
    | EBX -> Some (Obj.magic (Coq_inr (Coq_inl ())))
    | ESI -> Some (Obj.magic (Coq_inr (Coq_inr (Coq_inl ()))))
    | EDI -> Some (Obj.magic (Coq_inr (Coq_inr (Coq_inr ()))))
    | _ -> None))

(** val si_b : bigrammar **)

let si_b =
  map (seq scale_b reg) ((fun p ->
    match snd (Obj.magic p) with
    | ESP -> Obj.magic None
    | _ -> Obj.magic (Some p)), (fun v ->
    match Obj.magic v with
    | Some y ->
      let (s, p) = y in
      (match p with
       | ESP -> None
       | _ -> Some (Obj.magic (s, p)))
    | None -> Some (Obj.magic (Scale1, ESP))))

(** val sib_b : bigrammar **)

let sib_b =
  seq si_b reg

(** val coq_Address_op_inv : operand -> address option **)

let coq_Address_op_inv = function
| Address_op addr -> Some addr
| _ -> None

(** val coq_SSE_Addr_op_inv : sse_operand -> address option **)

let coq_SSE_Addr_op_inv = function
| SSE_Addr_op addr -> Some addr
| _ -> None

(** val rm00 : bigrammar **)

let rm00 =
  alt
    (alt reg_no_esp_ebp
      (bitsleft ('1'::('0'::('0'::[]))) (seq si_b reg_no_ebp)))
    (alt
      (bitsleft ('1'::('0'::('0'::[])))
        (seq si_b (bitsleft ('1'::('0'::('1'::[]))) word)))
      (bitsleft ('1'::('0'::('1'::[]))) word))

(** val rm01 : bigrammar **)

let rm01 =
  alt (seq reg_no_esp byte)
    (bitsleft ('1'::('0'::('0'::[]))) (seq sib_b byte))

(** val rm10 : bigrammar **)

let rm10 =
  alt (seq reg_no_esp word)
    (bitsleft ('1'::('0'::('0'::[]))) (seq sib_b word))

(** val modrm_gen_noreg : bigrammar -> bigrammar **)

let modrm_gen_noreg reg_b =
  map
    (alt (bitsleft ('0'::('0'::[])) (seq reg_b rm00))
      (alt (bitsleft ('0'::('1'::[])) (seq reg_b rm01))
        (bitsleft ('1'::('0'::[])) (seq reg_b rm10)))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (r, v1) = y in
      let addr =
        match v1 with
        | Coq_inl y0 ->
          (match y0 with
           | Coq_inl base ->
             { addrDisp = (Word.repr size32 Big.zero); addrBase = (Some
               base); addrIndex = None }
           | Coq_inr y1 ->
             let (si, base) = y1 in
             { addrDisp = (Word.repr size32 Big.zero); addrBase = (Some
             base); addrIndex = si })
        | Coq_inr y0 ->
          (match y0 with
           | Coq_inl y1 ->
             let (si, disp) = y1 in
             { addrDisp = disp; addrBase = None; addrIndex = si }
           | Coq_inr disp ->
             { addrDisp = disp; addrBase = None; addrIndex = None })
      in
      Obj.magic (r, addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         let (r, v1) = y0 in
         let addr =
           match v1 with
           | Coq_inl y1 ->
             let (bs, disp) = y1 in
             { addrDisp = (sign_extend8_32 disp); addrBase = (Some bs);
             addrIndex = None }
           | Coq_inr y1 ->
             let (y2, disp) = y1 in
             let (si, bs) = y2 in
             { addrDisp = (sign_extend8_32 disp); addrBase = (Some bs);
             addrIndex = si }
         in
         Obj.magic (r, addr)
       | Coq_inr y0 ->
         let (r, v1) = y0 in
         let addr =
           match v1 with
           | Coq_inl y1 ->
             let (bs, disp) = y1 in
             { addrDisp = disp; addrBase = (Some bs); addrIndex = None }
           | Coq_inr y1 ->
             let (y2, disp) = y1 in
             let (si, bs) = y2 in
             { addrDisp = disp; addrBase = (Some bs); addrIndex = si }
         in
         Obj.magic (r, addr))), (fun u ->
    let (r, addr) = Obj.magic u in
    let { addrDisp = disp; addrBase = addrBase0; addrIndex = addrIndex0 } =
      addr
    in
    (match addrBase0 with
     | Some bs ->
       (match addrIndex0 with
        | Some sci ->
          if register_eq_dec (snd sci) ESP
          then None
          else if register_eq_dec bs EBP
               then if repr_in_signed_byte_dec disp
                    then Some
                           (Obj.magic (Coq_inr (Coq_inl (r, (Coq_inr (((Some
                             sci), bs), (sign_shrink32_8 disp)))))))
                    else Some
                           (Obj.magic (Coq_inr (Coq_inr (r, (Coq_inr (((Some
                             sci), bs), disp))))))
               else if zeq disp (Word.zero size32)
                    then Some
                           (Obj.magic (Coq_inl (r, (Coq_inl (Coq_inr ((Some
                             sci), bs))))))
                    else if repr_in_signed_byte_dec disp
                         then Some
                                (Obj.magic (Coq_inr (Coq_inl (r, (Coq_inr
                                  (((Some sci), bs),
                                  (sign_shrink32_8 disp)))))))
                         else Some
                                (Obj.magic (Coq_inr (Coq_inr (r, (Coq_inr
                                  (((Some sci), bs), disp))))))
        | None ->
          if register_eq_dec bs ESP
          then if zeq disp (Word.zero size32)
               then Some
                      (Obj.magic (Coq_inl (r, (Coq_inl (Coq_inr (None,
                        ESP))))))
               else if repr_in_signed_byte_dec disp
                    then Some
                           (Obj.magic (Coq_inr (Coq_inl (r, (Coq_inr ((None,
                             ESP), (sign_shrink32_8 disp)))))))
                    else Some
                           (Obj.magic (Coq_inr (Coq_inr (r, (Coq_inr ((None,
                             ESP), disp))))))
          else if register_eq_dec bs EBP
               then if repr_in_signed_byte_dec disp
                    then Some
                           (Obj.magic (Coq_inr (Coq_inl (r, (Coq_inl (bs,
                             (sign_shrink32_8 disp)))))))
                    else Some
                           (Obj.magic (Coq_inr (Coq_inr (r, (Coq_inl (bs,
                             disp))))))
               else if zeq disp (Word.zero size32)
                    then Some
                           (Obj.magic (Coq_inl (r, (Coq_inl (Coq_inl bs)))))
                    else if repr_in_signed_byte_dec disp
                         then Some
                                (Obj.magic (Coq_inr (Coq_inl (r, (Coq_inl
                                  (bs, (sign_shrink32_8 disp)))))))
                         else Some
                                (Obj.magic (Coq_inr (Coq_inr (r, (Coq_inl
                                  (bs, disp)))))))
     | None ->
       (match addrIndex0 with
        | Some si ->
          Some
            (Obj.magic (Coq_inl (r, (Coq_inr (Coq_inl ((Some si), disp))))))
        | None -> Some (Obj.magic (Coq_inl (r, (Coq_inr (Coq_inr disp)))))))))

(** val modrm_gen : bigrammar -> bigrammar **)

let modrm_gen reg_b =
  alt (modrm_gen_noreg reg_b) (bitsleft ('1'::('1'::[])) (seq reg_b reg_b))

(** val ext_op_modrm_noreg_ret_addr : char list -> bigrammar **)

let ext_op_modrm_noreg_ret_addr bs =
  map (modrm_gen_noreg (bitsmatch bs)) ((fun v -> snd (Obj.magic v)),
    (fun u -> Some (Obj.magic ((), u))))

(** val ext_op_modrm_noreg : char list -> bigrammar **)

let ext_op_modrm_noreg bs =
  map (ext_op_modrm_noreg_ret_addr bs) ((Obj.magic (fun x -> Address_op x)),
    (Obj.magic coq_Address_op_inv))

(** val modrm_ret_reg : bigrammar **)

let modrm_ret_reg =
  map (modrm_gen reg) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (r, addr) = y in Obj.magic (r, (Address_op addr))
    | Coq_inr y -> let (r1, r2) = y in Obj.magic (r1, (Reg_op r2))),
    (fun u ->
    let (r1, y) = Obj.magic u in
    (match y with
     | Reg_op r2 -> Some (Obj.magic (Coq_inr (r1, r2)))
     | Address_op addr -> Some (Obj.magic (Coq_inl (r1, addr)))
     | _ -> None)))

(** val modrm : bigrammar **)

let modrm =
  map modrm_ret_reg ((fun v ->
    let (r1, op2) = Obj.magic v in Obj.magic ((Reg_op r1), op2)), (fun u ->
    let (y, op2) = Obj.magic u in
    (match y with
     | Reg_op r1 -> Some (Obj.magic (r1, op2))
     | _ -> None)))

(** val modrm_noreg : bigrammar **)

let modrm_noreg =
  modrm_gen_noreg reg

(** val modrm_bv2_noreg : bigrammar **)

let modrm_bv2_noreg =
  modrm_gen_noreg (field_intn (Big.succ (Big.succ Big.zero)))

(** val ext_op_modrm : char list -> bigrammar **)

let ext_op_modrm bs =
  map
    (alt (ext_op_modrm_noreg_ret_addr bs)
      (bitsleft ('1'::('1'::[])) (bitsleft bs reg))) ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (Address_op addr)
    | Coq_inr r -> Obj.magic (Reg_op r)), (fun u ->
    match Obj.magic u with
    | Reg_op r -> Some (Obj.magic (Coq_inr r))
    | Address_op addr -> Some (Obj.magic (Coq_inl addr))
    | _ -> None))

(** val seg_modrm : bigrammar **)

let seg_modrm =
  map
    (alt (modrm_gen_noreg segment_reg_b)
      (bitsleft ('1'::('1'::[])) (seq segment_reg_b reg))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (sr, addr) = y in Obj.magic (sr, (Address_op addr))
    | Coq_inr y -> let (sr, r) = y in Obj.magic (sr, (Reg_op r))), (fun u ->
    let (sr, y) = Obj.magic u in
    (match y with
     | Reg_op r -> Some (Obj.magic (Coq_inr (sr, r)))
     | Address_op addr -> Some (Obj.magic (Coq_inl (sr, addr)))
     | _ -> None)))

(** val imm_b : bool -> bigrammar **)

let imm_b = function
| true ->
  map halfword ((fun w -> Obj.magic sign_extend16_32 w), (fun w ->
    if repr_in_signed_halfword_dec (Obj.magic w)
    then Some (Obj.magic sign_shrink32_16 w)
    else None))
| false -> word

(** val coq_AAA_b : bigrammar **)

let coq_AAA_b =
  bitsmatch ('0'::('0'::('1'::('1'::('0'::('1'::('1'::('1'::[]))))))))

(** val coq_AAD_b : bigrammar **)

let coq_AAD_b =
  bitsmatch
    ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))

(** val coq_AAM_b : bigrammar **)

let coq_AAM_b =
  bitsmatch
    ('1'::('1'::('0'::('1'::('0'::('1'::('0'::('0'::('0'::('0'::('0'::('0'::('1'::('0'::('1'::('0'::[]))))))))))))))))

(** val coq_AAS_b : bigrammar **)

let coq_AAS_b =
  bitsmatch ('0'::('0'::('1'::('1'::('1'::('1'::('1'::('1'::[]))))))))

(** val logic_or_arith_b : bool -> char list -> char list -> bigrammar **)

let logic_or_arith_b opsize_override opcode1 opcode2 =
  let gt = BNode ((Big.double (Big.double Big.one)), (BNode ((Big.double
    Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft opcode1
      (bitsleft ('0'::[]) (seq anybit (seq anybit modrm_ret_reg)))),
    (fun v ->
    let (d, i) = Obj.magic v in
    let (w, i0) = i in
    let (r1, op2) = i0 in
    if d
    then Obj.magic (w, ((Reg_op r1), op2))
    else Obj.magic (w, (op2, (Reg_op r1)))))), (BLeaf (Big.one,
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::[])) (bitsleft opcode2 (seq reg byte))))),
    (fun v ->
    let (r, imm) = Obj.magic v in
    Obj.magic (true, ((Reg_op r), (Imm_op (sign_extend8_32 imm))))))))),
    (BLeaf ((Big.double Big.one),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::[])) (bitsleft opcode2 (seq reg byte))))),
    (fun v ->
    let (r, imm) = Obj.magic v in
    Obj.magic (false, ((Reg_op r), (Imm_op (zero_extend8_32 imm))))))))),
    (BNode ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::[]))
          (bitsleft opcode2 (seq reg (imm_b opsize_override)))))), (fun v ->
    let (r, imm) = Obj.magic v in
    Obj.magic (true, ((Reg_op r), (Imm_op imm)))))), (BLeaf ((Big.double
    (Big.double Big.one)),
    (bitsleft opcode1 (bitsleft ('1'::('0'::('0'::[]))) byte)), (fun imm ->
    Obj.magic (false, ((Reg_op EAX), (Imm_op
      (zero_extend8_32 (Obj.magic imm)))))))))))), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BNode ((Big.doubleplusone (Big.double
    Big.one)), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    (bitsleft opcode1
      (bitsleft ('1'::('0'::('1'::[]))) (imm_b opsize_override))),
    (fun imm ->
    Obj.magic (true, ((Reg_op EAX), (Imm_op (Obj.magic imm))))))), (BLeaf
    ((Big.double (Big.doubleplusone Big.one)),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (seq (ext_op_modrm_noreg_ret_addr opcode2) byte))), (fun v ->
    let (addr, imm) = Obj.magic v in
    Obj.magic (false, ((Address_op addr), (Imm_op (zero_extend8_32 imm))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone Big.one)), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (seq (ext_op_modrm_noreg_ret_addr opcode2) byte))), (fun v ->
    let (addr, imm) = Obj.magic v in
    Obj.magic (true, ((Address_op addr), (Imm_op (sign_extend8_32 imm))))))),
    (BLeaf ((Big.double (Big.double (Big.double Big.one))),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (seq (ext_op_modrm_noreg_ret_addr opcode2) (imm_b opsize_override)))),
    (fun v ->
    let (addr, imm) = Obj.magic v in
    Obj.magic (true, ((Address_op addr), (Imm_op imm)))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree MLeaf))) in
  let case1 = MLTree (MLTree (MLTree (MRTree MLeaf))) in
  let case2 = MLTree (MLTree (MRTree MLeaf)) in
  let case3 = MLTree (MRTree (MLTree MLeaf)) in
  let case4 = MLTree (MRTree (MRTree MLeaf)) in
  let case5 = MRTree (MLTree (MLTree MLeaf)) in
  let case6 = MRTree (MLTree (MRTree MLeaf)) in
  let case7 = MRTree (MRTree (MLTree MLeaf)) in
  let case8 = MRTree (MRTree (MRTree MLeaf)) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (w, ops) = Obj.magic u in
    let (op1, op2) = ops in
    (match op1 with
     | Reg_op r1 ->
       (match op2 with
        | Imm_op imm ->
          (match r1 with
           | EAX ->
             if w
             then inv_case_some case5 (Obj.magic imm)
             else if repr_in_unsigned_byte_dec imm
                  then inv_case_some case4 (Obj.magic zero_shrink32_8 imm)
                  else None
           | _ ->
             if w
             then if repr_in_signed_byte_dec imm
                  then inv_case_some case1
                         (Obj.magic (r1, (sign_shrink32_8 imm)))
                  else inv_case_some case3 (Obj.magic (r1, imm))
             else if repr_in_unsigned_byte_dec imm
                  then inv_case_some case2
                         (Obj.magic (r1, (zero_shrink32_8 imm)))
                  else None)
        | Offset_op _ -> None
        | x -> inv_case_some case0 (Obj.magic (true, (w, (r1, x)))))
     | Address_op a ->
       (match op2 with
        | Imm_op imm ->
          if w
          then if repr_in_signed_byte_dec imm
               then inv_case_some case7
                      (Obj.magic (a, (sign_shrink32_8 imm)))
               else inv_case_some case8 (Obj.magic (a, imm))
          else if repr_in_unsigned_byte_dec imm
               then inv_case_some case6
                      (Obj.magic (a, (zero_shrink32_8 imm)))
               else None
        | Reg_op r2 ->
          inv_case_some case0 (Obj.magic (false, (w, (r2, (Address_op a)))))
        | _ -> None)
     | _ -> None)))

(** val coq_ADC_b : bool -> bigrammar **)

let coq_ADC_b s =
  logic_or_arith_b s ('0'::('0'::('0'::('1'::('0'::[])))))
    ('0'::('1'::('0'::[])))

(** val coq_ADD_b : bool -> bigrammar **)

let coq_ADD_b s =
  logic_or_arith_b s ('0'::('0'::('0'::('0'::('0'::[])))))
    ('0'::('0'::('0'::[])))

(** val coq_AND_b : bool -> bigrammar **)

let coq_AND_b s =
  logic_or_arith_b s ('0'::('0'::('1'::('0'::('0'::[])))))
    ('1'::('0'::('0'::[])))

(** val coq_CMP_b : bool -> bigrammar **)

let coq_CMP_b s =
  logic_or_arith_b s ('0'::('0'::('1'::('1'::('1'::[])))))
    ('1'::('1'::('1'::[])))

(** val coq_OR_b : bool -> bigrammar **)

let coq_OR_b s =
  logic_or_arith_b s ('0'::('0'::('0'::('0'::('1'::[])))))
    ('0'::('0'::('1'::[])))

(** val coq_SBB_b : bool -> bigrammar **)

let coq_SBB_b s =
  logic_or_arith_b s ('0'::('0'::('0'::('1'::('1'::[])))))
    ('0'::('1'::('1'::[])))

(** val coq_SUB_b : bool -> bigrammar **)

let coq_SUB_b s =
  logic_or_arith_b s ('0'::('0'::('1'::('0'::('1'::[])))))
    ('1'::('0'::('1'::[])))

(** val coq_XOR_b : bool -> bigrammar **)

let coq_XOR_b s =
  logic_or_arith_b s ('0'::('0'::('1'::('1'::('0'::[])))))
    ('1'::('1'::('0'::[])))

(** val coq_ARPL_b : bigrammar **)

let coq_ARPL_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm)

(** val coq_BOUND_b : bigrammar **)

let coq_BOUND_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm)

(** val coq_BSF_b : bigrammar **)

let coq_BSF_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('0'::('0'::[])))) modrm)))

(** val coq_BSR_b : bigrammar **)

let coq_BSR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('0'::('1'::[])))) modrm)))

(** val coq_BSWAP_b : bigrammar **)

let coq_BSWAP_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('0'::[])))) (bitsleft ('1'::[]) reg)))

(** val bit_test_b : char list -> char list -> bigrammar **)

let bit_test_b opcode1 opcode2 =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('1'::[]))))
          (bitsleft ('1'::('0'::('1'::('0'::[]))))
            (bitsleft ('1'::('1'::[])) (bitsleft opcode1 (seq reg byte))))))),
    (fun v ->
    let (r1, b) = Obj.magic v in
    Obj.magic ((Reg_op r1), (Imm_op (zero_extend8_32 b)))))), (BLeaf
    (Big.one,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('1'::[]))))
          (bitsleft ('1'::('0'::('1'::('0'::[]))))
            (seq (ext_op_modrm_noreg_ret_addr opcode1) byte))))), (fun v ->
    let (addr, b) = Obj.magic v in
    Obj.magic ((Address_op addr), (Imm_op (zero_extend8_32 b)))))))), (BLeaf
    ((Big.double Big.one),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::[])))
          (bitsleft opcode2 (bitsleft ('0'::('1'::('1'::[]))) modrm_ret_reg))))),
    (fun v -> let (r2, op1) = Obj.magic v in Obj.magic (op1, (Reg_op r2))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree MLeaf in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (op1, op2) = Obj.magic u in
    (match op1 with
     | Reg_op r1 ->
       (match op2 with
        | Imm_op b ->
          if repr_in_unsigned_byte_dec b
          then inv_case_some case0 (Obj.magic (r1, (zero_shrink32_8 b)))
          else None
        | Reg_op r2 -> inv_case_some case2 (Obj.magic (r2, op1))
        | _ -> None)
     | Address_op addr ->
       (match op2 with
        | Imm_op b ->
          if repr_in_unsigned_byte_dec b
          then inv_case_some case1 (Obj.magic (addr, (zero_shrink32_8 b)))
          else None
        | Reg_op r2 -> inv_case_some case2 (Obj.magic (r2, op1))
        | _ -> None)
     | _ -> None)))

(** val coq_BT_b : bigrammar **)

let coq_BT_b =
  bit_test_b ('1'::('0'::('0'::[]))) ('0'::('0'::[]))

(** val coq_BTC_b : bigrammar **)

let coq_BTC_b =
  bit_test_b ('1'::('1'::('1'::[]))) ('1'::('1'::[]))

(** val coq_BTR_b : bigrammar **)

let coq_BTR_b =
  bit_test_b ('1'::('1'::('0'::[]))) ('1'::('0'::[]))

(** val coq_BTS_b : bigrammar **)

let coq_BTS_b =
  bit_test_b ('1'::('0'::('1'::[]))) ('0'::('1'::[]))

(** val coq_CALL_b : bigrammar **)

let coq_CALL_b =
  map
    (alt
      (alt
        (bitsleft ('1'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('0'::('0'::('0'::[])))) word))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm ('0'::('1'::('0'::[])))))))
      (alt
        (bitsleft ('1'::('0'::('0'::('1'::[]))))
          (bitsleft ('1'::('0'::('1'::('0'::[])))) (seq word halfword)))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::('1'::[]))))
            (ext_op_modrm ('0'::('1'::('1'::[])))))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      (match y with
       | Coq_inl w -> Obj.magic (true, (false, ((Imm_op w), None)))
       | Coq_inr op -> Obj.magic (true, (true, (op, None))))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         let (w, hw) = y0 in
         Obj.magic (false, (true, ((Imm_op w), (Some hw))))
       | Coq_inr op -> Obj.magic (false, (true, (op, None))))), (fun u ->
    let (near, u1) = Obj.magic u in
    let (absolute, opsel) = u1 in
    if near
    then if absolute
         then let (i, i0) = opsel in
              (match i with
               | Reg_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> Some (Obj.magic (Coq_inl (Coq_inr (fst opsel)))))
               | Address_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> Some (Obj.magic (Coq_inl (Coq_inr (fst opsel)))))
               | _ -> None)
         else let (i, i0) = opsel in
              (match i with
               | Imm_op w ->
                 (match i0 with
                  | Some _ -> None
                  | None -> Some (Obj.magic (Coq_inl (Coq_inl w))))
               | _ -> None)
    else if absolute
         then let (i, i0) = opsel in
              (match i with
               | Imm_op w ->
                 (match i0 with
                  | Some hw -> Some (Obj.magic (Coq_inr (Coq_inl (w, hw))))
                  | None -> None)
               | Reg_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> Some (Obj.magic (Coq_inr (Coq_inr (fst opsel)))))
               | Address_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> Some (Obj.magic (Coq_inr (Coq_inr (fst opsel)))))
               | Offset_op _ -> None)
         else None))

(** val coq_CDQ_b : bigrammar **)

let coq_CDQ_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('0'::('0'::('1'::[])))))

(** val coq_CLC_b : bigrammar **)

let coq_CLC_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('0'::('0'::('0'::[])))))

(** val coq_CLD_b : bigrammar **)

let coq_CLD_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('1'::('0'::('0'::[])))))

(** val coq_CLI_b : bigrammar **)

let coq_CLI_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('0'::('1'::('0'::[])))))

(** val coq_CLTS_b : bigrammar **)

let coq_CLTS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsmatch ('0'::('1'::('1'::('0'::[])))))))

(** val coq_CMC_b : bigrammar **)

let coq_CMC_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('0'::('1'::('0'::('1'::[])))))

(** val coq_CMPS_b : bigrammar **)

let coq_CMPS_b =
  bitsleft ('1'::('0'::('1'::('0'::[]))))
    (bitsleft ('0'::('1'::('1'::[]))) anybit)

(** val coq_CMPXCHG_b : bigrammar **)

let coq_CMPXCHG_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('0'::[]))) (seq anybit modrm))))

(** val coq_CPUID_b : bigrammar **)

let coq_CPUID_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[]))))
        (bitsmatch ('0'::('0'::('1'::('0'::[])))))))

(** val coq_CWDE_b : bigrammar **)

let coq_CWDE_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('0'::('0'::('0'::[])))))

(** val coq_DAA_b : bigrammar **)

let coq_DAA_b =
  bitsleft ('0'::('0'::('1'::('0'::[]))))
    (bitsmatch ('0'::('1'::('1'::('1'::[])))))

(** val coq_DAS_b : bigrammar **)

let coq_DAS_b =
  bitsleft ('0'::('0'::('1'::('0'::[]))))
    (bitsmatch ('1'::('1'::('1'::('1'::[])))))

(** val coq_DEC_b : bigrammar **)

let coq_DEC_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::[])))
          (seq anybit (bitsleft ('1'::('1'::('0'::('0'::('1'::[]))))) reg))))
      (alt (bitsleft ('0'::('1'::('0'::('0'::[])))) (bitsleft ('1'::[]) reg))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::[])))
            (seq anybit
              (ext_op_modrm_noreg_ret_addr ('0'::('0'::('1'::[])))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, r) = y in Obj.magic (w, (Reg_op r))
    | Coq_inr y ->
      (match y with
       | Coq_inl r -> Obj.magic (true, (Reg_op r))
       | Coq_inr y0 -> let (w, addr) = y0 in Obj.magic (w, (Address_op addr)))),
    (fun u ->
    let (_, op) = Obj.magic u in
    (match op with
     | Reg_op r -> Some (Obj.magic (Coq_inl ((fst (Obj.magic u)), r)))
     | Address_op addr ->
       Some (Obj.magic (Coq_inr (Coq_inr ((fst (Obj.magic u)), addr))))
     | _ -> None)))

(** val coq_DIV_b : bigrammar **)

let coq_DIV_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit (bitsleft ('1'::('1'::('1'::('1'::('0'::[]))))) reg))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit (ext_op_modrm_noreg_ret_addr ('1'::('1'::('0'::[]))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, r) = y in Obj.magic (w, (Reg_op r))
    | Coq_inr y -> let (w, addr) = y in Obj.magic (w, (Address_op addr))),
    (fun u ->
    let (_, op) = Obj.magic u in
    (match op with
     | Reg_op r -> Some (Obj.magic (Coq_inl ((fst (Obj.magic u)), r)))
     | Address_op addr ->
       Some (Obj.magic (Coq_inr ((fst (Obj.magic u)), addr)))
     | _ -> None)))

(** val coq_HLT_b : bigrammar **)

let coq_HLT_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('0'::('1'::('0'::('0'::[])))))

(** val coq_IDIV_b : bigrammar **)

let coq_IDIV_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit (bitsleft ('1'::('1'::('1'::('1'::('1'::[]))))) reg))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit (ext_op_modrm_noreg_ret_addr ('1'::('1'::('1'::[]))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, r) = y in Obj.magic (w, (Reg_op r))
    | Coq_inr y -> let (w, addr) = y in Obj.magic (w, (Address_op addr))),
    (fun u ->
    let (_, op) = Obj.magic u in
    (match op with
     | Reg_op r -> Some (Obj.magic (Coq_inl ((fst (Obj.magic u)), r)))
     | Address_op addr ->
       Some (Obj.magic (Coq_inr ((fst (Obj.magic u)), addr)))
     | _ -> None)))

(** val coq_IMUL_b : bool -> bigrammar **)

let coq_IMUL_b opsize_override =
  map
    (alt
      (alt
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('1'::[])))
            (seq anybit (ext_op_modrm ('1'::('0'::('1'::[])))))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (bitsleft ('1'::('1'::('1'::('1'::[]))))
            (bitsleft ('1'::('0'::('1'::('0'::[]))))
              (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_ret_reg)))))
      (alt
        (bitsleft ('0'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('0'::('1'::('1'::[])))) (seq modrm_ret_reg byte)))
        (bitsleft ('0'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('0'::('0'::('1'::[]))))
            (seq modrm_ret_reg (imm_b opsize_override)))))) ((fun u ->
    match Obj.magic u with
    | Coq_inl y ->
      (match y with
       | Coq_inl y0 ->
         let (w, op1) = y0 in Obj.magic (w, (op1, (None, None)))
       | Coq_inr y0 ->
         let (r1, op2) = y0 in
         Obj.magic (false, ((Reg_op r1), ((Some op2), None))))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 ->
         let (y1, b) = y0 in
         let (r1, op2) = y1 in
         Obj.magic (true, ((Reg_op r1), ((Some op2), (Some
           (sign_extend8_32 b)))))
       | Coq_inr y0 ->
         let (y1, imm) = y0 in
         let (r1, op2) = y1 in
         Obj.magic ((negb opsize_override), ((Reg_op r1), ((Some op2), (Some
           imm)))))), (fun u ->
    let (w, u1) = Obj.magic u in
    let (op1, u2) = u1 in
    let (i, i0) = u2 in
    (match i with
     | Some op2 ->
       (match i0 with
        | Some imm ->
          (match op1 with
           | Reg_op r1 ->
             (match op2 with
              | Reg_op _ ->
                if w
                then if repr_in_signed_byte_dec imm
                     then Some
                            (Obj.magic (Coq_inr (Coq_inl ((r1, op2),
                              (sign_shrink32_8 imm)))))
                     else if opsize_override
                          then None
                          else Some
                                 (Obj.magic (Coq_inr (Coq_inr ((r1, op2),
                                   imm))))
                else if opsize_override
                     then Some
                            (Obj.magic (Coq_inr (Coq_inr ((r1, op2), imm))))
                     else None
              | Address_op _ ->
                if w
                then if repr_in_signed_byte_dec imm
                     then Some
                            (Obj.magic (Coq_inr (Coq_inl ((r1, op2),
                              (sign_shrink32_8 imm)))))
                     else if opsize_override
                          then None
                          else Some
                                 (Obj.magic (Coq_inr (Coq_inr ((r1, op2),
                                   imm))))
                else if opsize_override
                     then Some
                            (Obj.magic (Coq_inr (Coq_inr ((r1, op2), imm))))
                     else None
              | _ -> None)
           | _ -> None)
        | None ->
          if w
          then None
          else (match op1 with
                | Reg_op r1 ->
                  (match op2 with
                   | Reg_op _ ->
                     Some (Obj.magic (Coq_inl (Coq_inr (r1, op2))))
                   | Address_op _ ->
                     Some (Obj.magic (Coq_inl (Coq_inr (r1, op2))))
                   | _ -> None)
                | _ -> None))
     | None ->
       (match i0 with
        | Some _ -> None
        | None ->
          (match op1 with
           | Reg_op _ -> Some (Obj.magic (Coq_inl (Coq_inl (w, op1))))
           | Address_op _ -> Some (Obj.magic (Coq_inl (Coq_inl (w, op1))))
           | _ -> None)))))

(** val coq_IN_b : bigrammar **)

let coq_IN_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::('0'::[]))) (seq anybit byte)))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('0'::[]))) anybit))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, b) = y in Obj.magic (w, (Some b))
    | Coq_inr w -> Obj.magic (w, None)), (fun u ->
    let (w, y) = Obj.magic u in
    (match y with
     | Some b -> Some (Obj.magic (Coq_inl (w, b)))
     | None -> Some (Obj.magic (Coq_inr w)))))

(** val coq_INC_b : bigrammar **)

let coq_INC_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::[])))
          (seq anybit (bitsleft ('1'::('1'::('0'::('0'::('0'::[]))))) reg))))
      (alt (bitsleft ('0'::('1'::('0'::('0'::[])))) (bitsleft ('0'::[]) reg))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::[])))
            (seq anybit
              (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[])))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, r) = y in Obj.magic (w, (Reg_op r))
    | Coq_inr y ->
      (match y with
       | Coq_inl r -> Obj.magic (true, (Reg_op r))
       | Coq_inr y0 -> let (w, addr) = y0 in Obj.magic (w, (Address_op addr)))),
    (fun u ->
    let (w, op) = Obj.magic u in
    (match op with
     | Reg_op r ->
       if w
       then Some (Obj.magic (Coq_inr (Coq_inl r)))
       else Some (Obj.magic (Coq_inl (w, r)))
     | Address_op addr -> Some (Obj.magic (Coq_inr (Coq_inr (w, addr))))
     | _ -> None)))

(** val coq_INS_b : bigrammar **)

let coq_INS_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsleft ('1'::('1'::('0'::[]))) anybit)

(** val coq_INTn_b : bigrammar **)

let coq_INTn_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('0'::('1'::[])))) byte)

(** val coq_INT_b : bigrammar **)

let coq_INT_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsmatch ('1'::('1'::('0'::('0'::[])))))

(** val coq_INTO_b : bigrammar **)

let coq_INTO_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsmatch ('1'::('1'::('1'::('0'::[])))))

(** val coq_INVD_b : bigrammar **)

let coq_INVD_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsmatch ('1'::('0'::('0'::('0'::[])))))))

(** val coq_INVLPG_b : bigrammar **)

let coq_INVLPG_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm_noreg ('1'::('1'::('1'::[])))))))

(** val coq_IRET_b : bigrammar **)

let coq_IRET_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsmatch ('1'::('1'::('1'::('1'::[])))))

(** val coq_Jcc_b : bigrammar **)

let coq_Jcc_b =
  map
    (alt (bitsleft ('0'::('1'::('1'::('1'::[])))) (seq tttn byte))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('0'::('0'::('0'::[])))) (seq tttn word)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (ct, b) = y in Obj.magic (ct, (sign_extend8_32 b))
    | Coq_inr y -> let (ct, imm) = y in Obj.magic (ct, imm)), (fun u ->
    let (ct, imm) = Obj.magic u in
    if repr_in_signed_byte_dec imm
    then Some (Obj.magic (Coq_inl (ct, (sign_shrink32_8 imm))))
    else Some (Obj.magic (Coq_inr (ct, imm)))))

(** val coq_JCXZ_b : bigrammar **)

let coq_JCXZ_b =
  bitsleft ('1'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[])))) byte)

(** val coq_JMP_b : bigrammar **)

let coq_JMP_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[])))) byte)), (fun b ->
    Obj.magic (true, (false, ((Imm_op (sign_extend8_32 (Obj.magic b))),
      None)))))), (BLeaf (Big.one,
    (bitsleft ('1'::('1'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('0'::('1'::[])))) word)), (fun imm ->
    Obj.magic (true, (false, ((Imm_op (Obj.magic imm)), None)))))))), (BLeaf
    ((Big.double Big.one),
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (ext_op_modrm ('1'::('0'::('0'::[])))))), (fun op ->
    Obj.magic (true, (true, (op, None)))))))), (BNode ((Big.doubleplusone
    Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('1'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[])))) (seq word halfword))),
    (fun v ->
    let (base, offset) = Obj.magic v in
    Obj.magic (false, (true, ((Imm_op base), (Some offset))))))), (BLeaf
    ((Big.double (Big.double Big.one)),
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (ext_op_modrm ('1'::('0'::('1'::[])))))), (fun op ->
    Obj.magic (false, (true, (op, None)))))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree MLeaf) in
  let case4 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (near, u1) = Obj.magic u in
    let (absolute, u2) = u1 in
    if near
    then if absolute
         then let (i, i0) = u2 in
              (match i with
               | Reg_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> inv_case_some case2 (fst (Obj.magic u2)))
               | Address_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> inv_case_some case2 (fst (Obj.magic u2)))
               | _ -> None)
         else let (i, i0) = u2 in
              (match i with
               | Imm_op imm ->
                 (match i0 with
                  | Some _ -> None
                  | None ->
                    if repr_in_signed_byte_dec imm
                    then inv_case_some case0 (Obj.magic sign_shrink32_8 imm)
                    else inv_case_some case1 (Obj.magic imm))
               | _ -> None)
    else if absolute
         then let (i, i0) = u2 in
              (match i with
               | Imm_op base ->
                 (match i0 with
                  | Some offset ->
                    inv_case_some case3 (Obj.magic (base, offset))
                  | None -> None)
               | Reg_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> inv_case_some case4 (fst (Obj.magic u2)))
               | Address_op _ ->
                 (match i0 with
                  | Some _ -> None
                  | None -> inv_case_some case4 (fst (Obj.magic u2)))
               | Offset_op _ -> None)
         else None))

(** val coq_LAHF_b : bigrammar **)

let coq_LAHF_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('1'::('1'::('1'::[])))))

(** val coq_LAR_b : bigrammar **)

let coq_LAR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm)))

(** val coq_LDS_b : bigrammar **)

let coq_LDS_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm)

(** val coq_LEA_b : bigrammar **)

let coq_LEA_b =
  map
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[])))) modrm_noreg)) ((fun v ->
    Obj.magic ((Reg_op (fst (Obj.magic v))), (Address_op
      (snd (Obj.magic v))))), (fun u ->
    let (i, i0) = Obj.magic u in
    (match i with
     | Reg_op r ->
       (match i0 with
        | Address_op addr -> Some (Obj.magic (r, addr))
        | _ -> None)
     | _ -> None)))

(** val coq_LEAVE_b : bigrammar **)

let coq_LEAVE_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsmatch ('1'::('0'::('0'::('1'::[])))))

(** val coq_LES_b : bigrammar **)

let coq_LES_b =
  bitsleft ('1'::('1'::('0'::('0'::[]))))
    (bitsleft ('0'::('1'::('0'::('0'::[])))) modrm)

(** val coq_LFS_b : bigrammar **)

let coq_LFS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('0'::[])))) modrm)))

(** val coq_LGDT_b : bigrammar **)

let coq_LGDT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm_noreg ('0'::('1'::('0'::[])))))))

(** val coq_LGS_b : bigrammar **)

let coq_LGS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm)))

(** val coq_LIDT_b : bigrammar **)

let coq_LIDT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm_noreg ('0'::('1'::('1'::[])))))))

(** val coq_LLDT_b : bigrammar **)

let coq_LLDT_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('0'::('0'::('0'::('0'::[]))))
              (bitsleft ('1'::('1'::[]))
                (bitsleft ('0'::('1'::('0'::[]))) reg))))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('0'::('0'::('0'::('0'::[]))))
              (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[])))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl r -> Obj.magic (Reg_op r)
    | Coq_inr addr -> Obj.magic (Address_op addr)), (fun u ->
    match Obj.magic u with
    | Reg_op r -> Some (Obj.magic (Coq_inl r))
    | Address_op addr -> Some (Obj.magic (Coq_inr addr))
    | _ -> None))

(** val coq_LMSW_b : bigrammar **)

let coq_LMSW_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('0'::('0'::('0'::('1'::[]))))
              (bitsleft ('1'::('1'::[]))
                (bitsleft ('1'::('1'::('0'::[]))) reg))))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('0'::('0'::('0'::('1'::[]))))
              (ext_op_modrm_noreg_ret_addr ('1'::('1'::('0'::[])))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl r -> Obj.magic (Reg_op r)
    | Coq_inr addr -> Obj.magic (Address_op addr)), (fun u ->
    match Obj.magic u with
    | Reg_op r -> Some (Obj.magic (Coq_inl r))
    | Address_op addr -> Some (Obj.magic (Coq_inr addr))
    | _ -> None))

(** val coq_LODS_b : bigrammar **)

let coq_LODS_b =
  bitsleft ('1'::('0'::('1'::('0'::[]))))
    (bitsleft ('1'::('1'::('0'::[]))) anybit)

(** val coq_LOOP_b : bigrammar **)

let coq_LOOP_b =
  bitsleft ('1'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('1'::('0'::[])))) byte)

(** val coq_LOOPZ_b : bigrammar **)

let coq_LOOPZ_b =
  bitsleft ('1'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('0'::('1'::[])))) byte)

(** val coq_LOOPNZ_b : bigrammar **)

let coq_LOOPNZ_b =
  bitsleft ('1'::('1'::('1'::('0'::[]))))
    (bitsleft ('0'::('0'::('0'::('0'::[])))) byte)

(** val coq_LSL_b : bigrammar **)

let coq_LSL_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm)))

(** val coq_LSS_b : bigrammar **)

let coq_LSS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm)))

(** val coq_LTR_b : bigrammar **)

let coq_LTR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (ext_op_modrm ('0'::('1'::('1'::[])))))))

(** val coq_CMOVcc_b : bigrammar **)

let coq_CMOVcc_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('0'::[])))) (seq tttn modrm)))

(** val coq_MOV_b : bool -> bigrammar **)

let coq_MOV_b opsize_override =
  let gt = BNode ((Big.doubleplusone (Big.double Big.one)), (BNode
    ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero,
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('0'::('1'::[]))) (seq anybit modrm_ret_reg))),
    (fun v ->
    let (w, i) = Obj.magic v in
    let (r1, op2) = i in Obj.magic (w, ((Reg_op r1), op2))))), (BLeaf
    (Big.one,
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('0'::('0'::[]))) (seq anybit modrm_ret_reg))),
    (fun v ->
    let (w, i) = Obj.magic v in
    let (r1, op2) = i in Obj.magic (w, (op2, (Reg_op r1)))))))), (BLeaf
    ((Big.double Big.one),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('0'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::[]))
          (bitsleft ('0'::('0'::('0'::[])))
            (seq reg (imm_b opsize_override)))))), (fun v ->
    let (r, imm) = Obj.magic v in
    Obj.magic (true, ((Reg_op r), (Imm_op imm)))))))), (BNode ((Big.double
    (Big.double Big.one)), (BNode ((Big.doubleplusone Big.one), (BLeaf
    ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::[]))
          (bitsleft ('0'::('0'::('0'::[]))) (seq reg byte))))), (fun v ->
    let (r, b) = Obj.magic v in
    Obj.magic (false, ((Reg_op r), (Imm_op (zero_extend8_32 b))))))), (BLeaf
    ((Big.double (Big.double Big.one)),
    (bitsleft ('1'::('0'::('1'::('1'::[]))))
      (bitsleft ('1'::[]) (seq reg (imm_b opsize_override)))), (fun v ->
    let (r, imm) = Obj.magic v in
    Obj.magic (true, ((Reg_op r), (Imm_op imm)))))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)),
    (bitsleft ('1'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::[]) (seq reg byte))), (fun v ->
    let (r, b) = Obj.magic v in
    Obj.magic (false, ((Reg_op r), (Imm_op (zero_extend8_32 b))))))))))),
    (BNode ((Big.double (Big.double (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BLeaf ((Big.double (Big.doubleplusone
    Big.one)),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('0'::('1'::('1'::('1'::[]))))
        (seq (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[]))))
          (imm_b opsize_override)))), (fun v ->
    let (addr, imm) = Obj.magic v in
    Obj.magic (true, ((Address_op addr), (Imm_op imm)))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (seq (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[])))) byte))),
    (fun v ->
    let (addr, b) = Obj.magic v in
    Obj.magic (false, ((Address_op addr), (Imm_op (zero_extend8_32 b))))))))),
    (BLeaf ((Big.double (Big.double (Big.double Big.one))),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[])))) word)), (fun imm ->
    Obj.magic (true, ((Reg_op EAX), (Offset_op (Obj.magic imm))))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[])))) word)), (fun imm ->
    Obj.magic (false, ((Reg_op EAX), (Offset_op (Obj.magic imm))))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[])))) word)), (fun imm ->
    Obj.magic (true, ((Offset_op (Obj.magic imm)), (Reg_op EAX)))))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[])))) word)), (fun imm ->
    Obj.magic (false, ((Offset_op (Obj.magic imm)), (Reg_op EAX)))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree MLeaf))) in
  let case1 = MLTree (MLTree (MLTree (MRTree MLeaf))) in
  let case4 = MLTree (MRTree (MLTree (MRTree MLeaf))) in
  let case5 = MLTree (MRTree (MRTree MLeaf)) in
  let case6 = MRTree (MLTree (MLTree (MLTree MLeaf))) in
  let case7 = MRTree (MLTree (MLTree (MRTree MLeaf))) in
  let case8 = MRTree (MLTree (MRTree MLeaf)) in
  let case9 = MRTree (MRTree (MLTree (MLTree MLeaf))) in
  let case10 = MRTree (MRTree (MLTree (MRTree MLeaf))) in
  let case11 = MRTree (MRTree (MRTree MLeaf)) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (w, u1) = Obj.magic u in
    let (op1, op2) = u1 in
    (match op1 with
     | Imm_op _ -> None
     | Reg_op r1 ->
       (match op2 with
        | Imm_op imm ->
          if w
          then inv_case_some case4 (Obj.magic (r1, imm))
          else if repr_in_unsigned_byte_dec imm
               then inv_case_some case5
                      (Obj.magic (r1, (zero_shrink32_8 imm)))
               else None
        | Offset_op imm ->
          (match r1 with
           | EAX ->
             if w
             then inv_case_some case8 (Obj.magic imm)
             else inv_case_some case9 (Obj.magic imm)
           | _ -> None)
        | _ -> inv_case_some case0 (Obj.magic (w, (r1, op2))))
     | Address_op addr ->
       (match op2 with
        | Imm_op imm ->
          if w
          then inv_case_some case6 (Obj.magic (addr, imm))
          else if repr_in_unsigned_byte_dec imm
               then inv_case_some case7
                      (Obj.magic (addr, (zero_shrink32_8 imm)))
               else None
        | Reg_op r ->
          inv_case_some case1 (Obj.magic (w, (r, (Address_op addr))))
        | _ -> None)
     | Offset_op imm ->
       (match op2 with
        | Reg_op r ->
          (match r with
           | EAX ->
             if w
             then inv_case_some case10 (Obj.magic imm)
             else inv_case_some case11 (Obj.magic imm)
           | _ -> None)
        | _ -> None))))

(** val coq_MOVCR_b : bigrammar **)

let coq_MOVCR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('0'::('0'::[]))
          (seq anybit
            (bitsleft ('0'::[])
              (bitsleft ('1'::('1'::[])) (seq control_reg_b reg)))))))

(** val coq_MOVDR_b : bigrammar **)

let coq_MOVDR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('0'::('0'::[]))
          (seq anybit
            (bitsleft ('1'::('1'::('1'::[]))) (seq debug_reg_b reg))))))

(** val coq_MOVSR_b : bigrammar **)

let coq_MOVSR_b =
  bitsleft ('1'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::[])) (seq anybit (bitsleft ('0'::[]) seg_modrm)))

(** val coq_MOVBE_b : bigrammar **)

let coq_MOVBE_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[]))))
          (bitsleft ('1'::('0'::('0'::('0'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[]))))
              (bitsleft ('0'::('0'::('0'::[]))) (seq anybit modrm_ret_reg)))))))
    ((fun v ->
    let (w, i) = Obj.magic v in
    let (r1, op2) = i in
    if w then Obj.magic (op2, (Reg_op r1)) else Obj.magic ((Reg_op r1), op2)),
    (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | Reg_op r1 ->
       (match y0 with
        | Reg_op r2 -> Some (Obj.magic (true, (r2, (Reg_op r1))))
        | Address_op _ -> Some (Obj.magic (false, (r1, (snd (Obj.magic u)))))
        | _ -> None)
     | Address_op _ ->
       (match y0 with
        | Reg_op r1 -> Some (Obj.magic (true, (r1, (fst (Obj.magic u)))))
        | _ -> None)
     | _ -> None)))

(** val coq_MOVS_b : bigrammar **)

let coq_MOVS_b =
  bitsleft ('1'::('0'::('1'::('0'::[]))))
    (bitsleft ('0'::('1'::('0'::[]))) anybit)

(** val coq_MOVSX_b : bigrammar **)

let coq_MOVSX_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::[]))) (seq anybit modrm))))

(** val coq_MOVZX_b : bigrammar **)

let coq_MOVZX_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[]))) (seq anybit modrm))))

(** val coq_MUL_b : bigrammar **)

let coq_MUL_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('1'::('1'::[])))
      (seq anybit (ext_op_modrm ('1'::('0'::('0'::[]))))))

(** val coq_NEG_b : bigrammar **)

let coq_NEG_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('1'::('1'::[])))
      (seq anybit (ext_op_modrm ('0'::('1'::('1'::[]))))))

(** val coq_NOP_b : bigrammar **)

let coq_NOP_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (ext_op_modrm ('0'::('0'::('0'::[])))))))

(** val coq_NOT_b : bigrammar **)

let coq_NOT_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('1'::('1'::[])))
      (seq anybit (ext_op_modrm ('0'::('1'::('0'::[]))))))

(** val coq_OUT_b : bigrammar **)

let coq_OUT_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::('1'::[]))) (seq anybit byte)))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::[]))) anybit))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (w, b) = y in Obj.magic (w, (Some b))
    | Coq_inr w -> Obj.magic (w, None)), (fun u ->
    let (w, i) = Obj.magic u in
    (match i with
     | Some b -> Some (Obj.magic (Coq_inl (w, b)))
     | None -> Some (Obj.magic (Coq_inr w)))))

(** val coq_OUTS_b : bigrammar **)

let coq_OUTS_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::[]))) anybit)

(** val coq_POP_b : bigrammar **)

let coq_POP_b =
  map
    (alt
      (bitsleft ('1'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (ext_op_modrm ('0'::('0'::('0'::[]))))))
      (bitsleft ('0'::('1'::('0'::('1'::[])))) (bitsleft ('1'::[]) reg)))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl op -> op
    | Coq_inr r -> Obj.magic (Reg_op r)), (fun u ->
    match Obj.magic u with
    | Reg_op r -> Some (Obj.magic (Coq_inr r))
    | Address_op _ -> Some (Obj.magic (Coq_inl u))
    | _ -> None))

(** val coq_POPSR_b : bigrammar **)

let coq_POPSR_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('0'::('0'::[])) (bitsmatch ('1'::('1'::('1'::[])))))),
    (fun _ -> Obj.magic ES))), (BLeaf (Big.one,
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('1'::('0'::[])) (bitsmatch ('1'::('1'::('1'::[])))))),
    (fun _ -> Obj.magic SS))))), (BLeaf ((Big.double Big.one),
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('1'::('1'::[])) (bitsmatch ('1'::('1'::('1'::[])))))),
    (fun _ -> Obj.magic DS))))), (BNode ((Big.doubleplusone Big.one), (BLeaf
    ((Big.doubleplusone Big.one),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::[]))
          (bitsleft ('1'::('0'::('0'::[])))
            (bitsmatch ('0'::('0'::('1'::[])))))))), (fun _ ->
    Obj.magic FS))), (BLeaf ((Big.double (Big.double Big.one)),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::[]))
          (bitsleft ('1'::('0'::('1'::[])))
            (bitsmatch ('0'::('0'::('1'::[])))))))), (fun _ ->
    Obj.magic GS))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree MLeaf) in
  let case4 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | ES -> inv_case_some case0 (Obj.magic ())
    | CS -> None
    | SS -> inv_case_some case1 (Obj.magic ())
    | DS -> inv_case_some case2 (Obj.magic ())
    | FS -> inv_case_some case3 (Obj.magic ())
    | GS -> inv_case_some case4 (Obj.magic ())))

(** val coq_POPA_b : bigrammar **)

let coq_POPA_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsmatch ('0'::('0'::('0'::('1'::[])))))

(** val coq_POPF_b : bigrammar **)

let coq_POPF_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('1'::('0'::('1'::[])))))

(** val coq_PUSH_b : bigrammar **)

let coq_PUSH_b =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (ext_op_modrm_noreg_ret_addr ('1'::('1'::('0'::[])))))), (fun addr ->
    Obj.magic (true, (Address_op (Obj.magic addr)))))), (BLeaf (Big.one,
    (bitsleft ('0'::('1'::('0'::('1'::[])))) (bitsleft ('0'::[]) reg)),
    (fun r -> Obj.magic (true, (Reg_op (Obj.magic r)))))))), (BNode
    ((Big.double Big.one), (BLeaf ((Big.double Big.one),
    (bitsleft ('0'::('1'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[])))) byte)), (fun b ->
    Obj.magic (false, (Imm_op (sign_extend8_32 (Obj.magic b))))))), (BLeaf
    ((Big.doubleplusone Big.one),
    (bitsleft ('0'::('1'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('0'::('0'::[])))) word)), (fun w ->
    Obj.magic (true, (Imm_op (Obj.magic w)))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (y, y0) = Obj.magic u in
    if y
    then (match y0 with
          | Imm_op w -> inv_case_some case3 (Obj.magic w)
          | Reg_op r -> inv_case_some case1 (Obj.magic r)
          | Address_op addr -> inv_case_some case0 (Obj.magic addr)
          | Offset_op _ -> None)
    else (match y0 with
          | Imm_op w ->
            if repr_in_signed_byte_dec w
            then inv_case_some case2 (Obj.magic sign_shrink32_8 w)
            else None
          | _ -> None)))

(** val coq_PUSHSR_b : bigrammar **)

let coq_PUSHSR_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('0'::('0'::[])) (bitsmatch ('1'::('1'::('0'::[])))))),
    (fun _ -> Obj.magic ES))), (BLeaf (Big.one,
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('0'::('1'::[])) (bitsmatch ('1'::('1'::('0'::[])))))),
    (fun _ -> Obj.magic CS))))), (BLeaf ((Big.double Big.one),
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('1'::('0'::[])) (bitsmatch ('1'::('1'::('0'::[])))))),
    (fun _ -> Obj.magic SS))))), (BNode ((Big.double (Big.double Big.one)),
    (BNode ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('0'::('0'::('0'::[])))
      (bitsleft ('1'::('1'::[])) (bitsmatch ('1'::('1'::('0'::[])))))),
    (fun _ -> Obj.magic DS))), (BLeaf ((Big.double (Big.double Big.one)),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::[]))
          (bitsleft ('1'::('0'::('0'::[])))
            (bitsmatch ('0'::('0'::('0'::[])))))))), (fun _ ->
    Obj.magic FS))))), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::[]))
          (bitsleft ('1'::('0'::('1'::[])))
            (bitsmatch ('0'::('0'::('0'::[])))))))), (fun _ ->
    Obj.magic GS))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree (MLTree MLeaf)) in
  let case4 = MRTree (MLTree (MRTree MLeaf)) in
  let case5 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | ES -> inv_case_some case0 (Obj.magic ())
    | CS -> inv_case_some case1 (Obj.magic ())
    | SS -> inv_case_some case2 (Obj.magic ())
    | DS -> inv_case_some case3 (Obj.magic ())
    | FS -> inv_case_some case4 (Obj.magic ())
    | GS -> inv_case_some case5 (Obj.magic ())))

(** val coq_PUSHA_b : bigrammar **)

let coq_PUSHA_b =
  bitsleft ('0'::('1'::('1'::('0'::[]))))
    (bitsmatch ('0'::('0'::('0'::('0'::[])))))

(** val coq_PUSHF_b : bigrammar **)

let coq_PUSHF_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('1'::('0'::('0'::[])))))

(** val rotate_b : char list -> bigrammar **)

let rotate_b extop =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('0'::('0'::[]))) (seq anybit (ext_op_modrm extop))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::[]))))
          (bitsleft ('0'::('0'::('1'::[])))
            (seq anybit (ext_op_modrm extop))))
        (bitsleft ('1'::('1'::('0'::('0'::[]))))
          (bitsleft ('0'::('0'::('0'::[])))
            (seq anybit (seq (ext_op_modrm extop) byte)))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (w, op) = y in
      Obj.magic (w, (op, (Imm_ri (Word.repr size8 Big.one))))
    | Coq_inr y ->
      (match y with
       | Coq_inl y0 -> let (w, op) = y0 in Obj.magic (w, (op, (Reg_ri ECX)))
       | Coq_inr y0 ->
         let (w, y1) = y0 in
         let (op, b) = y1 in Obj.magic (w, (op, (Imm_ri b))))), (fun u ->
    let (w, u1) = Obj.magic u in
    let (i, i0) = u1 in
    (match i with
     | Reg_op _ ->
       (match i0 with
        | Reg_ri r ->
          (match r with
           | ECX -> Some (Obj.magic (Coq_inr (Coq_inl (w, (fst u1)))))
           | _ -> None)
        | Imm_ri b -> Some (Obj.magic (Coq_inr (Coq_inr (w, ((fst u1), b))))))
     | Address_op _ ->
       (match i0 with
        | Reg_ri r ->
          (match r with
           | ECX -> Some (Obj.magic (Coq_inr (Coq_inl (w, (fst u1)))))
           | _ -> None)
        | Imm_ri b -> Some (Obj.magic (Coq_inr (Coq_inr (w, ((fst u1), b))))))
     | _ -> None)))

(** val coq_RCL_b : bigrammar **)

let coq_RCL_b =
  rotate_b ('0'::('1'::('0'::[])))

(** val coq_RCR_b : bigrammar **)

let coq_RCR_b =
  rotate_b ('0'::('1'::('1'::[])))

(** val coq_RDMSR_b : bigrammar **)

let coq_RDMSR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('1'::('0'::[])))))))

(** val coq_RDPMC_b : bigrammar **)

let coq_RDPMC_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('1'::('1'::[])))))))

(** val coq_RDTSC_b : bigrammar **)

let coq_RDTSC_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('0'::('1'::[])))))))

(** val coq_RDTSCP_b : bigrammar **)

let coq_RDTSCP_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::('1'::[]))))
            (bitsmatch ('1'::('0'::('0'::('1'::[])))))))))

(** val coq_RET_b : bigrammar **)

let coq_RET_b =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsmatch ('0'::('0'::('1'::('1'::[])))))), (fun _ ->
    Obj.magic (true, None)))), (BLeaf (Big.one,
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[])))) halfword)), (fun h ->
    Obj.magic (true, (Some h))))))), (BNode ((Big.double Big.one), (BLeaf
    ((Big.double Big.one),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsmatch ('1'::('0'::('1'::('1'::[])))))), (fun _ ->
    Obj.magic (false, None)))), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('1'::('0'::('0'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[])))) halfword)), (fun h ->
    Obj.magic (false, (Some h))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (y, y0) = Obj.magic u in
    if y
    then (match y0 with
          | Some h -> inv_case_some case1 h
          | None -> inv_case_some case0 (Obj.magic ()))
    else (match y0 with
          | Some h -> inv_case_some case3 h
          | None -> inv_case_some case2 (Obj.magic ()))))

(** val coq_ROL_b : bigrammar **)

let coq_ROL_b =
  rotate_b ('0'::('0'::('0'::[])))

(** val coq_ROR_b : bigrammar **)

let coq_ROR_b =
  rotate_b ('0'::('0'::('1'::[])))

(** val coq_RSM_b : bigrammar **)

let coq_RSM_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[]))))
        (bitsmatch ('1'::('0'::('1'::('0'::[])))))))

(** val coq_SAHF_b : bigrammar **)

let coq_SAHF_b =
  bitsleft ('1'::('0'::('0'::('1'::[]))))
    (bitsmatch ('1'::('1'::('1'::('0'::[])))))

(** val coq_SAR_b : bigrammar **)

let coq_SAR_b =
  rotate_b ('1'::('1'::('1'::[])))

(** val coq_SCAS_b : bigrammar **)

let coq_SCAS_b =
  bitsleft ('1'::('0'::('1'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::[]))) anybit)

(** val coq_SETcc_b : bigrammar **)

let coq_SETcc_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('1'::[])))) (seq tttn modrm_ret_reg))))
    ((fun v -> Obj.magic ((fst (Obj.magic v)), (snd (snd (Obj.magic v))))),
    (fun u ->
    let (_, op) = Obj.magic u in
    (match op with
     | Reg_op _ ->
       Some (Obj.magic ((fst (Obj.magic u)), (EAX, (snd (Obj.magic u)))))
     | Address_op _ ->
       Some (Obj.magic ((fst (Obj.magic u)), (EAX, (snd (Obj.magic u)))))
     | _ -> None)))

(** val coq_SGDT_b : bigrammar **)

let coq_SGDT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm_noreg ('0'::('0'::('0'::[])))))))

(** val coq_SHL_b : bigrammar **)

let coq_SHL_b =
  rotate_b ('1'::('0'::('0'::[])))

(** val shiftdouble_b : char list -> bigrammar **)

let shiftdouble_b opcode =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[]))))
          (bitsleft opcode
            (bitsleft ('0'::('0'::[]))
              (bitsleft ('1'::('1'::[])) (seq reg (seq reg byte)))))))),
    (fun v ->
    let (r2, i) = Obj.magic v in
    let (r1, b) = i in Obj.magic ((Reg_op r1), (r2, (Imm_ri b)))))), (BLeaf
    (Big.one,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[]))))
          (bitsleft opcode
            (bitsleft ('0'::('0'::[])) (seq modrm_noreg byte)))))), (fun v ->
    let (i, b) = Obj.magic v in
    let (r, addr) = i in Obj.magic ((Address_op addr), (r, (Imm_ri b)))))))),
    (BNode ((Big.double Big.one), (BLeaf ((Big.double Big.one),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[]))))
          (bitsleft opcode
            (bitsleft ('0'::('1'::[]))
              (bitsleft ('1'::('1'::[])) (seq reg reg))))))), (fun v ->
    let (r2, r1) = Obj.magic v in Obj.magic ((Reg_op r1), (r2, (Reg_ri ECX)))))),
    (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[]))))
          (bitsleft opcode (bitsleft ('0'::('1'::[])) modrm_noreg))))),
    (fun v ->
    let (r, addr) = Obj.magic v in
    Obj.magic ((Address_op addr), (r, (Reg_ri ECX)))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (op1, u1) = Obj.magic u in
    let (r2, ri) = u1 in
    (match op1 with
     | Reg_op r1 ->
       (match ri with
        | Reg_ri r ->
          (match r with
           | ECX -> inv_case_some case2 (Obj.magic (r2, r1))
           | _ -> None)
        | Imm_ri b -> inv_case_some case0 (Obj.magic (r2, (r1, b))))
     | Address_op addr ->
       (match ri with
        | Reg_ri r ->
          (match r with
           | ECX -> inv_case_some case3 (Obj.magic (r2, addr))
           | _ -> None)
        | Imm_ri b -> inv_case_some case1 (Obj.magic ((r2, addr), b)))
     | _ -> None)))

(** val coq_SHLD_b : bigrammar **)

let coq_SHLD_b =
  shiftdouble_b ('0'::('1'::[]))

(** val coq_SHR_b : bigrammar **)

let coq_SHR_b =
  rotate_b ('1'::('0'::('1'::[])))

(** val coq_SHRD_b : bigrammar **)

let coq_SHRD_b =
  shiftdouble_b ('1'::('1'::[]))

(** val coq_SIDT_b : bigrammar **)

let coq_SIDT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm_noreg ('0'::('0'::('1'::[])))))))

(** val coq_SLDT_b : bigrammar **)

let coq_SLDT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (ext_op_modrm ('0'::('0'::('0'::[])))))))

(** val coq_SMSW_b : bigrammar **)

let coq_SMSW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (ext_op_modrm ('1'::('0'::('0'::[])))))))

(** val coq_STC_b : bigrammar **)

let coq_STC_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('0'::('0'::('1'::[])))))

(** val coq_STD_b : bigrammar **)

let coq_STD_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('1'::('0'::('1'::[])))))

(** val coq_STI_b : bigrammar **)

let coq_STI_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsmatch ('1'::('0'::('1'::('1'::[])))))

(** val coq_STOS_b : bigrammar **)

let coq_STOS_b =
  bitsleft ('1'::('0'::('1'::('0'::[]))))
    (bitsleft ('1'::('0'::('1'::[]))) anybit)

(** val coq_STR_b : bigrammar **)

let coq_STR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (ext_op_modrm ('0'::('0'::('1'::[])))))))

(** val coq_TEST_b : bool -> bigrammar **)

let coq_TEST_b opsize_override =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('1'::[]))))
        (seq (ext_op_modrm ('0'::('0'::('0'::[])))) (imm_b opsize_override)))),
    (fun v ->
    Obj.magic (true, ((let (x, _) = Obj.magic v in x), (Imm_op
      (let (_, y) = Obj.magic v in y))))))), (BLeaf (Big.one,
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (seq (ext_op_modrm ('0'::('0'::('0'::[])))) byte))), (fun v ->
    Obj.magic (false, ((let (x, _) = Obj.magic v in x), (Imm_op
      (zero_extend8_32 (let (_, y) = Obj.magic v in y)))))))))), (BLeaf
    ((Big.double Big.one),
    (bitsleft ('1'::('0'::('0'::('0'::[]))))
      (bitsleft ('0'::('1'::('0'::[]))) (seq anybit modrm_ret_reg))),
    (fun v ->
    let (w, i) = Obj.magic v in
    let (r1, op2) = i in Obj.magic (w, ((Reg_op r1), op2))))))), (BNode
    ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('0'::('1'::[])))) (imm_b opsize_override))),
    (fun v -> Obj.magic (true, ((Imm_op (Obj.magic v)), (Reg_op EAX)))))),
    (BLeaf ((Big.double (Big.double Big.one)),
    (bitsleft ('1'::('0'::('1'::('0'::[]))))
      (bitsleft ('1'::('0'::('0'::('0'::[])))) byte)), (fun b ->
    Obj.magic (false, ((Reg_op EAX), (Imm_op
      (zero_extend8_32 (Obj.magic b)))))))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree MLeaf) in
  let case3 = MRTree (MLTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (w, u1) = Obj.magic u in
    let (op1, op2) = u1 in
    (match op2 with
     | Imm_op imm ->
       (match op1 with
        | Imm_op _ -> None
        | Offset_op _ -> None
        | _ ->
          if w
          then inv_case_some case0 (Obj.magic (op1, imm))
          else if repr_in_unsigned_byte_dec imm
               then inv_case_some case1
                      (Obj.magic (op1, (zero_shrink32_8 imm)))
               else None)
     | Reg_op r2 ->
       (match op1 with
        | Imm_op i ->
          if register_eq_dec r2 EAX
          then if w then inv_case_some case3 (Obj.magic i) else None
          else None
        | Reg_op r1 -> inv_case_some case2 (Obj.magic (w, (r1, op2)))
        | _ -> None)
     | Address_op _ ->
       (match op1 with
        | Reg_op r1 -> inv_case_some case2 (Obj.magic (w, (r1, op2)))
        | _ -> None)
     | Offset_op _ -> None)))

(** val coq_UD2_b : bigrammar **)

let coq_UD2_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsmatch ('1'::('0'::('1'::('1'::[])))))))

(** val coq_VERR_b : bigrammar **)

let coq_VERR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (ext_op_modrm ('1'::('0'::('0'::[])))))))

(** val coq_VERW_b : bigrammar **)

let coq_VERW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('0'::('0'::[]))))
          (ext_op_modrm ('1'::('0'::('1'::[])))))))

(** val coq_WBINVD_b : bigrammar **)

let coq_WBINVD_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsmatch ('1'::('0'::('0'::('1'::[])))))))

(** val coq_WRMSR_b : bigrammar **)

let coq_WRMSR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('0'::('0'::[])))))))

(** val coq_XADD_b : bigrammar **)

let coq_XADD_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('0'::('0'::[]))))
          (bitsleft ('0'::('0'::('0'::[]))) (seq anybit modrm))))) ((fun v ->
    let (w, y) = Obj.magic v in
    let (op1, op2) = y in Obj.magic (w, (op2, op1))), (fun u ->
    let (w, y) = Obj.magic u in
    let (op2, op1) = y in Some (Obj.magic (w, (op1, op2)))))

(** val coq_XCHG_b : bigrammar **)

let coq_XCHG_b =
  map
    (alt
      (bitsleft ('1'::('0'::('0'::('0'::[]))))
        (bitsleft ('0'::('1'::('1'::[]))) (seq anybit modrm_ret_reg)))
      (bitsleft ('1'::('0'::('0'::('1'::[])))) (bitsleft ('0'::[]) reg)))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (w, y0) = y in
      let (r1, op2) = y0 in Obj.magic (w, (op2, (Reg_op r1)))
    | Coq_inr r1 -> Obj.magic (true, ((Reg_op EAX), (Reg_op r1)))), (fun u ->
    let (w, u1) = Obj.magic u in
    let (op2, op1) = u1 in
    (match op2 with
     | Reg_op r2 ->
       (match op1 with
        | Reg_op r1 ->
          if register_eq_dec r2 EAX
          then if w
               then Some (Obj.magic (Coq_inr r1))
               else Some (Obj.magic (Coq_inl (w, (r1, op2))))
          else Some (Obj.magic (Coq_inl (w, (r1, op2))))
        | _ -> None)
     | Address_op _ ->
       (match op1 with
        | Reg_op r1 -> Some (Obj.magic (Coq_inl (w, (r1, op2))))
        | _ -> None)
     | _ -> None)))

(** val coq_XLAT_b : bigrammar **)

let coq_XLAT_b =
  bitsleft ('1'::('1'::('0'::('1'::[]))))
    (bitsmatch ('0'::('1'::('1'::('1'::[])))))

(** val fpu_reg_op_b : bigrammar **)

let fpu_reg_op_b =
  map fpu_reg ((fun v -> Obj.magic (FPS_op (Obj.magic v))), (fun u ->
    match Obj.magic u with
    | FPS_op v -> Some (Obj.magic v)
    | _ -> None))

(** val ext_op_modrm_FPM32_noreg : char list -> bigrammar **)

let ext_op_modrm_FPM32_noreg bs =
  map (ext_op_modrm_noreg_ret_addr bs) ((fun v ->
    Obj.magic (FPM32_op (Obj.magic v))), (fun u ->
    match Obj.magic u with
    | FPM32_op v -> Some (Obj.magic v)
    | _ -> None))

(** val ext_op_modrm_FPM64_noreg : char list -> bigrammar **)

let ext_op_modrm_FPM64_noreg bs =
  map (ext_op_modrm_noreg_ret_addr bs) ((fun v ->
    Obj.magic (FPM64_op (Obj.magic v))), (fun u ->
    match Obj.magic u with
    | FPM64_op v -> Some (Obj.magic v)
    | _ -> None))

(** val fp_condition_type_to_Z : fp_condition_type -> Big.big_int **)

let fp_condition_type_to_Z = function
| B_fct -> Big.zero
| E_fct -> Big.one
| BE_fct -> (Big.double Big.one)
| U_fct -> (Big.doubleplusone Big.one)
| NB_fct -> (Big.double (Big.double Big.one))
| NE_fct -> (Big.doubleplusone (Big.double Big.one))
| NBE_fct -> (Big.double (Big.doubleplusone Big.one))
| NU_fct -> (Big.doubleplusone (Big.doubleplusone Big.one))

(** val coq_F2XM1_b : bigrammar **)

let coq_F2XM1_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('0'::('0'::('0'::[])))))))

(** val coq_FABS_b : bigrammar **)

let coq_FABS_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('0'::('0'::('1'::[])))))))

(** val fp_arith_b : char list -> char list -> bigrammar **)

let fp_arith_b bs0 bs1 =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('0'::('0'::[]))) (ext_op_modrm_noreg_ret_addr bs0))),
    (fun addr -> Obj.magic (true, (FPM32_op (Obj.magic addr)))))), (BLeaf
    (Big.one,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('1'::('0'::('0'::[]))) (ext_op_modrm_noreg_ret_addr bs0))),
    (fun addr -> Obj.magic (true, (FPM64_op (Obj.magic addr)))))))), (BNode
    ((Big.double Big.one), (BLeaf ((Big.double Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::[])
        (bitsleft ('0'::('0'::('1'::('1'::[])))) (bitsleft bs0 fpu_reg)))),
    (fun fr -> Obj.magic (true, (FPS_op (Obj.magic fr)))))), (BLeaf
    ((Big.doubleplusone Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('1'::[])
        (bitsleft ('0'::('0'::('1'::('1'::[])))) (bitsleft bs1 fpu_reg)))),
    (fun fr -> Obj.magic (false, (FPS_op (Obj.magic fr)))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (y, y0) = Obj.magic u in
    if y
    then (match y0 with
          | FPS_op fr -> inv_case_some case2 (Obj.magic fr)
          | FPM32_op addr -> inv_case_some case0 (Obj.magic addr)
          | FPM64_op addr -> inv_case_some case1 (Obj.magic addr)
          | _ -> None)
    else (match y0 with
          | FPS_op fr -> inv_case_some case3 (Obj.magic fr)
          | _ -> None)))

(** val coq_FADD_b : bigrammar **)

let coq_FADD_b =
  fp_arith_b ('0'::('0'::('0'::[]))) ('0'::('0'::('0'::[])))

(** val coq_FADDP_b : bigrammar **)

let coq_FADDP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('0'::('0'::('0'::[]))))) fpu_reg_op_b))

(** val coq_FBLD_b : bigrammar **)

let coq_FBLD_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('1'::[])))
      (ext_op_modrm_FPM64_noreg ('1'::('0'::('0'::[])))))

(** val coq_FBSTP_b : bigrammar **)

let coq_FBSTP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('1'::[])))
      (ext_op_modrm_FPM64_noreg ('1'::('1'::('0'::[])))))

(** val coq_FCHS_b : bigrammar **)

let coq_FCHS_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('0'::('0'::('0'::[])))))))

(** val coq_FCMOVcc_b : bigrammar **)

let coq_FCMOVcc_b =
  map
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('1'::[]))
        (seq anybit
          (bitsleft ('1'::('1'::('0'::[])))
            (seq anybit (seq anybit fpu_reg_op_b)))))) ((fun v ->
    let (b2, y) = Obj.magic v in
    let (b1, y0) = y in
    let (b0, op) = y0 in
    let n =
      int_of_bitsn (Big.succ (Big.succ (Big.succ Big.zero)))
        (Obj.magic (b2, (b1, (b0, ()))))
    in
    Obj.magic ((coq_Z_to_fp_condition_type (Obj.magic n)), op)), (fun u ->
    let (ct, op) = Obj.magic u in
    let bs =
      bitsn_of_int (Big.succ (Big.succ (Big.succ Big.zero)))
        (Obj.magic fp_condition_type_to_Z ct)
    in
    (match bs with
     | Some i ->
       let (b2, i0) = Obj.magic i in
       let (b1, i1) = i0 in
       let (b0, _) = i1 in Some (Obj.magic (b2, (b1, (b0, op))))
     | None -> None)))

(** val coq_FCOM_b : bigrammar **)

let coq_FCOM_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('0'::('0'::('0'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('0'::('0'::[])))
            (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('0'::('0'::('0'::[])))
            (bitsleft ('1'::('1'::('0'::('1'::('0'::[]))))) fpu_reg)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM32_op addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl addr -> Obj.magic (FPM64_op addr)
       | Coq_inr fr -> Obj.magic (FPS_op fr))), (fun u ->
    match Obj.magic u with
    | FPS_op fr -> Some (Obj.magic (Coq_inr (Coq_inr fr)))
    | FPM32_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM64_op addr -> Some (Obj.magic (Coq_inr (Coq_inl addr)))
    | _ -> None))

(** val coq_FCOMP_b : bigrammar **)

let coq_FCOMP_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('0'::('0'::('0'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[]))))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('0'::('0'::[])))
            (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[]))))))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('0'::('0'::('0'::[])))
            (bitsleft ('1'::('1'::('0'::('1'::('1'::[]))))) fpu_reg)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM32_op addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl addr -> Obj.magic (FPM64_op addr)
       | Coq_inr fr -> Obj.magic (FPS_op fr))), (fun u ->
    match Obj.magic u with
    | FPS_op fr -> Some (Obj.magic (Coq_inr (Coq_inr fr)))
    | FPM32_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM64_op addr -> Some (Obj.magic (Coq_inr (Coq_inl addr)))
    | _ -> None))

(** val coq_FCOMPP_b : bigrammar **)

let coq_FCOMPP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsmatch ('0'::('0'::('1'::[]))))))

(** val coq_FCOMIP_b : bigrammar **)

let coq_FCOMIP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('1'::('0'::[]))))) fpu_reg_op_b))

(** val coq_FCOS_b : bigrammar **)

let coq_FCOS_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::[])))
        (bitsmatch ('1'::('1'::('1'::('1'::('1'::[]))))))))

(** val coq_FDECSTP_b : bigrammar **)

let coq_FDECSTP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::[])))
        (bitsmatch ('1'::('0'::('1'::('1'::('0'::[]))))))))

(** val coq_FDIV_b : bigrammar **)

let coq_FDIV_b =
  fp_arith_b ('1'::('1'::('0'::[]))) ('1'::('1'::('1'::[])))

(** val coq_FDIVP_b : bigrammar **)

let coq_FDIVP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('1'::('1'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FDIVR_b : bigrammar **)

let coq_FDIVR_b =
  fp_arith_b ('1'::('1'::('1'::[]))) ('1'::('1'::('0'::[])))

(** val coq_FDIVRP_b : bigrammar **)

let coq_FDIVRP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('1'::('1'::('0'::[]))))) fpu_reg_op_b))

(** val coq_FFREE_b : bigrammar **)

let coq_FFREE_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('0'::('0'::('0'::[]))))) fpu_reg_op_b))

(** val fp_iarith_b : char list -> bigrammar **)

let fp_iarith_b bs =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('1'::('0'::[]))) (ext_op_modrm_noreg_ret_addr bs)))
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('0'::('1'::('0'::[]))) (ext_op_modrm_noreg_ret_addr bs))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM16_op addr)
    | Coq_inr addr -> Obj.magic (FPM32_op addr)), (fun u ->
    match Obj.magic u with
    | FPM16_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM32_op addr -> Some (Obj.magic (Coq_inr addr))
    | _ -> None))

(** val coq_FIADD_b : bigrammar **)

let coq_FIADD_b =
  fp_iarith_b ('0'::('0'::('0'::[])))

(** val coq_FICOM_b : bigrammar **)

let coq_FICOM_b =
  fp_iarith_b ('0'::('1'::('0'::[])))

(** val coq_FICOMP_b : bigrammar **)

let coq_FICOMP_b =
  fp_iarith_b ('0'::('1'::('1'::[])))

(** val coq_FIDIV_b : bigrammar **)

let coq_FIDIV_b =
  fp_iarith_b ('1'::('1'::('0'::[])))

(** val coq_FIDIVR_b : bigrammar **)

let coq_FIDIVR_b =
  fp_iarith_b ('1'::('1'::('1'::[])))

(** val coq_FILD_b : bigrammar **)

let coq_FILD_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('1'::('1'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[]))))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('0'::('1'::('1'::[])))
            (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[]))))))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('1'::('1'::[])))
            (ext_op_modrm_noreg_ret_addr ('1'::('0'::('1'::[]))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM16_op addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl addr -> Obj.magic (FPM32_op addr)
       | Coq_inr addr -> Obj.magic (FPM64_op addr))), (fun u ->
    match Obj.magic u with
    | FPM16_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM32_op addr -> Some (Obj.magic (Coq_inr (Coq_inl addr)))
    | FPM64_op addr -> Some (Obj.magic (Coq_inr (Coq_inr addr)))
    | _ -> None))

(** val coq_FIMUL_b : bigrammar **)

let coq_FIMUL_b =
  fp_iarith_b ('0'::('0'::('1'::[])))

(** val coq_FINCSTP_b : bigrammar **)

let coq_FINCSTP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('1'::('1'::('1'::[])))))))

(** val coq_FIST_b : bigrammar **)

let coq_FIST_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('1'::('1'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('0'::('1'::('1'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM16_op addr)
    | Coq_inr addr -> Obj.magic (FPM32_op addr)), (fun u ->
    match Obj.magic u with
    | FPM16_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM32_op addr -> Some (Obj.magic (Coq_inr addr))
    | _ -> None))

(** val coq_FISTP_b : bigrammar **)

let coq_FISTP_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('1'::('1'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[]))))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('0'::('1'::('1'::[])))
            (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[]))))))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('1'::('1'::[])))
            (ext_op_modrm_noreg_ret_addr ('1'::('1'::('1'::[]))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM16_op addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl addr -> Obj.magic (FPM32_op addr)
       | Coq_inr addr -> Obj.magic (FPM64_op addr))), (fun u ->
    match Obj.magic u with
    | FPM16_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM32_op addr -> Some (Obj.magic (Coq_inr (Coq_inl addr)))
    | FPM64_op addr -> Some (Obj.magic (Coq_inr (Coq_inr addr)))
    | _ -> None))

(** val coq_FISUB_b : bigrammar **)

let coq_FISUB_b =
  fp_iarith_b ('1'::('0'::('0'::[])))

(** val coq_FISUBR_b : bigrammar **)

let coq_FISUBR_b =
  fp_iarith_b ('1'::('0'::('1'::[])))

(** val coq_FLD_b : bigrammar **)

let coq_FLD_b =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('0'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[])))))), (fun addr ->
    Obj.magic (FPM32_op (Obj.magic addr))))), (BLeaf (Big.one,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('1'::('0'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('0'::('0'::('0'::[])))))), (fun addr ->
    Obj.magic (FPM64_op (Obj.magic addr))))))), (BNode ((Big.double Big.one),
    (BLeaf ((Big.double Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('1'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('1'::('0'::('1'::[])))))), (fun addr ->
    Obj.magic (FPM80_op (Obj.magic addr))))), (BLeaf ((Big.doubleplusone
    Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('0'::('1'::[])))
        (bitsleft ('1'::('1'::('0'::('0'::('0'::[]))))) fpu_reg))),
    (fun fr -> Obj.magic (FPS_op (Obj.magic fr))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | FPS_op fr -> inv_case_some case3 (Obj.magic fr)
    | FPM16_op _ -> None
    | FPM32_op addr -> inv_case_some case0 (Obj.magic addr)
    | FPM64_op addr -> inv_case_some case1 (Obj.magic addr)
    | FPM80_op addr -> inv_case_some case2 (Obj.magic addr)))

(** val coq_FLD1_b : bigrammar **)

let coq_FLD1_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('0'::('0'::('0'::[])))))))

(** val coq_FLDCW_b : bigrammar **)

let coq_FLDCW_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (ext_op_modrm_FPM32_noreg ('1'::('0'::('1'::[])))))

(** val coq_FLDENV_b : bigrammar **)

let coq_FLDENV_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (ext_op_modrm_FPM32_noreg ('1'::('0'::('0'::[])))))

(** val coq_FLDL2E_b : bigrammar **)

let coq_FLDL2E_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('0'::('1'::('0'::[])))))))

(** val coq_FLDL2T_b : bigrammar **)

let coq_FLDL2T_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('0'::('0'::('1'::[])))))))

(** val coq_FLDLG2_b : bigrammar **)

let coq_FLDLG2_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('1'::('0'::('0'::[])))))))

(** val coq_FLDLN2_b : bigrammar **)

let coq_FLDLN2_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('1'::('0'::('1'::[])))))))

(** val coq_FLDPI_b : bigrammar **)

let coq_FLDPI_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('0'::('1'::('1'::[])))))))

(** val coq_FLDZ_b : bigrammar **)

let coq_FLDZ_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('1'::('1'::('0'::[])))))))

(** val coq_FMUL_b : bigrammar **)

let coq_FMUL_b =
  fp_arith_b ('0'::('0'::('1'::[]))) ('0'::('0'::('1'::[])))

(** val coq_FMULP_b : bigrammar **)

let coq_FMULP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('0'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FNCLEX_b : bigrammar **)

let coq_FNCLEX_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('1'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('0'::('1'::('0'::[])))))))

(** val coq_FNINIT_b : bigrammar **)

let coq_FNINIT_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('1'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('0'::('1'::('1'::[])))))))

(** val coq_FNOP_b : bigrammar **)

let coq_FNOP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('0'::[]))))))
      (bitsmatch ('1'::('0'::('0'::('0'::('0'::[])))))))

(** val coq_FNSAVE_b : bigrammar **)

let coq_FNSAVE_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::('1'::('0'::('1'::[]))))))))
    (ext_op_modrm_FPM64_noreg ('1'::('1'::('0'::[]))))

(** val coq_FNSTCW_b : bigrammar **)

let coq_FNSTCW_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (ext_op_modrm_FPM32_noreg ('1'::('1'::('1'::[])))))

(** val coq_FNSTSW_b : bigrammar **)

let coq_FNSTSW_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('1'::('1'::[])))
          (bitsleft ('1'::('1'::('1'::[])))
            (bitsmatch ('0'::('0'::('0'::('0'::('0'::[])))))))))
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('1'::('0'::('1'::[])))
          (ext_op_modrm_FPM32_noreg ('1'::('1'::('1'::[]))))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic None
    | Coq_inr op -> Obj.magic (Some op)), (fun u ->
    match Obj.magic u with
    | Some op -> Some (Obj.magic (Coq_inr op))
    | None -> Some (Obj.magic (Coq_inl ()))))

(** val coq_FPATAN_b : bigrammar **)

let coq_FPATAN_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('0'::('1'::('1'::[])))))))

(** val coq_FPREM_b : bigrammar **)

let coq_FPREM_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('0'::('0'::('0'::[])))))))

(** val coq_FPREM1_b : bigrammar **)

let coq_FPREM1_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('1'::('0'::('1'::[])))))))

(** val coq_FPTAN_b : bigrammar **)

let coq_FPTAN_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('0'::('1'::('0'::[])))))))

(** val coq_FRNDINT_b : bigrammar **)

let coq_FRNDINT_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('1'::('0'::('0'::[])))))))

(** val coq_FRSTOR_b : bigrammar **)

let coq_FRSTOR_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('0'::('1'::[])))
      (ext_op_modrm_FPM32_noreg ('1'::('0'::('0'::[])))))

(** val coq_FSCALE_b : bigrammar **)

let coq_FSCALE_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('1'::('0'::('1'::[])))))))

(** val coq_FSIN_b : bigrammar **)

let coq_FSIN_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('1'::('1'::('0'::[])))))))

(** val coq_FSINCOS_b : bigrammar **)

let coq_FSINCOS_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('0'::('1'::('1'::[])))))))

(** val coq_FSQRT_b : bigrammar **)

let coq_FSQRT_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('0'::('1'::('0'::[])))))))

(** val coq_FST_b : bigrammar **)

let coq_FST_b =
  map
    (alt
      (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
        (bitsleft ('0'::('0'::('1'::[])))
          (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))
      (alt
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('0'::('1'::[])))
            (ext_op_modrm_noreg_ret_addr ('0'::('1'::('0'::[]))))))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
          (bitsleft ('1'::('0'::('1'::[])))
            (bitsleft ('1'::('1'::('0'::('1'::('0'::[]))))) fpu_reg)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl addr -> Obj.magic (FPM32_op addr)
    | Coq_inr y ->
      (match y with
       | Coq_inl addr -> Obj.magic (FPM64_op addr)
       | Coq_inr fr -> Obj.magic (FPS_op fr))), (fun u ->
    match Obj.magic u with
    | FPS_op fr -> Some (Obj.magic (Coq_inr (Coq_inr fr)))
    | FPM32_op addr -> Some (Obj.magic (Coq_inl addr))
    | FPM64_op addr -> Some (Obj.magic (Coq_inr (Coq_inl addr)))
    | _ -> None))

(** val coq_FSTENV_b : bigrammar **)

let coq_FSTENV_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (ext_op_modrm_FPM32_noreg ('1'::('1'::('0'::[])))))

(** val coq_FSTP_b : bigrammar **)

let coq_FSTP_b =
  let gt = BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('0'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[])))))), (fun addr ->
    Obj.magic (FPM32_op (Obj.magic addr))))), (BLeaf (Big.one,
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('1'::('0'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('0'::('1'::('1'::[])))))), (fun addr ->
    Obj.magic (FPM64_op (Obj.magic addr))))))), (BNode ((Big.double Big.one),
    (BLeaf ((Big.double Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('0'::('1'::('1'::[])))
        (ext_op_modrm_noreg_ret_addr ('1'::('1'::('1'::[])))))), (fun addr ->
    Obj.magic (FPM80_op (Obj.magic addr))))), (BLeaf ((Big.doubleplusone
    Big.one),
    (bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
      (bitsleft ('1'::('0'::('1'::[])))
        (bitsleft ('1'::('1'::('0'::('1'::('1'::[]))))) fpu_reg))),
    (fun fr -> Obj.magic (FPS_op (Obj.magic fr))))))))
  in
  let case0 = MLTree (MLTree MLeaf) in
  let case1 = MLTree (MRTree MLeaf) in
  let case2 = MRTree (MLTree MLeaf) in
  let case3 = MRTree (MRTree MLeaf) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | FPS_op fr -> inv_case_some case3 (Obj.magic fr)
    | FPM16_op _ -> None
    | FPM32_op addr -> inv_case_some case0 (Obj.magic addr)
    | FPM64_op addr -> inv_case_some case1 (Obj.magic addr)
    | FPM80_op addr -> inv_case_some case2 (Obj.magic addr)))

(** val coq_FSUB_b : bigrammar **)

let coq_FSUB_b =
  fp_arith_b ('1'::('0'::('0'::[]))) ('1'::('0'::('1'::[])))

(** val coq_FSUBP_b : bigrammar **)

let coq_FSUBP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FSUBR_b : bigrammar **)

let coq_FSUBR_b =
  fp_arith_b ('1'::('0'::('1'::[]))) ('1'::('0'::('0'::[])))

(** val coq_FSUBRP_b : bigrammar **)

let coq_FSUBRP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('0'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('0'::[]))))) fpu_reg_op_b))

(** val coq_FTST_b : bigrammar **)

let coq_FTST_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('1'::('0'::('0'::[])))))))

(** val coq_FUCOM_b : bigrammar **)

let coq_FUCOM_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('0'::[]))))) fpu_reg_op_b))

(** val coq_FUCOMP_b : bigrammar **)

let coq_FUCOMP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FUCOMPP_b : bigrammar **)

let coq_FUCOMPP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('1'::('0'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('1'::('0'::('0'::('1'::[])))))))

(** val coq_FUCOMI_b : bigrammar **)

let coq_FUCOMI_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('1'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FUCOMIP_b : bigrammar **)

let coq_FUCOMIP_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('1'::('1'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FXAM_b : bigrammar **)

let coq_FXAM_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('0'::('0'::('1'::('0'::('1'::[])))))))

(** val coq_FXCH_b : bigrammar **)

let coq_FXCH_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('0'::('0'::('1'::[]))))) fpu_reg_op_b))

(** val coq_FXTRACT_b : bigrammar **)

let coq_FXTRACT_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::[])))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsmatch ('0'::('1'::('0'::('0'::[])))))))

(** val coq_FYL2X_b : bigrammar **)

let coq_FYL2X_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('0'::('0'::('0'::('1'::[])))))))

(** val coq_FYL2XP1_b : bigrammar **)

let coq_FYL2XP1_b =
  bitsleft ('1'::('1'::('0'::('1'::('1'::[])))))
    (bitsleft ('0'::('0'::('1'::('1'::('1'::('1'::[]))))))
      (bitsmatch ('1'::('1'::('0'::('0'::('1'::[])))))))

(** val coq_FWAIT_b : bigrammar **)

let coq_FWAIT_b =
  bitsmatch ('1'::('0'::('0'::('1'::('1'::('0'::('1'::('1'::[]))))))))

(** val modrm_mmx_noreg : bigrammar **)

let modrm_mmx_noreg =
  modrm_gen_noreg mmx_reg

(** val modrm_mmx_ret_reg : bigrammar **)

let modrm_mmx_ret_reg =
  map (modrm_gen mmx_reg) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (r, addr) = y in Obj.magic (r, (MMX_Addr_op addr))
    | Coq_inr y -> let (r1, r2) = y in Obj.magic (r1, (MMX_Reg_op r2))),
    (fun u ->
    let (r1, y) = Obj.magic u in
    (match y with
     | MMX_Addr_op addr -> Some (Obj.magic (Coq_inl (r1, addr)))
     | MMX_Reg_op r2 -> Some (Obj.magic (Coq_inr (r1, r2)))
     | _ -> None)))

(** val modrm_mmx : bigrammar **)

let modrm_mmx =
  map modrm_mmx_ret_reg ((fun v ->
    let (r1, op2) = Obj.magic v in Obj.magic ((MMX_Reg_op r1), op2)),
    (fun u ->
    let (y, op2) = Obj.magic u in
    (match y with
     | MMX_Reg_op r1 -> Some (Obj.magic (r1, op2))
     | _ -> None)))

(** val mmx_gg_b_8_16_32 : bigrammar **)

let mmx_gg_b_8_16_32 =
  map
    (alt (bitsmatch ('0'::('0'::[])))
      (alt (bitsmatch ('0'::('1'::[]))) (bitsmatch ('1'::('0'::[])))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic MMX_8
    | Coq_inr y ->
      (match y with
       | Coq_inl _ -> Obj.magic MMX_16
       | Coq_inr _ -> Obj.magic MMX_32)), (fun u ->
    match Obj.magic u with
    | MMX_8 -> Some (Obj.magic (Coq_inl ()))
    | MMX_16 -> Some (Obj.magic (Coq_inr (Coq_inl ())))
    | MMX_32 -> Some (Obj.magic (Coq_inr (Coq_inr ())))
    | MMX_64 -> None))

(** val mmx_gg_b_8_16 : bigrammar **)

let mmx_gg_b_8_16 =
  map (alt (bitsmatch ('0'::('0'::[]))) (bitsmatch ('0'::('1'::[]))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic MMX_8
    | Coq_inr _ -> Obj.magic MMX_16), (fun u ->
    match Obj.magic u with
    | MMX_8 -> Some (Obj.magic (Coq_inl ()))
    | MMX_16 -> Some (Obj.magic (Coq_inr ()))
    | _ -> None))

(** val mmx_gg_b_16_32_64 : bigrammar **)

let mmx_gg_b_16_32_64 =
  map
    (alt (bitsmatch ('0'::('1'::[])))
      (alt (bitsmatch ('1'::('0'::[]))) (bitsmatch ('1'::('1'::[])))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic MMX_16
    | Coq_inr y ->
      (match y with
       | Coq_inl _ -> Obj.magic MMX_32
       | Coq_inr _ -> Obj.magic MMX_64)), (fun u ->
    match Obj.magic u with
    | MMX_8 -> None
    | MMX_16 -> Some (Obj.magic (Coq_inl ()))
    | MMX_32 -> Some (Obj.magic (Coq_inr (Coq_inl ())))
    | MMX_64 -> Some (Obj.magic (Coq_inr (Coq_inr ())))))

(** val mmx_gg_b_16_32 : bigrammar **)

let mmx_gg_b_16_32 =
  map (alt (bitsmatch ('0'::('1'::[]))) (bitsmatch ('1'::('0'::[]))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic MMX_16
    | Coq_inr _ -> Obj.magic MMX_32), (fun u ->
    match Obj.magic u with
    | MMX_16 -> Some (Obj.magic (Coq_inl ()))
    | MMX_32 -> Some (Obj.magic (Coq_inr ()))
    | _ -> None))

(** val coq_EMMS_b : bigrammar **)

let coq_EMMS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('1'::[]))))
        (bitsmatch ('0'::('1'::('1'::('1'::[])))))))

(** val coq_MOVD_b : bigrammar **)

let coq_MOVD_b =
  let gt = BNode (Big.zero, (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit
            (bitsleft ('1'::('1'::('1'::('0'::[]))))
              (bitsleft ('1'::('1'::[])) (seq mmx_reg reg))))))), (fun v ->
    let (d, v1) = Obj.magic v in
    let (mr, r) = v1 in
    if d
    then Obj.magic ((MMX_Reg_op mr), (GP_Reg_op r))
    else Obj.magic ((GP_Reg_op r), (MMX_Reg_op mr))))), (BLeaf (Big.one,
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit
            (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_mmx_noreg))))),
    (fun v ->
    let (d, v1) = Obj.magic v in
    let (mr, addr) = v1 in
    if d
    then Obj.magic ((MMX_Addr_op addr), (MMX_Reg_op mr))
    else Obj.magic ((MMX_Reg_op mr), (MMX_Addr_op addr))))))
  in
  let case0 = MLTree MLeaf in
  let case1 = MRTree MLeaf in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | GP_Reg_op r ->
       (match y0 with
        | MMX_Reg_op mr -> inv_case_some case0 (Obj.magic (false, (mr, r)))
        | _ -> None)
     | MMX_Addr_op addr ->
       (match y0 with
        | MMX_Reg_op mr -> inv_case_some case1 (Obj.magic (true, (mr, addr)))
        | _ -> None)
     | MMX_Reg_op mr ->
       (match y0 with
        | GP_Reg_op r -> inv_case_some case0 (Obj.magic (true, (mr, r)))
        | MMX_Addr_op addr ->
          inv_case_some case1 (Obj.magic (false, (mr, addr)))
        | _ -> None)
     | MMX_Imm_op _ -> None)))

(** val coq_MOVQ_b : bigrammar **)

let coq_MOVQ_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::[])))
          (seq anybit (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_mmx)))))
    ((fun v ->
    let (d, v1) = Obj.magic v in
    let (op1, op2) = v1 in
    if d then Obj.magic (op2, op1) else Obj.magic (op1, op2)), (fun u ->
    let (op1, op2) = Obj.magic u in
    (match op1 with
     | MMX_Reg_op _ -> Some (Obj.magic (false, (op1, op2)))
     | _ ->
       (match op2 with
        | MMX_Reg_op _ -> Some (Obj.magic (true, (op2, op1)))
        | _ -> None))))

(** val coq_PACKSSDW_b : bigrammar **)

let coq_PACKSSDW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_PACKSSWB_b : bigrammar **)

let coq_PACKSSWB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_PACKUSWB_b : bigrammar **)

let coq_PACKUSWB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_PADD_b : bigrammar **)

let coq_PADD_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PADDS_b : bigrammar **)

let coq_PADDS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::[])) (seq mmx_gg_b_8_16 modrm_mmx))))

(** val coq_PADDUS_b : bigrammar **)

let coq_PADDUS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::[])) (seq mmx_gg_b_8_16 modrm_mmx))))

(** val coq_PAND_b : bigrammar **)

let coq_PAND_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_PANDN_b : bigrammar **)

let coq_PANDN_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_PCMPEQ_b : bigrammar **)

let coq_PCMPEQ_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PCMPGT_b : bigrammar **)

let coq_PCMPGT_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PMADDWD_b : bigrammar **)

let coq_PMADDWD_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm_mmx)))

(** val coq_PMULHUW_b : bigrammar **)

let coq_PMULHUW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::('0'::('0'::[])))) modrm_mmx)))

(** val coq_PMULHW_b : bigrammar **)

let coq_PMULHW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm_mmx)))

(** val coq_PMULLW_b : bigrammar **)

let coq_PMULLW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm_mmx)))

(** val coq_POR_b : bigrammar **)

let coq_POR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::('1'::('1'::[])))) modrm_mmx)))

(** val pshift_b : char list -> bigrammar -> bigrammar **)

let pshift_b bs gg_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::[]))
            (bitsleft bs
              (bitsleft ('0'::('0'::[])) (seq gg_b modrm_mmx_ret_reg))))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('1'::('1'::[]))))
            (bitsleft ('0'::('0'::[]))
              (seq gg_b
                (bitsleft ('1'::('1'::[]))
                  (bitsleft bs (bitsleft ('0'::[]) (seq mmx_reg byte))))))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (gg, y0) = y in
      let (r1, op2) = y0 in Obj.magic (gg, ((MMX_Reg_op r1), op2))
    | Coq_inr y ->
      let (gg, y0) = y in
      let (r1, imm) = y0 in
      Obj.magic (gg, ((MMX_Reg_op r1), (MMX_Imm_op (zero_extend8_32 imm))))),
    (fun u ->
    let (gg, u1) = Obj.magic u in
    let (op1, op2) = u1 in
    (match op1 with
     | MMX_Reg_op r1 ->
       (match op2 with
        | GP_Reg_op _ -> None
        | MMX_Addr_op _ -> Some (Obj.magic (Coq_inl (gg, (r1, op2))))
        | MMX_Reg_op _ -> Some (Obj.magic (Coq_inl (gg, (r1, op2))))
        | MMX_Imm_op imm ->
          if repr_in_unsigned_byte_dec imm
          then Some (Obj.magic (Coq_inr (gg, (r1, (zero_shrink32_8 imm)))))
          else None)
     | _ -> None)))

(** val coq_PSLL_b : bigrammar **)

let coq_PSLL_b =
  pshift_b ('1'::('1'::[])) mmx_gg_b_16_32_64

(** val coq_PSRA_b : bigrammar **)

let coq_PSRA_b =
  pshift_b ('1'::('0'::[])) mmx_gg_b_16_32

(** val coq_PSRL_b : bigrammar **)

let coq_PSRL_b =
  pshift_b ('0'::('1'::[])) mmx_gg_b_16_32_64

(** val coq_PSUB_b : bigrammar **)

let coq_PSUB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('0'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PSUBS_b : bigrammar **)

let coq_PSUBS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::[])) (seq mmx_gg_b_8_16 modrm_mmx))))

(** val coq_PSUBUS_b : bigrammar **)

let coq_PSUBUS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::[])) (seq mmx_gg_b_8_16 modrm_mmx))))

(** val coq_PUNPCKH_b : bigrammar **)

let coq_PUNPCKH_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PUNPCKL_b : bigrammar **)

let coq_PUNPCKL_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('1'::('0'::[]))))
        (bitsleft ('0'::('0'::[])) (seq mmx_gg_b_8_16_32 modrm_mmx))))

(** val coq_PXOR_b : bigrammar **)

let coq_PXOR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_mmx)))

(** val coq_SSE_XMM_Reg_op_b : bigrammar **)

let coq_SSE_XMM_Reg_op_b =
  map sse_reg ((fun r -> Obj.magic (SSE_XMM_Reg_op (Obj.magic r))),
    (fun op ->
    match Obj.magic op with
    | SSE_XMM_Reg_op r -> Some (Obj.magic r)
    | _ -> None))

(** val coq_SSE_GP_Reg_op_b : bigrammar **)

let coq_SSE_GP_Reg_op_b =
  map reg ((fun r -> Obj.magic (SSE_GP_Reg_op (Obj.magic r))), (fun op ->
    match Obj.magic op with
    | SSE_GP_Reg_op r -> Some (Obj.magic r)
    | _ -> None))

(** val coq_SSE_MM_Reg_op_b : bigrammar **)

let coq_SSE_MM_Reg_op_b =
  map mmx_reg ((fun r -> Obj.magic (SSE_MM_Reg_op (Obj.magic r))), (fun op ->
    match Obj.magic op with
    | SSE_MM_Reg_op r -> Some (Obj.magic r)
    | _ -> None))

(** val modrm_xmm_ret_reg : bigrammar **)

let modrm_xmm_ret_reg =
  map (modrm_gen sse_reg) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (r, addr) = y in Obj.magic (r, (SSE_Addr_op addr))
    | Coq_inr y -> let (r1, r2) = y in Obj.magic (r1, (SSE_XMM_Reg_op r2))),
    (fun u ->
    let (r1, y) = Obj.magic u in
    (match y with
     | SSE_XMM_Reg_op r2 -> Some (Obj.magic (Coq_inr (r1, r2)))
     | SSE_Addr_op addr -> Some (Obj.magic (Coq_inl (r1, addr)))
     | _ -> None)))

(** val modrm_xmm : bigrammar **)

let modrm_xmm =
  map modrm_xmm_ret_reg ((fun v ->
    let (sr1, op2) = Obj.magic v in Obj.magic ((SSE_XMM_Reg_op sr1), op2)),
    (fun u ->
    let (y, op2) = Obj.magic u in
    (match y with
     | SSE_XMM_Reg_op sr1 -> Some (Obj.magic (sr1, op2))
     | _ -> None)))

(** val modrm_mm_ret_reg : bigrammar **)

let modrm_mm_ret_reg =
  map (modrm_gen mmx_reg) ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (r, addr) = y in Obj.magic (r, (SSE_Addr_op addr))
    | Coq_inr y -> let (r1, r2) = y in Obj.magic (r1, (SSE_MM_Reg_op r2))),
    (fun u ->
    let (r1, y) = Obj.magic u in
    (match y with
     | SSE_MM_Reg_op r2 -> Some (Obj.magic (Coq_inr (r1, r2)))
     | SSE_Addr_op addr -> Some (Obj.magic (Coq_inl (r1, addr)))
     | _ -> None)))

(** val modrm_mm : bigrammar **)

let modrm_mm =
  map modrm_mm_ret_reg ((fun v ->
    let (mr1, op2) = Obj.magic v in Obj.magic ((SSE_MM_Reg_op mr1), op2)),
    (fun u ->
    let (y, op2) = Obj.magic u in
    (match y with
     | SSE_MM_Reg_op mr1 -> Some (Obj.magic (mr1, op2))
     | _ -> None)))

(** val modrm_xmm_byte : bigrammar **)

let modrm_xmm_byte =
  map (seq modrm_xmm byte) ((fun v ->
    let (y, b) = Obj.magic v in
    let (op1, op2) = y in Obj.magic (op1, (op2, b))), (fun u ->
    let (op1, u1) = Obj.magic u in
    let (op2, b) = u1 in Some (Obj.magic ((op1, op2), b))))

(** val ext_op_modrm_sse_noreg : char list -> bigrammar **)

let ext_op_modrm_sse_noreg bs =
  map (ext_op_modrm_noreg_ret_addr bs) ((Obj.magic (fun x -> SSE_Addr_op x)),
    (Obj.magic coq_SSE_Addr_op_inv))

(** val coq_ADDPS_b : bigrammar **)

let coq_ADDPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('0'::[])))) modrm_xmm)))

(** val coq_ADDSS_b : bigrammar **)

let coq_ADDSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('0'::('0'::('0'::[])))) modrm_xmm)))))

(** val coq_ANDNPS_b : bigrammar **)

let coq_ANDNPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm_xmm)))

(** val coq_ANDPS_b : bigrammar **)

let coq_ANDPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('0'::[])))) modrm_xmm)))

(** val coq_CMPPS_b : bigrammar **)

let coq_CMPPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('0'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm_xmm_byte)))

(** val coq_CMPSS_b : bigrammar **)

let coq_CMPSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('0'::('0'::[]))))
            (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm_xmm_byte)))))

(** val coq_COMISS_b : bigrammar **)

let coq_COMISS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_xmm)))

(** val coq_CVTPI2PS_b : bigrammar **)

let coq_CVTPI2PS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[])))) modrm_xmm)))

(** val coq_CVTPS2PI_b : bigrammar **)

let coq_CVTPS2PI_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('1'::('0'::[]))))
            (bitsleft ('1'::('1'::('0'::('1'::[]))))
              (bitsleft ('1'::('1'::[])) (seq sse_reg mmx_reg))))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('1'::('0'::[]))))
            (bitsleft ('1'::('1'::('0'::('1'::[])))) modrm_bv2_noreg)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (sr, mr) = y in Obj.magic ((SSE_XMM_Reg_op sr), (SSE_MM_Reg_op mr))
    | Coq_inr y ->
      let (sr, addr) = y in
      Obj.magic ((SSE_XMM_Reg_op sr), (SSE_Addr_op addr))), (fun u ->
    let (op1, op2) = Obj.magic u in
    (match op1 with
     | SSE_XMM_Reg_op sr ->
       (match op2 with
        | SSE_MM_Reg_op mr -> Some (Obj.magic (Coq_inl (sr, mr)))
        | SSE_Addr_op addr -> Some (Obj.magic (Coq_inr (sr, addr)))
        | _ -> None)
     | _ -> None)))

(** val coq_CVTSI2SS_b : bigrammar **)

let coq_CVTSI2SS_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[]))))
              (bitsleft ('0'::('0'::('1'::('0'::[]))))
                (bitsleft ('1'::('0'::('1'::('0'::[]))))
                  (bitsleft ('1'::('1'::[])) (seq sse_reg reg))))))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[]))))
              (bitsleft ('0'::('0'::('1'::('0'::[]))))
                (bitsleft ('1'::('0'::('1'::('0'::[])))) modrm_bv2_noreg)))))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (sr, r) = y in Obj.magic ((SSE_XMM_Reg_op sr), (SSE_GP_Reg_op r))
    | Coq_inr y ->
      let (sr, addr) = y in
      Obj.magic ((SSE_XMM_Reg_op sr), (SSE_Addr_op addr))), (fun u ->
    let (op1, op2) = Obj.magic u in
    (match op1 with
     | SSE_XMM_Reg_op sr ->
       (match op2 with
        | SSE_Addr_op addr -> Some (Obj.magic (Coq_inr (sr, addr)))
        | SSE_GP_Reg_op r -> Some (Obj.magic (Coq_inl (sr, r)))
        | _ -> None)
     | _ -> None)))

(** val ss2si_b : char list -> bigrammar **)

let ss2si_b bs =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[]))))
              (bitsleft ('0'::('0'::('1'::('0'::[]))))
                (bitsleft bs (bitsleft ('1'::('1'::[])) (seq reg sse_reg))))))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[]))))
              (bitsleft ('0'::('0'::('1'::('0'::[]))))
                (bitsleft bs modrm_noreg))))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (r, sr) = y in Obj.magic ((SSE_GP_Reg_op r), (SSE_XMM_Reg_op sr))
    | Coq_inr y ->
      let (r, addr) = y in Obj.magic ((SSE_GP_Reg_op r), (SSE_Addr_op addr))),
    (fun u ->
    let (op1, op2) = Obj.magic u in
    (match op1 with
     | SSE_GP_Reg_op r ->
       (match op2 with
        | SSE_XMM_Reg_op sr -> Some (Obj.magic (Coq_inl (r, sr)))
        | SSE_Addr_op addr -> Some (Obj.magic (Coq_inr (r, addr)))
        | _ -> None)
     | _ -> None)))

(** val coq_CVTSS2SI_b : bigrammar **)

let coq_CVTSS2SI_b =
  ss2si_b ('1'::('1'::('0'::('1'::[]))))

(** val coq_CVTTPS2PI_b : bigrammar **)

let coq_CVTTPS2PI_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('0'::('0'::[])))) modrm_xmm)))

(** val coq_CVTTSS2SI_b : bigrammar **)

let coq_CVTTSS2SI_b =
  ss2si_b ('1'::('1'::('0'::('0'::[]))))

(** val coq_DIVPS_b : bigrammar **)

let coq_DIVPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_xmm)))

(** val coq_DIVSS_b : bigrammar **)

let coq_DIVSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_xmm)))))

(** val coq_LDMXCSR_b : bigrammar **)

let coq_LDMXCSR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('1'::('0'::[])))))))

(** val coq_MAXPS_b : bigrammar **)

let coq_MAXPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_xmm)))

(** val coq_MAXSS_b : bigrammar **)

let coq_MAXSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('1'::('1'::('1'::[])))) modrm_xmm)))))

(** val coq_MINPS_b : bigrammar **)

let coq_MINPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('0'::('1'::[])))) modrm_xmm)))

(** val coq_MINSS_b : bigrammar **)

let coq_MINSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('1'::('0'::('1'::[])))) modrm_xmm)))))

(** val sse_mov_b : char list -> bigrammar **)

let sse_mov_b bs =
  map (bitsleft bs (seq anybit modrm_xmm)) ((fun v ->
    let (d, p) = Obj.magic v in
    let (op1, op2) = p in
    if d then Obj.magic (op2, op1) else Obj.magic (op1, op2)), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_XMM_Reg_op _ ->
       (match y0 with
        | SSE_XMM_Reg_op _ -> Some (Obj.magic (false, u))
        | SSE_Addr_op _ -> Some (Obj.magic (false, u))
        | _ -> None)
     | SSE_Addr_op _ ->
       (match y0 with
        | SSE_XMM_Reg_op _ ->
          Some (Obj.magic (true, ((snd (Obj.magic u)), (fst (Obj.magic u)))))
        | _ -> None)
     | _ -> None)))

(** val coq_MOVAPS_b : bigrammar **)

let coq_MOVAPS_b =
  sse_mov_b
    ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('1'::('0'::('1'::('0'::('0'::[])))))))))))))))

(** val coq_MOVHLPS_b : bigrammar **)

let coq_MOVHLPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_XMM_Reg_op_b coq_SSE_XMM_Reg_op_b)))))

(** val sse_mov_ps_b : char list -> bigrammar **)

let sse_mov_ps_b bs =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[]))))
          (bitsleft bs (seq anybit modrm_bv2_noreg))))) ((fun v ->
    let (d, y) = Obj.magic v in
    let (sr, addr) = y in
    if d
    then Obj.magic ((SSE_Addr_op addr), (SSE_XMM_Reg_op sr))
    else Obj.magic ((SSE_XMM_Reg_op sr), (SSE_Addr_op addr))), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_XMM_Reg_op sr ->
       (match y0 with
        | SSE_Addr_op addr -> Some (Obj.magic (false, (sr, addr)))
        | _ -> None)
     | SSE_Addr_op addr ->
       (match y0 with
        | SSE_XMM_Reg_op sr -> Some (Obj.magic (true, (sr, addr)))
        | _ -> None)
     | _ -> None)))

(** val coq_MOVHPS_b : bigrammar **)

let coq_MOVHPS_b =
  sse_mov_ps_b ('0'::('1'::('1'::[])))

(** val coq_MOVLHPS_b : bigrammar **)

let coq_MOVLHPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_XMM_Reg_op_b coq_SSE_XMM_Reg_op_b)))))

(** val coq_MOVLPS_b : bigrammar **)

let coq_MOVLPS_b =
  sse_mov_ps_b ('0'::('0'::('1'::[])))

(** val coq_MOVMSKPS_b : bigrammar **)

let coq_MOVMSKPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_GP_Reg_op_b coq_SSE_XMM_Reg_op_b)))))

(** val coq_MOVSS_b : bigrammar **)

let coq_MOVSS_b =
  sse_mov_b
    ('1'::('1'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))))))))))

(** val coq_MOVUPS_b : bigrammar **)

let coq_MOVUPS_b =
  sse_mov_b
    ('0'::('0'::('0'::('0'::('1'::('1'::('1'::('1'::('0'::('0'::('0'::('1'::('0'::('0'::('0'::[])))))))))))))))

(** val coq_MULPS_b : bigrammar **)

let coq_MULPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('1'::[])))) modrm_xmm)))

(** val coq_MULSS_b : bigrammar **)

let coq_MULSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('0'::('0'::('1'::[])))) modrm_xmm)))))

(** val coq_ORPS_b : bigrammar **)

let coq_ORPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('0'::[])))) modrm_xmm)))

(** val coq_RCPPS_b : bigrammar **)

let coq_RCPPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm_xmm)))

(** val coq_RCPSS_b : bigrammar **)

let coq_RCPSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm_xmm)))))

(** val coq_RSQRTPS_b : bigrammar **)

let coq_RSQRTPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm_xmm)))

(** val coq_RSQRTSS_b : bigrammar **)

let coq_RSQRTSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('0'::('0'::('1'::('0'::[])))) modrm_xmm)))))

(** val coq_SHUFPS_b : bigrammar **)

let coq_SHUFPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('0'::[]))))
        (bitsleft ('0'::('1'::('1'::('0'::[])))) modrm_xmm_byte)))

(** val coq_SQRTPS_b : bigrammar **)

let coq_SQRTPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('0'::('0'::('1'::[])))) modrm_xmm)))

(** val coq_SQRTSS_b : bigrammar **)

let coq_SQRTSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('0'::('0'::('0'::('1'::[])))) modrm_xmm)))))

(** val coq_STMXCSR_b : bigrammar **)

let coq_STMXCSR_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('1'::('1'::[])))))))

(** val coq_SUBPS_b : bigrammar **)

let coq_SUBPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('0'::('0'::[])))) modrm_xmm)))

(** val coq_SUBSS_b : bigrammar **)

let coq_SUBSS_b =
  bitsleft ('1'::('1'::('1'::('1'::[]))))
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('1'::('0'::('1'::[]))))
            (bitsleft ('1'::('1'::('0'::('0'::[])))) modrm_xmm)))))

(** val coq_UCOMISS_b : bigrammar **)

let coq_UCOMISS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_xmm)))

(** val coq_UNPCKHPS_b : bigrammar **)

let coq_UNPCKHPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[])))) modrm_xmm)))

(** val coq_UNPCKLPS_b : bigrammar **)

let coq_UNPCKLPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('0'::('0'::[])))) modrm_xmm)))

(** val coq_XORPS_b : bigrammar **)

let coq_XORPS_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('1'::[])))) modrm_xmm)))

(** val coq_PAVGB_b : bigrammar **)

let coq_PAVGB_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::('0'::[]))))
            (bitsleft ('0'::('0'::('0'::('0'::[])))) modrm_mm_ret_reg))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('1'::('0'::[]))))
            (bitsleft ('0'::('0'::('1'::('1'::[])))) modrm_mm_ret_reg)))))
    ((fun v ->
    match Obj.magic v with
    | Coq_inl y -> let (mr1, op2) = y in Obj.magic ((SSE_MM_Reg_op mr1), op2)
    | Coq_inr y -> let (mr1, op2) = y in Obj.magic (op2, (SSE_MM_Reg_op mr1))),
    (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_MM_Reg_op mr1 ->
       (match y0 with
        | SSE_MM_Reg_op _ ->
          Some (Obj.magic (Coq_inl (mr1, (snd (Obj.magic u)))))
        | SSE_Addr_op _ ->
          Some (Obj.magic (Coq_inl (mr1, (snd (Obj.magic u)))))
        | _ -> None)
     | SSE_Addr_op _ ->
       (match y0 with
        | SSE_MM_Reg_op mr1 ->
          Some (Obj.magic (Coq_inr (mr1, (fst (Obj.magic u)))))
        | _ -> None)
     | _ -> None)))

(** val coq_PEXTRW_b : bigrammar **)

let coq_PEXTRW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('0'::[]))))
        (bitsleft ('0'::('1'::('0'::('1'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_GP_Reg_op_b (seq coq_SSE_MM_Reg_op_b byte))))))

(** val coq_PINSRW_b : bigrammar **)

let coq_PINSRW_b =
  map
    (alt
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('0'::('0'::[]))))
            (bitsleft ('0'::('1'::('0'::('0'::[]))))
              (bitsleft ('1'::('1'::[])) (seq mmx_reg (seq reg byte)))))))
      (bitsleft ('0'::('0'::('0'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::('0'::('0'::[]))))
            (bitsleft ('0'::('1'::('0'::('0'::[]))))
              (seq modrm_bv2_noreg byte)))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl y ->
      let (mr, y0) = y in
      let (r, imm) = y0 in
      Obj.magic ((SSE_MM_Reg_op mr), ((SSE_GP_Reg_op r), imm))
    | Coq_inr y ->
      let (y0, imm) = y in
      let (mr, addr) = y0 in
      Obj.magic ((SSE_MM_Reg_op mr), ((SSE_Addr_op addr), imm))), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_MM_Reg_op mr ->
       let (y1, imm) = y0 in
       (match y1 with
        | SSE_Addr_op addr -> Some (Obj.magic (Coq_inr ((mr, addr), imm)))
        | SSE_GP_Reg_op r -> Some (Obj.magic (Coq_inl (mr, (r, imm))))
        | _ -> None)
     | _ -> None)))

(** val coq_PMAXSW_b : bigrammar **)

let coq_PMAXSW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_mm)))

(** val coq_PMAXUB_b : bigrammar **)

let coq_PMAXUB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[])))) modrm_mm)))

(** val coq_PMINSW_b : bigrammar **)

let coq_PMINSW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('0'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[])))) modrm_mm)))

(** val coq_PMINUB_b : bigrammar **)

let coq_PMINUB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('1'::('0'::[])))) modrm_mm)))

(** val coq_PMOVMSKB_b : bigrammar **)

let coq_PMOVMSKB_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('0'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_GP_Reg_op_b coq_SSE_MM_Reg_op_b)))))

(** val coq_PSADBW_b : bigrammar **)

let coq_PSADBW_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('0'::[])))) modrm_mm)))

(** val coq_PSHUFW_b : bigrammar **)

let coq_PSHUFW_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('1'::[]))))
          (bitsleft ('0'::('0'::('0'::('0'::[])))) (seq modrm_mm byte)))))
    ((fun v ->
    let (y, imm) = Obj.magic v in
    let (op1, op2) = y in Obj.magic (op1, (op2, imm))), (fun u ->
    let (op1, y) = Obj.magic u in
    let (op2, imm) = y in Some (Obj.magic ((op1, op2), imm))))

(** val coq_MASKMOVQ_b : bigrammar **)

let coq_MASKMOVQ_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('1'::('1'::('1'::[]))))
          (bitsleft ('1'::('1'::[]))
            (seq coq_SSE_MM_Reg_op_b coq_SSE_MM_Reg_op_b)))))

(** val coq_MOVNTPS_b : bigrammar **)

let coq_MOVNTPS_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('0'::('0'::('1'::('0'::[]))))
          (bitsleft ('1'::('0'::('1'::('1'::[])))) modrm_bv2_noreg))))
    ((fun v ->
    let (mr, addr) = Obj.magic v in
    Obj.magic ((SSE_Addr_op addr), (SSE_XMM_Reg_op mr))), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_Addr_op addr ->
       (match y0 with
        | SSE_XMM_Reg_op mr -> Some (Obj.magic (mr, addr))
        | _ -> None)
     | _ -> None)))

(** val coq_MOVNTQ_b : bigrammar **)

let coq_MOVNTQ_b =
  map
    (bitsleft ('0'::('0'::('0'::('0'::[]))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[]))))
          (bitsleft ('0'::('1'::('1'::('1'::[])))) modrm_bv2_noreg))))
    ((fun v ->
    let (mr, addr) = Obj.magic v in
    Obj.magic ((SSE_Addr_op addr), (SSE_MM_Reg_op mr))), (fun u ->
    let (y, y0) = Obj.magic u in
    (match y with
     | SSE_Addr_op addr ->
       (match y0 with
        | SSE_MM_Reg_op mr -> Some (Obj.magic (mr, addr))
        | _ -> None)
     | _ -> None)))

(** val coq_PREFETCHT0_b : bigrammar **)

let coq_PREFETCHT0_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('0'::('1'::[])))))))

(** val coq_PREFETCHT1_b : bigrammar **)

let coq_PREFETCHT1_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('1'::('0'::[])))))))

(** val coq_PREFETCHT2_b : bigrammar **)

let coq_PREFETCHT2_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('1'::('1'::[])))))))

(** val coq_PREFETCHNTA_b : bigrammar **)

let coq_PREFETCHNTA_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('0'::('0'::('0'::('1'::[]))))
        (bitsleft ('1'::('0'::('0'::('0'::[]))))
          (ext_op_modrm_sse_noreg ('0'::('0'::('0'::[])))))))

(** val coq_SFENCE_b : bigrammar **)

let coq_SFENCE_b =
  bitsleft ('0'::('0'::('0'::('0'::[]))))
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsleft ('1'::('0'::('1'::('0'::[]))))
        (bitsleft ('1'::('1'::('1'::('0'::[]))))
          (bitsleft ('1'::('1'::('1'::('1'::[]))))
            (bitsmatch ('1'::('0'::('0'::('0'::[])))))))))
