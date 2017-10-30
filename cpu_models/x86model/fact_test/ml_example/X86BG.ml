open BiGrammar
open Datatypes
open GrammarType
open ParserArg
open X86BG_ins
open X86Syntax

(** val lock_b : bigrammar **)

let lock_b =
  map
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsmatch ('0'::('0'::('0'::('0'::[])))))) ((fun _ ->
    Obj.magic Coq_lock), (fun lr ->
    match Obj.magic lr with
    | Coq_lock -> Some (Obj.magic ())
    | _ -> None))

(** val rep_or_repn_b : bigrammar **)

let rep_or_repn_b =
  map
    (alt
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('1'::('0'::[]))))))
      (bitsleft ('1'::('1'::('1'::('1'::[]))))
        (bitsmatch ('0'::('0'::('1'::('1'::[]))))))) ((fun v ->
    match Obj.magic v with
    | Coq_inl _ -> Obj.magic Coq_repn
    | Coq_inr _ -> Obj.magic Coq_rep), (fun u ->
    match Obj.magic u with
    | Coq_lock -> None
    | Coq_rep -> Some (Obj.magic (Coq_inr ()))
    | Coq_repn -> Some (Obj.magic (Coq_inl ()))))

(** val rep_b : bigrammar **)

let rep_b =
  map
    (bitsleft ('1'::('1'::('1'::('1'::[]))))
      (bitsmatch ('0'::('0'::('1'::('1'::[])))))) ((fun _ ->
    Obj.magic Coq_rep), (fun u ->
    match Obj.magic u with
    | Coq_rep -> Some (Obj.magic ())
    | _ -> None))

(** val segment_override_b : bigrammar **)

let segment_override_b =
  let gt = BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero,
    (bitsleft ('0'::('0'::('1'::('0'::[]))))
      (bitsmatch ('1'::('1'::('1'::('0'::[])))))), (fun _ -> Obj.magic CS))),
    (BLeaf (Big.one,
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsmatch ('0'::('1'::('1'::('0'::[])))))), (fun _ ->
    Obj.magic SS))))), (BLeaf ((Big.double Big.one),
    (bitsleft ('0'::('0'::('1'::('1'::[]))))
      (bitsmatch ('1'::('1'::('1'::('0'::[])))))), (fun _ ->
    Obj.magic DS))))), (BNode ((Big.double (Big.double Big.one)), (BNode
    ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (bitsleft ('0'::('0'::('1'::('0'::[]))))
      (bitsmatch ('0'::('1'::('1'::('0'::[])))))), (fun _ -> Obj.magic ES))),
    (BLeaf ((Big.double (Big.double Big.one)),
    (bitsleft ('0'::('1'::('1'::('0'::[]))))
      (bitsmatch ('0'::('1'::('0'::('0'::[])))))), (fun _ ->
    Obj.magic FS))))), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    (bitsleft ('0'::('1'::('1'::('0'::[]))))
      (bitsmatch ('0'::('1'::('0'::('1'::[])))))), (fun _ ->
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
    | ES -> inv_case_some case3 (Obj.magic ())
    | CS -> inv_case_some case0 (Obj.magic ())
    | SS -> inv_case_some case1 (Obj.magic ())
    | DS -> inv_case_some case2 (Obj.magic ())
    | FS -> inv_case_some case4 (Obj.magic ())
    | GS -> inv_case_some case5 (Obj.magic ())))

(** val op_s : char list **)

let op_s =
  '0'::('1'::('1'::('0'::('0'::('1'::('1'::('0'::[])))))))

(** val op_override_b : bigrammar **)

let op_override_b =
  map (bitsleft op_s (Star (bitsmatch op_s))) ((fun _ -> Obj.magic true),
    (fun b -> if Obj.magic b then Some (Obj.magic []) else None))

(** val prefix_grammar_rep : bigrammar **)

let prefix_grammar_rep =
  map (option_perm3 rep_b segment_override_b op_override_b) ((fun v ->
    let (l, y) = Obj.magic v in
    let (s, op) = y in
    Obj.magic { lock_rep = l; seg_override = s; op_override =
      (match op with
       | Some b -> b
       | None -> false); addr_override = false }), (fun u ->
    if (Obj.magic u).op_override
    then if (Obj.magic u).addr_override
         then None
         else Some
                (Obj.magic ((Obj.magic u).lock_rep,
                  ((Obj.magic u).seg_override, (Some true))))
    else if (Obj.magic u).addr_override
         then None
         else Some
                (Obj.magic ((Obj.magic u).lock_rep,
                  ((Obj.magic u).seg_override, None)))))

(** val prefix_grammar_rep_or_repn : bigrammar **)

let prefix_grammar_rep_or_repn =
  map (option_perm3 rep_or_repn_b segment_override_b op_override_b)
    ((fun v ->
    let (l, y) = Obj.magic v in
    let (s, op) = y in
    Obj.magic { lock_rep = l; seg_override = s; op_override =
      (match op with
       | Some b -> b
       | None -> false); addr_override = false }), (fun u ->
    if (Obj.magic u).op_override
    then if (Obj.magic u).addr_override
         then None
         else Some
                (Obj.magic ((Obj.magic u).lock_rep,
                  ((Obj.magic u).seg_override, (Some true))))
    else if (Obj.magic u).addr_override
         then None
         else Some
                (Obj.magic ((Obj.magic u).lock_rep,
                  ((Obj.magic u).seg_override, None)))))

(** val prefix_grammar_lock_with_op_override : bigrammar **)

let prefix_grammar_lock_with_op_override =
  map (option_perm3_variation lock_b segment_override_b op_override_b)
    ((fun v ->
    let (l, y) = Obj.magic v in
    let (s, op) = y in
    Obj.magic { lock_rep = l; seg_override = s; op_override = op;
      addr_override = false }), (fun u ->
    if (Obj.magic u).addr_override
    then None
    else Some
           (Obj.magic ((Obj.magic u).lock_rep, ((Obj.magic u).seg_override,
             (Obj.magic u).op_override)))))

(** val prefix_grammar_lock_no_op_override : bigrammar **)

let prefix_grammar_lock_no_op_override =
  map (option_perm2 lock_b segment_override_b) ((fun v ->
    let (l, s) = Obj.magic v in
    Obj.magic { lock_rep = l; seg_override = s; op_override = false;
      addr_override = false }), (fun u ->
    if (Obj.magic u).op_override
    then None
    else if (Obj.magic u).addr_override
         then None
         else Some
                (Obj.magic ((Obj.magic u).lock_rep,
                  (Obj.magic u).seg_override))))

(** val prefix_grammar_seg_with_op_override : bigrammar **)

let prefix_grammar_seg_with_op_override =
  map (option_perm2_variation segment_override_b op_override_b) ((fun v ->
    let (s, op) = Obj.magic v in
    Obj.magic { lock_rep = None; seg_override = s; op_override = op;
      addr_override = false }), (fun u ->
    if (Obj.magic u).addr_override
    then None
    else (match (Obj.magic u).lock_rep with
          | Some _ -> None
          | None ->
            Some
              (Obj.magic ((Obj.magic u).seg_override,
                (Obj.magic u).op_override)))))

(** val prefix_grammar_seg_op_override : bigrammar **)

let prefix_grammar_seg_op_override =
  map (option_perm2 segment_override_b op_override_b) ((fun v ->
    let (s, op) = Obj.magic v in
    Obj.magic { lock_rep = None; seg_override = s; op_override =
      (match op with
       | Some b -> b
       | None -> false); addr_override = false }), (fun u ->
    if (Obj.magic u).op_override
    then if (Obj.magic u).addr_override
         then None
         else (match (Obj.magic u).lock_rep with
               | Some _ -> None
               | None ->
                 Some (Obj.magic ((Obj.magic u).seg_override, (Some true))))
    else if (Obj.magic u).addr_override
         then None
         else (match (Obj.magic u).lock_rep with
               | Some _ -> None
               | None -> Some (Obj.magic ((Obj.magic u).seg_override, None)))))

(** val prefix_grammar_only_seg_override : bigrammar **)

let prefix_grammar_only_seg_override =
  map (option_perm segment_override_b) ((fun s ->
    Obj.magic { lock_rep = None; seg_override = (Obj.magic s); op_override =
      false; addr_override = false }), (fun u ->
    if (Obj.magic u).op_override
    then None
    else if (Obj.magic u).addr_override
         then None
         else (match (Obj.magic u).lock_rep with
               | Some _ -> None
               | None -> Some (Obj.magic seg_override u))))

(** val i_instr1_b : bigrammar **)

let i_instr1_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.double (Big.double Big.one))),
    (BNode ((Big.double (Big.double Big.one)), (BNode ((Big.double Big.one),
    (BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero, coq_AAA_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_AAA))), (BLeaf (Big.one, coq_AAD_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_AAD))))), (BLeaf ((Big.double Big.one),
    coq_AAM_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_AAM))))), (BNode
    ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    coq_AAS_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_AAS))), (BLeaf
    ((Big.double (Big.double Big.one)), coq_CLC_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_CLC))))))), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BNode ((Big.doubleplusone (Big.double
    Big.one)), (BLeaf ((Big.doubleplusone (Big.double Big.one)), coq_CLD_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.I_CLD))), (BLeaf ((Big.double
    (Big.doubleplusone Big.one)), coq_CLI_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_CLI))))), (BNode ((Big.doubleplusone
    (Big.doubleplusone Big.one)), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone Big.one)), coq_CLTS_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_CLTS))), (BLeaf ((Big.double (Big.double
    (Big.double Big.one))), coq_CMC_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_CMC))))))))), (BNode ((Big.doubleplusone
    (Big.double (Big.doubleplusone Big.one))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), (BNode ((Big.double
    (Big.doubleplusone (Big.double Big.one))), (BNode ((Big.doubleplusone
    (Big.double (Big.double Big.one))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.double Big.one))), coq_CPUID_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_CPUID))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double Big.one))), coq_DAA_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_DAA))))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), coq_DAS_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_DAS))))), (BNode ((Big.double (Big.double
    (Big.doubleplusone Big.one))), (BLeaf ((Big.double (Big.double
    (Big.doubleplusone Big.one))), coq_HLT_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_HLT))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one))), coq_INT_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_INT))))))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone Big.one))), (BNode ((Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one))), coq_INTO_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_INTO))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone Big.one))), coq_INVD_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_INVD))))), (BNode ((Big.double (Big.double
    (Big.double (Big.double Big.one)))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.double Big.one)))), coq_IRET_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_IRET))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.double (Big.double Big.one)))), coq_LAHF_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_LAHF))))))))))), (BNode ((Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))), (BNode
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (BNode ((Big.double (Big.double (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double Big.one)))), (BNode ((Big.double
    (Big.doubleplusone (Big.double (Big.double Big.one)))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double (Big.double Big.one)))),
    coq_LEAVE_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_LEAVE))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_POPA_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_POPA))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_POPF_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_POPF))))),
    (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))), coq_PUSHA_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_PUSHA))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))),
    coq_PUSHF_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_PUSHF))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), coq_RDMSR_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_RDMSR))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.doubleplusone Big.one)))), coq_RDPMC_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_RDPMC))))), (BNode ((Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), coq_RDTSC_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_RDTSC))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_RDTSCP_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_RDTSCP))))))))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one)))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one)))), coq_RSM_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_RSM))), (BLeaf ((Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one)))), coq_SAHF_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_SAHF))))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))), coq_STC_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.I_STC))))), (BNode ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one)))), coq_STD_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_STD))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_STI_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_STI))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (BNode ((Big.double (Big.double (Big.double (Big.double
    (Big.double Big.one))))), (BLeaf ((Big.double (Big.double (Big.double
    (Big.double (Big.double Big.one))))), coq_UD2_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_UD2))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.double (Big.double (Big.double Big.one))))), coq_WBINVD_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_WBINVD))))), (BNode ((Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double Big.one))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))), coq_WRMSR_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.I_WRMSR))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double (Big.double Big.one))))),
    coq_XLAT_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_XLAT))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case2 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case4 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case7 = MLTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case8 = MLTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case10 = MLTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case11 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case12 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case13 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case14 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case15 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case16 = MLTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case17 = MLTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case18 = MRTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case19 = MRTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case20 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case21 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case22 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case23 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case24 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case25 = MRTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case26 = MRTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case27 = MRTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case28 = MRTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case29 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case30 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case31 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case32 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case33 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case34 = MRTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case35 = MRTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.I_AAA -> inv_case_some case0 (Obj.magic ())
    | X86_PARSER_ARG.I_AAD -> inv_case_some case1 (Obj.magic ())
    | X86_PARSER_ARG.I_AAM -> inv_case_some case2 (Obj.magic ())
    | X86_PARSER_ARG.I_AAS -> inv_case_some case3 (Obj.magic ())
    | X86_PARSER_ARG.I_CLC -> inv_case_some case4 (Obj.magic ())
    | X86_PARSER_ARG.I_CLD -> inv_case_some case5 (Obj.magic ())
    | X86_PARSER_ARG.I_CLI -> inv_case_some case6 (Obj.magic ())
    | X86_PARSER_ARG.I_CLTS -> inv_case_some case7 (Obj.magic ())
    | X86_PARSER_ARG.I_CMC -> inv_case_some case8 (Obj.magic ())
    | X86_PARSER_ARG.I_CPUID -> inv_case_some case9 (Obj.magic ())
    | X86_PARSER_ARG.I_DAA -> inv_case_some case10 (Obj.magic ())
    | X86_PARSER_ARG.I_DAS -> inv_case_some case11 (Obj.magic ())
    | X86_PARSER_ARG.I_HLT -> inv_case_some case12 (Obj.magic ())
    | X86_PARSER_ARG.I_INT -> inv_case_some case13 (Obj.magic ())
    | X86_PARSER_ARG.I_INTO -> inv_case_some case14 (Obj.magic ())
    | X86_PARSER_ARG.I_INVD -> inv_case_some case15 (Obj.magic ())
    | X86_PARSER_ARG.I_IRET -> inv_case_some case16 (Obj.magic ())
    | X86_PARSER_ARG.I_LAHF -> inv_case_some case17 (Obj.magic ())
    | X86_PARSER_ARG.I_LEAVE -> inv_case_some case18 (Obj.magic ())
    | X86_PARSER_ARG.I_POPA -> inv_case_some case19 (Obj.magic ())
    | X86_PARSER_ARG.I_POPF -> inv_case_some case20 (Obj.magic ())
    | X86_PARSER_ARG.I_PUSHA -> inv_case_some case21 (Obj.magic ())
    | X86_PARSER_ARG.I_PUSHF -> inv_case_some case22 (Obj.magic ())
    | X86_PARSER_ARG.I_RDMSR -> inv_case_some case23 (Obj.magic ())
    | X86_PARSER_ARG.I_RDPMC -> inv_case_some case24 (Obj.magic ())
    | X86_PARSER_ARG.I_RDTSC -> inv_case_some case25 (Obj.magic ())
    | X86_PARSER_ARG.I_RDTSCP -> inv_case_some case26 (Obj.magic ())
    | X86_PARSER_ARG.I_RSM -> inv_case_some case27 (Obj.magic ())
    | X86_PARSER_ARG.I_SAHF -> inv_case_some case28 (Obj.magic ())
    | X86_PARSER_ARG.I_STC -> inv_case_some case29 (Obj.magic ())
    | X86_PARSER_ARG.I_STD -> inv_case_some case30 (Obj.magic ())
    | X86_PARSER_ARG.I_STI -> inv_case_some case31 (Obj.magic ())
    | X86_PARSER_ARG.I_UD2 -> inv_case_some case32 (Obj.magic ())
    | X86_PARSER_ARG.I_WBINVD -> inv_case_some case33 (Obj.magic ())
    | X86_PARSER_ARG.I_WRMSR -> inv_case_some case34 (Obj.magic ())
    | X86_PARSER_ARG.I_XLAT -> inv_case_some case35 (Obj.magic ())))

(** val i_instr2_b : bigrammar **)

let i_instr2_b =
  let gt = BNode ((Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one))), (BNode ((Big.doubleplusone (Big.doubleplusone Big.one)),
    (BNode ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode (Big.zero,
    (BLeaf (Big.zero, coq_ARPL_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_ARPL (op1, op2))))), (BLeaf (Big.one,
    coq_BOUND_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_BOUND (op1, op2))))))), (BNode ((Big.double
    Big.one), (BLeaf ((Big.double Big.one), coq_BSF_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_BSF (op1, op2))))), (BLeaf
    ((Big.doubleplusone Big.one), coq_BSR_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_BSR (op1, op2))))))))), (BNode
    ((Big.doubleplusone (Big.double Big.one)), (BNode ((Big.double
    (Big.double Big.one)), (BLeaf ((Big.double (Big.double Big.one)),
    coq_BSWAP_b, (fun r ->
    Obj.magic (X86_PARSER_ARG.I_BSWAP (Obj.magic r))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)), coq_BT_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_BT (op1, op2))))))), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BLeaf ((Big.double (Big.doubleplusone
    Big.one)), coq_CALL_b, (fun v ->
    let (near, i) = Obj.magic v in
    let (abs, i0) = i in
    let (op1, sel) = i0 in
    Obj.magic (X86_PARSER_ARG.I_CALL (near, abs, op1, sel))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_IN_b, (fun v ->
    let (w, p) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_IN (w, p))))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    (BNode ((Big.doubleplusone (Big.double (Big.double Big.one))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))), coq_INTn_b, (fun it ->
    Obj.magic (X86_PARSER_ARG.I_INTn (Obj.magic it))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_INVLPG_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.I_INVLPG (Obj.magic op))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double Big.one))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))), coq_Jcc_b,
    (fun v ->
    let (ct, disp) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_Jcc (ct, disp))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    coq_JCXZ_b, (fun b ->
    Obj.magic (X86_PARSER_ARG.I_JCXZ (Obj.magic b))))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))), (BNode
    ((Big.double (Big.double (Big.doubleplusone Big.one))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone Big.one))), coq_JMP_b,
    (fun v ->
    let (near, i) = Obj.magic v in
    let (abs, i0) = i in
    let (op1, sel) = i0 in
    Obj.magic (X86_PARSER_ARG.I_JMP (near, abs, op1, sel))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))), coq_LAR_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LAR (op1, op2))))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one))), coq_LDS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LDS (op1, op2))))))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.double Big.one)))), (BNode ((Big.double (Big.double (Big.double
    (Big.double Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone Big.one))), coq_LEA_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LEA (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), coq_LES_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LES (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), coq_LFS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LFS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.double Big.one)))), coq_LGDT_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.I_LGDT (Obj.magic op))))))))),
    (BNode ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone
    (Big.double (Big.double Big.one)))), coq_LGS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LGS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone (Big.double Big.one)))), coq_LIDT_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.I_LIDT (Obj.magic op))))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_LLDT_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_LLDT (Obj.magic op))))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), (BNode ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), coq_LMSW_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_LMSW (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), coq_LOOP_b, (fun di ->
    Obj.magic (X86_PARSER_ARG.I_LOOP (Obj.magic di))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    (BLeaf ((Big.double (Big.double (Big.double (Big.doubleplusone
    Big.one)))), coq_LOOPZ_b, (fun di ->
    Obj.magic (X86_PARSER_ARG.I_LOOPZ (Obj.magic di))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), coq_LOOPNZ_b, (fun di ->
    Obj.magic (X86_PARSER_ARG.I_LOOPNZ (Obj.magic di))))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone Big.one)))), coq_LSL_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LSL (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_LSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_LSS (op1, op2))))))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))), coq_LTR_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.I_LTR (Obj.magic op))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case2 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case4 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case7 = MLTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case8 = MLTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case10 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case11 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case12 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case13 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case14 = MLTree (MRTree (MRTree (MRTree MLeaf))) in
  let case15 = MRTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case16 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case17 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case18 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case19 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case20 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case21 = MRTree (MLTree (MRTree (MRTree MLeaf))) in
  let case22 = MRTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case23 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case24 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case25 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case26 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case27 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case28 = MRTree (MRTree (MRTree (MRTree MLeaf))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.I_ARPL (op1, op2) ->
      inv_case_some case0 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_BOUND (op1, op2) ->
      inv_case_some case1 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_BSF (op1, op2) ->
      inv_case_some case2 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_BSR (op1, op2) ->
      inv_case_some case3 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_BSWAP r -> inv_case_some case4 (Obj.magic r)
    | X86_PARSER_ARG.I_BT (op1, op2) ->
      inv_case_some case5 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_CALL (near, abs, op1, sel) ->
      inv_case_some case6 (Obj.magic (near, (abs, (op1, sel))))
    | X86_PARSER_ARG.I_IN (w, p) -> inv_case_some case7 (Obj.magic (w, p))
    | X86_PARSER_ARG.I_INTn it -> inv_case_some case8 (Obj.magic it)
    | X86_PARSER_ARG.I_INVLPG op -> inv_case_some case9 (Obj.magic op)
    | X86_PARSER_ARG.I_Jcc (ct, disp) ->
      inv_case_some case10 (Obj.magic (ct, disp))
    | X86_PARSER_ARG.I_JCXZ b -> inv_case_some case11 (Obj.magic b)
    | X86_PARSER_ARG.I_JMP (near, abs, op1, sel) ->
      inv_case_some case12 (Obj.magic (near, (abs, (op1, sel))))
    | X86_PARSER_ARG.I_LAR (op1, op2) ->
      inv_case_some case13 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LDS (op1, op2) ->
      inv_case_some case14 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LEA (op1, op2) ->
      inv_case_some case15 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LES (op1, op2) ->
      inv_case_some case16 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LFS (op1, op2) ->
      inv_case_some case17 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LGDT op1 -> inv_case_some case18 (Obj.magic op1)
    | X86_PARSER_ARG.I_LGS (op1, op2) ->
      inv_case_some case19 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LIDT op1 -> inv_case_some case20 (Obj.magic op1)
    | X86_PARSER_ARG.I_LLDT op1 -> inv_case_some case21 (Obj.magic op1)
    | X86_PARSER_ARG.I_LMSW op1 -> inv_case_some case22 (Obj.magic op1)
    | X86_PARSER_ARG.I_LOOP disp -> inv_case_some case23 (Obj.magic disp)
    | X86_PARSER_ARG.I_LOOPZ disp -> inv_case_some case24 (Obj.magic disp)
    | X86_PARSER_ARG.I_LOOPNZ disp -> inv_case_some case25 (Obj.magic disp)
    | X86_PARSER_ARG.I_LSL (op1, op2) ->
      inv_case_some case26 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LSS (op1, op2) ->
      inv_case_some case27 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_LTR op1 -> inv_case_some case28 (Obj.magic op1)))

(** val i_instr3_b : bigrammar **)

let i_instr3_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.double Big.one))),
    (BNode ((Big.double (Big.double Big.one)), (BNode ((Big.double Big.one),
    (BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero, coq_MOVCR_b,
    (fun v ->
    let (d, i) = Obj.magic v in
    let (cr, r) = i in Obj.magic (X86_PARSER_ARG.I_MOVCR (d, cr, r))))),
    (BLeaf (Big.one, coq_MOVDR_b, (fun v ->
    let (d, i) = Obj.magic v in
    let (cr, r) = i in Obj.magic (X86_PARSER_ARG.I_MOVDR (d, cr, r))))))),
    (BLeaf ((Big.double Big.one), coq_MOVSR_b, (fun v ->
    let (d, i) = Obj.magic v in
    let (cr, r) = i in Obj.magic (X86_PARSER_ARG.I_MOVSR (d, cr, r))))))),
    (BNode ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    coq_MOVBE_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_MOVBE (op1, op2))))), (BLeaf ((Big.double
    (Big.double Big.one)), coq_OUT_b, (fun v ->
    let (w, p) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_OUT (w, p))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone Big.one)), (BNode
    ((Big.double (Big.doubleplusone Big.one)), (BNode ((Big.doubleplusone
    (Big.double Big.one)), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    coq_POP_b, (fun op -> Obj.magic (X86_PARSER_ARG.I_POP (Obj.magic op))))),
    (BLeaf ((Big.double (Big.doubleplusone Big.one)), coq_POPSR_b, (fun sr ->
    Obj.magic (X86_PARSER_ARG.I_POPSR (Obj.magic sr))))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_PUSH_b, (fun v ->
    let (w, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_PUSH (w, op1))))))),
    (BNode ((Big.double (Big.double (Big.double Big.one))), (BLeaf
    ((Big.double (Big.double (Big.double Big.one))), coq_PUSHSR_b, (fun sr ->
    Obj.magic (X86_PARSER_ARG.I_PUSHSR (Obj.magic sr))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_RCL_b,
    (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_RCL (w, op1, ri))))))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BNode ((Big.double (Big.double (Big.doubleplusone Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.double (Big.doubleplusone (Big.double Big.one))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))), coq_RCR_b,
    (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_RCR (w, op1, ri))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    coq_SETcc_b, (fun v ->
    let (ct, op1) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.I_SETcc (ct, op1))))))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone Big.one))), coq_SGDT_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_SGDT (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_SIDT_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_SIDT (Obj.magic op))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one))), coq_SLDT_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_SLDT (Obj.magic op))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.double Big.one)))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one))), coq_SMSW_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_SMSW (Obj.magic op))))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), coq_STR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_STR (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), coq_VERR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_VERR (Obj.magic op))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.double Big.one)))), coq_VERW_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.I_VERW (Obj.magic op))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case2 = MLTree (MLTree (MLTree (MRTree MLeaf))) in
  let case3 = MLTree (MLTree (MRTree (MLTree MLeaf))) in
  let case4 = MLTree (MLTree (MRTree (MRTree MLeaf))) in
  let case5 = MLTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case6 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case7 = MLTree (MRTree (MLTree (MRTree MLeaf))) in
  let case8 = MLTree (MRTree (MRTree (MLTree MLeaf))) in
  let case9 = MLTree (MRTree (MRTree (MRTree MLeaf))) in
  let case10 = MRTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case11 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case12 = MRTree (MLTree (MLTree (MRTree MLeaf))) in
  let case13 = MRTree (MLTree (MRTree (MLTree MLeaf))) in
  let case14 = MRTree (MLTree (MRTree (MRTree MLeaf))) in
  let case15 = MRTree (MRTree (MLTree (MLTree MLeaf))) in
  let case16 = MRTree (MRTree (MLTree (MRTree MLeaf))) in
  let case17 = MRTree (MRTree (MRTree (MLTree MLeaf))) in
  let case18 = MRTree (MRTree (MRTree (MRTree MLeaf))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.I_MOVCR (d, cr, r) ->
      inv_case_some case0 (Obj.magic (d, (cr, r)))
    | X86_PARSER_ARG.I_MOVDR (d, cr, r) ->
      inv_case_some case1 (Obj.magic (d, (cr, r)))
    | X86_PARSER_ARG.I_MOVSR (d, cr, r) ->
      inv_case_some case2 (Obj.magic (d, (cr, r)))
    | X86_PARSER_ARG.I_MOVBE (op1, op2) ->
      inv_case_some case3 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.I_OUT (w, p) -> inv_case_some case4 (Obj.magic (w, p))
    | X86_PARSER_ARG.I_POP op -> inv_case_some case5 (Obj.magic op)
    | X86_PARSER_ARG.I_POPSR sr -> inv_case_some case6 (Obj.magic sr)
    | X86_PARSER_ARG.I_PUSH (w, op1) ->
      inv_case_some case7 (Obj.magic (w, op1))
    | X86_PARSER_ARG.I_PUSHSR sr -> inv_case_some case8 (Obj.magic sr)
    | X86_PARSER_ARG.I_RCL (w, op1, ri) ->
      inv_case_some case9 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_RCR (w, op1, ri) ->
      inv_case_some case10 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_SETcc (ct, op1) ->
      inv_case_some case11 (Obj.magic (ct, op1))
    | X86_PARSER_ARG.I_SGDT op -> inv_case_some case12 (Obj.magic op)
    | X86_PARSER_ARG.I_SIDT op -> inv_case_some case13 (Obj.magic op)
    | X86_PARSER_ARG.I_SLDT op -> inv_case_some case14 (Obj.magic op)
    | X86_PARSER_ARG.I_SMSW op -> inv_case_some case15 (Obj.magic op)
    | X86_PARSER_ARG.I_STR op -> inv_case_some case16 (Obj.magic op)
    | X86_PARSER_ARG.I_VERR op -> inv_case_some case17 (Obj.magic op)
    | X86_PARSER_ARG.I_VERW op -> inv_case_some case18 (Obj.magic op)))

(** val i_instr4_b : bigrammar **)

let i_instr4_b =
  let gt = BNode ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode
    (Big.zero, (BLeaf (Big.zero, (seq prefix_grammar_rep coq_INS_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_INS
      (let (_, y) = Obj.magic v in y)))))), (BLeaf (Big.one,
    (seq prefix_grammar_rep coq_OUTS_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_OUTS
      (let (_, y) = Obj.magic v in y)))))))), (BNode ((Big.double Big.one),
    (BLeaf ((Big.double Big.one), (seq prefix_grammar_rep coq_MOVS_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_MOVS
      (let (_, y) = Obj.magic v in y)))))), (BLeaf ((Big.doubleplusone
    Big.one), (seq prefix_grammar_rep coq_LODS_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_LODS
      (let (_, y) = Obj.magic v in y)))))))))), (BNode ((Big.doubleplusone
    (Big.double Big.one)), (BNode ((Big.double (Big.double Big.one)), (BLeaf
    ((Big.double (Big.double Big.one)), (seq prefix_grammar_rep coq_STOS_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_STOS
      (let (_, y) = Obj.magic v in y)))))), (BLeaf ((Big.doubleplusone
    (Big.double Big.one)), (seq prefix_grammar_rep coq_RET_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_RET
      ((let (x, _) = let (_, y) = Obj.magic v in y in x),
      (let (_, y) = let (_, y) = Obj.magic v in y in y))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double Big.one))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))),
    (seq prefix_grammar_rep_or_repn coq_CMPS_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_CMPS
      (let (_, y) = Obj.magic v in y)))))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))),
    (seq prefix_grammar_rep_or_repn coq_SCAS_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x), (X86_PARSER_ARG.I_SCAS
      (let (_, y) = Obj.magic v in y)))))))))))
  in
  let case0 = MLTree (MLTree (MLTree MLeaf)) in
  let case1 = MLTree (MLTree (MRTree MLeaf)) in
  let case2 = MLTree (MRTree (MLTree MLeaf)) in
  let case3 = MLTree (MRTree (MRTree MLeaf)) in
  let case4 = MRTree (MLTree (MLTree MLeaf)) in
  let case5 = MRTree (MLTree (MRTree MLeaf)) in
  let case10 = MRTree (MRTree (MLTree MLeaf)) in
  let case11 = MRTree (MRTree (MRTree MLeaf)) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match snd (Obj.magic u) with
    | X86_PARSER_ARG.I_INS a1 ->
      inv_case_some case0 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_OUTS a1 ->
      inv_case_some case1 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_MOVS a1 ->
      inv_case_some case2 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_LODS a1 ->
      inv_case_some case3 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_STOS a1 ->
      inv_case_some case4 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_RET (a1, a2) ->
      inv_case_some case5 (Obj.magic ((fst (Obj.magic u)), (a1, a2)))
    | X86_PARSER_ARG.I_CMPS a1 ->
      inv_case_some case10 (Obj.magic ((fst (Obj.magic u)), a1))
    | X86_PARSER_ARG.I_SCAS a1 ->
      inv_case_some case11 (Obj.magic ((fst (Obj.magic u)), a1))))

(** val from_instr5' : (prefix * X86_PARSER_ARG.i_instr5) -> interp option **)

let from_instr5' u =
  match snd u with
  | X86_PARSER_ARG.I_ADC (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inl
             ((fst u), (a1, (a2, a3))))))))))
    else Some
           (Obj.magic (Coq_inl (Coq_inr (Coq_inl (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_ADD (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inr
             ((fst u), (a1, (a2, a3))))))))))
    else Some
           (Obj.magic (Coq_inl (Coq_inr (Coq_inl (Coq_inr (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_AND (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inl (Coq_inr (Coq_inl (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_BTC (a1, a2) ->
    Some
      (Obj.magic (Coq_inl (Coq_inr (Coq_inr (Coq_inl (Coq_inl ((fst u), (a1,
        a2))))))))
  | X86_PARSER_ARG.I_BTR (a1, a2) ->
    Some
      (Obj.magic (Coq_inl (Coq_inr (Coq_inr (Coq_inl (Coq_inr ((fst u), (a1,
        a2))))))))
  | X86_PARSER_ARG.I_BTS (a1, a2) ->
    Some
      (Obj.magic (Coq_inl (Coq_inr (Coq_inr (Coq_inr (Coq_inl ((fst u), (a1,
        a2))))))))
  | X86_PARSER_ARG.I_CMP (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inr
             ((fst u), (a1, (a2, a3))))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inr (Coq_inl (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_CMPXCHG (a1, a2, a3) ->
    Some
      (Obj.magic (Coq_inl (Coq_inr (Coq_inr (Coq_inr (Coq_inr ((fst u), (a1,
        (a2, a3)))))))))
  | X86_PARSER_ARG.I_DEC (a1, a2) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inl (Coq_inr (Coq_inl ((fst u),
             (a1, a2))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inl
             ((fst u), (a1, a2)))))))))
  | X86_PARSER_ARG.I_IMUL (a1, a2, a3, a4) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inl (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, (a3, a4))))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inr (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, (a3, a4))))))))))
  | X86_PARSER_ARG.I_INC (a1, a2) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inl (Coq_inr (Coq_inr ((fst u),
             (a1, a2))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inl (Coq_inr
             ((fst u), (a1, a2)))))))))
  | X86_PARSER_ARG.I_MOV (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inl (Coq_inr (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inr (Coq_inr (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_NEG (a1, a2) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inr (Coq_inl (Coq_inl (Coq_inl
             ((fst u), (a1, a2)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inr ((fst u),
             (a1, a2))))))))
  | X86_PARSER_ARG.I_NOT (a1, a2) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inr (Coq_inl (Coq_inl (Coq_inr
             ((fst u), (a1, a2)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inl (Coq_inr (Coq_inl ((fst u),
             (a1, a2))))))))
  | X86_PARSER_ARG.I_OR (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inr (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inl (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_SBB (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inr (Coq_inr (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inr (Coq_inl (Coq_inl ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_SUB (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inl (Coq_inr (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inr (Coq_inl (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_TEST (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inl (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inr (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_XADD (a1, a2, a3) ->
    Some
      (Obj.magic (Coq_inr (Coq_inl (Coq_inr (Coq_inr (Coq_inl ((fst u), (a1,
        (a2, a3)))))))))
  | X86_PARSER_ARG.I_XCHG (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inl
             ((fst u), (a1, (a2, a3))))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inl (Coq_inr (Coq_inr (Coq_inr ((fst u),
             (a1, (a2, a3)))))))))
  | X86_PARSER_ARG.I_XOR (a1, a2, a3) ->
    if (fst u).op_override
    then Some
           (Obj.magic (Coq_inl (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inr
             ((fst u), (a1, (a2, a3))))))))))
    else Some
           (Obj.magic (Coq_inr (Coq_inr (Coq_inl (Coq_inl (Coq_inl (Coq_inl
             ((fst u), (a1, (a2, a3))))))))))

(** val i_instr5_b : bigrammar **)

let i_instr5_b =
  let gt = BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one)))), (BNode ((Big.doubleplusone (Big.double
    (Big.double Big.one))), (BNode ((Big.double (Big.double Big.one)), (BNode
    ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, (seq prefix_grammar_lock_with_op_override (coq_ADC_b true)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_ADC (b, op1, op2)))))), (BLeaf
    (Big.one, (seq prefix_grammar_lock_with_op_override (coq_ADD_b true)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_ADD (b, op1, op2)))))))),
    (BLeaf ((Big.double Big.one),
    (seq prefix_grammar_lock_with_op_override (coq_AND_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_AND (b, op1, op2)))))))),
    (BNode ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    (seq prefix_grammar_lock_with_op_override coq_DEC_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_DEC (b, op)))))), (BLeaf ((Big.double (Big.double
    Big.one)), (seq prefix_grammar_lock_with_op_override coq_INC_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_INC (b, op)))))))))), (BNode ((Big.doubleplusone
    (Big.doubleplusone Big.one)), (BNode ((Big.double (Big.doubleplusone
    Big.one)), (BNode ((Big.doubleplusone (Big.double Big.one)), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)),
    (seq prefix_grammar_lock_with_op_override coq_NEG_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_NEG (b, op)))))), (BLeaf ((Big.double
    (Big.doubleplusone Big.one)),
    (seq prefix_grammar_lock_with_op_override coq_NOT_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_NOT (b, op)))))))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone Big.one)),
    (seq prefix_grammar_lock_with_op_override (coq_OR_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_OR (b, op1, op2)))))))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))),
    (seq prefix_grammar_lock_with_op_override (coq_SBB_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_SBB (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))),
    (seq prefix_grammar_lock_with_op_override (coq_SUB_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_SUB (b, op1, op2)))))))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (BNode ((Big.double (Big.double (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one))), (BNode ((Big.double (Big.doubleplusone
    (Big.double Big.one))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double Big.one))),
    (seq prefix_grammar_lock_with_op_override coq_XCHG_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_XCHG (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    (seq prefix_grammar_lock_with_op_override (coq_XOR_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_XOR (b, op1, op2)))))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (seq prefix_grammar_lock_no_op_override (coq_ADC_b false)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_ADC (b, op1, op2)))))))),
    (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))),
    (seq prefix_grammar_lock_no_op_override (coq_ADD_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_ADD (b, op1, op2)))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (seq prefix_grammar_lock_no_op_override (coq_AND_b false)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_AND (b, op1, op2)))))))))),
    (BNode ((Big.double (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_BTC_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (op1, op2) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_BTC (op1, op2)))))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_BTR_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (op1, op2) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_BTR (op1, op2)))))))), (BNode ((Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (seq prefix_grammar_lock_no_op_override coq_BTS_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (op1, op2) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_BTS (op1, op2)))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_CMPXCHG_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_CMPXCHG (b, op1, op2)))))))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone Big.one)))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (seq prefix_grammar_lock_no_op_override coq_DEC_b),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_DEC (b, op)))))), (BLeaf ((Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_INC_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_INC (b, op)))))))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_NEG_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_NEG (b, op)))))))), (BNode ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override coq_NOT_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, op) = let (_, y) = Obj.magic v in y in
       X86_PARSER_ARG.I_NOT (b, op)))))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (seq prefix_grammar_lock_no_op_override (coq_OR_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_OR (b, op1, op2)))))))))),
    (BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    (Big.double Big.one))))), (BNode ((Big.double (Big.double (Big.double
    (Big.double (Big.double Big.one))))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.double (Big.double Big.one))))),
    (seq prefix_grammar_lock_no_op_override (coq_SBB_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_SBB (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (seq prefix_grammar_lock_no_op_override (coq_SUB_b false)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_SUB (b, op1, op2)))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double Big.one))))),
    (seq prefix_grammar_lock_no_op_override coq_XADD_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_XADD (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))),
    (seq prefix_grammar_lock_no_op_override coq_XCHG_b), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_XCHG (b, op1, op2)))))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double Big.one))))), (BNode ((Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone (Big.double Big.one))))),
    (BNode ((Big.double (Big.double (Big.double (Big.doubleplusone
    (Big.double Big.one))))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double Big.one))))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    Big.one))))), (seq prefix_grammar_lock_no_op_override (coq_XOR_b false)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_XOR (b, op1, op2)))))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one))))), (seq prefix_grammar_seg_with_op_override (coq_CMP_b true)),
    (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_CMP (b, op1, op2)))))))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.double Big.one))))),
    (seq prefix_grammar_seg_with_op_override (coq_IMUL_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, i0) = i in
       let (opopt, iopt) = i0 in X86_PARSER_ARG.I_IMUL (b, op1, opopt, iopt)))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one))))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double Big.one))))),
    (seq prefix_grammar_seg_with_op_override (coq_MOV_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_MOV (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one))))),
    (seq prefix_grammar_seg_with_op_override (coq_TEST_b true)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_TEST (b, op1, op2)))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one))))), (BNode ((Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.doubleplusone Big.one))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one))))),
    (seq prefix_grammar_only_seg_override (coq_CMP_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_CMP (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one))))),
    (seq prefix_grammar_only_seg_override (coq_IMUL_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, i0) = i in
       let (opopt, iopt) = i0 in X86_PARSER_ARG.I_IMUL (b, op1, opopt, iopt)))))))),
    (BNode ((Big.double (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one))))), (BLeaf ((Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one))))),
    (seq prefix_grammar_only_seg_override (coq_MOV_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_MOV (b, op1, op2)))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one))))),
    (seq prefix_grammar_only_seg_override (coq_TEST_b false)), (fun v ->
    Obj.magic ((let (x, _) = Obj.magic v in x),
      (let (b, i) = let (_, y) = Obj.magic v in y in
       let (op1, op2) = i in X86_PARSER_ARG.I_TEST (b, op1, op2)))))))))))))))
  in
  map (comb_bigrammar gt) ((comb_map gt), (Obj.magic from_instr5'))

(** val i_instr6_b : bigrammar **)

let i_instr6_b =
  let gt = BNode ((Big.doubleplusone (Big.doubleplusone Big.one)), (BNode
    ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, coq_CDQ_b, (fun _ -> Obj.magic X86_PARSER_ARG.I_CDQ))), (BLeaf
    (Big.one, coq_CMOVcc_b, (fun v ->
    let (ct, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.I_CMOVcc (ct, op1, op2))))))),
    (BNode ((Big.double Big.one), (BLeaf ((Big.double Big.one), coq_CWDE_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.I_CWDE))), (BLeaf ((Big.doubleplusone
    Big.one), coq_DIV_b, (fun v ->
    let (w, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_DIV (w, op1))))))))),
    (BNode ((Big.doubleplusone (Big.double Big.one)), (BNode ((Big.double
    (Big.double Big.one)), (BLeaf ((Big.double (Big.double Big.one)),
    coq_IDIV_b, (fun v ->
    let (w, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_IDIV (w, op1))))),
    (BLeaf ((Big.doubleplusone (Big.double Big.one)), coq_MOVSX_b, (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.I_MOVSX (w, op1, op2))))))),
    (BNode ((Big.double (Big.doubleplusone Big.one)), (BLeaf ((Big.double
    (Big.doubleplusone Big.one)), coq_MOVZX_b, (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.I_MOVZX (w, op1, op2))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_MUL_b,
    (fun v ->
    let (w, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.I_MUL (w, op1))))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    (BNode ((Big.doubleplusone (Big.double (Big.double Big.one))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))), coq_NOP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.I_NOP (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_ROL_b,
    (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_ROL (w, op1, ri))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double Big.one))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))), coq_ROR_b,
    (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_ROR (w, op1, ri))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    coq_SAR_b, (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_SAR (w, op1, ri))))))))),
    (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    (BNode ((Big.double (Big.double (Big.doubleplusone Big.one))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone Big.one))), coq_SHL_b,
    (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_SHL (w, op1, ri))))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_SHLD_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (r, ri) = i in Obj.magic (X86_PARSER_ARG.I_SHLD (op1, r, ri))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_SHR_b, (fun v ->
    let (w, i) = Obj.magic v in
    let (op1, ri) = i in Obj.magic (X86_PARSER_ARG.I_SHR (w, op1, ri))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one))), coq_SHRD_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (r, ri) = i in Obj.magic (X86_PARSER_ARG.I_SHRD (op1, r, ri))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree MLeaf))) in
  let case1 = MLTree (MLTree (MLTree (MRTree MLeaf))) in
  let case2 = MLTree (MLTree (MRTree (MLTree MLeaf))) in
  let case3 = MLTree (MLTree (MRTree (MRTree MLeaf))) in
  let case4 = MLTree (MRTree (MLTree (MLTree MLeaf))) in
  let case5 = MLTree (MRTree (MLTree (MRTree MLeaf))) in
  let case6 = MLTree (MRTree (MRTree (MLTree MLeaf))) in
  let case7 = MLTree (MRTree (MRTree (MRTree MLeaf))) in
  let case8 = MRTree (MLTree (MLTree (MLTree MLeaf))) in
  let case9 = MRTree (MLTree (MLTree (MRTree MLeaf))) in
  let case10 = MRTree (MLTree (MRTree (MLTree MLeaf))) in
  let case11 = MRTree (MLTree (MRTree (MRTree MLeaf))) in
  let case12 = MRTree (MRTree (MLTree (MLTree MLeaf))) in
  let case13 = MRTree (MRTree (MLTree (MRTree MLeaf))) in
  let case14 = MRTree (MRTree (MRTree (MLTree MLeaf))) in
  let case15 = MRTree (MRTree (MRTree (MRTree MLeaf))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.I_CDQ -> inv_case_some case0 (Obj.magic ())
    | X86_PARSER_ARG.I_CMOVcc (ct, op1, op2) ->
      inv_case_some case1 (Obj.magic (ct, (op1, op2)))
    | X86_PARSER_ARG.I_CWDE -> inv_case_some case2 (Obj.magic ())
    | X86_PARSER_ARG.I_DIV (w, op1) ->
      inv_case_some case3 (Obj.magic (w, op1))
    | X86_PARSER_ARG.I_IDIV (w, op1) ->
      inv_case_some case4 (Obj.magic (w, op1))
    | X86_PARSER_ARG.I_MOVSX (w, op1, op2) ->
      inv_case_some case5 (Obj.magic (w, (op1, op2)))
    | X86_PARSER_ARG.I_MOVZX (w, op1, op2) ->
      inv_case_some case6 (Obj.magic (w, (op1, op2)))
    | X86_PARSER_ARG.I_MUL (w, op1) ->
      inv_case_some case7 (Obj.magic (w, op1))
    | X86_PARSER_ARG.I_NOP op -> inv_case_some case8 (Obj.magic op)
    | X86_PARSER_ARG.I_ROL (w, op1, ri) ->
      inv_case_some case9 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_ROR (w, op1, ri) ->
      inv_case_some case10 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_SAR (w, op1, ri) ->
      inv_case_some case11 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_SHL (w, op1, ri) ->
      inv_case_some case12 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_SHLD (op1, r, ri) ->
      inv_case_some case13 (Obj.magic (op1, (r, ri)))
    | X86_PARSER_ARG.I_SHR (w, op1, ri) ->
      inv_case_some case14 (Obj.magic (w, (op1, ri)))
    | X86_PARSER_ARG.I_SHRD (op1, r, ri) ->
      inv_case_some case15 (Obj.magic (op1, (r, ri)))))

(** val f_instr1_b : bigrammar **)

let f_instr1_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.double (Big.doubleplusone
    (Big.double Big.one))), (BNode ((Big.doubleplusone (Big.double Big.one)),
    (BNode ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, coq_F2XM1_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_F2XM1))),
    (BLeaf (Big.one, coq_FABS_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FABS))))), (BLeaf ((Big.double Big.one),
    coq_FADD_b, (fun v ->
    let (z, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FADD (z, op1))))))),
    (BNode ((Big.double (Big.double Big.one)), (BNode ((Big.doubleplusone
    Big.one), (BLeaf ((Big.doubleplusone Big.one), coq_FADDP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FADDP (Obj.magic op))))), (BLeaf ((Big.double
    (Big.double Big.one)), coq_FBLD_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FBLD (Obj.magic op))))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)), coq_FBSTP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FBSTP (Obj.magic op))))))))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BLeaf ((Big.double (Big.doubleplusone
    Big.one)), coq_FCHS_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FCHS))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_FCMOVcc_b,
    (fun v ->
    let (ct, op1) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.F_FCMOVcc (ct, op1))))))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))), coq_FCOM_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FCOM (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_FCOMP_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.F_FCOMP (Obj.magic op))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double Big.one))), coq_FCOMPP_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FCOMPP))))))))), (BNode ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))), (BNode
    ((Big.double (Big.double (Big.doubleplusone Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    coq_FCOMIP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FCOMIP (Obj.magic op))))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone Big.one))), coq_FCOS_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FCOS))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_FDECSTP_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FDECSTP))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_FDIV_b, (fun v ->
    let (z, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FDIV (z, op1))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one))), coq_FDIVP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FDIVP (Obj.magic op))))))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.double Big.one)))),
    coq_FDIVR_b, (fun v ->
    let (z, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FDIVR (z, op1))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.double Big.one)))), (BNode ((Big.doubleplusone (Big.double
    (Big.double (Big.double Big.one)))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.double (Big.double Big.one)))), coq_FDIVRP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FDIVRP (Obj.magic op))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double (Big.double Big.one)))),
    coq_FFREE_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FFREE (Obj.magic op))))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_FIADD_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FIADD (Obj.magic op))))))), (BNode
    ((Big.double (Big.double (Big.doubleplusone (Big.double Big.one)))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_FICOM_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FICOM (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_FICOMP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FICOMP (Obj.magic op))))))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one)))), (BNode ((Big.double (Big.double
    (Big.double (Big.doubleplusone Big.one)))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))), (BNode
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), coq_FIDIV_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FIDIV (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), coq_FIDIVR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FIDIVR (Obj.magic op))))))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    coq_FILD_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FILD (Obj.magic op))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone Big.one)))), coq_FIMUL_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FIMUL (Obj.magic op))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))),
    coq_FINCSTP_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FINCSTP))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_FIST_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FIST (Obj.magic op))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.doubleplusone Big.one)))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_FISTP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FISTP (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), coq_FISUB_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FISUB (Obj.magic op))))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one)))), coq_FISUBR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FISUBR (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_FLD_b, (fun op -> Obj.magic (X86_PARSER_ARG.F_FLD (Obj.magic op))))),
    (BLeaf ((Big.double (Big.double (Big.double (Big.double (Big.double
    Big.one))))), coq_FLD1_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FLD1))))))))), (BNode ((Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double Big.one))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))), (BNode ((Big.double (Big.doubleplusone
    (Big.double (Big.double (Big.double Big.one))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (BLeaf ((Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double Big.one))))), coq_FLDCW_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FLDCW (Obj.magic op))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double Big.one))))),
    coq_FLDENV_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FLDENV (Obj.magic op))))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    (Big.double Big.one))))), coq_FLDL2E_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FLDL2E))))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.double (Big.double Big.one))))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone (Big.double (Big.double
    Big.one))))), coq_FLDL2T_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FLDL2T))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double (Big.double Big.one))))),
    coq_FLDLG2_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FLDLG2))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one))))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double Big.one))))), (BNode
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double Big.one))))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double Big.one))))), coq_FLDLN2_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FLDLN2))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.double Big.one))))), coq_FLDPI_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FLDPI))))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.doubleplusone (Big.double Big.one))))), coq_FLDZ_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FLDZ))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    (Big.double Big.one))))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone (Big.double Big.one))))), coq_FMUL_b,
    (fun v ->
    let (z, op1) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FMUL (z, op1))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one))))), coq_FMULP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FMULP (Obj.magic op))))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case2 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MLTree (MLTree MLeaf))))) in
  let case4 = MLTree (MLTree (MLTree (MRTree (MLTree (MRTree MLeaf))))) in
  let case5 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case7 = MLTree (MLTree (MRTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case8 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case9 = MLTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case10 = MLTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case11 = MLTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case12 = MLTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case13 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case14 = MLTree (MRTree (MLTree (MRTree (MLTree (MLTree MLeaf))))) in
  let case15 = MLTree (MRTree (MLTree (MRTree (MLTree (MRTree MLeaf))))) in
  let case16 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case17 = MLTree (MRTree (MRTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case18 = MLTree (MRTree (MRTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case19 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case20 = MLTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case21 = MLTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case22 = MRTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case23 = MRTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case24 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case25 = MRTree (MLTree (MLTree (MRTree (MLTree (MLTree MLeaf))))) in
  let case26 = MRTree (MLTree (MLTree (MRTree (MLTree (MRTree MLeaf))))) in
  let case27 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case28 = MRTree (MLTree (MRTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case29 = MRTree (MLTree (MRTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case30 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case31 = MRTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case32 = MRTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case33 = MRTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case34 = MRTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case35 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case36 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case37 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case38 = MRTree (MRTree (MRTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case39 = MRTree (MRTree (MRTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case40 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case41 = MRTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case42 = MRTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.F_F2XM1 -> inv_case_some case0 (Obj.magic ())
    | X86_PARSER_ARG.F_FABS -> inv_case_some case1 (Obj.magic ())
    | X86_PARSER_ARG.F_FADD (z, op1) ->
      inv_case_some case2 (Obj.magic (z, op1))
    | X86_PARSER_ARG.F_FADDP op -> inv_case_some case3 (Obj.magic op)
    | X86_PARSER_ARG.F_FBLD op -> inv_case_some case4 (Obj.magic op)
    | X86_PARSER_ARG.F_FBSTP op -> inv_case_some case5 (Obj.magic op)
    | X86_PARSER_ARG.F_FCHS -> inv_case_some case6 (Obj.magic ())
    | X86_PARSER_ARG.F_FCMOVcc (ct, op) ->
      inv_case_some case7 (Obj.magic (ct, op))
    | X86_PARSER_ARG.F_FCOM op -> inv_case_some case8 (Obj.magic op)
    | X86_PARSER_ARG.F_FCOMP op -> inv_case_some case9 (Obj.magic op)
    | X86_PARSER_ARG.F_FCOMPP -> inv_case_some case10 (Obj.magic ())
    | X86_PARSER_ARG.F_FCOMIP op -> inv_case_some case11 (Obj.magic op)
    | X86_PARSER_ARG.F_FCOS -> inv_case_some case12 (Obj.magic ())
    | X86_PARSER_ARG.F_FDECSTP -> inv_case_some case13 (Obj.magic ())
    | X86_PARSER_ARG.F_FDIV (z, op) ->
      inv_case_some case14 (Obj.magic (z, op))
    | X86_PARSER_ARG.F_FDIVP op -> inv_case_some case15 (Obj.magic op)
    | X86_PARSER_ARG.F_FDIVR (z, op) ->
      inv_case_some case16 (Obj.magic (z, op))
    | X86_PARSER_ARG.F_FDIVRP op -> inv_case_some case17 (Obj.magic op)
    | X86_PARSER_ARG.F_FFREE op -> inv_case_some case18 (Obj.magic op)
    | X86_PARSER_ARG.F_FIADD op -> inv_case_some case19 (Obj.magic op)
    | X86_PARSER_ARG.F_FICOM op -> inv_case_some case20 (Obj.magic op)
    | X86_PARSER_ARG.F_FICOMP op -> inv_case_some case21 (Obj.magic op)
    | X86_PARSER_ARG.F_FIDIV op -> inv_case_some case22 (Obj.magic op)
    | X86_PARSER_ARG.F_FIDIVR op -> inv_case_some case23 (Obj.magic op)
    | X86_PARSER_ARG.F_FILD op -> inv_case_some case24 (Obj.magic op)
    | X86_PARSER_ARG.F_FIMUL op -> inv_case_some case25 (Obj.magic op)
    | X86_PARSER_ARG.F_FINCSTP -> inv_case_some case26 (Obj.magic ())
    | X86_PARSER_ARG.F_FIST op -> inv_case_some case27 (Obj.magic op)
    | X86_PARSER_ARG.F_FISTP op -> inv_case_some case28 (Obj.magic op)
    | X86_PARSER_ARG.F_FISUB op -> inv_case_some case29 (Obj.magic op)
    | X86_PARSER_ARG.F_FISUBR op -> inv_case_some case30 (Obj.magic op)
    | X86_PARSER_ARG.F_FLD op -> inv_case_some case31 (Obj.magic op)
    | X86_PARSER_ARG.F_FLD1 -> inv_case_some case32 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDCW op -> inv_case_some case33 (Obj.magic op)
    | X86_PARSER_ARG.F_FLDENV op -> inv_case_some case34 (Obj.magic op)
    | X86_PARSER_ARG.F_FLDL2E -> inv_case_some case35 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDL2T -> inv_case_some case36 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDLG2 -> inv_case_some case37 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDLN2 -> inv_case_some case38 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDPI -> inv_case_some case39 (Obj.magic ())
    | X86_PARSER_ARG.F_FLDZ -> inv_case_some case40 (Obj.magic ())
    | X86_PARSER_ARG.F_FMUL (z, op) ->
      inv_case_some case41 (Obj.magic (z, op))
    | X86_PARSER_ARG.F_FMULP op -> inv_case_some case42 (Obj.magic op)))

(** val f_instr2_b : bigrammar **)

let f_instr2_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.double (Big.double Big.one))),
    (BNode ((Big.double (Big.double Big.one)), (BNode ((Big.double Big.one),
    (BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero, coq_FNCLEX_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FNCLEX))), (BLeaf (Big.one,
    coq_FNINIT_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FNINIT))))), (BLeaf
    ((Big.double Big.one), coq_FNOP_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FNOP))))), (BNode ((Big.doubleplusone
    Big.one), (BLeaf ((Big.doubleplusone Big.one), coq_FNSAVE_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FNSAVE (Obj.magic op))))), (BLeaf
    ((Big.double (Big.double Big.one)), coq_FNSTCW_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FNSTCW (Obj.magic op))))))))), (BNode
    ((Big.double (Big.doubleplusone Big.one)), (BNode ((Big.doubleplusone
    (Big.double Big.one)), (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    coq_FNSTSW_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FNSTSW (Obj.magic op))))), (BLeaf
    ((Big.double (Big.doubleplusone Big.one)), coq_FPATAN_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FPATAN))))), (BNode ((Big.doubleplusone
    (Big.doubleplusone Big.one)), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone Big.one)), coq_FPREM_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FPREM))), (BLeaf ((Big.double (Big.double
    (Big.double Big.one))), coq_FPREM1_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FPREM1))))))))), (BNode ((Big.doubleplusone
    (Big.double (Big.doubleplusone Big.one))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), (BNode ((Big.double
    (Big.doubleplusone (Big.double Big.one))), (BNode ((Big.doubleplusone
    (Big.double (Big.double Big.one))), (BLeaf ((Big.doubleplusone
    (Big.double (Big.double Big.one))), coq_FPTAN_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FPTAN))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double Big.one))), coq_FRNDINT_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FRNDINT))))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), coq_FRSTOR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FRSTOR (Obj.magic op))))))), (BNode
    ((Big.double (Big.double (Big.doubleplusone Big.one))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone Big.one))), coq_FSCALE_b,
    (fun _ -> Obj.magic X86_PARSER_ARG.F_FSCALE))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_FSIN_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FSIN))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_FSINCOS_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FSINCOS))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_FSQRT_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FSQRT))))), (BNode
    ((Big.double (Big.double (Big.double (Big.double Big.one)))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.double Big.one)))), coq_FST_b,
    (fun op -> Obj.magic (X86_PARSER_ARG.F_FST (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    coq_FSTENV_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FSTENV (Obj.magic op))))))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.double Big.one)))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double Big.one)))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.double Big.one)))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_FSTP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FSTP (Obj.magic op))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_FSUB_b, (fun v ->
    let (z, op) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FSUB (z, op))))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_FSUBP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FSUBP (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))), coq_FSUBR_b, (fun v ->
    let (z, op) = Obj.magic v in Obj.magic (X86_PARSER_ARG.F_FSUBR (z, op))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), coq_FSUBRP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FSUBRP (Obj.magic op))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), coq_FTST_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FTST))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.doubleplusone Big.one)))), coq_FUCOM_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FUCOM (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one)))), coq_FUCOMP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FUCOMP (Obj.magic op))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_FUCOMPP_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FUCOMPP))))))))), (BNode ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    (BNode ((Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone (Big.double
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))),
    coq_FUCOMI_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FUCOMI (Obj.magic op))))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), coq_FUCOMIP_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FUCOMIP (Obj.magic op))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), coq_FXAM_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FXAM))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_FXCH_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.F_FXCH (Obj.magic op))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one)))), coq_FXTRACT_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FXTRACT))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.double (Big.double Big.one))))), coq_FYL2X_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FYL2X))))), (BNode ((Big.doubleplusone
    (Big.double (Big.double (Big.double (Big.double Big.one))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    Big.one))))), coq_FYL2XP1_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.F_FYL2XP1))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double Big.one))))),
    coq_FWAIT_b, (fun _ -> Obj.magic X86_PARSER_ARG.F_FWAIT))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case2 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case4 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case7 = MLTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case8 = MLTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case10 = MLTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case11 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case12 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case13 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case14 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case15 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case16 = MLTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case17 = MLTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case18 = MRTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case19 = MRTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case20 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case21 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case22 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case23 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case24 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case25 = MRTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case26 = MRTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case27 = MRTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case28 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case29 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case30 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case31 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case32 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case33 = MRTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case34 = MRTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.F_FNCLEX -> inv_case_some case0 (Obj.magic ())
    | X86_PARSER_ARG.F_FNINIT -> inv_case_some case1 (Obj.magic ())
    | X86_PARSER_ARG.F_FNOP -> inv_case_some case2 (Obj.magic ())
    | X86_PARSER_ARG.F_FNSAVE op -> inv_case_some case3 (Obj.magic op)
    | X86_PARSER_ARG.F_FNSTCW op -> inv_case_some case4 (Obj.magic op)
    | X86_PARSER_ARG.F_FNSTSW op -> inv_case_some case5 (Obj.magic op)
    | X86_PARSER_ARG.F_FPATAN -> inv_case_some case6 (Obj.magic ())
    | X86_PARSER_ARG.F_FPREM -> inv_case_some case7 (Obj.magic ())
    | X86_PARSER_ARG.F_FPREM1 -> inv_case_some case8 (Obj.magic ())
    | X86_PARSER_ARG.F_FPTAN -> inv_case_some case9 (Obj.magic ())
    | X86_PARSER_ARG.F_FRNDINT -> inv_case_some case10 (Obj.magic ())
    | X86_PARSER_ARG.F_FRSTOR op -> inv_case_some case11 (Obj.magic op)
    | X86_PARSER_ARG.F_FSCALE -> inv_case_some case12 (Obj.magic ())
    | X86_PARSER_ARG.F_FSIN -> inv_case_some case13 (Obj.magic ())
    | X86_PARSER_ARG.F_FSINCOS -> inv_case_some case14 (Obj.magic ())
    | X86_PARSER_ARG.F_FSQRT -> inv_case_some case15 (Obj.magic ())
    | X86_PARSER_ARG.F_FST op -> inv_case_some case16 (Obj.magic op)
    | X86_PARSER_ARG.F_FSTENV op -> inv_case_some case17 (Obj.magic op)
    | X86_PARSER_ARG.F_FSTP op -> inv_case_some case18 (Obj.magic op)
    | X86_PARSER_ARG.F_FSUB (z, op) ->
      inv_case_some case19 (Obj.magic (z, op))
    | X86_PARSER_ARG.F_FSUBP op -> inv_case_some case20 (Obj.magic op)
    | X86_PARSER_ARG.F_FSUBR (z, op) ->
      inv_case_some case21 (Obj.magic (z, op))
    | X86_PARSER_ARG.F_FSUBRP op -> inv_case_some case22 (Obj.magic op)
    | X86_PARSER_ARG.F_FTST -> inv_case_some case23 (Obj.magic ())
    | X86_PARSER_ARG.F_FUCOM op -> inv_case_some case24 (Obj.magic op)
    | X86_PARSER_ARG.F_FUCOMP op -> inv_case_some case25 (Obj.magic op)
    | X86_PARSER_ARG.F_FUCOMPP -> inv_case_some case26 (Obj.magic ())
    | X86_PARSER_ARG.F_FUCOMI op -> inv_case_some case27 (Obj.magic op)
    | X86_PARSER_ARG.F_FUCOMIP op -> inv_case_some case28 (Obj.magic op)
    | X86_PARSER_ARG.F_FXAM -> inv_case_some case29 (Obj.magic ())
    | X86_PARSER_ARG.F_FXCH op -> inv_case_some case30 (Obj.magic op)
    | X86_PARSER_ARG.F_FXTRACT -> inv_case_some case31 (Obj.magic ())
    | X86_PARSER_ARG.F_FYL2X -> inv_case_some case32 (Obj.magic ())
    | X86_PARSER_ARG.F_FYL2XP1 -> inv_case_some case33 (Obj.magic ())
    | X86_PARSER_ARG.F_FWAIT -> inv_case_some case34 (Obj.magic ())))

(** val m_instr_b : bigrammar **)

let m_instr_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one))), (BNode ((Big.double (Big.doubleplusone Big.one)), (BNode
    ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, coq_EMMS_b, (fun _ -> Obj.magic X86_PARSER_ARG.M_EMMS))),
    (BLeaf (Big.one, coq_MOVD_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_MOVD (op1, op2))))))), (BNode ((Big.double
    Big.one), (BLeaf ((Big.double Big.one), coq_MOVQ_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_MOVQ (op1, op2))))), (BLeaf
    ((Big.doubleplusone Big.one), coq_PACKSSDW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PACKSSDW (op1, op2))))))))), (BNode
    ((Big.doubleplusone (Big.double Big.one)), (BNode ((Big.double
    (Big.double Big.one)), (BLeaf ((Big.double (Big.double Big.one)),
    coq_PACKSSWB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PACKSSWB (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)), coq_PACKUSWB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PACKUSWB (op1, op2))))))), (BLeaf
    ((Big.double (Big.doubleplusone Big.one)), coq_PADD_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PADD (gg, op1, op2))))))))),
    (BNode ((Big.double (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_PADDS_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PADDS (gg, op1, op2))))),
    (BLeaf ((Big.double (Big.double (Big.double Big.one))), coq_PADDUS_b,
    (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PADDUS (gg, op1, op2))))))),
    (BNode ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_PAND_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PAND (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double Big.one))), coq_PANDN_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PANDN (op1, op2))))))))), (BNode ((Big.double
    (Big.double (Big.doubleplusone Big.one))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), coq_PCMPEQ_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PCMPEQ (gg, op1, op2))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone Big.one))),
    coq_PCMPGT_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PCMPGT (gg, op1, op2))))))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_PMADDWD_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PMADDWD (op1, op2))))))))))), (BNode
    ((Big.double (Big.double (Big.doubleplusone (Big.double Big.one)))),
    (BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one))), (BNode ((Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one))), coq_PMULHUW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PMULHUW (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_PMULHW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PMULHW (op1, op2))))))), (BNode ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), coq_PMULLW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PMULLW (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    coq_POR_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_POR (op1, op2))))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.double Big.one)))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double (Big.double Big.one)))), coq_PSLL_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSLL (gg, op1, op2))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_PSRA_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSRA (gg, op1, op2))))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_PSRL_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSRL (gg, op1, op2))))))))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.double (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), (BNode ((Big.doubleplusone
    (Big.double (Big.doubleplusone (Big.double Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_PSUB_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSUB (gg, op1, op2))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), coq_PSUBS_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSUBS (gg, op1, op2))))))),
    (BLeaf ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), coq_PSUBUS_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PSUBUS (gg, op1, op2))))))),
    (BNode ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.double (Big.double
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.double (Big.double
    (Big.double (Big.doubleplusone Big.one)))), coq_PUNPCKH_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PUNPCKH (gg, op1, op2))))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), coq_PUNPCKL_b, (fun v ->
    let (gg, i) = Obj.magic v in
    let (op1, op2) = i in Obj.magic (X86_PARSER_ARG.M_PUNPCKL (gg, op1, op2))))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_PXOR_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.M_PXOR (op1, op2))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case2 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case4 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MRTree MLeaf))) in
  let case7 = MLTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case8 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case10 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case11 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case12 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case13 = MLTree (MRTree (MRTree (MRTree MLeaf))) in
  let case14 = MRTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case15 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case16 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case17 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case18 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case19 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case20 = MRTree (MLTree (MRTree (MRTree MLeaf))) in
  let case21 = MRTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case22 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case23 = MRTree (MRTree (MLTree (MRTree MLeaf))) in
  let case24 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case25 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case26 = MRTree (MRTree (MRTree (MRTree MLeaf))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.M_EMMS -> inv_case_some case0 (Obj.magic ())
    | X86_PARSER_ARG.M_MOVD (op1, op2) ->
      inv_case_some case1 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_MOVQ (op1, op2) ->
      inv_case_some case2 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PACKSSDW (op1, op2) ->
      inv_case_some case3 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PACKSSWB (op1, op2) ->
      inv_case_some case4 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PACKUSWB (op1, op2) ->
      inv_case_some case5 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PADD (gg, op1, op2) ->
      inv_case_some case6 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PADDS (gg, op1, op2) ->
      inv_case_some case7 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PADDUS (gg, op1, op2) ->
      inv_case_some case8 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PAND (op1, op2) ->
      inv_case_some case9 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PANDN (op1, op2) ->
      inv_case_some case10 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PCMPEQ (gg, op1, op2) ->
      inv_case_some case11 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PCMPGT (gg, op1, op2) ->
      inv_case_some case12 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PMADDWD (op1, op2) ->
      inv_case_some case13 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PMULHUW (op1, op2) ->
      inv_case_some case14 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PMULHW (op1, op2) ->
      inv_case_some case15 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PMULLW (op1, op2) ->
      inv_case_some case16 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_POR (op1, op2) ->
      inv_case_some case17 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.M_PSLL (gg, op1, op2) ->
      inv_case_some case18 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PSRA (gg, op1, op2) ->
      inv_case_some case19 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PSRL (gg, op1, op2) ->
      inv_case_some case20 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PSUB (gg, op1, op2) ->
      inv_case_some case21 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PSUBS (gg, op1, op2) ->
      inv_case_some case22 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PSUBUS (gg, op1, op2) ->
      inv_case_some case23 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PUNPCKH (gg, op1, op2) ->
      inv_case_some case24 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PUNPCKL (gg, op1, op2) ->
      inv_case_some case25 (Obj.magic (gg, (op1, op2)))
    | X86_PARSER_ARG.M_PXOR (op1, op2) ->
      inv_case_some case26 (Obj.magic (op1, op2))))

(** val s_instr1_b : bigrammar **)

let s_instr1_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.double (Big.double Big.one))),
    (BNode ((Big.double (Big.double Big.one)), (BNode ((Big.double Big.one),
    (BNode (Big.one, (BNode (Big.zero, (BLeaf (Big.zero, coq_ADDPS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_ADDPS (op1, op2))))), (BLeaf (Big.one,
    coq_ADDSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_ADDSS (op1, op2))))))), (BLeaf ((Big.double
    Big.one), coq_ANDNPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_ANDNPS (op1, op2))))))), (BNode
    ((Big.doubleplusone Big.one), (BLeaf ((Big.doubleplusone Big.one),
    coq_ANDPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_ANDPS (op1, op2))))), (BLeaf ((Big.double
    (Big.double Big.one)), coq_CMPPS_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_CMPPS (op1, op2, imm))))))))),
    (BNode ((Big.double (Big.doubleplusone Big.one)), (BNode
    ((Big.doubleplusone (Big.double Big.one)), (BLeaf ((Big.doubleplusone
    (Big.double Big.one)), coq_CMPSS_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_CMPSS (op1, op2, imm))))),
    (BLeaf ((Big.double (Big.doubleplusone Big.one)), coq_COMISS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_COMISS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_CVTPI2PS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTPI2PS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))), coq_CVTPS2PI_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTPS2PI (op1, op2))))))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.double (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_CVTSI2SS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTSI2SS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double Big.one))), coq_CVTSS2SI_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTSS2SI (op1, op2))))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double Big.one))),
    coq_CVTTPS2PI_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTTPS2PI (op1, op2))))))), (BNode
    ((Big.double (Big.double (Big.doubleplusone Big.one))), (BLeaf
    ((Big.double (Big.double (Big.doubleplusone Big.one))), coq_CVTTSS2SI_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_CVTTSS2SI (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_DIVPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_DIVPS (op1, op2))))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_DIVSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_DIVSS (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_LDMXCSR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_LDMXCSR (Obj.magic op))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.double Big.one)))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.double Big.one)))),
    coq_MAXPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MAXPS (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    coq_MAXSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MAXSS (op1, op2))))))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BNode ((Big.double (Big.double
    (Big.doubleplusone (Big.double Big.one)))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.double Big.one)))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.double Big.one)))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_MINPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MINPS (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_MINSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MINSS (op1, op2))))))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone (Big.double Big.one)))), coq_MOVAPS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVAPS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))), coq_MOVHLPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVHLPS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))),
    coq_MOVHPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVHPS (op1, op2))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    (BNode ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.double Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), coq_MOVLHPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVLHPS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.doubleplusone Big.one)))), coq_MOVLPS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVLPS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.doubleplusone
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one)))), coq_MOVMSKPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVMSKPS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))),
    coq_MOVSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVSS (op1, op2))))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BNode ((Big.double (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double (Big.doubleplusone Big.one)))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_MOVUPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVUPS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_MULPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MULPS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.doubleplusone (Big.doubleplusone
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one)))), coq_MULSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MULSS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_ORPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_ORPS (op1, op2))))))))), (BNode ((Big.double
    (Big.double (Big.double (Big.double (Big.double Big.one))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one)))),
    coq_RCPPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_RCPPS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.double (Big.double Big.one))))),
    coq_RCPSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_RCPSS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double (Big.double (Big.double
    Big.one))))), (BLeaf ((Big.doubleplusone (Big.double (Big.double
    (Big.double (Big.double Big.one))))), coq_RSQRTPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_RSQRTPS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double (Big.double (Big.double Big.one))))),
    coq_RSQRTSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_RSQRTSS (op1, op2))))))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case2 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case4 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case7 = MLTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case8 = MLTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case10 = MLTree (MRTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case11 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case12 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case13 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case14 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case15 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case16 = MLTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case17 = MLTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case18 = MRTree (MLTree (MLTree (MLTree (MLTree (MLTree MLeaf))))) in
  let case19 = MRTree (MLTree (MLTree (MLTree (MLTree (MRTree MLeaf))))) in
  let case20 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case21 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case22 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case23 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case24 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case25 = MRTree (MLTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case26 = MRTree (MLTree (MRTree (MRTree (MRTree MLeaf)))) in
  let case27 = MRTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case28 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case29 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case30 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case31 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case32 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case33 = MRTree (MRTree (MRTree (MRTree (MLTree MLeaf)))) in
  let case34 = MRTree (MRTree (MRTree (MRTree (MRTree MLeaf)))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.S_ADDPS (op1, op2) ->
      inv_case_some case0 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_ADDSS (op1, op2) ->
      inv_case_some case1 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_ANDNPS (op1, op2) ->
      inv_case_some case2 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_ANDPS (op1, op2) ->
      inv_case_some case3 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CMPPS (op1, op2, imm) ->
      inv_case_some case4 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_CMPSS (op1, op2, imm) ->
      inv_case_some case5 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_COMISS (op1, op2) ->
      inv_case_some case6 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTPI2PS (op1, op2) ->
      inv_case_some case7 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTPS2PI (op1, op2) ->
      inv_case_some case8 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTSI2SS (op1, op2) ->
      inv_case_some case9 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTSS2SI (op1, op2) ->
      inv_case_some case10 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTTPS2PI (op1, op2) ->
      inv_case_some case11 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_CVTTSS2SI (op1, op2) ->
      inv_case_some case12 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_DIVPS (op1, op2) ->
      inv_case_some case13 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_DIVSS (op1, op2) ->
      inv_case_some case14 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_LDMXCSR op -> inv_case_some case15 (Obj.magic op)
    | X86_PARSER_ARG.S_MAXPS (op1, op2) ->
      inv_case_some case16 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MAXSS (op1, op2) ->
      inv_case_some case17 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MINPS (op1, op2) ->
      inv_case_some case18 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MINSS (op1, op2) ->
      inv_case_some case19 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVAPS (op1, op2) ->
      inv_case_some case20 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVHLPS (op1, op2) ->
      inv_case_some case21 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVHPS (op1, op2) ->
      inv_case_some case22 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVLHPS (op1, op2) ->
      inv_case_some case23 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVLPS (op1, op2) ->
      inv_case_some case24 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVMSKPS (op1, op2) ->
      inv_case_some case25 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVSS (op1, op2) ->
      inv_case_some case26 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVUPS (op1, op2) ->
      inv_case_some case27 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MULPS (op1, op2) ->
      inv_case_some case28 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MULSS (op1, op2) ->
      inv_case_some case29 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_ORPS (op1, op2) ->
      inv_case_some case30 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_RCPPS (op1, op2) ->
      inv_case_some case31 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_RCPSS (op1, op2) ->
      inv_case_some case32 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_RSQRTPS (op1, op2) ->
      inv_case_some case33 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_RSQRTSS (op1, op2) ->
      inv_case_some case34 (Obj.magic (op1, op2))))

(** val s_instr2_b : bigrammar **)

let s_instr2_b =
  let gt = BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one))), (BNode ((Big.double (Big.doubleplusone Big.one)), (BNode
    ((Big.doubleplusone Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, coq_SHUFPS_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_SHUFPS (op1, op2, imm))))),
    (BLeaf (Big.one, coq_SQRTPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_SQRTPS (op1, op2))))))), (BNode ((Big.double
    Big.one), (BLeaf ((Big.double Big.one), coq_SQRTSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_SQRTSS (op1, op2))))), (BLeaf
    ((Big.doubleplusone Big.one), coq_STMXCSR_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_STMXCSR (Obj.magic op))))))))), (BNode
    ((Big.doubleplusone (Big.double Big.one)), (BNode ((Big.double
    (Big.double Big.one)), (BLeaf ((Big.double (Big.double Big.one)),
    coq_SUBPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_SUBPS (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double Big.one)), coq_SUBSS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_SUBSS (op1, op2))))))), (BLeaf ((Big.double
    (Big.doubleplusone Big.one)), coq_UCOMISS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_UCOMISS (op1, op2))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double Big.one))), (BNode
    ((Big.double (Big.double (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)), coq_UNPCKHPS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_UNPCKHPS (op1, op2))))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))), coq_UNPCKLPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_UNPCKLPS (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))), coq_XORPS_b,
    (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_XORPS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.double Big.one))), coq_PAVGB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PAVGB (op1, op2))))))))), (BNode ((Big.double
    (Big.double (Big.doubleplusone Big.one))), (BNode ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), (BLeaf ((Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one))), coq_PEXTRW_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_PEXTRW (op1, op2, imm))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone Big.one))),
    coq_PINSRW_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_PINSRW (op1, op2, imm))))))),
    (BLeaf ((Big.doubleplusone (Big.double (Big.doubleplusone Big.one))),
    coq_PMAXSW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PMAXSW (op1, op2))))))))))), (BNode
    ((Big.double (Big.double (Big.doubleplusone (Big.double Big.one)))),
    (BNode ((Big.doubleplusone (Big.double (Big.double (Big.double
    Big.one)))), (BNode ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone Big.one))), (BNode ((Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.doubleplusone Big.one))), coq_PMAXUB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PMAXUB (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone Big.one))),
    coq_PMINSW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PMINSW (op1, op2))))))), (BNode ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), (BLeaf ((Big.double
    (Big.double (Big.double (Big.double Big.one)))), coq_PMINUB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PMINUB (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double (Big.double Big.one)))),
    coq_PMOVMSKB_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PMOVMSKB (op1, op2))))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), (BNode ((Big.double (Big.doubleplusone (Big.double
    (Big.double Big.one)))), (BLeaf ((Big.double (Big.doubleplusone
    (Big.double (Big.double Big.one)))), coq_PSADBW_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_PSADBW (op1, op2))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.double
    Big.one)))), coq_PSHUFW_b, (fun v ->
    let (op1, i) = Obj.magic v in
    let (op2, imm) = i in Obj.magic (X86_PARSER_ARG.S_PSHUFW (op1, op2, imm))))))),
    (BLeaf ((Big.double (Big.double (Big.doubleplusone (Big.double
    Big.one)))), coq_MASKMOVQ_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MASKMOVQ (op1, op2))))))))), (BNode
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    (BNode ((Big.double (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (BNode ((Big.doubleplusone (Big.double (Big.doubleplusone
    (Big.double Big.one)))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.doubleplusone (Big.double Big.one)))), coq_MOVNTPS_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVNTPS (op1, op2))))), (BLeaf ((Big.double
    (Big.doubleplusone (Big.doubleplusone (Big.double Big.one)))),
    coq_MOVNTQ_b, (fun v ->
    let (op1, op2) = Obj.magic v in
    Obj.magic (X86_PARSER_ARG.S_MOVNTQ (op1, op2))))))), (BNode
    ((Big.doubleplusone (Big.doubleplusone (Big.doubleplusone (Big.double
    Big.one)))), (BLeaf ((Big.doubleplusone (Big.doubleplusone
    (Big.doubleplusone (Big.double Big.one)))), coq_PREFETCHT0_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_PREFETCHT0 (Obj.magic op))))), (BLeaf
    ((Big.double (Big.double (Big.double (Big.doubleplusone Big.one)))),
    coq_PREFETCHT1_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_PREFETCHT1 (Obj.magic op))))))))), (BNode
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), (BNode ((Big.doubleplusone (Big.double (Big.double
    (Big.doubleplusone Big.one)))), (BLeaf ((Big.doubleplusone (Big.double
    (Big.double (Big.doubleplusone Big.one)))), coq_PREFETCHT2_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_PREFETCHT2 (Obj.magic op))))), (BLeaf
    ((Big.double (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_PREFETCHNTA_b, (fun op ->
    Obj.magic (X86_PARSER_ARG.S_PREFETCHNTA (Obj.magic op))))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone (Big.double (Big.doubleplusone
    Big.one)))), coq_SFENCE_b, (fun _ ->
    Obj.magic X86_PARSER_ARG.S_SFENCE))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case1 = MLTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case2 = MLTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case3 = MLTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case4 = MLTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case5 = MLTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case6 = MLTree (MLTree (MRTree (MRTree MLeaf))) in
  let case7 = MLTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case8 = MLTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case9 = MLTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case10 = MLTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case11 = MLTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case12 = MLTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case13 = MLTree (MRTree (MRTree (MRTree MLeaf))) in
  let case14 = MRTree (MLTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case15 = MRTree (MLTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case16 = MRTree (MLTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case17 = MRTree (MLTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case18 = MRTree (MLTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case19 = MRTree (MLTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case20 = MRTree (MLTree (MRTree (MRTree MLeaf))) in
  let case21 = MRTree (MRTree (MLTree (MLTree (MLTree MLeaf)))) in
  let case22 = MRTree (MRTree (MLTree (MLTree (MRTree MLeaf)))) in
  let case23 = MRTree (MRTree (MLTree (MRTree (MLTree MLeaf)))) in
  let case24 = MRTree (MRTree (MLTree (MRTree (MRTree MLeaf)))) in
  let case25 = MRTree (MRTree (MRTree (MLTree (MLTree MLeaf)))) in
  let case26 = MRTree (MRTree (MRTree (MLTree (MRTree MLeaf)))) in
  let case27 = MRTree (MRTree (MRTree (MRTree MLeaf))) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    match Obj.magic u with
    | X86_PARSER_ARG.S_SHUFPS (op1, op2, imm) ->
      inv_case_some case0 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_SQRTPS (op1, op2) ->
      inv_case_some case1 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_SQRTSS (op1, op2) ->
      inv_case_some case2 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_STMXCSR op -> inv_case_some case3 (Obj.magic op)
    | X86_PARSER_ARG.S_SUBPS (op1, op2) ->
      inv_case_some case4 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_SUBSS (op1, op2) ->
      inv_case_some case5 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_UCOMISS (op1, op2) ->
      inv_case_some case6 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_UNPCKHPS (op1, op2) ->
      inv_case_some case7 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_UNPCKLPS (op1, op2) ->
      inv_case_some case8 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_XORPS (op1, op2) ->
      inv_case_some case9 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PAVGB (op1, op2) ->
      inv_case_some case10 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PEXTRW (op1, op2, imm) ->
      inv_case_some case11 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_PINSRW (op1, op2, imm) ->
      inv_case_some case12 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_PMAXSW (op1, op2) ->
      inv_case_some case13 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PMAXUB (op1, op2) ->
      inv_case_some case14 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PMINSW (op1, op2) ->
      inv_case_some case15 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PMINUB (op1, op2) ->
      inv_case_some case16 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PMOVMSKB (op1, op2) ->
      inv_case_some case17 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PSADBW (op1, op2) ->
      inv_case_some case18 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PSHUFW (op1, op2, imm) ->
      inv_case_some case19 (Obj.magic (op1, (op2, imm)))
    | X86_PARSER_ARG.S_MASKMOVQ (op1, op2) ->
      inv_case_some case20 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVNTPS (op1, op2) ->
      inv_case_some case21 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_MOVNTQ (op1, op2) ->
      inv_case_some case22 (Obj.magic (op1, op2))
    | X86_PARSER_ARG.S_PREFETCHT0 op -> inv_case_some case23 (Obj.magic op)
    | X86_PARSER_ARG.S_PREFETCHT1 op -> inv_case_some case24 (Obj.magic op)
    | X86_PARSER_ARG.S_PREFETCHT2 op -> inv_case_some case25 (Obj.magic op)
    | X86_PARSER_ARG.S_PREFETCHNTA op -> inv_case_some case26 (Obj.magic op)
    | X86_PARSER_ARG.S_SFENCE -> inv_case_some case27 (Obj.magic ())))

(** val instr_bigrammar : bigrammar **)

let instr_bigrammar =
  let gt = BNode ((Big.doubleplusone (Big.double Big.one)), (BNode
    ((Big.double Big.one), (BNode (Big.one, (BNode (Big.zero, (BLeaf
    (Big.zero, (seq prefix_grammar_only_seg_override i_instr1_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_AAA -> AAA
       | X86_PARSER_ARG.I_AAD -> AAD
       | X86_PARSER_ARG.I_AAM -> AAM
       | X86_PARSER_ARG.I_AAS -> AAS
       | X86_PARSER_ARG.I_CLC -> CLC
       | X86_PARSER_ARG.I_CLD -> CLD
       | X86_PARSER_ARG.I_CLI -> CLI
       | X86_PARSER_ARG.I_CLTS -> CLTS
       | X86_PARSER_ARG.I_CMC -> CMC
       | X86_PARSER_ARG.I_CPUID -> CPUID
       | X86_PARSER_ARG.I_DAA -> DAA
       | X86_PARSER_ARG.I_DAS -> DAS
       | X86_PARSER_ARG.I_HLT -> HLT
       | X86_PARSER_ARG.I_INT -> INT
       | X86_PARSER_ARG.I_INTO -> INTO
       | X86_PARSER_ARG.I_INVD -> INVD
       | X86_PARSER_ARG.I_IRET -> IRET
       | X86_PARSER_ARG.I_LAHF -> LAHF
       | X86_PARSER_ARG.I_LEAVE -> LEAVE
       | X86_PARSER_ARG.I_POPA -> POPA
       | X86_PARSER_ARG.I_POPF -> POPF
       | X86_PARSER_ARG.I_PUSHA -> PUSHA
       | X86_PARSER_ARG.I_PUSHF -> PUSHF
       | X86_PARSER_ARG.I_RDMSR -> RDMSR
       | X86_PARSER_ARG.I_RDPMC -> RDPMC
       | X86_PARSER_ARG.I_RDTSC -> RDTSC
       | X86_PARSER_ARG.I_RDTSCP -> RDTSCP
       | X86_PARSER_ARG.I_RSM -> RSM
       | X86_PARSER_ARG.I_SAHF -> SAHF
       | X86_PARSER_ARG.I_STC -> STC
       | X86_PARSER_ARG.I_STD -> STD
       | X86_PARSER_ARG.I_STI -> STI
       | X86_PARSER_ARG.I_UD2 -> UD2
       | X86_PARSER_ARG.I_WBINVD -> WBINVD
       | X86_PARSER_ARG.I_WRMSR -> WRMSR
       | X86_PARSER_ARG.I_XLAT -> XLAT))))), (BLeaf (Big.one,
    (seq prefix_grammar_only_seg_override i_instr2_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_ARPL (op1, op2) -> ARPL (op1, op2)
       | X86_PARSER_ARG.I_BOUND (op1, op2) -> BOUND (op1, op2)
       | X86_PARSER_ARG.I_BSF (op1, op2) -> BSF (op1, op2)
       | X86_PARSER_ARG.I_BSR (op1, op2) -> BSR (op1, op2)
       | X86_PARSER_ARG.I_BSWAP r -> BSWAP r
       | X86_PARSER_ARG.I_BT (op1, op2) -> BT (op1, op2)
       | X86_PARSER_ARG.I_CALL (near, abs, op, sel) ->
         CALL (near, abs, op, sel)
       | X86_PARSER_ARG.I_IN (w, p) -> IN (w, p)
       | X86_PARSER_ARG.I_INTn it -> INTn it
       | X86_PARSER_ARG.I_INVLPG op -> INVLPG op
       | X86_PARSER_ARG.I_Jcc (ct, disp) -> Jcc (ct, disp)
       | X86_PARSER_ARG.I_JCXZ b -> JCXZ b
       | X86_PARSER_ARG.I_JMP (near, abs, op, sel) ->
         JMP (near, abs, op, sel)
       | X86_PARSER_ARG.I_LAR (op1, op2) -> LAR (op1, op2)
       | X86_PARSER_ARG.I_LDS (op1, op2) -> LDS (op1, op2)
       | X86_PARSER_ARG.I_LEA (op1, op2) -> LEA (op1, op2)
       | X86_PARSER_ARG.I_LES (op1, op2) -> LES (op1, op2)
       | X86_PARSER_ARG.I_LFS (op1, op2) -> LFS (op1, op2)
       | X86_PARSER_ARG.I_LGDT op -> LGDT op
       | X86_PARSER_ARG.I_LGS (op1, op2) -> LGS (op1, op2)
       | X86_PARSER_ARG.I_LIDT op -> LIDT op
       | X86_PARSER_ARG.I_LLDT op -> LLDT op
       | X86_PARSER_ARG.I_LMSW op -> LMSW op
       | X86_PARSER_ARG.I_LOOP disp -> LOOP disp
       | X86_PARSER_ARG.I_LOOPZ disp -> LOOPZ disp
       | X86_PARSER_ARG.I_LOOPNZ disp -> LOOPNZ disp
       | X86_PARSER_ARG.I_LSL (op1, op2) -> LSL (op1, op2)
       | X86_PARSER_ARG.I_LSS (op1, op2) -> LSS (op1, op2)
       | X86_PARSER_ARG.I_LTR op -> LTR op))))))), (BLeaf ((Big.double
    Big.one), (seq prefix_grammar_only_seg_override i_instr3_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_MOVCR (d, cr, r) -> MOVCR (d, cr, r)
       | X86_PARSER_ARG.I_MOVDR (d, cr, r) -> MOVDR (d, cr, r)
       | X86_PARSER_ARG.I_MOVSR (d, cr, r) -> MOVSR (d, cr, r)
       | X86_PARSER_ARG.I_MOVBE (op1, op2) -> MOVBE (op1, op2)
       | X86_PARSER_ARG.I_OUT (w, p) -> OUT (w, p)
       | X86_PARSER_ARG.I_POP op -> POP op
       | X86_PARSER_ARG.I_POPSR sr -> POPSR sr
       | X86_PARSER_ARG.I_PUSH (w, op) -> PUSH (w, op)
       | X86_PARSER_ARG.I_PUSHSR sr -> PUSHSR sr
       | X86_PARSER_ARG.I_RCL (w, op1, ri) -> RCL (w, op1, ri)
       | X86_PARSER_ARG.I_RCR (w, op1, ri) -> RCR (w, op1, ri)
       | X86_PARSER_ARG.I_SETcc (ct, op) -> SETcc (ct, op)
       | X86_PARSER_ARG.I_SGDT op -> SGDT op
       | X86_PARSER_ARG.I_SIDT op -> SIDT op
       | X86_PARSER_ARG.I_SLDT op -> SLDT op
       | X86_PARSER_ARG.I_SMSW op -> SMSW op
       | X86_PARSER_ARG.I_STR op -> STR op
       | X86_PARSER_ARG.I_VERR op -> VERR op
       | X86_PARSER_ARG.I_VERW op -> VERW op))))))), (BNode ((Big.double
    (Big.double Big.one)), (BNode ((Big.doubleplusone Big.one), (BLeaf
    ((Big.doubleplusone Big.one), i_instr4_b, (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_INS b -> INS b
       | X86_PARSER_ARG.I_OUTS b -> OUTS b
       | X86_PARSER_ARG.I_MOVS b -> MOVS b
       | X86_PARSER_ARG.I_LODS b -> LODS b
       | X86_PARSER_ARG.I_STOS b -> STOS b
       | X86_PARSER_ARG.I_RET (ss, disp) -> RET (ss, disp)
       | X86_PARSER_ARG.I_CMPS b -> CMPS b
       | X86_PARSER_ARG.I_SCAS b -> SCAS b))))), (BLeaf ((Big.double
    (Big.double Big.one)), i_instr5_b, (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_ADC (w, op1, op2) -> ADC (w, op1, op2)
       | X86_PARSER_ARG.I_ADD (w, op1, op2) -> ADD (w, op1, op2)
       | X86_PARSER_ARG.I_AND (w, op1, op2) -> AND (w, op1, op2)
       | X86_PARSER_ARG.I_BTC (op1, op2) -> BTC (op1, op2)
       | X86_PARSER_ARG.I_BTR (op1, op2) -> BTR (op1, op2)
       | X86_PARSER_ARG.I_BTS (op1, op2) -> BTS (op1, op2)
       | X86_PARSER_ARG.I_CMP (w, op1, op2) -> CMP (w, op1, op2)
       | X86_PARSER_ARG.I_CMPXCHG (w, op1, op2) -> CMPXCHG (w, op1, op2)
       | X86_PARSER_ARG.I_DEC (w, op1) -> DEC (w, op1)
       | X86_PARSER_ARG.I_IMUL (w, op1, opopt, iopt) ->
         IMUL (w, op1, opopt, iopt)
       | X86_PARSER_ARG.I_INC (w, op1) -> INC (w, op1)
       | X86_PARSER_ARG.I_MOV (w, op1, op2) -> MOV (w, op1, op2)
       | X86_PARSER_ARG.I_NEG (w, op) -> NEG (w, op)
       | X86_PARSER_ARG.I_NOT (w, op) -> NOT (w, op)
       | X86_PARSER_ARG.I_OR (w, op1, op2) -> OR (w, op1, op2)
       | X86_PARSER_ARG.I_SBB (w, op1, op2) -> SBB (w, op1, op2)
       | X86_PARSER_ARG.I_SUB (w, op1, op2) -> SUB (w, op1, op2)
       | X86_PARSER_ARG.I_TEST (w, op1, op2) -> TEST (w, op1, op2)
       | X86_PARSER_ARG.I_XADD (w, op1, op2) -> XADD (w, op1, op2)
       | X86_PARSER_ARG.I_XCHG (w, op1, op2) -> XCHG (w, op1, op2)
       | X86_PARSER_ARG.I_XOR (w, op1, op2) -> XOR (w, op1, op2)))))))),
    (BLeaf ((Big.doubleplusone (Big.double Big.one)),
    (seq prefix_grammar_seg_op_override i_instr6_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.I_CDQ -> CDQ
       | X86_PARSER_ARG.I_CMOVcc (ct, op1, op2) -> CMOVcc (ct, op1, op2)
       | X86_PARSER_ARG.I_CWDE -> CWDE
       | X86_PARSER_ARG.I_DIV (w, op1) -> DIV (w, op1)
       | X86_PARSER_ARG.I_IDIV (w, op1) -> IDIV (w, op1)
       | X86_PARSER_ARG.I_MOVSX (w, op1, op2) -> MOVSX (w, op1, op2)
       | X86_PARSER_ARG.I_MOVZX (w, op1, op2) -> MOVZX (w, op1, op2)
       | X86_PARSER_ARG.I_MUL (w, op1) -> MUL (w, op1)
       | X86_PARSER_ARG.I_NOP op -> NOP op
       | X86_PARSER_ARG.I_ROL (w, op1, ri) -> ROL (w, op1, ri)
       | X86_PARSER_ARG.I_ROR (w, op1, ri) -> ROR (w, op1, ri)
       | X86_PARSER_ARG.I_SAR (w, op1, ri) -> SAR (w, op1, ri)
       | X86_PARSER_ARG.I_SHL (w, op1, ri) -> SHL (w, op1, ri)
       | X86_PARSER_ARG.I_SHLD (op1, r, ri) -> SHLD (op1, r, ri)
       | X86_PARSER_ARG.I_SHR (w, op1, ri) -> SHR (w, op1, ri)
       | X86_PARSER_ARG.I_SHRD (op1, r, ri) -> SHRD (op1, r, ri)))))))))),
    (BNode ((Big.double (Big.double (Big.double Big.one))), (BNode
    ((Big.doubleplusone (Big.doubleplusone Big.one)), (BNode ((Big.double
    (Big.doubleplusone Big.one)), (BLeaf ((Big.double (Big.doubleplusone
    Big.one)), (seq prefix_grammar_only_seg_override f_instr1_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.F_F2XM1 -> F2XM1
       | X86_PARSER_ARG.F_FABS -> FABS
       | X86_PARSER_ARG.F_FADD (z, op1) -> FADD (z, op1)
       | X86_PARSER_ARG.F_FADDP op -> FADDP op
       | X86_PARSER_ARG.F_FBLD op -> FBLD op
       | X86_PARSER_ARG.F_FBSTP op -> FBSTP op
       | X86_PARSER_ARG.F_FCHS -> FCHS
       | X86_PARSER_ARG.F_FCMOVcc (ct, op) -> FCMOVcc (ct, op)
       | X86_PARSER_ARG.F_FCOM op -> FCOM op
       | X86_PARSER_ARG.F_FCOMP op -> FCOMP op
       | X86_PARSER_ARG.F_FCOMPP -> FCOMPP
       | X86_PARSER_ARG.F_FCOMIP op -> FCOMIP op
       | X86_PARSER_ARG.F_FCOS -> FCOS
       | X86_PARSER_ARG.F_FDECSTP -> FDECSTP
       | X86_PARSER_ARG.F_FDIV (z, op) -> FDIV (z, op)
       | X86_PARSER_ARG.F_FDIVP op -> FDIVP op
       | X86_PARSER_ARG.F_FDIVR (z, op) -> FDIVR (z, op)
       | X86_PARSER_ARG.F_FDIVRP op -> FDIVRP op
       | X86_PARSER_ARG.F_FFREE op -> FFREE op
       | X86_PARSER_ARG.F_FIADD op -> FIADD op
       | X86_PARSER_ARG.F_FICOM op -> FICOM op
       | X86_PARSER_ARG.F_FICOMP op -> FICOMP op
       | X86_PARSER_ARG.F_FIDIV op -> FIDIV op
       | X86_PARSER_ARG.F_FIDIVR op -> FIDIVR op
       | X86_PARSER_ARG.F_FILD op -> FILD op
       | X86_PARSER_ARG.F_FIMUL op -> FIMUL op
       | X86_PARSER_ARG.F_FINCSTP -> FINCSTP
       | X86_PARSER_ARG.F_FIST op -> FIST op
       | X86_PARSER_ARG.F_FISTP op -> FISTP op
       | X86_PARSER_ARG.F_FISUB op -> FISUB op
       | X86_PARSER_ARG.F_FISUBR op -> FISUBR op
       | X86_PARSER_ARG.F_FLD op -> FLD op
       | X86_PARSER_ARG.F_FLD1 -> FLD1
       | X86_PARSER_ARG.F_FLDCW op -> FLDCW op
       | X86_PARSER_ARG.F_FLDENV op -> FLDENV op
       | X86_PARSER_ARG.F_FLDL2E -> FLDL2E
       | X86_PARSER_ARG.F_FLDL2T -> FLDL2T
       | X86_PARSER_ARG.F_FLDLG2 -> FLDLG2
       | X86_PARSER_ARG.F_FLDLN2 -> FLDLN2
       | X86_PARSER_ARG.F_FLDPI -> FLDPI
       | X86_PARSER_ARG.F_FLDZ -> FLDZ
       | X86_PARSER_ARG.F_FMUL (z, op) -> FMUL (z, op)
       | X86_PARSER_ARG.F_FMULP op -> FMULP op))))), (BLeaf
    ((Big.doubleplusone (Big.doubleplusone Big.one)),
    (seq prefix_grammar_only_seg_override f_instr2_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.F_FNCLEX -> FNCLEX
       | X86_PARSER_ARG.F_FNINIT -> FNINIT
       | X86_PARSER_ARG.F_FNOP -> FNOP
       | X86_PARSER_ARG.F_FNSAVE op -> FNSAVE op
       | X86_PARSER_ARG.F_FNSTCW op -> FNSTCW op
       | X86_PARSER_ARG.F_FNSTSW op -> FNSTSW op
       | X86_PARSER_ARG.F_FPATAN -> FPATAN
       | X86_PARSER_ARG.F_FPREM -> FPREM
       | X86_PARSER_ARG.F_FPREM1 -> FPREM1
       | X86_PARSER_ARG.F_FPTAN -> FPTAN
       | X86_PARSER_ARG.F_FRNDINT -> FRNDINT
       | X86_PARSER_ARG.F_FRSTOR op -> FRSTOR op
       | X86_PARSER_ARG.F_FSCALE -> FSCALE
       | X86_PARSER_ARG.F_FSIN -> FSIN
       | X86_PARSER_ARG.F_FSINCOS -> FSINCOS
       | X86_PARSER_ARG.F_FSQRT -> FSQRT
       | X86_PARSER_ARG.F_FST op -> FST op
       | X86_PARSER_ARG.F_FSTENV op -> FSTENV op
       | X86_PARSER_ARG.F_FSTP op -> FSTP op
       | X86_PARSER_ARG.F_FSUB (z, op) -> FSUB (z, op)
       | X86_PARSER_ARG.F_FSUBP op -> FSUBP op
       | X86_PARSER_ARG.F_FSUBR (z, op) -> FSUBR (z, op)
       | X86_PARSER_ARG.F_FSUBRP op -> FSUBRP op
       | X86_PARSER_ARG.F_FTST -> FTST
       | X86_PARSER_ARG.F_FUCOM op -> FUCOM op
       | X86_PARSER_ARG.F_FUCOMP op -> FUCOMP op
       | X86_PARSER_ARG.F_FUCOMPP -> FUCOMPP
       | X86_PARSER_ARG.F_FUCOMI op -> FUCOMI op
       | X86_PARSER_ARG.F_FUCOMIP op -> FUCOMIP op
       | X86_PARSER_ARG.F_FXAM -> FXAM
       | X86_PARSER_ARG.F_FXCH op -> FXCH op
       | X86_PARSER_ARG.F_FXTRACT -> FXTRACT
       | X86_PARSER_ARG.F_FYL2X -> FYL2X
       | X86_PARSER_ARG.F_FYL2XP1 -> FYL2XP1
       | X86_PARSER_ARG.F_FWAIT -> FWAIT))))))), (BLeaf ((Big.double
    (Big.double (Big.double Big.one))),
    (seq prefix_grammar_only_seg_override m_instr_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.M_EMMS -> EMMS
       | X86_PARSER_ARG.M_MOVD (op1, op2) -> MOVD (op1, op2)
       | X86_PARSER_ARG.M_MOVQ (op1, op2) -> MOVQ (op1, op2)
       | X86_PARSER_ARG.M_PACKSSDW (op1, op2) -> PACKSSDW (op1, op2)
       | X86_PARSER_ARG.M_PACKSSWB (op1, op2) -> PACKSSWB (op1, op2)
       | X86_PARSER_ARG.M_PACKUSWB (op1, op2) -> PACKUSWB (op1, op2)
       | X86_PARSER_ARG.M_PADD (gg, op1, op2) -> PADD (gg, op1, op2)
       | X86_PARSER_ARG.M_PADDS (gg, op1, op2) -> PADDS (gg, op1, op2)
       | X86_PARSER_ARG.M_PADDUS (gg, op1, op2) -> PADDUS (gg, op1, op2)
       | X86_PARSER_ARG.M_PAND (op1, op2) -> PAND (op1, op2)
       | X86_PARSER_ARG.M_PANDN (op1, op2) -> PANDN (op1, op2)
       | X86_PARSER_ARG.M_PCMPEQ (gg, op1, op2) -> PCMPEQ (gg, op1, op2)
       | X86_PARSER_ARG.M_PCMPGT (gg, op1, op2) -> PCMPGT (gg, op1, op2)
       | X86_PARSER_ARG.M_PMADDWD (op1, op2) -> PMADDWD (op1, op2)
       | X86_PARSER_ARG.M_PMULHUW (op1, op2) -> PMULHUW (op1, op2)
       | X86_PARSER_ARG.M_PMULHW (op1, op2) -> PMULHW (op1, op2)
       | X86_PARSER_ARG.M_PMULLW (op1, op2) -> PMULLW (op1, op2)
       | X86_PARSER_ARG.M_POR (op1, op2) -> POR (op1, op2)
       | X86_PARSER_ARG.M_PSLL (gg, op1, op2) -> PSLL (gg, op1, op2)
       | X86_PARSER_ARG.M_PSRA (gg, op1, op2) -> PSRA (gg, op1, op2)
       | X86_PARSER_ARG.M_PSRL (gg, op1, op2) -> PSRL (gg, op1, op2)
       | X86_PARSER_ARG.M_PSUB (gg, op1, op2) -> PSUB (gg, op1, op2)
       | X86_PARSER_ARG.M_PSUBS (gg, op1, op2) -> PSUBS (gg, op1, op2)
       | X86_PARSER_ARG.M_PSUBUS (gg, op1, op2) -> PSUBUS (gg, op1, op2)
       | X86_PARSER_ARG.M_PUNPCKH (gg, op1, op2) -> PUNPCKH (gg, op1, op2)
       | X86_PARSER_ARG.M_PUNPCKL (gg, op1, op2) -> PUNPCKL (gg, op1, op2)
       | X86_PARSER_ARG.M_PXOR (op1, op2) -> PXOR (op1, op2)))))))), (BNode
    ((Big.doubleplusone (Big.double (Big.double Big.one))), (BLeaf
    ((Big.doubleplusone (Big.double (Big.double Big.one))),
    (seq prefix_grammar_only_seg_override s_instr1_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.S_ADDPS (op1, op2) -> ADDPS (op1, op2)
       | X86_PARSER_ARG.S_ADDSS (op1, op2) -> ADDSS (op1, op2)
       | X86_PARSER_ARG.S_ANDNPS (op1, op2) -> ANDNPS (op1, op2)
       | X86_PARSER_ARG.S_ANDPS (op1, op2) -> ANDPS (op1, op2)
       | X86_PARSER_ARG.S_CMPPS (op1, op2, imm) -> CMPPS (op1, op2, imm)
       | X86_PARSER_ARG.S_CMPSS (op1, op2, imm) -> CMPSS (op1, op2, imm)
       | X86_PARSER_ARG.S_COMISS (op1, op2) -> COMISS (op1, op2)
       | X86_PARSER_ARG.S_CVTPI2PS (op1, op2) -> CVTPI2PS (op1, op2)
       | X86_PARSER_ARG.S_CVTPS2PI (op1, op2) -> CVTPS2PI (op1, op2)
       | X86_PARSER_ARG.S_CVTSI2SS (op1, op2) -> CVTSI2SS (op1, op2)
       | X86_PARSER_ARG.S_CVTSS2SI (op1, op2) -> CVTSS2SI (op1, op2)
       | X86_PARSER_ARG.S_CVTTPS2PI (op1, op2) -> CVTTPS2PI (op1, op2)
       | X86_PARSER_ARG.S_CVTTSS2SI (op1, op2) -> CVTTSS2SI (op1, op2)
       | X86_PARSER_ARG.S_DIVPS (op1, op2) -> DIVPS (op1, op2)
       | X86_PARSER_ARG.S_DIVSS (op1, op2) -> DIVSS (op1, op2)
       | X86_PARSER_ARG.S_LDMXCSR op -> LDMXCSR op
       | X86_PARSER_ARG.S_MAXPS (op1, op2) -> MAXPS (op1, op2)
       | X86_PARSER_ARG.S_MAXSS (op1, op2) -> MAXSS (op1, op2)
       | X86_PARSER_ARG.S_MINPS (op1, op2) -> MINPS (op1, op2)
       | X86_PARSER_ARG.S_MINSS (op1, op2) -> MINSS (op1, op2)
       | X86_PARSER_ARG.S_MOVAPS (op1, op2) -> MOVAPS (op1, op2)
       | X86_PARSER_ARG.S_MOVHLPS (op1, op2) -> MOVHLPS (op1, op2)
       | X86_PARSER_ARG.S_MOVHPS (op1, op2) -> MOVHPS (op1, op2)
       | X86_PARSER_ARG.S_MOVLHPS (op1, op2) -> MOVLHPS (op1, op2)
       | X86_PARSER_ARG.S_MOVLPS (op1, op2) -> MOVLPS (op1, op2)
       | X86_PARSER_ARG.S_MOVMSKPS (op1, op2) -> MOVMSKPS (op1, op2)
       | X86_PARSER_ARG.S_MOVSS (op1, op2) -> MOVSS (op1, op2)
       | X86_PARSER_ARG.S_MOVUPS (op1, op2) -> MOVUPS (op1, op2)
       | X86_PARSER_ARG.S_MULPS (op1, op2) -> MULPS (op1, op2)
       | X86_PARSER_ARG.S_MULSS (op1, op2) -> MULSS (op1, op2)
       | X86_PARSER_ARG.S_ORPS (op1, op2) -> ORPS (op1, op2)
       | X86_PARSER_ARG.S_RCPPS (op1, op2) -> RCPPS (op1, op2)
       | X86_PARSER_ARG.S_RCPSS (op1, op2) -> RCPSS (op1, op2)
       | X86_PARSER_ARG.S_RSQRTPS (op1, op2) -> RSQRTPS (op1, op2)
       | X86_PARSER_ARG.S_RSQRTSS (op1, op2) -> RSQRTSS (op1, op2)))))),
    (BLeaf ((Big.double (Big.doubleplusone (Big.double Big.one))),
    (seq prefix_grammar_only_seg_override s_instr2_b), (fun v ->
    let (pre, hi) = Obj.magic v in
    Obj.magic (pre,
      (match hi with
       | X86_PARSER_ARG.S_SHUFPS (op1, op2, imm) -> SHUFPS (op1, op2, imm)
       | X86_PARSER_ARG.S_SQRTPS (op1, op2) -> SQRTPS (op1, op2)
       | X86_PARSER_ARG.S_SQRTSS (op1, op2) -> SQRTSS (op1, op2)
       | X86_PARSER_ARG.S_STMXCSR op -> STMXCSR op
       | X86_PARSER_ARG.S_SUBPS (op1, op2) -> SUBPS (op1, op2)
       | X86_PARSER_ARG.S_SUBSS (op1, op2) -> SUBSS (op1, op2)
       | X86_PARSER_ARG.S_UCOMISS (op1, op2) -> UCOMISS (op1, op2)
       | X86_PARSER_ARG.S_UNPCKHPS (op1, op2) -> UNPCKHPS (op1, op2)
       | X86_PARSER_ARG.S_UNPCKLPS (op1, op2) -> UNPCKLPS (op1, op2)
       | X86_PARSER_ARG.S_XORPS (op1, op2) -> XORPS (op1, op2)
       | X86_PARSER_ARG.S_PAVGB (op1, op2) -> PAVGB (op1, op2)
       | X86_PARSER_ARG.S_PEXTRW (op1, op2, imm) -> PEXTRW (op1, op2, imm)
       | X86_PARSER_ARG.S_PINSRW (op1, op2, imm) -> PINSRW (op1, op2, imm)
       | X86_PARSER_ARG.S_PMAXSW (op1, op2) -> PMAXSW (op1, op2)
       | X86_PARSER_ARG.S_PMAXUB (op1, op2) -> PMAXUB (op1, op2)
       | X86_PARSER_ARG.S_PMINSW (op1, op2) -> PMINSW (op1, op2)
       | X86_PARSER_ARG.S_PMINUB (op1, op2) -> PMINUB (op1, op2)
       | X86_PARSER_ARG.S_PMOVMSKB (op1, op2) -> PMOVMSKB (op1, op2)
       | X86_PARSER_ARG.S_PSADBW (op1, op2) -> PSADBW (op1, op2)
       | X86_PARSER_ARG.S_PSHUFW (op1, op2, imm) -> PSHUFW (op1, op2, imm)
       | X86_PARSER_ARG.S_MASKMOVQ (op1, op2) -> MASKMOVQ (op1, op2)
       | X86_PARSER_ARG.S_MOVNTPS (op1, op2) -> MOVNTPS (op1, op2)
       | X86_PARSER_ARG.S_MOVNTQ (op1, op2) -> MOVNTQ (op1, op2)
       | X86_PARSER_ARG.S_PREFETCHT0 op -> PREFETCHT0 op
       | X86_PARSER_ARG.S_PREFETCHT1 op -> PREFETCHT1 op
       | X86_PARSER_ARG.S_PREFETCHT2 op -> PREFETCHT2 op
       | X86_PARSER_ARG.S_PREFETCHNTA op -> PREFETCHNTA op
       | X86_PARSER_ARG.S_SFENCE -> SFENCE))))))))))
  in
  let case0 = MLTree (MLTree (MLTree (MLTree MLeaf))) in
  let case1 = MLTree (MLTree (MLTree (MRTree MLeaf))) in
  let case2 = MLTree (MLTree (MRTree MLeaf)) in
  let case3 = MLTree (MRTree (MLTree (MLTree MLeaf))) in
  let case4 = MLTree (MRTree (MLTree (MRTree MLeaf))) in
  let case5 = MLTree (MRTree (MRTree MLeaf)) in
  let case6 = MRTree (MLTree (MLTree (MLTree MLeaf))) in
  let case7 = MRTree (MLTree (MLTree (MRTree MLeaf))) in
  let case8 = MRTree (MLTree (MRTree MLeaf)) in
  let case9 = MRTree (MRTree (MLTree MLeaf)) in
  let case10 = MRTree (MRTree (MRTree MLeaf)) in
  map (comb_bigrammar gt) ((comb_map gt), (fun u ->
    let (pre, i) = Obj.magic u in
    (match i with
     | AAA -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_AAA))
     | AAD -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_AAD))
     | AAM -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_AAM))
     | AAS -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_AAS))
     | ADC (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_ADC (w, op1, op2))))
     | ADD (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_ADD (w, op1, op2))))
     | AND (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_AND (w, op1, op2))))
     | ARPL (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_ARPL (op1, op2))))
     | BOUND (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_BOUND (op1, op2))))
     | BSF (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_BSF (op1, op2))))
     | BSR (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_BSR (op1, op2))))
     | BSWAP r ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_BSWAP r)))
     | BT (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_BT (op1, op2))))
     | BTC (op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_BTC (op1, op2))))
     | BTR (op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_BTR (op1, op2))))
     | BTS (op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_BTS (op1, op2))))
     | CALL (near, abs, op, sel) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_CALL (near, abs, op, sel))))
     | CDQ -> inv_case_some case5 (Obj.magic (pre, X86_PARSER_ARG.I_CDQ))
     | CLC -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CLC))
     | CLD -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CLD))
     | CLI -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CLI))
     | CLTS -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CLTS))
     | CMC -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CMC))
     | CMOVcc (ct, op1, op2) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_CMOVcc (ct, op1, op2))))
     | CMP (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_CMP (w, op1, op2))))
     | CMPS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_CMPS b)))
     | CMPXCHG (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_CMPXCHG (w, op1, op2))))
     | CPUID -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_CPUID))
     | CWDE -> inv_case_some case5 (Obj.magic (pre, X86_PARSER_ARG.I_CWDE))
     | DAA -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_DAA))
     | DAS -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_DAS))
     | DEC (w, op1) ->
       inv_case_some case4 (Obj.magic (pre, (X86_PARSER_ARG.I_DEC (w, op1))))
     | DIV (w, op1) ->
       inv_case_some case5 (Obj.magic (pre, (X86_PARSER_ARG.I_DIV (w, op1))))
     | F2XM1 -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_F2XM1))
     | FABS -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FABS))
     | FADD (z, op1) ->
       inv_case_some case6
         (Obj.magic (pre, (X86_PARSER_ARG.F_FADD (z, op1))))
     | FADDP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FADDP op)))
     | FBLD op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FBLD op)))
     | FBSTP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FBSTP op)))
     | FCHS -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FCHS))
     | FCMOVcc (ct, op) ->
       inv_case_some case6
         (Obj.magic (pre, (X86_PARSER_ARG.F_FCMOVcc (ct, op))))
     | FCOM op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FCOM op)))
     | FCOMP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FCOMP op)))
     | FCOMPP ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FCOMPP))
     | FCOMIP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FCOMIP op)))
     | FCOS -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FCOS))
     | FDECSTP ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FDECSTP))
     | FDIV (z, op) ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FDIV (z, op))))
     | FDIVP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FDIVP op)))
     | FDIVR (z, op) ->
       inv_case_some case6
         (Obj.magic (pre, (X86_PARSER_ARG.F_FDIVR (z, op))))
     | FDIVRP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FDIVRP op)))
     | FFREE op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FFREE op)))
     | FIADD op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FIADD op)))
     | FICOM op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FICOM op)))
     | FICOMP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FICOMP op)))
     | FIDIV op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FIDIV op)))
     | FIDIVR op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FIDIVR op)))
     | FILD op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FILD op)))
     | FIMUL op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FIMUL op)))
     | FINCSTP ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FINCSTP))
     | FIST op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FIST op)))
     | FISTP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FISTP op)))
     | FISUB op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FISUB op)))
     | FISUBR op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FISUBR op)))
     | FLD op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FLD op)))
     | FLD1 -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLD1))
     | FLDCW op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FLDCW op)))
     | FLDENV op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FLDENV op)))
     | FLDL2E ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDL2E))
     | FLDL2T ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDL2T))
     | FLDLG2 ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDLG2))
     | FLDLN2 ->
       inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDLN2))
     | FLDPI -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDPI))
     | FLDZ -> inv_case_some case6 (Obj.magic (pre, X86_PARSER_ARG.F_FLDZ))
     | FMUL (z, op) ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FMUL (z, op))))
     | FMULP op ->
       inv_case_some case6 (Obj.magic (pre, (X86_PARSER_ARG.F_FMULP op)))
     | FNCLEX ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FNCLEX))
     | FNINIT ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FNINIT))
     | FNOP -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FNOP))
     | FNSAVE op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FNSAVE op)))
     | FNSTCW op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FNSTCW op)))
     | FNSTSW op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FNSTSW op)))
     | FPATAN ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FPATAN))
     | FPREM -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FPREM))
     | FPREM1 ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FPREM1))
     | FPTAN -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FPTAN))
     | FRNDINT ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FRNDINT))
     | FRSTOR op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FRSTOR op)))
     | FSCALE ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FSCALE))
     | FSIN -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FSIN))
     | FSINCOS ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FSINCOS))
     | FSQRT -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FSQRT))
     | FST op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FST op)))
     | FSTENV op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FSTENV op)))
     | FSTP op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FSTP op)))
     | FSUB (z, op) ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FSUB (z, op))))
     | FSUBP op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FSUBP op)))
     | FSUBR (z, op) ->
       inv_case_some case7
         (Obj.magic (pre, (X86_PARSER_ARG.F_FSUBR (z, op))))
     | FSUBRP op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FSUBRP op)))
     | FTST -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FTST))
     | FUCOM op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FUCOM op)))
     | FUCOMP op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FUCOMP op)))
     | FUCOMPP ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FUCOMPP))
     | FUCOMI op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FUCOMI op)))
     | FUCOMIP op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FUCOMIP op)))
     | FXAM -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FXAM))
     | FXCH op ->
       inv_case_some case7 (Obj.magic (pre, (X86_PARSER_ARG.F_FXCH op)))
     | FXTRACT ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FXTRACT))
     | FYL2X -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FYL2X))
     | FYL2XP1 ->
       inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FYL2XP1))
     | FWAIT -> inv_case_some case7 (Obj.magic (pre, X86_PARSER_ARG.F_FWAIT))
     | EMMS -> inv_case_some case8 (Obj.magic (pre, X86_PARSER_ARG.M_EMMS))
     | MOVD (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_MOVD (op1, op2))))
     | MOVQ (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_MOVQ (op1, op2))))
     | PACKSSDW (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PACKSSDW (op1, op2))))
     | PACKSSWB (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PACKSSWB (op1, op2))))
     | PACKUSWB (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PACKUSWB (op1, op2))))
     | PADD (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PADD (gg, op1, op2))))
     | PADDS (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PADDS (gg, op1, op2))))
     | PADDUS (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PADDUS (gg, op1, op2))))
     | PAND (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PAND (op1, op2))))
     | PANDN (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PANDN (op1, op2))))
     | PCMPEQ (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PCMPEQ (gg, op1, op2))))
     | PCMPGT (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PCMPGT (gg, op1, op2))))
     | PMADDWD (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PMADDWD (op1, op2))))
     | PMULHUW (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PMULHUW (op1, op2))))
     | PMULHW (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PMULHW (op1, op2))))
     | PMULLW (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PMULLW (op1, op2))))
     | POR (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_POR (op1, op2))))
     | PSLL (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSLL (gg, op1, op2))))
     | PSRA (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSRA (gg, op1, op2))))
     | PSRL (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSRL (gg, op1, op2))))
     | PSUB (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSUB (gg, op1, op2))))
     | PSUBS (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSUBS (gg, op1, op2))))
     | PSUBUS (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PSUBUS (gg, op1, op2))))
     | PUNPCKH (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PUNPCKH (gg, op1, op2))))
     | PUNPCKL (gg, op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PUNPCKL (gg, op1, op2))))
     | PXOR (op1, op2) ->
       inv_case_some case8
         (Obj.magic (pre, (X86_PARSER_ARG.M_PXOR (op1, op2))))
     | ADDPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_ADDPS (op1, op2))))
     | ADDSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_ADDSS (op1, op2))))
     | ANDNPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_ANDNPS (op1, op2))))
     | ANDPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_ANDPS (op1, op2))))
     | CMPPS (op1, op2, imm) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CMPPS (op1, op2, imm))))
     | CMPSS (op1, op2, imm) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CMPSS (op1, op2, imm))))
     | COMISS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_COMISS (op1, op2))))
     | CVTPI2PS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTPI2PS (op1, op2))))
     | CVTPS2PI (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTPS2PI (op1, op2))))
     | CVTSI2SS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTSI2SS (op1, op2))))
     | CVTSS2SI (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTSS2SI (op1, op2))))
     | CVTTPS2PI (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTTPS2PI (op1, op2))))
     | CVTTSS2SI (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_CVTTSS2SI (op1, op2))))
     | DIVPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_DIVPS (op1, op2))))
     | DIVSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_DIVSS (op1, op2))))
     | LDMXCSR op ->
       inv_case_some case9 (Obj.magic (pre, (X86_PARSER_ARG.S_LDMXCSR op)))
     | MAXPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MAXPS (op1, op2))))
     | MAXSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MAXSS (op1, op2))))
     | MINPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MINPS (op1, op2))))
     | MINSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MINSS (op1, op2))))
     | MOVAPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVAPS (op1, op2))))
     | MOVHLPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVHLPS (op1, op2))))
     | MOVHPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVHPS (op1, op2))))
     | MOVLHPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVLHPS (op1, op2))))
     | MOVLPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVLPS (op1, op2))))
     | MOVMSKPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVMSKPS (op1, op2))))
     | MOVSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVSS (op1, op2))))
     | MOVUPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVUPS (op1, op2))))
     | MULPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MULPS (op1, op2))))
     | MULSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_MULSS (op1, op2))))
     | ORPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_ORPS (op1, op2))))
     | RCPPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_RCPPS (op1, op2))))
     | RCPSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_RCPSS (op1, op2))))
     | RSQRTPS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_RSQRTPS (op1, op2))))
     | RSQRTSS (op1, op2) ->
       inv_case_some case9
         (Obj.magic (pre, (X86_PARSER_ARG.S_RSQRTSS (op1, op2))))
     | SHUFPS (op1, op2, imm) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_SHUFPS (op1, op2, imm))))
     | SQRTPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_SQRTPS (op1, op2))))
     | SQRTSS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_SQRTSS (op1, op2))))
     | STMXCSR op ->
       inv_case_some case10 (Obj.magic (pre, (X86_PARSER_ARG.S_STMXCSR op)))
     | SUBPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_SUBPS (op1, op2))))
     | SUBSS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_SUBSS (op1, op2))))
     | UCOMISS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_UCOMISS (op1, op2))))
     | UNPCKHPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_UNPCKHPS (op1, op2))))
     | UNPCKLPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_UNPCKLPS (op1, op2))))
     | XORPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_XORPS (op1, op2))))
     | PAVGB (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PAVGB (op1, op2))))
     | PEXTRW (op1, op2, imm) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PEXTRW (op1, op2, imm))))
     | PINSRW (op1, op2, imm) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PINSRW (op1, op2, imm))))
     | PMAXSW (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PMAXSW (op1, op2))))
     | PMAXUB (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PMAXUB (op1, op2))))
     | PMINSW (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PMINSW (op1, op2))))
     | PMINUB (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PMINUB (op1, op2))))
     | PMOVMSKB (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PMOVMSKB (op1, op2))))
     | PSADBW (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PSADBW (op1, op2))))
     | PSHUFW (op1, op2, imm) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PSHUFW (op1, op2, imm))))
     | MASKMOVQ (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_MASKMOVQ (op1, op2))))
     | MOVNTPS (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVNTPS (op1, op2))))
     | MOVNTQ (op1, op2) ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_MOVNTQ (op1, op2))))
     | PREFETCHT0 op ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PREFETCHT0 op)))
     | PREFETCHT1 op ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PREFETCHT1 op)))
     | PREFETCHT2 op ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PREFETCHT2 op)))
     | PREFETCHNTA op ->
       inv_case_some case10
         (Obj.magic (pre, (X86_PARSER_ARG.S_PREFETCHNTA op)))
     | SFENCE ->
       inv_case_some case10 (Obj.magic (pre, X86_PARSER_ARG.S_SFENCE))
     | HLT -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_HLT))
     | IDIV (w, op1) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_IDIV (w, op1))))
     | IMUL (w, op1, opopt, iopt) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_IMUL (w, op1, opopt, iopt))))
     | IN (w, p) ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_IN (w, p))))
     | INC (w, op1) ->
       inv_case_some case4 (Obj.magic (pre, (X86_PARSER_ARG.I_INC (w, op1))))
     | INS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_INS b)))
     | INTn it ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_INTn it)))
     | INT -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_INT))
     | INTO -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_INTO))
     | INVD -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_INVD))
     | INVLPG op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_INVLPG op)))
     | IRET -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_IRET))
     | Jcc (ct, disp) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_Jcc (ct, disp))))
     | JCXZ b ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_JCXZ b)))
     | JMP (near, abs, op, sel) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_JMP (near, abs, op, sel))))
     | LAHF -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_LAHF))
     | LAR (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LAR (op1, op2))))
     | LDS (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LDS (op1, op2))))
     | LEA (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LEA (op1, op2))))
     | LEAVE -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_LEAVE))
     | LES (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LES (op1, op2))))
     | LFS (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LFS (op1, op2))))
     | LGDT op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LGDT op)))
     | LGS (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LGS (op1, op2))))
     | LIDT op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LIDT op)))
     | LLDT op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LLDT op)))
     | LMSW op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LMSW op)))
     | LODS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_LODS b)))
     | LOOP disp ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LOOP disp)))
     | LOOPZ disp ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LOOPZ disp)))
     | LOOPNZ disp ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LOOPNZ disp)))
     | LSL (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LSL (op1, op2))))
     | LSS (op1, op2) ->
       inv_case_some case1
         (Obj.magic (pre, (X86_PARSER_ARG.I_LSS (op1, op2))))
     | LTR op ->
       inv_case_some case1 (Obj.magic (pre, (X86_PARSER_ARG.I_LTR op)))
     | MOV (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOV (w, op1, op2))))
     | MOVCR (d, cr, r) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVCR (d, cr, r))))
     | MOVDR (d, cr, r) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVDR (d, cr, r))))
     | MOVSR (d, cr, r) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVSR (d, cr, r))))
     | MOVBE (op1, op2) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVBE (op1, op2))))
     | MOVS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_MOVS b)))
     | MOVSX (w, op1, op2) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVSX (w, op1, op2))))
     | MOVZX (w, op1, op2) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_MOVZX (w, op1, op2))))
     | MUL (w, op1) ->
       inv_case_some case5 (Obj.magic (pre, (X86_PARSER_ARG.I_MUL (w, op1))))
     | NEG (w, op) ->
       inv_case_some case4 (Obj.magic (pre, (X86_PARSER_ARG.I_NEG (w, op))))
     | NOP op ->
       inv_case_some case5 (Obj.magic (pre, (X86_PARSER_ARG.I_NOP op)))
     | NOT (w, op) ->
       inv_case_some case4 (Obj.magic (pre, (X86_PARSER_ARG.I_NOT (w, op))))
     | OR (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_OR (w, op1, op2))))
     | OUT (w, p) ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_OUT (w, p))))
     | OUTS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_OUTS b)))
     | POP op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_POP op)))
     | POPSR sr ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_POPSR sr)))
     | POPA -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_POPA))
     | POPF -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_POPF))
     | PUSH (w, op) ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_PUSH (w, op))))
     | PUSHSR sr ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_PUSHSR sr)))
     | PUSHA -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_PUSHA))
     | PUSHF -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_PUSHF))
     | RCL (w, op1, ri) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_RCL (w, op1, ri))))
     | RCR (w, op1, ri) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_RCR (w, op1, ri))))
     | RDMSR -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_RDMSR))
     | RDPMC -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_RDPMC))
     | RDTSC -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_RDTSC))
     | RDTSCP ->
       inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_RDTSCP))
     | RET (ss, disp) ->
       inv_case_some case3
         (Obj.magic (pre, (X86_PARSER_ARG.I_RET (ss, disp))))
     | ROL (w, op1, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_ROL (w, op1, ri))))
     | ROR (w, op1, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_ROR (w, op1, ri))))
     | RSM -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_RSM))
     | SAHF -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_SAHF))
     | SAR (w, op1, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_SAR (w, op1, ri))))
     | SBB (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_SBB (w, op1, op2))))
     | SCAS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_SCAS b)))
     | SETcc (ct, op) ->
       inv_case_some case2
         (Obj.magic (pre, (X86_PARSER_ARG.I_SETcc (ct, op))))
     | SGDT op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_SGDT op)))
     | SHL (w, op1, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_SHL (w, op1, ri))))
     | SHLD (op1, r, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_SHLD (op1, r, ri))))
     | SHR (w, op1, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_SHR (w, op1, ri))))
     | SHRD (op1, r, ri) ->
       inv_case_some case5
         (Obj.magic (pre, (X86_PARSER_ARG.I_SHRD (op1, r, ri))))
     | SIDT op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_SIDT op)))
     | SLDT op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_SLDT op)))
     | SMSW op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_SMSW op)))
     | STC -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_STC))
     | STD -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_STD))
     | STI -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_STI))
     | STOS b ->
       inv_case_some case3 (Obj.magic (pre, (X86_PARSER_ARG.I_STOS b)))
     | STR op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_STR op)))
     | SUB (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_SUB (w, op1, op2))))
     | TEST (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_TEST (w, op1, op2))))
     | UD2 -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_UD2))
     | VERR op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_VERR op)))
     | VERW op ->
       inv_case_some case2 (Obj.magic (pre, (X86_PARSER_ARG.I_VERW op)))
     | WBINVD ->
       inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_WBINVD))
     | WRMSR -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_WRMSR))
     | XADD (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_XADD (w, op1, op2))))
     | XCHG (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_XCHG (w, op1, op2))))
     | XLAT -> inv_case_some case0 (Obj.magic (pre, X86_PARSER_ARG.I_XLAT))
     | XOR (w, op1, op2) ->
       inv_case_some case4
         (Obj.magic (pre, (X86_PARSER_ARG.I_XOR (w, op1, op2)))))))
