open BiGrammar
open Datatypes
open GrammarType
open ParserArg
open X86BG_ins
open X86Syntax

val lock_b : bigrammar

val rep_or_repn_b : bigrammar

val rep_b : bigrammar

val segment_override_b : bigrammar

val op_s : char list

val op_override_b : bigrammar

val prefix_grammar_rep : bigrammar

val prefix_grammar_rep_or_repn : bigrammar

val prefix_grammar_lock_with_op_override : bigrammar

val prefix_grammar_lock_no_op_override : bigrammar

val prefix_grammar_seg_with_op_override : bigrammar

val prefix_grammar_seg_op_override : bigrammar

val prefix_grammar_only_seg_override : bigrammar

val i_instr1_b : bigrammar

val i_instr2_b : bigrammar

val i_instr3_b : bigrammar

val i_instr4_b : bigrammar

val from_instr5' : (prefix * X86_PARSER_ARG.i_instr5) -> interp option

val i_instr5_b : bigrammar

val i_instr6_b : bigrammar

val f_instr1_b : bigrammar

val f_instr2_b : bigrammar

val m_instr_b : bigrammar

val s_instr1_b : bigrammar

val s_instr2_b : bigrammar

val instr_bigrammar : bigrammar
