open Datatypes
open Grammar
open GrammarType
open Monad

type bigrammar =
| Eps
| Zero
| Char of char_p
| Any
| Cat of bigrammar * bigrammar
| Alt of bigrammar * bigrammar
| Star of bigrammar
| Map of ((interp -> interp) * (interp -> interp option)) * bigrammar

val pretty_print : bigrammar -> interp -> char_p list option

val empty : bigrammar

val map :
  bigrammar -> ((interp -> interp) * (interp -> interp option)) -> bigrammar

val seq : bigrammar -> bigrammar -> bigrammar

val alt : bigrammar -> bigrammar -> bigrammar

type index = Big.big_int

type bgr_tree =
| BLeaf of index * bigrammar * (interp -> interp)
| BNode of index * bgr_tree * bgr_tree

val comb_bigrammar : bgr_tree -> bigrammar

val comb_map : bgr_tree -> interp -> interp

type tmember =
| MLeaf
| MLTree of tmember
| MRTree of tmember

val inv_case : tmember -> interp -> interp

val inv_case_some : tmember -> interp -> interp option

val perm2 : bigrammar -> bigrammar -> bigrammar

val option_perm : bigrammar -> bigrammar

val option_perm2 : bigrammar -> bigrammar -> bigrammar

val option_perm3 : bigrammar -> bigrammar -> bigrammar -> bigrammar

val option_perm2_variation : bigrammar -> bigrammar -> bigrammar

val option_perm3_variation : bigrammar -> bigrammar -> bigrammar -> bigrammar

val bigrammar_to_grammar : bigrammar -> grammar
