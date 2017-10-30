open Datatypes
open GrammarType
open List0
open Regexp
open Xform

type grammar =
| Eps
| Zero
| Char of char_p
| Any
| Cat of grammar * grammar
| Alt of grammar * grammar
| Star of grammar
| Map of (interp -> interp) * grammar

type fixfn = xt_interp -> interp

val re_and_fn : regexp -> fixfn -> regexp*fixfn

val split_grammar : grammar -> regexp*fixfn
