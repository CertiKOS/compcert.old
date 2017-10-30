open Datatypes
open List0
open OrdersAlt
open ParserArg
open Xform

type regexp =
| Coq_rEps
| Coq_rZero
| Coq_rChar of X86_PARSER_ARG.char_p
| Coq_rAny
| Coq_rCat of regexp * regexp
| Coq_rAlt of regexp * regexp
| Coq_rStar of regexp

val regexp_type : regexp -> xtype

val regexp_extract_nil : regexp -> xt_interp list

val compare_re : regexp -> regexp -> comparison

module REOrderedTypeAlt :
 sig
  type t = regexp

  val compare : regexp -> regexp -> comparison
 end

module REOrderedType :
 sig
  type t = REOrderedTypeAlt.t

  val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

  val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
 end
