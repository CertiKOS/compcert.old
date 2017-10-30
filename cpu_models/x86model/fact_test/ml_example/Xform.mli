open Datatypes
open List0
open ParserArg

type __ = Obj.t

type xtype =
| Coq_xUnit_t
| Coq_xChar_t
| Coq_xVoid_t
| Coq_xPair_t of xtype * xtype
| Coq_xSum_t of xtype * xtype
| Coq_xList_t of xtype

type xt_interp = __

type xform =
| Xid
| Xzero
| Xcomp of xform * xform
| Xchar of X86_PARSER_ARG.char_p
| Xunit
| Xempty
| Xpair of xform * xform
| Xfst
| Xsnd
| Xinl
| Xinr
| Xmatch of xform * xform
| Xcons of xform * xform
| Xfoldr of xform * xform * xform

val xinterp : xform -> xt_interp -> xt_interp

val xcoerce : xform -> xform

val xchar : X86_PARSER_ARG.char_p -> xform

val xpair_fst : xform -> xform

val xmatch_inl : xform -> xform

val xmatch_empty : xform -> xform

val xmatch : xform -> xform -> xform

val xcomp_pair : xform -> xform -> xform -> xform

val xcomp_inl : xform -> xform

val xcomp_inr : xform -> xform

val xcomp_empty : xform -> xform

val xcomp_cons : xform -> xform -> xform -> xform

val xfoldr' : xform -> xform -> xform -> xform

val xfoldr : xform -> xform -> xform -> xform

val xcomp_r : xform -> xform -> xform

val xcomp : xform -> xform -> xform

val xcomp' : xform -> xform -> xform

val xopt : xform -> xform

val xmap : xform -> xform

val xmapenv : xform -> xform

val xcross : __ -> xform
