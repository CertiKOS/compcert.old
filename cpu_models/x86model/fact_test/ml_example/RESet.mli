open Datatypes
open List0
open MSetAVL
open Regexp
open Xform

type __ = Obj.t

module type RESETXFORM =
 sig
  type elt = REOrderedTypeAlt.t

  type t

  val empty : t

  val is_empty : t -> bool

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val singleton : elt -> t

  val remove : elt -> t -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val filter : (elt -> bool) -> t -> t

  val partition : (elt -> bool) -> t -> t * t

  val cardinal : t -> Big.big_int

  val elements : t -> elt list

  val choose : t -> elt option

  val eq_dec : t -> t -> bool

  val re_set_type : t -> xtype

  type rs_xf_pair = t*xform

  type re_xf_pair = regexp*xform

  val union_xform : xtype -> rs_xf_pair -> rs_xf_pair -> rs_xf_pair

  val empty_xform : xtype -> rs_xf_pair

  val singleton_xform : regexp -> rs_xf_pair

  val add_xform : xtype -> re_xf_pair -> rs_xf_pair -> rs_xf_pair

  val fold_xform :
    xtype -> (re_xf_pair -> 'a1 -> 'a1) -> rs_xf_pair -> 'a1 -> 'a1

  val set_cat_re : t -> regexp -> t

  val cat_re_xform : xtype -> rs_xf_pair -> regexp -> rs_xf_pair

  val equal_xform : t -> t -> xform

  val re_set_extract_nil : t -> xt_interp list
 end

module RawRESet :
 sig
  module Raw :
   sig
    type elt = REOrderedTypeAlt.t

    type tree =
    | Leaf
    | Node of Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : REOrderedTypeAlt.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux :
      REOrderedTypeAlt.t list -> tree -> REOrderedTypeAlt.t list

    val elements : tree -> REOrderedTypeAlt.t list

    val rev_elements_aux :
      REOrderedTypeAlt.t list -> tree -> REOrderedTypeAlt.t list

    val rev_elements : tree -> REOrderedTypeAlt.t list

    val cardinal : tree -> Big.big_int

    val maxdepth : tree -> Big.big_int

    val mindepth : tree -> Big.big_int

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      REOrderedTypeAlt.t -> (enumeration -> comparison) -> enumeration ->
      comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> REOrderedTypeAlt.t -> tree -> bool

    val subsetr : (tree -> bool) -> REOrderedTypeAlt.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val height : t -> Int.Z_as_Int.t

    val singleton : REOrderedTypeAlt.t -> tree

    val create : t -> REOrderedTypeAlt.t -> t -> tree

    val assert_false : t -> REOrderedTypeAlt.t -> t -> tree

    val bal : t -> REOrderedTypeAlt.t -> t -> tree

    val add : REOrderedTypeAlt.t -> tree -> tree

    val join : tree -> elt -> t -> t

    val remove_min : tree -> elt -> t -> t * elt

    val merge : tree -> tree -> tree

    val remove : REOrderedTypeAlt.t -> tree -> tree

    val concat : tree -> tree -> tree

    type triple = { t_left : t; t_in : bool; t_right : t }

    val t_left : triple -> t

    val t_in : triple -> bool

    val t_right : triple -> t

    val split : REOrderedTypeAlt.t -> tree -> triple

    val inter : tree -> tree -> tree

    val diff : tree -> tree -> tree

    val union : tree -> tree -> tree

    val filter : (elt -> bool) -> tree -> tree

    val partition : (elt -> bool) -> t -> t * t

    val ltb_tree : REOrderedTypeAlt.t -> tree -> bool

    val gtb_tree : REOrderedTypeAlt.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = REOrderedTypeAlt.t

          val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

          val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
         end

        module TO :
         sig
          type t = REOrderedTypeAlt.t

          val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

          val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
         end
       end

      val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

      val lt_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

      val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
    | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * 
       tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * elt option
       * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
    | R_max_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * 
       tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * elt option
       * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = REOrderedTypeAlt.t

            val compare :
              REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

            val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
           end

          module TO :
           sig
            type t = REOrderedTypeAlt.t

            val compare :
              REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

            val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
           end
         end

        val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

        val lt_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

        val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    type coq_R_bal =
    | R_bal_0 of t * REOrderedTypeAlt.t * t
    | R_bal_1 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_2 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_3 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_4 of t * REOrderedTypeAlt.t * t
    | R_bal_5 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_6 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_7 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree
    | R_bal_8 of t * REOrderedTypeAlt.t * t

    type coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree * (t * elt) * coq_R_remove_min * t * 
       elt

    type coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       elt

    type coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       elt

    type coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union =
    | R_union_0 of tree * tree
    | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_union * tree * coq_R_union
   end

  module E :
   sig
    type t = REOrderedTypeAlt.t

    val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

    val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
   end

  type elt = REOrderedTypeAlt.t

  type t_ =
    Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> Big.big_int

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option
 end

module Raw :
 sig
  type elt = REOrderedTypeAlt.t

  type tree = RawRESet.Raw.tree =
  | Leaf
  | Node of Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree

  val empty : tree

  val is_empty : tree -> bool

  val mem : REOrderedTypeAlt.t -> tree -> bool

  val min_elt : tree -> elt option

  val max_elt : tree -> elt option

  val choose : tree -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

  val elements_aux :
    REOrderedTypeAlt.t list -> tree -> REOrderedTypeAlt.t list

  val elements : tree -> REOrderedTypeAlt.t list

  val rev_elements_aux :
    REOrderedTypeAlt.t list -> tree -> REOrderedTypeAlt.t list

  val rev_elements : tree -> REOrderedTypeAlt.t list

  val cardinal : tree -> Big.big_int

  val maxdepth : tree -> Big.big_int

  val mindepth : tree -> Big.big_int

  val for_all : (elt -> bool) -> tree -> bool

  val exists_ : (elt -> bool) -> tree -> bool

  type enumeration = RawRESet.Raw.enumeration =
  | End
  | More of elt * tree * enumeration

  val cons : tree -> enumeration -> enumeration

  val compare_more :
    REOrderedTypeAlt.t -> (enumeration -> comparison) -> enumeration ->
    comparison

  val compare_cont :
    tree -> (enumeration -> comparison) -> enumeration -> comparison

  val compare_end : enumeration -> comparison

  val compare : tree -> tree -> comparison

  val equal : tree -> tree -> bool

  val subsetl : (tree -> bool) -> REOrderedTypeAlt.t -> tree -> bool

  val subsetr : (tree -> bool) -> REOrderedTypeAlt.t -> tree -> bool

  val subset : tree -> tree -> bool

  type t = tree

  val height : t -> Int.Z_as_Int.t

  val singleton : REOrderedTypeAlt.t -> tree

  val create : t -> REOrderedTypeAlt.t -> t -> tree

  val assert_false : t -> REOrderedTypeAlt.t -> t -> tree

  val bal : t -> REOrderedTypeAlt.t -> t -> tree

  val add : REOrderedTypeAlt.t -> tree -> tree

  val join : tree -> elt -> t -> t

  val remove_min : tree -> elt -> t -> t * elt

  val merge : tree -> tree -> tree

  val remove : REOrderedTypeAlt.t -> tree -> tree

  val concat : tree -> tree -> tree

  type triple = RawRESet.Raw.triple = { t_left : t; t_in : bool; t_right : t }

  val t_left : triple -> t

  val t_in : triple -> bool

  val t_right : triple -> t

  val split : REOrderedTypeAlt.t -> tree -> triple

  val inter : tree -> tree -> tree

  val diff : tree -> tree -> tree

  val union : tree -> tree -> tree

  val filter : (elt -> bool) -> tree -> tree

  val partition : (elt -> bool) -> t -> t * t

  val ltb_tree : REOrderedTypeAlt.t -> tree -> bool

  val gtb_tree : REOrderedTypeAlt.t -> tree -> bool

  val isok : tree -> bool

  module MX :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = REOrderedTypeAlt.t

        val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

        val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
       end

      module TO :
       sig
        type t = REOrderedTypeAlt.t

        val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

        val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
       end
     end

    val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

    val lt_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

    val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
   end

  type coq_R_min_elt = RawRESet.Raw.coq_R_min_elt =
  | R_min_elt_0 of tree
  | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
  | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * 
     tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * elt option
     * coq_R_min_elt

  type coq_R_max_elt = RawRESet.Raw.coq_R_max_elt =
  | R_max_elt_0 of tree
  | R_max_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
  | R_max_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * 
     tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * elt option
     * coq_R_max_elt

  module L :
   sig
    module MO :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = REOrderedTypeAlt.t

          val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

          val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
         end

        module TO :
         sig
          type t = REOrderedTypeAlt.t

          val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

          val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
         end
       end

      val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

      val lt_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool

      val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
     end
   end

  val flatten_e : enumeration -> elt list

  type coq_R_bal = RawRESet.Raw.coq_R_bal =
  | R_bal_0 of t * REOrderedTypeAlt.t * t
  | R_bal_1 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree
  | R_bal_2 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree
  | R_bal_3 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_bal_4 of t * REOrderedTypeAlt.t * t
  | R_bal_5 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree
  | R_bal_6 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree
  | R_bal_7 of t * REOrderedTypeAlt.t * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_bal_8 of t * REOrderedTypeAlt.t * t

  type coq_R_remove_min = RawRESet.Raw.coq_R_remove_min =
  | R_remove_min_0 of tree * elt * t
  | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
     * REOrderedTypeAlt.t * tree * (t * elt) * coq_R_remove_min * t * 
     elt

  type coq_R_merge = RawRESet.Raw.coq_R_merge =
  | R_merge_0 of tree * tree
  | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     elt

  type coq_R_concat = RawRESet.Raw.coq_R_concat =
  | R_concat_0 of tree * tree
  | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     elt

  type coq_R_inter = RawRESet.Raw.coq_R_inter =
  | R_inter_0 of tree * tree
  | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     bool * t * tree * coq_R_inter * tree * coq_R_inter
  | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     bool * t * tree * coq_R_inter * tree * coq_R_inter

  type coq_R_diff = RawRESet.Raw.coq_R_diff =
  | R_diff_0 of tree * tree
  | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     bool * t * tree * coq_R_diff * tree * coq_R_diff
  | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     bool * t * tree * coq_R_diff * tree * coq_R_diff

  type coq_R_union = RawRESet.Raw.coq_R_union =
  | R_union_0 of tree * tree
  | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree
  | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
     * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
     bool * t * tree * coq_R_union * tree * coq_R_union
 end

module E :
 sig
  type t = REOrderedTypeAlt.t

  val compare : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> comparison

  val eq_dec : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
 end

type elt = REOrderedTypeAlt.t

type t_ =
  Raw.t
  (* singleton inductive, whose constructor was Mkt *)

val this : t_ -> Raw.t

type t = t_

val mem : elt -> t -> bool

val add : elt -> t -> t

val remove : elt -> t -> t

val singleton : elt -> t

val union : t -> t -> t

val inter : t -> t -> t

val diff : t -> t -> t

val equal : t -> t -> bool

val subset : t -> t -> bool

val empty : t

val is_empty : t -> bool

val elements : t -> elt list

val choose : t -> elt option

val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

val cardinal : t -> Big.big_int

val filter : (elt -> bool) -> t -> t

val for_all : (elt -> bool) -> t -> bool

val exists_ : (elt -> bool) -> t -> bool

val partition : (elt -> bool) -> t -> t * t

val eq_dec : t -> t -> bool

val compare : t -> t -> comparison

val min_elt : t -> elt option

val max_elt : t -> elt option

type re_xf_pair = regexp*xform

val tree_to_regexp : Raw.tree -> regexp

val tree_type : Raw.tree -> xtype

type tree_xf_pair = Raw.tree*xform

val re_set_type : t -> xtype

type rs_xf_pair = t*xform

val tree_extract_nil : Raw.tree -> xt_interp list

val re_set_extract_nil : t -> xt_interp list

val empty_xform : __ -> rs_xf_pair

val singleton_xform : regexp -> rs_xf_pair

val create_xform :
  Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair

val find_xform : Raw.tree -> regexp -> xform

val inject_xform_tree : Raw.tree -> Raw.tree -> xform

val inject_xform : RawRESet.t -> RawRESet.t -> xform

val equal_xform : RawRESet.t -> RawRESet.t -> xform

type ctxt =
| Hole
| LeftNode of Int.Z_as_Int.t * ctxt * REOrderedTypeAlt.t * Raw.tree
| RightNode of Int.Z_as_Int.t * Raw.tree * REOrderedTypeAlt.t * ctxt

val ctxt_rect :
  'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree ->
  'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt -> 'a1 ->
  'a1) -> ctxt -> 'a1

val ctxt_rec :
  'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree ->
  'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt -> 'a1 ->
  'a1) -> ctxt -> 'a1

val fill : ctxt -> Raw.tree -> Raw.tree

val fill_ctxt : ctxt -> ctxt -> ctxt

val cast : 'a1 -> 'a2

val find_subtree' : Raw.tree -> ctxt -> xform

val find_subtree : Raw.tree -> Raw.tree -> ctxt -> xform

val assert_false_xform :
  Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair

val bal_xform :
  Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> tree_xf_pair

val add_xform_tree : regexp -> xform -> Raw.tree -> xform -> Raw.tree*xform

val join_xform :
  Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform -> Raw.tree*xform

type triple_xform = { t_left : Raw.tree; t_left_xform : xform;
                      t_in : xform option; t_right : Raw.tree;
                      t_right_xform : xform }

val t_left : xtype -> regexp -> triple_xform -> Raw.tree

val t_left_xform : xtype -> regexp -> triple_xform -> xform

val t_in : xtype -> regexp -> triple_xform -> xform option

val t_right : xtype -> regexp -> triple_xform -> Raw.tree

val t_right_xform : xtype -> regexp -> triple_xform -> xform

val split_xform : regexp -> Raw.tree -> xform -> triple_xform

val union_xform_tree :
  Raw.tree -> xform -> Raw.tree -> xform -> Raw.tree*xform

val add_xform : re_xf_pair -> rs_xf_pair -> rs_xf_pair

val union_xform : rs_xf_pair -> rs_xf_pair -> rs_xf_pair

val fold_tree_xform :
  (re_xf_pair -> 'a1 -> 'a1) -> Raw.tree -> xform -> 'a1 -> 'a1

val fold_xform : (re_xf_pair -> 'a1 -> 'a1) -> rs_xf_pair -> 'a1 -> 'a1

val map_xform : (re_xf_pair -> re_xf_pair) -> rs_xf_pair -> rs_xf_pair

val set_cat_re : RawRESet.t -> regexp -> RawRESet.t

val simple_cat_re_xform : rs_xf_pair -> regexp -> rs_xf_pair

val cat_re_xform : rs_xf_pair -> regexp -> rs_xf_pair
