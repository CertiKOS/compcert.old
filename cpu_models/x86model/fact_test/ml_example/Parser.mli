open Basics
open Coqlib
open Datatypes
open Grammar
open GrammarType
open List0
open MSetsMore
open Nat0
open RESet
open Regexp
open Specif
open Vector
open Xform

type __ = Obj.t

module RES :
 sig
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

      type triple = RawRESet.Raw.triple = { t_left : t; t_in : bool;
                                            t_right : t }

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

      type coq_R_min_elt = RawRESet.Raw.coq_R_min_elt =
      | R_min_elt_0 of tree
      | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
         * elt option * coq_R_min_elt

      type coq_R_max_elt = RawRESet.Raw.coq_R_max_elt =
      | R_max_elt_0 of tree
      | R_max_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_max_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
         * elt option * coq_R_max_elt

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

      type coq_R_bal = RawRESet.Raw.coq_R_bal =
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

      type coq_R_remove_min = RawRESet.Raw.coq_R_remove_min =
      | R_remove_min_0 of tree * elt * t
      | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
         * REOrderedTypeAlt.t * tree * (t * elt) * coq_R_remove_min * 
         t * elt

      type coq_R_merge = RawRESet.Raw.coq_R_merge =
      | R_merge_0 of tree * tree
      | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * elt

      type coq_R_concat = RawRESet.Raw.coq_R_concat =
      | R_concat_0 of tree * tree
      | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree
         * REOrderedTypeAlt.t * tree
      | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree
         * REOrderedTypeAlt.t * tree * Int.Z_as_Int.t * tree
         * REOrderedTypeAlt.t * tree * t * elt

      type coq_R_inter = RawRESet.Raw.coq_R_inter =
      | R_inter_0 of tree * tree
      | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * bool * t * tree * coq_R_inter * tree * coq_R_inter
      | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * bool * t * tree * coq_R_inter * tree * coq_R_inter

      type coq_R_diff = RawRESet.Raw.coq_R_diff =
      | R_diff_0 of tree * tree
      | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * bool * t * tree * coq_R_diff * tree * coq_R_diff
      | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * bool * t * tree * coq_R_diff * tree * coq_R_diff

      type coq_R_union = RawRESet.Raw.coq_R_union =
      | R_union_0 of tree * tree
      | R_union_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree
      | R_union_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
         * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * 
         t * bool * t * tree * coq_R_union * tree * coq_R_union
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

    type tree = RESet.RawRESet.Raw.tree =
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

    type enumeration = RESet.RawRESet.Raw.enumeration =
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

    type triple = RESet.RawRESet.Raw.triple = { t_left : t; t_in : bool;
                                                t_right : t }

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

    type coq_R_min_elt = RESet.RawRESet.Raw.coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree
    | R_min_elt_2 of tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * 
       tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * elt option
       * coq_R_min_elt

    type coq_R_max_elt = RESet.RawRESet.Raw.coq_R_max_elt =
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

    type coq_R_bal = RESet.RawRESet.Raw.coq_R_bal =
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

    type coq_R_remove_min = RESet.RawRESet.Raw.coq_R_remove_min =
    | R_remove_min_0 of tree * elt * t
    | R_remove_min_1 of tree * elt * t * Int.Z_as_Int.t * tree
       * REOrderedTypeAlt.t * tree * (t * elt) * coq_R_remove_min * t * 
       elt

    type coq_R_merge = RESet.RawRESet.Raw.coq_R_merge =
    | R_merge_0 of tree * tree
    | R_merge_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_merge_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       elt

    type coq_R_concat = RESet.RawRESet.Raw.coq_R_concat =
    | R_concat_0 of tree * tree
    | R_concat_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_concat_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       elt

    type coq_R_inter = RESet.RawRESet.Raw.coq_R_inter =
    | R_inter_0 of tree * tree
    | R_inter_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_inter_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter
    | R_inter_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_inter * tree * coq_R_inter

    type coq_R_diff = RESet.RawRESet.Raw.coq_R_diff =
    | R_diff_0 of tree * tree
    | R_diff_1 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree
    | R_diff_2 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff
    | R_diff_3 of tree * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t
       * tree * Int.Z_as_Int.t * tree * REOrderedTypeAlt.t * tree * t * 
       bool * t * tree * coq_R_diff * tree * coq_R_diff

    type coq_R_union = RESet.RawRESet.Raw.coq_R_union =
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

  val empty_xform : xtype -> rs_xf_pair

  val singleton_xform : regexp -> rs_xf_pair

  val create_xform :
    xtype -> Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform ->
    tree_xf_pair

  val find_xform : Raw.tree -> regexp -> xform

  val inject_xform_tree : Raw.tree -> Raw.tree -> xform

  val inject_xform : RawRESet.t -> RawRESet.t -> xform

  val equal_xform : RawRESet.t -> RawRESet.t -> xform

  type ctxt = RESet.ctxt =
  | Hole
  | LeftNode of Int.Z_as_Int.t * ctxt * REOrderedTypeAlt.t * Raw.tree
  | RightNode of Int.Z_as_Int.t * Raw.tree * REOrderedTypeAlt.t * ctxt

  val ctxt_rect :
    'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree
    -> 'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt ->
    'a1 -> 'a1) -> ctxt -> 'a1

  val ctxt_rec :
    'a1 -> (Int.Z_as_Int.t -> ctxt -> 'a1 -> REOrderedTypeAlt.t -> Raw.tree
    -> 'a1) -> (Int.Z_as_Int.t -> Raw.tree -> REOrderedTypeAlt.t -> ctxt ->
    'a1 -> 'a1) -> ctxt -> 'a1

  val fill : ctxt -> Raw.tree -> Raw.tree

  val fill_ctxt : ctxt -> ctxt -> ctxt

  val cast : 'a1 -> 'a2

  val find_subtree' : Raw.tree -> ctxt -> xform

  val find_subtree : Raw.tree -> Raw.tree -> ctxt -> xform

  val assert_false_xform :
    xtype -> Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform ->
    tree_xf_pair

  val bal_xform :
    xtype -> Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform ->
    tree_xf_pair

  val add_xform_tree :
    xtype -> regexp -> xform -> Raw.tree -> xform -> Raw.tree*xform

  val join_xform :
    xtype -> Raw.tree -> xform -> regexp -> xform -> Raw.tree -> xform ->
    Raw.tree*xform

  type triple_xform = RESet.triple_xform = { t_left : Raw.tree;
                                             t_left_xform : xform;
                                             t_in : xform option;
                                             t_right : Raw.tree;
                                             t_right_xform : xform }

  val t_left : xtype -> regexp -> triple_xform -> Raw.tree

  val t_left_xform : xtype -> regexp -> triple_xform -> xform

  val t_in : xtype -> regexp -> triple_xform -> xform option

  val t_right : xtype -> regexp -> triple_xform -> Raw.tree

  val t_right_xform : xtype -> regexp -> triple_xform -> xform

  val split_xform : xtype -> regexp -> Raw.tree -> xform -> triple_xform

  val union_xform_tree :
    xtype -> Raw.tree -> xform -> Raw.tree -> xform -> Raw.tree*xform

  val add_xform : xtype -> re_xf_pair -> rs_xf_pair -> rs_xf_pair

  val union_xform : xtype -> rs_xf_pair -> rs_xf_pair -> rs_xf_pair

  val fold_tree_xform :
    xtype -> (re_xf_pair -> 'a1 -> 'a1) -> Raw.tree -> xform -> 'a1 -> 'a1

  val fold_xform :
    xtype -> (re_xf_pair -> 'a1 -> 'a1) -> rs_xf_pair -> 'a1 -> 'a1

  val map_xform :
    xtype -> xtype -> (re_xf_pair -> re_xf_pair) -> rs_xf_pair -> rs_xf_pair

  val set_cat_re : RawRESet.t -> regexp -> RawRESet.t

  val simple_cat_re_xform : xtype -> rs_xf_pair -> regexp -> rs_xf_pair

  val cat_re_xform : xtype -> rs_xf_pair -> regexp -> rs_xf_pair
 end

type rs_xf_pair = RES.rs_xf_pair

type re_xf_pair = RES.re_xf_pair

val erase : rs_xf_pair -> RES.t

val nullable : regexp -> bool*xform

val pdrv : char_p -> regexp -> rs_xf_pair

val pdrv_rex : char_p -> re_xf_pair -> rs_xf_pair

val pdrv_set : char_p -> rs_xf_pair -> rs_xf_pair

val wpdrv : char_p list -> rs_xf_pair -> rs_xf_pair

val wpdrv_re_set : char_p list -> RES.t -> rs_xf_pair

module POW :
 sig
  module MM :
   sig
    module Raw :
     sig
      type elt = RES.t

      type t = elt list

      val empty : t

      val is_empty : t -> bool

      val mem : elt -> t -> bool

      val add : elt -> t -> t

      val singleton : elt -> t

      val remove : elt -> t -> t

      val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

      val union : t -> t -> t

      val diff : t -> t -> t

      val inter : t -> t -> t

      val subset : t -> t -> bool

      val equal : t -> t -> bool

      val filter : (elt -> bool) -> t -> t

      val for_all : (elt -> bool) -> t -> bool

      val exists_ : (elt -> bool) -> t -> bool

      val partition : (elt -> bool) -> t -> t * t

      val cardinal : t -> Big.big_int

      val elements : t -> elt list

      val choose : t -> elt option

      val isok : elt list -> bool
     end

    module E :
     sig
      type t = RES.t

      val eq_dec : t -> t -> bool
     end

    type elt = RES.t

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
   end

  module MMF :
   sig
    type proper_map = (MM.elt -> MM.elt)

    val get_fun : proper_map -> MM.elt -> MM.elt

    val map : proper_map -> MM.t -> MM.t
   end

  module P :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
       end

      module MSetLogicalFacts :
       sig
        
       end

      module MSetDecideAuxiliary :
       sig
        
       end

      module MSetDecideTestCases :
       sig
        
       end
     end

    module FM :
     sig
      val eqb : REOrderedTypeAlt.t -> REOrderedTypeAlt.t -> bool
     end

    val coq_In_dec : RES.elt -> RES.t -> bool

    val of_list : RES.elt list -> RES.t

    val to_list : RES.t -> RES.elt list

    val fold_rec :
      (RES.elt -> 'a1 -> 'a1) -> 'a1 -> RES.t -> (RES.t -> __ -> 'a2) ->
      (RES.elt -> 'a1 -> RES.t -> RES.t -> __ -> __ -> __ -> 'a2 -> 'a2) ->
      'a2

    val fold_rec_bis :
      (RES.elt -> 'a1 -> 'a1) -> 'a1 -> RES.t -> (RES.t -> RES.t -> 'a1 -> __
      -> 'a2 -> 'a2) -> 'a2 -> (RES.elt -> 'a1 -> RES.t -> __ -> __ -> 'a2 ->
      'a2) -> 'a2

    val fold_rec_nodep :
      (RES.elt -> 'a1 -> 'a1) -> 'a1 -> RES.t -> 'a2 -> (RES.elt -> 'a1 -> __
      -> 'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (RES.elt -> 'a1 -> 'a1) -> 'a1 -> (RES.t -> RES.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (RES.elt -> 'a1 -> RES.t -> __ -> 'a2 -> 'a2) ->
      RES.t -> 'a2

    val fold_rel :
      (RES.elt -> 'a1 -> 'a1) -> (RES.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 ->
      RES.t -> 'a3 -> (RES.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (RES.t -> __ -> 'a1) -> (RES.t -> RES.t -> 'a1 -> RES.elt -> __ -> __
      -> 'a1) -> RES.t -> 'a1

    val set_induction_bis :
      (RES.t -> RES.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (RES.elt -> RES.t -> __
      -> 'a1 -> 'a1) -> RES.t -> 'a1

    val cardinal_inv_2 : RES.t -> Big.big_int -> RES.elt

    val cardinal_inv_2b : RES.t -> RES.elt
   end

  module PM :
   sig
    
   end

  module PP :
   sig
    module Dec :
     sig
      module F :
       sig
        val eqb : RES.t -> RES.t -> bool
       end

      module MSetLogicalFacts :
       sig
        
       end

      module MSetDecideAuxiliary :
       sig
        
       end

      module MSetDecideTestCases :
       sig
        
       end
     end

    module FM :
     sig
      val eqb : RES.t -> RES.t -> bool
     end

    val coq_In_dec : MM.elt -> MM.t -> bool

    val of_list : MM.elt list -> MM.t

    val to_list : MM.t -> MM.elt list

    val fold_rec :
      (MM.elt -> 'a1 -> 'a1) -> 'a1 -> MM.t -> (MM.t -> __ -> 'a2) -> (MM.elt
      -> 'a1 -> MM.t -> MM.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (MM.elt -> 'a1 -> 'a1) -> 'a1 -> MM.t -> (MM.t -> MM.t -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2 -> (MM.elt -> 'a1 -> MM.t -> __ -> __ -> 'a2 -> 'a2)
      -> 'a2

    val fold_rec_nodep :
      (MM.elt -> 'a1 -> 'a1) -> 'a1 -> MM.t -> 'a2 -> (MM.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (MM.elt -> 'a1 -> 'a1) -> 'a1 -> (MM.t -> MM.t -> 'a1 -> __ -> 'a2 ->
      'a2) -> 'a2 -> (MM.elt -> 'a1 -> MM.t -> __ -> 'a2 -> 'a2) -> MM.t ->
      'a2

    val fold_rel :
      (MM.elt -> 'a1 -> 'a1) -> (MM.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> MM.t
      -> 'a3 -> (MM.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (MM.t -> __ -> 'a1) -> (MM.t -> MM.t -> 'a1 -> MM.elt -> __ -> __ ->
      'a1) -> MM.t -> 'a1

    val set_induction_bis :
      (MM.t -> MM.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (MM.elt -> MM.t -> __ ->
      'a1 -> 'a1) -> MM.t -> 'a1

    val cardinal_inv_2 : MM.t -> Big.big_int -> MM.elt

    val cardinal_inv_2b : MM.t -> MM.elt
   end

  module PPM :
   sig
    
   end

  val add_elm : RES.elt -> MMF.proper_map

  val powerset_fold_op : RES.elt -> MM.t -> MM.t

  val powerset : RES.t -> MM.t
 end

module RESetSet :
 sig
  module Raw :
   sig
    type elt = RES.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> Big.big_int

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = RES.t

    val eq_dec : t -> t -> bool
   end

  type elt = RES.t

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

  val get_element : Big.big_int -> t -> elt option

  val get_index : elt -> t -> Big.big_int option

  val add_set : t -> t -> t
 end

module RESS :
 sig
  module Raw :
   sig
    type elt = RES.t

    type t = elt list

    val empty : t

    val is_empty : t -> bool

    val mem : elt -> t -> bool

    val add : elt -> t -> t

    val singleton : elt -> t

    val remove : elt -> t -> t

    val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val subset : t -> t -> bool

    val equal : t -> t -> bool

    val filter : (elt -> bool) -> t -> t

    val for_all : (elt -> bool) -> t -> bool

    val exists_ : (elt -> bool) -> t -> bool

    val partition : (elt -> bool) -> t -> t * t

    val cardinal : t -> Big.big_int

    val elements : t -> elt list

    val choose : t -> elt option

    val isok : elt list -> bool
   end

  module E :
   sig
    type t = RES.t

    val eq_dec : t -> t -> bool
   end

  type elt = RES.t

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

  val get_element : Big.big_int -> t -> elt option

  val get_index : elt -> t -> Big.big_int option

  val add_set : t -> t -> t
 end

type state = RES.t

type states = RESS.t

type wf_state = state

type wf_states = states

val cardinal_wfs : wf_states -> Big.big_int

type wfs_xf_pair = wf_state*xform

val wpdrv_wf : char_p list -> wf_state -> wfs_xf_pair

val add_wfs : wf_state -> wf_states -> wf_states

val get_index_wfs : wf_state -> wf_states -> Big.big_int option

val get_index_wfs2 : wf_state -> wf_states -> Big.big_int option

val get_element_wfs : Big.big_int -> wf_states -> RESS.elt option

val get_element_wfs2 : Big.big_int -> wf_states -> wf_state option

val get_state : Big.big_int -> wf_states -> RES.t

type entry_t = { next_state : Big.big_int; next_xform : xform }

val next_state : regexp -> Big.big_int -> wf_states -> entry_t -> Big.big_int

val next_xform : regexp -> Big.big_int -> wf_states -> entry_t -> xform

type entries_t = entry_t list

type transition_t = { row_num : Big.big_int; row_entries : entries_t;
                      row_nils : xt_interp list }

val row_num : regexp -> wf_states -> transition_t -> Big.big_int

val row_entries : regexp -> wf_states -> transition_t -> entries_t

val row_nils : regexp -> wf_states -> transition_t -> xt_interp list

type transitions_t = transition_t list

type coq_DFA = { dfa_num_states : Big.big_int; dfa_states : wf_states;
                 dfa_transition : transitions_t }

val dfa_num_states : regexp -> coq_DFA -> Big.big_int

val dfa_states : regexp -> coq_DFA -> wf_states

val dfa_transition : regexp -> coq_DFA -> transitions_t

type ventries_t = entry_t vector

type vtransition_t = { vrow_num : Big.big_int; vrow_entries : ventries_t;
                       vrow_nils : xt_interp list }

val vrow_entries : regexp -> wf_states -> vtransition_t -> ventries_t

val vrow_nils : regexp -> wf_states -> vtransition_t -> xt_interp list

type vtransitions_t = vtransition_t vector

type vDFA = { vdfa_num_states : Big.big_int; vdfa_states : wf_states;
              vdfa_transition : vtransitions_t }

val vdfa_states : regexp -> vDFA -> wf_states

val vdfa_transition : regexp -> vDFA -> vtransitions_t

val transition_to_vtransition : wf_states -> transition_t -> vtransition_t

val dfa_to_vdfa : coq_DFA -> vDFA

val gen_backward_xform : wf_state -> wf_states -> Big.big_int -> xform

type gen_row_ret_t = wf_states*(entries_t*__)

val gen_row' :
  wf_state -> Big.big_int -> wf_states -> token_id -> gen_row_ret_t

val gen_row : wf_state -> wf_states -> gen_row_ret_t

val coerce_entry : entry_t -> entry_t

val coerce_nils : xt_interp -> xt_interp

val coerce_transitions :
  wf_states -> wf_states -> transitions_t -> transitions_t

val cons_transition : Big.big_int -> wf_states -> entries_t -> transition_t

val build_table_func :
  (wf_states*(transitions_t*Big.big_int)) -> wf_states*transitions_t

val build_table :
  wf_states -> transitions_t -> Big.big_int -> wf_states*transitions_t

val ini_state : regexp -> wf_state

val ini_states : regexp -> wf_states

val build_transition_table : regexp -> wf_states*transitions_t

val build_dfa : regexp -> coq_DFA

val build_vdfa : regexp -> vDFA

val coerce_dom : (xt_interp -> 'a1) -> xt_interp -> 'a1

type naiveParserState = { rx_nps : rs_xf_pair;
                          fixup_nps : (xt_interp -> interp) }

val rx_nps : xtype -> coq_type -> naiveParserState -> rs_xf_pair

val fixup_nps : xtype -> coq_type -> naiveParserState -> xt_interp -> interp

val naive_parse_token :
  naiveParserState -> token_id -> naiveParserState * interp list

val initial_naive_parser_state : grammar -> naiveParserState

type re_set_fixfn = xt_interp -> __ list

type instParserState = { dfa_ps : coq_DFA; row_ps : Big.big_int;
                         fixup_ps : re_set_fixfn }

val dfa_ps : coq_type -> regexp -> instParserState -> coq_DFA

val row_ps : coq_type -> regexp -> instParserState -> Big.big_int

val fixup_ps : coq_type -> regexp -> instParserState -> re_set_fixfn

type dfa_builder_tp = regexp -> coq_DFA

type wf_dfa_builder = dfa_builder_tp

val build_dfa_wf_builder : wf_dfa_builder

val coerce_dfa : coq_DFA -> coq_DFA

val initial_parser_state' : wf_dfa_builder -> grammar -> instParserState

val initial_parser_state : grammar -> instParserState

val coerce : 'a1 -> 'a2

val nth_error2 : 'a1 list -> Big.big_int -> 'a1 option

val parse_token : instParserState -> token_id -> instParserState * interp list

val ps_extract_nil : instParserState -> __ list

val parse_tokens :
  instParserState -> token_id list -> (token_id
  list * instParserState) * interp list

type vinstParserState = { vdfa_ps : vDFA; vrow_ps : Big.big_int;
                          vfixup_ps : re_set_fixfn }

val vdfa_ps : coq_type -> regexp -> vinstParserState -> vDFA

val vrow_ps : coq_type -> regexp -> vinstParserState -> Big.big_int

val vfixup_ps : coq_type -> regexp -> vinstParserState -> re_set_fixfn

type vdfa_builder_tp = regexp -> vDFA

type wf_vdfa_builder = vdfa_builder_tp

val build_vdfa_wf_builder : wf_vdfa_builder

val vinitial_parser_state' : wf_vdfa_builder -> grammar -> vinstParserState

val vinitial_parser_state : grammar -> vinstParserState

val flat_map' : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val compose_flat_map :
  ('a1 -> 'a2 list) -> ('a3 -> 'a1 list) -> 'a3 -> 'a2 list

val vparse_token :
  vinstParserState -> token_id -> vinstParserState*xt_interp list

val vps_extract_nil : vinstParserState -> __ list

val vparse_tokens :
  coq_type -> regexp -> vinstParserState -> token_id list -> (token_id
  list * vinstParserState) * interp list
