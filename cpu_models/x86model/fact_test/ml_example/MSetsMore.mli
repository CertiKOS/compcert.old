open MSetInterface
open MSetProperties
open MSetWeakList

type __ = Obj.t

module WMoreProperties :
 functor (M:WSets) ->
 sig
  
 end

module MapSetGen :
 functor (M:WSets) ->
 functor (M':WSets) ->
 sig
  type proper_map = (M.elt -> M'.elt)

  val get_fun : proper_map -> M.elt -> M'.elt

  val map : proper_map -> M.t -> M'.t
 end

module MapSet :
 functor (M:WSets) ->
 sig
  type proper_map = (M.elt -> M.elt)

  val get_fun : proper_map -> M.elt -> M.elt

  val map : proper_map -> M.t -> M.t
 end

module ListPowerSet :
 functor (M:WSets) ->
 sig
  module MM :
   sig
    module Raw :
     sig
      type elt = M.t

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
      type t = M.t

      val eq_dec : t -> t -> bool
     end

    type elt = M.t

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
        val eqb : M.E.t -> M.E.t -> bool
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
      val eqb : M.E.t -> M.E.t -> bool
     end

    val coq_In_dec : M.elt -> M.t -> bool

    val of_list : M.elt list -> M.t

    val to_list : M.t -> M.elt list

    val fold_rec :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> __ -> 'a2) -> (M.elt ->
      'a1 -> M.t -> M.t -> __ -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_bis :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> (M.t -> M.t -> 'a1 -> __ -> 'a2
      -> 'a2) -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> __ -> 'a2 -> 'a2) -> 'a2

    val fold_rec_nodep :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> M.t -> 'a2 -> (M.elt -> 'a1 -> __ ->
      'a2 -> 'a2) -> 'a2

    val fold_rec_weak :
      (M.elt -> 'a1 -> 'a1) -> 'a1 -> (M.t -> M.t -> 'a1 -> __ -> 'a2 -> 'a2)
      -> 'a2 -> (M.elt -> 'a1 -> M.t -> __ -> 'a2 -> 'a2) -> M.t -> 'a2

    val fold_rel :
      (M.elt -> 'a1 -> 'a1) -> (M.elt -> 'a2 -> 'a2) -> 'a1 -> 'a2 -> M.t ->
      'a3 -> (M.elt -> 'a1 -> 'a2 -> __ -> 'a3 -> 'a3) -> 'a3

    val set_induction :
      (M.t -> __ -> 'a1) -> (M.t -> M.t -> 'a1 -> M.elt -> __ -> __ -> 'a1)
      -> M.t -> 'a1

    val set_induction_bis :
      (M.t -> M.t -> __ -> 'a1 -> 'a1) -> 'a1 -> (M.elt -> M.t -> __ -> 'a1
      -> 'a1) -> M.t -> 'a1

    val cardinal_inv_2 : M.t -> Big.big_int -> M.elt

    val cardinal_inv_2b : M.t -> M.elt
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
        val eqb : M.t -> M.t -> bool
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
      val eqb : M.t -> M.t -> bool
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

  val add_elm : M.elt -> MMF.proper_map

  val powerset_fold_op : M.elt -> MM.t -> MM.t

  val powerset : M.t -> MM.t
 end
