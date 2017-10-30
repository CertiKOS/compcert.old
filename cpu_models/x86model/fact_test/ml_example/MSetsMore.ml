open MSetInterface
open MSetProperties
open MSetWeakList

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module WMoreProperties =
 functor (M:WSets) ->
 struct
  (** val add_transpose : __ **)

  let add_transpose =
    __

  (** val subset_empty_uniq : __ **)

  let subset_empty_uniq =
    __

  type disjoint = __

  (** val disjoint_spec : __ **)

  let disjoint_spec =
    __

  (** val disjoint_subset : __ **)

  let disjoint_subset =
    __

  (** val disjoint_symm : __ **)

  let disjoint_symm =
    __

  (** val disjoint_empty : __ **)

  let disjoint_empty =
    __

  (** val disjoint_singleton : __ **)

  let disjoint_singleton =
    __

  (** val inclA_subset : __ **)

  let inclA_subset =
    __

  (** val elements_app_subset1 : __ **)

  let elements_app_subset1 =
    __

  (** val elements_app_subset2 : __ **)

  let elements_app_subset2 =
    __

  (** val elements_app_disjoint : __ **)

  let elements_app_disjoint =
    __
 end

module MapSetGen =
 functor (M:WSets) ->
 functor (M':WSets) ->
 struct
  type proper_map = (M.elt -> M'.elt)

  (** val get_fun : proper_map -> M.elt -> M'.elt **)

  let get_fun m =
    m

  type eq_proper_map = __

  type injective = __

  (** val injective_eq : __ **)

  let injective_eq =
    __

  (** val injective_subset : __ **)

  let injective_subset =
    __

  (** val injective_empty : __ **)

  let injective_empty =
    __

  (** val map : proper_map -> M.t -> M'.t **)

  let map m s =
    M.fold (fun x s0 -> M'.add (get_fun m x) s0) s M'.empty

  (** val map_intro : __ **)

  let map_intro =
    __

  (** val map_elim : __ **)

  let map_elim =
    __

  (** val map_subset : __ **)

  let map_subset =
    __

  (** val map_union : __ **)

  let map_union =
    __

  (** val map_cardinal : __ **)

  let map_cardinal =
    __

  (** val map_equal : __ **)

  let map_equal =
    __

  (** val map_cardinal_le : __ **)

  let map_cardinal_le =
    __
 end

module MapSet =
 functor (M:WSets) ->
 MapSetGen(M)(M)

module ListPowerSet =
 functor (M:WSets) ->
 struct
  module MM = Make(M)

  module MMF = MapSet(MM)

  module P = WProperties(M)

  module PM = WMoreProperties(M)

  module PP = WProperties(MM)

  module PPM = WMoreProperties(MM)

  (** val add_elm : M.elt -> MMF.proper_map **)

  let add_elm x =
    M.add x

  (** val powerset_fold_op : M.elt -> MM.t -> MM.t **)

  let powerset_fold_op x ss =
    MM.union ss (MMF.map (add_elm x) ss)

  (** val powerset : M.t -> MM.t **)

  let powerset s =
    M.fold powerset_fold_op s (MM.singleton M.empty)
 end
