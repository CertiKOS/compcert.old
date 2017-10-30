open Datatypes

(** val nth_error : 'a1 list -> Big.big_int -> 'a1 option **)

let rec nth_error l n =
  Big.nat_case
    (fun _ ->
    match l with
    | [] -> None
    | x :: _ -> Some x)
    (fun n0 ->
    match l with
    | [] -> None
    | _ :: l0 -> nth_error l0 n0)
    n

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| [] -> []
| x :: l' -> app (rev l') (x :: [])

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| [] -> []
| x :: t -> app (f x) (flat_map f t)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | [] -> a0
  | b :: t -> fold_left f t (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| [] -> a0
| b :: t -> f b (fold_right f a0 t)

(** val list_prod : 'a1 list -> 'a2 list -> ('a1 * 'a2) list **)

let rec list_prod l l' =
  match l with
  | [] -> []
  | x :: t -> app (map (fun y -> (x, y)) l') (list_prod t l')
