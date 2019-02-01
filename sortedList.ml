module type SL = sig
  type elt
  type t = L of elt list

  val empty : t
  val singleton : elt -> t
  val of_list : elt list -> t
  val to_list : t -> elt list
  val init : (int -> elt) -> int -> t
    
  val mem : elt -> t -> bool
  val hd : t -> elt
  val tl : t -> t
  val length : t -> int

  val partition : (elt -> bool) -> t -> t * t
  val filter : (elt -> bool) -> t -> t
  val uniq : t -> t
  val merge : t -> t -> t
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  
  val fold_left : ('a -> elt -> 'a) -> 'a -> t -> 'a
  val fold_right : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val map : (elt -> 'a) -> t -> 'a list
  val rev_map : (elt -> 'a) -> t -> 'a list
  val iter : (elt -> unit) -> t -> unit
end

module Make (Ord : Set.OrderedType) =
struct
  type elt = Ord.t
  type t = L of elt list

  (* construction *)
        
  let empty = L []
      
  let singleton e = L [e]

  let of_list l = L (List.sort Ord.compare l)

  let to_list (L l) = l

  let init f n =
    let rec init_list i acc =
      if i = 0 then
        acc
      else
        init_list (i - 1) (f (i - 1) :: acc)
    in
    L (List.sort Ord.compare (init_list n []))

  (* basic operations *)

  let mem x (L l) = List.mem x l

  let hd (L l) = List.hd l

  let tl (L l) = L(List.tl l)
  
  let length (L l) = List.length l

  (* splitting, filtering, and joining *)

  let partition f (L l) =
    let a, b = List.partition f l in
    (L a, L b)

  let filter f (L l) = L (List.filter f l)

  let uniq (L l) =
    let rec uniq_list l acc =
      match l with
      | x :: ((y :: _) as l') ->
        if Ord.compare x y = 0 then
          uniq_list l' acc
        else
          uniq_list l' (x :: acc)
      | [x] ->
        uniq_list [] (x :: acc)
      | [] -> List.rev acc
    in
    L (uniq_list l [])

  (** Merge two sorted list idempodently, resulting in sorted list with unique values. *)
  let merge (L l1) (L l2) =
    let rec merge_lists l1 l2 =
      match l1, l2 with
      | _, [] -> l1
      | [], _ ->l2
      | x :: l1', y :: l2' -> 
        let c = Ord.compare x y in
        if c = 0 then
          x :: (merge_lists l1' l2')
        else if c < 0 then
          x :: (merge_lists l1' l2)
        else
          y :: (merge_lists l1 l2')
    in
    L (merge_lists l1 l2)

  let for_all f (L l) = List.for_all f l
  
  let exists f (L l) = List.exists f l

  (* iteration *)
  
  let fold_left f acc (L l) = List.fold_left f acc l

  let fold_right f (L l) acc = List.fold_right f l acc
  
  let map f (L l) = List.map f l
      
  let rev_map f (L l) = List.rev_map f l

  let iter f (L l) = List.iter f l
end
