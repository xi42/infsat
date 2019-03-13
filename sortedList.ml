module type SL = sig
  type elt
  type t = L of elt list

  val empty : t
  val singleton : elt -> t
  val of_list : elt list -> t
  val to_list : t -> elt list
  val to_ilist : t -> (int * elt) list
  val init : (int -> elt) -> int -> t
    
  val mem : elt -> t -> bool
  val hd : t -> elt
  val hd_option : t -> elt option
  val hd_tl_option : t -> (elt * t) option
  val tl : t -> t
  val length : t -> int
  val is_empty : t -> bool
  val sublist : t -> t -> bool
  
  val partition : (elt -> bool) -> t -> t * t
  val filter : (elt -> bool) -> t -> t
  val uniq : t -> t
  val merge_custom : (elt -> elt -> elt) -> t -> t -> t
  val merge : t -> t -> t
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  
  val fold_left : ('a -> elt -> 'a) -> 'a -> t -> 'a
  val fold_left_short_circuit : 'a -> t -> 'a -> ('a -> elt -> 'a) -> 'a
  val fold_right : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val map : (elt -> 'a) -> t -> 'a list
  val map_monotonic : (elt -> elt) -> t -> t
  val rev_map : (elt -> 'a) -> t -> 'a list
  val iter : (elt -> unit) -> t -> unit
  val compare_custom : (elt -> elt -> int) -> t -> t -> int
  val compare : t -> t -> int
  val equal_custom : (elt -> elt -> int) -> t -> t -> bool
  val equal : t -> t -> bool

  val to_string : (elt -> string) -> t -> string
end

module Make (Ord : Set.OrderedType) =
struct
  type elt = Ord.t
  type t = L of elt list

  (* construction *)
        
  let empty = L []
      
  let singleton x = L [x]

  let of_list l = L (List.sort Ord.compare l)

  let to_list (L l) = l

  let to_ilist (L l) = List.mapi (fun i x -> (i, x)) l

  let init f n =
    let rec init_list i acc =
      if i = 0 then
        acc
      else
        init_list (i - 1) (f (i - 1) :: acc)
    in
    L (List.sort Ord.compare (init_list n []))

  (* basic operations *)
  
  let mem x (L l) =
    List.exists (fun y -> Ord.compare x y = 0) l

  let hd (L l) = List.hd l

  let hd_option (L l) =
    match l with
    | [] -> None
    | h :: l' -> Some h

  let hd_tl_option (L l) =
    match l with
    | [] -> None
    | h :: l' -> Some (h, L l')

  let tl (L l) = L (List.tl l)
  
  let length (L l) = List.length l

  let is_empty (L l) = l = []

  let sublist (L outer) (L inner) =
    let rec sublist_list outer inner =
      match outer, inner with
      | [], [] -> true
      | _, [] -> true
      | [], _ -> false
      | oh :: outer', ih :: inner' ->
        let c = Ord.compare oh ih in
        if c = 0 then
          sublist_list outer' inner'
        else if c < 0 then
          sublist_list outer' inner
        else
          false
    in
    sublist_list outer inner

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

  (** Merge two sorted lists with special merge function for equal values. *)
  let merge_custom merge_fun (L l1) (L l2) =
    let rec merge_lists l1 l2 =
      match l1, l2 with
      | _, [] -> l1
      | [], _ -> l2
      | x :: l1', y :: l2' -> 
        let c = Ord.compare x y in
        if c = 0 then
          (merge_fun x y) :: (merge_lists l1' l2')
        else if c < 0 then
          x :: (merge_lists l1' l2)
        else
          y :: (merge_lists l1 l2')
    in
    L (merge_lists l1 l2)

  (** Merge two sorted lists idempodently, resulting in sorted list with unique values. *)
  let merge sl1 sl2 =
    merge_custom (fun x _ -> x) sl1 sl2

  let for_all f (L l) = List.for_all f l
  
  let exists f (L l) = List.exists f l

  (* iteration *)
  
  let fold_left f acc (L l) = List.fold_left f acc l

  let fold_left_short_circuit acc (L l) bottom f = Utilities.fold_left_short_circuit acc l bottom f

  let fold_right f (L l) acc = List.fold_right f l acc
  
  let map f (L l) = List.map f l

  let map_monotonic f (L l) = L (List.map f l)
      
  let rev_map f (L l) = List.rev_map f l

  let iter f (L l) = List.iter f l

  let compare_custom compare_elt (L l1) (L l2) =
    let rec compare_lists l1 l2 =
      match l1, l2 with
      | x1 :: l1', x2 :: l2' ->
        let res = compare_elt x1 x2 in
        if res = 0 then
          compare_lists l1' l2'
        else
          res
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
    in
    compare_lists l1 l2

  let compare l1 l2 =
    compare_custom Ord.compare l1 l2

  let equal_custom compare_elt l1 l2 = compare_custom compare_elt l1 l2 = 0

  let equal = equal_custom Ord.compare

  (* pretty printing *)

  let to_string p (L l) =
    Utilities.string_of_list p l
end
