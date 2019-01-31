module Make (Ord : Set.OrderedType) =
struct
  type elt = Ord.t
  type t = SortedList of elt list

  let empty : t = SortedList []
      
  let singleton (e : elt) : t = SortedList [e]

  let of_list (l : elt list) : t = SortedList (List.sort Ord.compare l)

  let to_list (SortedList l : t) : elt list = l

  let length (SortedList l : t) : int = List.length l

  let fold_left f (SortedList l : t) = List.fold_left f l

  let map (f : elt -> 'a) (SortedList l : t) : 'a list = List.map f l

  let iter f (SortedList l : t) = List.iter f l

  let partition f (SortedList l : t) =
    let a, b = List.partition f l in
    (SortedList a, SortedList b)

  let mem (x : elt) (SortedList l : t) = List.mem x l

  let hd (SortedList l : t) : elt = List.hd l

  let tl (SortedList l : t) : t = SortedList(List.tl l)

  let uniq (SortedList l : t) : t =
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
    SortedList (uniq_list l [])

  let init (f : int -> elt) (n : int) : t =
    let rec init_list i acc =
      if i = 0 then
        acc
      else
        init_list (i - 1) (f (i - 1) :: acc)
    in
    SortedList (List.sort Ord.compare (init_list n []))

  (** Merge two sorted list idempodently, resulting in sorted list with unique values. *)
  let merge (SortedList l1 : t) (SortedList l2 : t) : t =
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
    SortedList (merge_lists l1 l2)
end
