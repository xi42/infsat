open Flags

let rec fold_left_short_circuit (f : 'a -> 'b -> 'a) (acc : 'a) (l : 'b list) (bottom : 'a) : 'a =
  match l with
  | [] -> acc
  | x :: l' ->
    if acc = bottom then
      acc
    else
      fold_left_short_circuit f (f acc x) l' bottom

let debug s =
  if
    !debugging
  then
    (print_string s; flush stdout)
  else 
    ()

(** A list of integers m, m + 1, ..., n - 1 (empty if m >= n). *)
let rec fromto m n =
  if m >= n then
    []
  else
    m :: (fromto (m + 1) n)

let rec list_repl n a l =
  match l with
    [] -> failwith "list_repl: position is wrong"
  | x::l' ->
     if n=0 then a::(List.tl l)
     else x::(list_repl (n-1) a l')

let rec list_take_n l n =
  if n=0 then []
  else
    match l with
      [] -> assert false
    | x::l' -> x::(list_take_n l' (n-1))

let rec list_take_n_and_rest l n =
  if n=0 then ([], l)
  else
    match l with
      [] -> assert false
    | x::l' -> 
       let (l1,l2) = list_take_n_and_rest l' (n-1) in
         (x::l1, l2)

let rec list_rem_n l n =
  if n=0 then l
  else 
    match l with
      [] -> assert false
    | x::l' -> list_rem_n l' (n-1)

let rec list_take_nth l n =
  match l with
  | [] -> failwith "list_take_nth: position is wrong"
  | a::l' ->
    if n=0 then (a, l')
    else
      let (x, l'') = list_take_nth l' (n-1) in
      (x, a::l'')

let rec is_sorted l =
  match l with
    [] -> true
  | [x] -> true
  | x::y::l ->
       compare x y<0 && is_sorted (y::l)

let rec merge comp l1 l2 =
  match (l1, l2) with
    (_,[]) -> l1
  | ([], _)->l2
  | (x::l1',y::l2') -> 
        let c = comp x y in
         if c<0 then x::(merge comp l1' l2)
         else y::(merge comp l1 l2');;
let list_flatten l =  List.fold_left (@) [] l;;

let rec merge_eqp l1 l2 =
  let l1' = List.filter (fun x -> not(List.memq x l2)) l1 in
    l1'@l2

(*** utility functions ***)
let id x = x;;
let rec delete_duplication l =
  match l with
    [] -> []
  | [x] -> [x]
  | x::y::l -> if x=y then delete_duplication (y::l)
               else x::(delete_duplication (y::l));;

let delete_duplication_unsorted c =
  let c' = List.sort compare c in
    delete_duplication c';;

let rec delete_duplication2 comp comb l =
  match l with
    [] -> []
  | [x] -> [x]
  | x::y::l -> if comp x y =0 then delete_duplication2 comp comb ((comb x y)::l)
               else x::(delete_duplication2 comp comb (y::l));;
let rec list_assoc2 x l =
  match l with
    [] -> raise Not_found
  | (y,v)::l' -> if x=y then (v, l')
                 else let (v1,l1) = list_assoc2 x l' in (v1, (y,v)::l1);;
let list_diff l1 l2 =
  List.filter (function x-> not(List.mem x l2)) l1;;

let list_filter2 p l =
  let rec f p l l1 l2 =
    match l with
       [] -> (l1,l2)
      | x::l' -> 
         if p x then f p l' (x::l1) l2
         else f p l' l1 (x::l2)
  in
    f p (List.rev l) [] []

let rec list_count l =
  match l with
     [] -> []
   | x::l' ->
     let lc = list_count l' in
       try 
         let (n,lc1) = list_assoc2 x lc in
           (x,n+1)::lc1
       with
         Not_found -> (x,1)::lc

let list_max c l =
  let rec f c l max =
    match l with
        [] -> max
      | x::l' ->
          if c x max >0 then
              f c l' x
          else
              f c l' max
  in
     f c (List.tl l) (List.hd l)

let rec list_last l =
  match l with
     [] -> raise Not_found
  | [x] -> x
  | x::l' -> list_last(l');;

let rec list_last_and_rest l =
  match l with
     [] -> raise Not_found
  | [x] -> (x, [])
  | x::l' -> 
     let (y, l'') = list_last_and_rest(l') 
     in (y, x::l'')

let rec subset_sortedlist comp l1 l2 =
  match l1 with
    [] -> true
  | x::l1' ->
      match l2 with
         [] -> false
       | y::l2' -> 
          let c = comp x y in
          if c=0 then subset_sortedlist comp l1' l2'
          else if c<0 then false
          else subset_sortedlist comp l1 l2'

let swap (x,y) = (y,x);;

let rec combination2 l =
  match l with
    [] -> []
  | x::l' ->
     let c1 = List.map (fun y->(x,y)) l' in
     let c2 = combination2 l' in
       c1@c2

let rec mk_list n x =
  if n<=0 then []
  else x::(mk_list (n-1) x)

(*** substitutions ***)
type ('a, 'b) substitution = ('a * 'b) list
let subst_empty = []
let subst_var s var default = 
  try
     List.assoc var s
  with 
     Not_found -> default
let make_subst x v = [(x,v)]
let list2subst x = x
let comp_subst subst s1 s2 =
  let s2' = List.map (fun (x,v)->(x,subst s1 v)) s2 in
  let s1' = List.filter (fun (x,v) -> List.for_all (fun (x',v')->x!=x') s2) s1 in
    s1'@s2'

(*** perfect_matching checks to see if there exists a perfect matching 
 *** The implementation is extremely naive, assuming
 *** that the size of the input graph is very small.
 *** For a large graph, an approximate, conservative
 *** algorithm should be used.
 ***)
let rec delete x l =
  match l with 
    [] -> raise Not_found
  | y::l' -> if x=y then l' else y::(delete x l')

let rec find nodes candidates =
  match candidates with
    [] -> true
  | nodes1::candidates' -> 
      List.exists (fun x->
                    try let nodes' = delete x nodes in find nodes' candidates'
                    with
                      Not_found -> false) 
      nodes1
       
let perfect_matching nodes1 nodes2 edges =
 let get_neighbors x = List.map snd (List.filter (fun (x',_) -> x=x') edges) in
 let sources = List.map fst edges in
 let sinks = List.map snd edges in
 if (List.exists (fun x -> not(List.mem x sources)) nodes1)
    || (List.exists (fun x -> not(List.mem x sinks)) nodes2)
    || List.length nodes1 != List.length nodes2
 then false (*** there is a node that is unrelated ***)
 else
   let neighbors = List.map get_neighbors nodes1 in
     find nodes2 neighbors

(*** hash ***)
let list2hash l =
  let h = Hashtbl.create (2*(List.length l)) in
    (List.iter (fun (x,y) -> Hashtbl.add h x y) l; h)

let hash2list h =
  Hashtbl.fold (fun x -> fun y -> fun l -> (x,y)::l) h []
let hash2elem h = 
  Hashtbl.fold (fun x _ -> fun l -> x::l) h []
  
let list_singleton l =
  match l with
    [_] -> true
  | _ -> false

let filter_tail p l =
  let rec f l r =
    match l with
      [] -> r
    | x::l' -> if p x then f l' (x::r) else f l' r
  in f l []

(* like List.assoc, but with a specialized equality function *)
let rec assoc_eq eq x l =
  match l with
    [] -> raise Not_found
 | (y,z)::l' ->
     if eq x y then z
     else assoc_eq eq x l'

let index_list l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine indices l

let index_list_r l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine l indices
