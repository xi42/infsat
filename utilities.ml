open Flags

(* --- either --- *)

type ('a, 'b) either = Left of 'a | Right of 'b

let get_left : ('a, 'b) either -> 'a = function
  | Left x -> x
  | Right _ -> failwith "Expected left"

let get_right : ('a, 'b) either -> 'b = function
  | Left _ -> failwith "Expected right"
  | Right x -> x

let either_map (f : 'a -> 'c) (g : 'b -> 'c) (e : ('a, 'b) either) : 'c =
  match e with
  | Left a -> f a
  | Right b -> g b

let either_bimap (f : 'a -> 'c) (g : 'b -> 'd) (e : ('a, 'b) either) : ('c, 'd) either =
  match e with
  | Left a -> Left (f a)
  | Right b -> Right (f b)

(* --- option --- *)

let option_map (default : 'b) (f : 'a -> 'b) : 'a option -> 'b = function
  | Some x -> f x
  | None -> default

let option_get : 'a option -> 'a = function
  | Some x -> x
  | None -> failwith "Expected Some"

(* --- printing --- *)

let string_of_bool = function
  | true -> "true"
  | false -> "false"

(* --- tuples --- *)

(** Lexicographical comparison of a pair with custom comparison of elements. *)
let compare_pair (cmp1 : 'a -> 'a -> int) (cmp2 : 'b -> 'b -> int)
    (x1, y1 : 'a * 'b) (x2, y2 : 'a * 'b) : int =
  let c1 = cmp1 x1 x2 in
  if c1 = 0 then
    cmp2 y1 y2
  else
    c1

(* --- lists --- *)

(** Version of fold_left that takes additional argument bottom. When acc is bottom after an
    application, bottom is returned and no further calls to f are made. Careful: it uses
    build-in Pervasives.compare equality. *)
let rec fold_left_short_circuit (acc : 'a) (l : 'b list) (bottom : 'a) (f : 'a -> 'b -> 'a) : 'a =
  match l with
  | [] -> acc
  | x :: l' ->
    if acc = bottom then
      acc
    else
      fold_left_short_circuit (f acc x) l' bottom f

(** Same as fold_left_short_circuit, but does not check for short-circuit at the very beginning. *)
let fold_left_short_circuit_after_first (acc : 'a) (l : 'b list) (bottom : 'a)
    (f : 'a -> 'b -> 'a) : 'a =
  match l with
  | [] -> acc
  | x :: l' ->
    fold_left_short_circuit (f acc x) l' bottom f

(** Given list of lists (treated as sets) l1, ..., lK, it creates a list with elements of product
    l1 x ... x lK. *)
let rec product : 'a list list -> 'a list list = function
  | [] -> []
  | [l] -> List.rev_map (fun x -> [x]) l
  | prefixes :: ls' ->
    let postfixes = product ls' in
    List.fold_left (fun acc prefix ->
        List.fold_left (fun acc postfix ->
            (prefix :: postfix) :: acc
          ) acc postfixes
    ) [] prefixes

(** Given list of lists (treated as sets) l1, ..., lK and fixed list of elements x1, ..., xK,
    it creates a list with sum of elements of products of at least one of sets {x1}, ..., {xK}
    and the rest from l1, ..., lK, in the order of ascending index. *)
let product_with_one_fixed (ls : 'a list list) (fixed : 'a list) : 'a list list =
  let rec product_with_one_fixed_aux prefix postfix fixed acc =
    match postfix, fixed with
    | [], [] -> acc
    | l :: postfix', f :: fixed' ->
      product_with_one_fixed_aux ((f :: l) :: prefix) postfix' fixed' @@
      List.rev_append (product @@ List.rev prefix @ ([f] :: postfix')) acc
    | _ -> failwith "ls and fixed should have the same length"
  in
  product_with_one_fixed_aux [] ls fixed []

(** Lexicographical comparison of lists with custom comparison of elements. *)
let rec compare_lists (cmp : 'a -> 'a -> int) (l1 : 'a list) (l2 : 'a list) : int =
  match l1, l2 with
  | x1 :: l1', x2 :: l2' ->
    let res = cmp x1 x2 in
    if res = 0 then
      compare_lists cmp l1' l2'
    else
      res
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1

(** A list of integers from m to n - 1 (empty if m >= n). *)
let rec fromto (m : int) (n : int) : int list =
  if m >= n then
    []
  else
    m :: fromto (m + 1) n

(** Puts 0-based index in a pair with each element of the input list. *)
let index_list (l : 'a list) : (int * 'a) list =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine indices l

(** Removes the first element in list l that satisfies f. *)
let remove_first (l : 'a list) (f : 'a -> bool) : 'a list =
  let rec remove_first_aux l acc =
    match l with
    | [] -> List.rev acc
    | x :: l' ->
      if f x then
        List.rev_append acc l'
      else
        remove_first_aux l' (x :: acc)
  in
  remove_first_aux l []

(** Replaces i-th element of list l with r. *)
let replace_nth (l : 'a list) (i : int) (r : 'a) : 'a list =
  let rec replace_nth_aux l i acc =
    match l, i with
    | _ :: l', 0 -> List.rev_append (r :: acc) l'
    | x :: l', _ -> replace_nth_aux l' (i - 1) (x :: acc)
    | [], _ -> failwith "List too short"
  in
  replace_nth_aux l i []

(** Change list to string as it would be represented in OCaml using custom function to change each
    element to string. *)
let string_of_list (p : 'a -> string) (l : 'a list) : string =
  match l with
  | [] -> "[]"
  | [x] -> "[" ^ p x ^ "]"
  | x :: l' ->
    "[" ^
    (List.fold_left (fun acc x ->
         acc ^ "; " ^ p x
       ) (p x) l') ^
    "]"

(* --- parsing --- *)

(** Removes a single parenthesis from the beginning and end of the string if present on both
    sides. *)
let trim_parens (str : string) : string =
  if String.length str >= 2 && str.[0] = '(' && str.[String.length str - 1] = ')' then
    String.sub str 1 (String.length str - 2)
  else
    str

(** Splits str on the first occurence of sep outside parentheses into two strings that do not
    contain the sep between them. *)
let split_outside_parens (str : string) (sep : string) : (string * string) option =
  assert (String.length sep > 0);
  let strlen = String.length str in
  let seplen = String.length sep in
  let i = ref 0 in
  let parens = ref 0 in
  let res = ref None in
  while !i < strlen && !res = None do
    if str.[!i] = '(' then
      parens := !parens + 1
    else if str.[!i] = ')' then
      parens := !parens - 1
    else if !parens = 0 && str.[!i] = sep.[0] && !i + seplen <= strlen then
      begin
        let j = ref 1 in
        while !j < seplen && str.[!i + !j] = sep.[!j] do
          j := !j + 1
        done;
        if !j = seplen then
          res := Some (String.sub str 0 !i,
                       String.sub str (!i + seplen) (strlen - seplen - !i));
      end;
    i := !i + 1
  done;
  !res

(** Delete all but one equal consecutive elements in the list using provided comparison. *)
let delete_consecutive_duplicates compare l =
  let rec delete_duplicates_aux l acc =
    match l with
    | [] -> List.rev acc
    | [x] -> List.rev (x :: acc)
    | x :: (y :: l as yl) ->
      if compare x y = 0 then
      delete_duplicates_aux yl acc
      else
        delete_duplicates_aux yl @@ x :: acc
  in
  delete_duplicates_aux l []

(** Sort the list and delete all but one equal elements in the list using Pervasives.compare. *)
let sort_and_delete_duplicates c =
  let c' = List.sort Pervasives.compare c in
  delete_consecutive_duplicates Pervasives.compare c'

let rec is_sorted cmp l =
  match l with
  | [] -> true
  | [x] -> true
  | x :: (y :: l as yl) ->
    cmp x y < 0 && is_sorted cmp yl

(* --- ? --- *)

let id (x : 'a) : 'a = x

let debug s =
  if
    !debugging
  then
    (print_string s; flush stdout)
  else 
    ()

let list_max c l =
  let rec f c l max =
    match l with
    | [] -> max
    | x::l' ->
      if c x max > 0 then
        f c l' x
      else
        f c l' max
  in
  f c (List.tl l) (List.hd l)

(*

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

let index_list_r l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine l indices
*)
