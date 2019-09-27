open Flags

(* --- either --- *)

type ('a, 'b) either = Left of 'a | Right of 'b

let get_left : ('a, 'b) either -> 'a = function
  | Left x -> x
  | Right _ -> failwith "Expected left."

let get_right : ('a, 'b) either -> 'b = function
  | Left _ -> failwith "Expected right."
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

let option_map (f : 'a -> 'b) : 'a option -> 'b option = function
  | Some x -> Some (f x)
  | None -> None

let option_map_or_default (default : 'b) (f : 'a -> 'b) : 'a option -> 'b = function
  | Some x -> f x
  | None -> default

let option_get : 'a option -> 'a = function
  | Some x -> x
  | None -> failwith "Expected Some."

let option_default (default : 'a) (o : 'a option) : 'a =
  match o with
  | Some x -> x
  | None -> default

let option_compare (cmp : 'a -> 'a -> int) (x1 : 'a option) (x2 : 'a option) : int =
  match x1, x2 with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some s1, Some s2 -> cmp s1 s2

let option_equal (eq : 'a -> 'a -> bool) (x1 : 'a option) (x2 : 'a option) : bool =
  match x1, x2 with
  | None, None -> true
  | None, Some _ -> false
  | Some _, None -> false
  | Some s1, Some s2 -> eq s1 s2

let list_of_option : 'a option -> 'a list = function
  | Some x -> [x]
  | None -> []

let is_some : 'a option -> bool = function
  | Some _ -> true
  | None -> false

let string_of_option (s : 'a -> string) : 'a option -> string = function
  | Some x -> "Some " ^ s x
  | None -> "None"

(* --- printing --- *)

let string_of_bool = function
  | true -> "true"
  | false -> "false"

let concat_map (sep : string) (f : 'a -> string) (s : 'a list) : string =
  String.concat sep @@ List.map f s

let concat_map_seq (sep : string) (f : 'a -> string) (s : 'a Seq.t) : string =
  String.concat sep @@ List.of_seq @@ Seq.map f s

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

let list_is_empty (l : 'a list) : bool =
  match l with
  | [] -> true
  | _ -> false

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

(** Given list of lists (treated as sets) l1, ..., lK, it creates a list with flattened elements
    of product l1 x ... x lK. *)
let rec flat_product : 'a list list -> 'a list = function
  | [] -> []
  | [l] -> l
  | prefixes :: ls' ->
    let postfixes = flat_product ls' in
    List.fold_left (fun acc prefix ->
        List.fold_left (fun acc postfix ->
            (prefix @ postfix) :: acc
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
    | _ -> failwith "ls and fixed should have the same length."
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

let compare_arrays (cmp : 'a -> 'a -> int) (a1 : 'a array) (a2 : 'a array) : int =
  let lc = compare (Array.length a1) (Array.length a2) in
  if lc <> 0 then
    lc
  else
    let rec aux i =
      if i >= Array.length a1 then
        0
      else
        let c = compare a1.(i) a2.(i) in
        if c <> 0 then
          c
        else
          aux (i + 1)
    in
    aux 0

(** A list of integers from m to n - 1 (empty if m >= n). *)
let rec range (m : int) (n : int) : int list =
  if m >= n then
    []
  else
    m :: range (m + 1) n

(** Puts 0-based index in a pair with each element of the input list. *)
let index_list (l : 'a list) : (int * 'a) list =
  let len = List.length l in
  let indices = range 0 len in
  List.combine indices l

(** Removes the first element in list l that satisfies f. *)
let remove_first (f : 'a -> bool) (l : 'a list) : 'a list =
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

(** Removes elements from the front of the list as long as they don't satisfy the condition f. *)
let rec remove_until (f : 'a -> bool) : 'a list -> 'a list = function
  | [] -> []
  | (x :: l') as l ->
    if f x then
      l
    else
      remove_until f l'

(** Replaces i-th element of list l with r. *)
let replace_nth (l : 'a list) (i : int) (r : 'a) : 'a list =
  let rec replace_nth_aux l i acc =
    match l, i with
    | _ :: l', 0 -> List.rev_append (r :: acc) l'
    | x :: l', _ -> replace_nth_aux l' (i - 1) (x :: acc)
    | [], _ -> failwith "List too short."
  in
  replace_nth_aux l i []

(** Returns list without first nth elements. 0-indexed. *)
let rec from_nth (nth : int) (l : 'a list) =
  if nth = 0 then
    l
  else
    from_nth (nth - 1) (List.tl l)

(* Splits the list into first prefix_size elements and the rest. *)
let split_list (prefix_size : int) (l : 'a list) : 'a list * 'a list =
  let rec split_list_aux rprefix postfix n =
    if n = 0 then
      (List.rev rprefix, postfix)
    else
      match postfix with
      | [] -> failwith "List too short in split_list."
      | x :: postfix' ->
        split_list_aux (x :: rprefix) postfix' (n - 1)
  in
  split_list_aux [] l prefix_size

(** Returns last element of a list. *)
let rec last : 'a list -> 'a = function
  | [x] -> x
  | _ :: (x :: _ as l) -> last l
  | [] -> failwith "Unexpected empty list in last."

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
  let c' = List.sort compare c in
  delete_consecutive_duplicates compare c'

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

let rec is_sorted cmp l =
  match l with
  | [] -> true
  | [x] -> true
  | x :: (y :: l as yl) ->
    cmp x y < 0 && is_sorted cmp yl

let array_listmap (a : 'a array) (f : int -> 'a -> 'b) : 'b list =
  let rec array_listmap_aux i acc =
    if i = 0 then
      acc
    else
      array_listmap_aux (i - 1) @@ f (i - 1) a.(i - 1) :: acc
  in
  array_listmap_aux (Array.length a) []

(* --- printing --- *)

(** Global, but only for the purpose of debugging *)
let indentation = ref 0

let indent (delta : int) : unit =
  indentation := !indentation + 2 * delta

let reset_indentation () : unit =
  indentation := 0

let indentation_str () =
  String.make !indentation ' '

(** When flag is true, computes and prints lazy string str followed by a new line and flushes
    stdout. *)
let print_verbose (flag : bool) (str : string Lazy.t) : unit =
  if flag then
    begin
      print_endline @@
      indentation_str () ^
      Str.global_replace (Str.regexp "\n") ("\n" ^ indentation_str ()) @@
      Lazy.force str
    end

(* --- generic collections --- *)

module IntMap = struct
  include Map.Make (struct
      type t = int
      let compare = compare
    end)

  let of_list (l : (int * 'a) list) : 'a t =
    of_seq @@ List.to_seq l

  let is_singleton (m : 'a t) : bool =
    not @@ is_empty m &&
    (fst @@ min_binding m) = (fst @@ max_binding m)
end

module IntSet = Set.Make (struct
    type t = int
    let compare = compare
  end)

(* --- other --- *)

let int_of_bool : bool -> int = function
  | true -> 1
  | false -> 0

let id (x : 'a) : 'a = x
