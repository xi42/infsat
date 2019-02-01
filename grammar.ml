open Utilities

exception Fatal of string

type nt_id = int (** names of non-terminal symbols; they are just integers **)
type var_id = nt_id * int (* pair of the non-terminal and the variable index *)
type term = A | B | E | NT of nt_id | Var of var_id | App of term * term
type kind = O | Kfun of kind * kind

type nonterminals = (string * kind) array 
(* store the original name of each non-terminal and its kind *)
type varinfo = string array array (* store the original name of each variable *)
(*type terminals = (nameT * int) list  (* -1 if the arity is unknown *)*)

type rule = (int * term)  (* int: the number of formal parameters *)
type rules = rule array

module SortedVars = SortedList.Make(struct
    type t = var_id
    let compare = Pervasives.compare
  end)

module SortedNTs = SortedList.Make(struct
    type t = nt_id
    let compare = Pervasives.compare
  end)

type gram = {nt: nonterminals; vinfo: varinfo; r: rules; s: nt_id}

let empty_grammar : gram = {nt=[||]; vinfo=[||]; r=[||]; s=0}

let gram : gram ref = ref empty_grammar (* stored here once the grammar has been read  *)

let get_def (f : nt_id) (g : gram) : int * term = 
  g.r.(f) 

let lookup_rule (f : nt_id) : int * term =
  get_def f (!gram)

let nt_count () = Array.length (!gram.r)

(** change normal tree with app nodes to tree with (head, list-of-arg-terms) nodes *)
let rec decompose_term (t : term) : term * term list =
  match t with
  | NT _ | A | B | E | Var _ -> (t, [])
  | App (t1, t2) ->
    let h, ts = decompose_term t1 in
    (h, ts @ [t2])

let head term =
  let h, _ = decompose_term term in h

let rec compose_term h terms =
  match terms with
  | [] -> h
  | t :: terms' -> compose_term (App(h,t)) terms'

let rec mk_app h terms =
  match terms with
  | [] -> h
  | t :: terms' -> mk_app (App (h, t)) terms'

let rec occur_nt_in_term nt term =
  match term with
  | NT f -> nt = f
  | A | B | E | Var _ -> false
  | App (t1, t2) -> (occur_nt_in_term nt t1) ||(occur_nt_in_term nt t2)

let rec contains_vars_in_term (term : term) : bool =
  match term with
  | Var _ -> true
  | App (t1, t2) ->
    contains_vars_in_term t1 || contains_vars_in_term t2
  | _ -> false

let rec vars_in_term (term : term) : SortedVars.t = 
  match term with
  | NT _ | A | B | E -> SortedVars.empty
  | Var v -> SortedVars.singleton v
  | App (t1, t2) ->
    SortedVars.merge (vars_in_term t1) (vars_in_term t2) 

let rec vars_in_terms (terms : term list) : SortedVars.t =
  match terms with
  | [] -> SortedVars.empty
  | t :: terms' ->
    SortedVars.merge (vars_in_term t) (vars_in_terms terms')

(** Returns ascending list of variables in term that are not in an argument of a nonterminal or
    a terminal and are applied to something. *)
let rec headvars_in_term (term : term) : SortedVars.t =
  match term with
  | NT _ | A | B | E -> SortedVars.empty
  | Var _ -> SortedVars.empty
  | App (Var x, t2) ->
    SortedVars.merge (SortedVars.singleton x) (headvars_in_term t2)
  | App (t1, t2) ->
    SortedVars.merge (headvars_in_term t1) (headvars_in_term t2)

(** List of nonterminals used in term. *)
let rec nt_in_term (term : term) : SortedNTs.t =
  match term with
  | NT x -> SortedNTs.singleton x
  | A | B | E | Var _ -> SortedNTs.empty
  | App (t1, t2) ->
    SortedNTs.merge (nt_in_term t1)  (nt_in_term t2) 

(* TODO Unused *)
let nt_in_rule (_, (_, term)) =
  nt_in_term term

(* TODO Unused *)
let rec nt_in_rules rules : SortedNTs.t =
  match rules with
  | [] -> SortedNTs.empty
  | r :: rules' ->
    SortedNTs.merge (nt_in_rule r) (nt_in_rules rules')

(* TODO Unused *)
let rec mk_depend g =
  let n = Array.length g.nt in
  let deptab = Array.make n SortedNTs.empty in
  for i = 0 to n - 1 do
    deptab.(i) <- nt_in_term (snd (get_def i g))
  done;
  deptab

let arity_of_t (a : term) : int =
  match a with
  | A -> 1
  | B -> 2
  | E -> 0
  | _ -> failwith "Expected a terminal"

let arity_of_nt f =
  fst (!gram).r.(f)

let name_of_nt f =
  fst (!gram).nt.(f)

let name_of_var x =
  let f, i = x in
     if f < 0 || f >= Array.length (!gram).vinfo (* variable added by normalization *)
     then ("v"^(string_of_int i))
     else if i>= Array.length (!gram).vinfo.(f) then
         ("v"^(string_of_int i))
     else
       (!gram).vinfo.(f).(i)

let rec string_of_term term =
  match term with
  | NT f -> name_of_nt f
  | A -> "a"
  | B -> "b"
  | E -> "e"
  | Var x -> name_of_var x
  | App (t1, t2) -> "("^(string_of_term t1)^" "^(string_of_term t2)^")"

let print_term term =
  print_string (string_of_term term)

let rec subst_term s term =
  match term with
  | A | B | E | NT _ -> term
  | Var x ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
  | App (t1, t2) -> App(subst_term s t1, subst_term s t2)

let rec subst_nt_in_term s term =
  match term with
  | Var _ | A | B | E -> term
  | NT x ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
| App (t1, t2) -> App(subst_nt_in_term s t1, subst_nt_in_term s t2)
    

let print_gram g =
  let n = Array.length g.r in
  for i = 0 to n - 1 do 
    let arity, body = g.r.(i) in
    begin
      print_string ((name_of_nt i)^" ");
      for j = 0 to arity - 1 do
        print_string ((name_of_var (i, j))^" ")
      done;
      print_string "-> ";
      print_term body;
      print_string "\n"
    end
  done

let rec arity2kind k =
  if k = 0 then O else Kfun(O, arity2kind(k - 1))
   
let rec size_of_term t =
  match t with
  | NT _ | A | B | E | Var _ -> 1
  | App (t1, t2) -> (size_of_term t1) + (size_of_term t2)

let rec size_of_rule r = 
  let _, t =  r in size_of_term t
      
let rec size_of g =
   Array.fold_left (fun n -> fun r -> n + (size_of_rule r)) 0 g.r

let rec arity_of_kind = function
  | O -> 0
  | Kfun (k1, k2) -> 1 + arity_of_kind k2

let report_grammar g =
  let r = Array.length g.r in
  let s = size_of g in
  print_gram g;  
  print_string ("\nThe number of rewrite rules: "^(string_of_int r)^"\n"^
                "The size of recursion scheme: "^(string_of_int s)^"\n")
