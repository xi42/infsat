open Utilities

exception Fatal of string

type nameNT = int (** names of non-terminal symbols; they are just integers **)
type nameT = string  (** names of terminal symbols **)
type nameV = nameNT * int (* pair of the non-terminal and the variable index *)
type term = NT of nameNT | A | B | E | Var of nameV | App of term * term
type kind = O | Kfun of kind * kind

type nonterminals = (string * kind) array 
  (* store the original name of each non-terminal and its kind *)
type varinfo = string array array (* store the original name of each variable *)
type terminals = (nameT * int) list  (* -1 if the arity is unknown *)

type rule = (int * term)  (* int: the number of formal parameters *)
type rules = rule array 

type gram = {nt: nonterminals; vinfo: varinfo; r: rules; s: nameNT}

let empty_grammar : gram= {nt=[||]; vinfo=[||]; r=[||]; s=0}

let gram : gram ref = ref empty_grammar (* stored here once the grammar has been read  *)

exception UndefinedNonterminal of string
exception DuplicatedNonterminal of string
exception InconsistentArity of nameT


let get_def (f: nameNT) (g:gram) = 
  g.r.(f) 

let lookup_rule (f: nameNT) =
  get_def f (!gram)

let nt_count() = Array.length (!gram.r)

(** change normal tree with app nodes to tree with (head, list-of-arg-terms) nodes *)
let rec decompose_term t =
  match t with
  | NT(_) | A | B | E | Var(_) -> (t, [])
  | App(t1, t2) ->
    let (h,ts)=decompose_term t1 in (h, ts @ [t2])

let head term =
  let (h,_) = decompose_term term in h

let rec compose_term h terms =
  match terms with
  | [] -> h
  | t::terms' -> compose_term (App(h,t)) terms'

let rec mk_app h terms =
  match terms with
  | [] -> h
  | t::terms' -> mk_app (App(h,t)) terms'

let rec occur_nt_in_term nt term =
  match term with
  | NT(f) -> nt=f
  | A | B | E | Var(_) -> false
  | App(t1,t2) -> (occur_nt_in_term nt t1) ||(occur_nt_in_term nt t2)

let rec vars_in_term term = 
  match term with
  | NT(_) | A | B | E -> []
  | Var(v) -> [v]
  | App(t1,t2) ->
     merge_and_unify compare (vars_in_term t1)  (vars_in_term t2) 

let rec vars_in_terms terms =
  match terms with
  | [] -> []
  | t::terms' -> merge_and_unify compare (vars_in_term t) (vars_in_terms terms')

(** Returns ascending list of variables in term that are not in an argument of a nonterminal or
    a terminal and are applied to something. *)
let rec headvars_in_term (term : term) : nameV list =
  match term with
  | NT(_) | A | B | E -> []
  | Var(_) -> []
  | App(Var(x), t2) -> merge_and_unify compare [x] (headvars_in_term t2)
  | App(t1, t2) -> merge_and_unify compare (headvars_in_term t1)
                     (headvars_in_term t2)

(** List of nonterminals used in term. *)
let rec nt_in_term term = 
  match term with
  | NT(x) -> [x]
  | A | B | E | Var(_) -> []
  | App(t1,t2) ->
     merge_and_unify compare (nt_in_term t1)  (nt_in_term t2) 

let nt_in_rule (f, (vars, term)) =
  nt_in_term term

let rec nt_in_rules rules =
  match rules with
  | [] -> []
  |r::rules' ->
    merge_and_unify compare (nt_in_rule r) (nt_in_rules rules')

let rec mk_depend g =
  let n = Array.length g.nt in
  let deptab = Array.make n [] in
   for i=0 to n-1 do
      deptab.(i) <- (let (vars,body) = get_def i g in nt_in_term body)
   done;
   deptab

let arity_of_t (a : term) : int =
  match a with
  | A -> 1
  | B -> 2
  | E -> 0
  | _ -> failwith "Expected a terminal"

let arity_of_nt f =
  let (arity,_) = (!gram).r.(f) in arity

let name_of_nt f =
  let (s,_) = (!gram).nt.(f) in s

let name_of_var x =
  let (f,i) = x in
     if f<0 || f>=Array.length (!gram).vinfo (* variable added by normalization *)
     then ("v"^(string_of_int i))
     else if i>= Array.length (!gram).vinfo.(f) then
         ("v"^(string_of_int i))
     else
       (!gram).vinfo.(f).(i)

let rec string_of_term term =
  match term with
  | NT(f) -> name_of_nt f
  | A -> "a"
  | B -> "b"
  | E -> "e"
  | Var(x) -> name_of_var x
  | App(t1,t2) -> "("^(string_of_term t1)^" "^(string_of_term t2)^")"

let print_term term =
  print_string (string_of_term term)

let rec subst_term s term =
  match term with
  | A | B | E |NT(_) -> term
  | Var(x) ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
  | App(t1,t2) -> App(subst_term s t1, subst_term s t2)

let rec subst_nt_in_term s term =
  match term with
  | Var(_) | A | B | E -> term
  | NT(x) ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
| App(t1,t2) -> App(subst_nt_in_term s t1, subst_nt_in_term s t2)
    

let print_gram g =
  let n = Array.length g.r in
  for i=0 to n-1 do 
    let (arity,body) =  g.r.(i) in
    (print_string ((name_of_nt i)^" ");
     for j=0 to arity-1 do
       print_string ((name_of_var (i,j))^" ")
     done;
     print_string "-> ";
     print_term body;
     print_string "\n")
  done

let rec arity2kind k =
  if k=0 then O else Kfun(O,arity2kind(k-1))
   
let rec size_of_term t =
  match t with
  | NT(_) | A | B | E | Var(_) -> 1
  | App(t1, t2) -> (size_of_term t1) + (size_of_term t2)

let rec size_of_rule r = 
  let (_, t) =  r in size_of_term t
      
let rec size_of g =
   Array.fold_left (fun n -> fun r -> n+(size_of_rule r)) 0 g.r

let rec arity_of_kind = function
  | O -> 0
  | Kfun (k1,k2) -> 1 + arity_of_kind k2

let report_grammar g =
  let r = Array.length g.r in
  let s = size_of g in
  print_gram g;  
  print_string ("\nThe number of rewrite rules: "^(string_of_int r)^"\n"^
                "The size of recursion scheme: "^(string_of_int s)^"\n")
