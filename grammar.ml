open Utilities

exception Fatal of string

type nt_id = int (** names of non-terminal symbols; they are just integers **)
type var_id = nt_id * int (* pair of the non-terminal and the variable index *)
type term = A | B | E | NT of nt_id | Var of var_id | App of term * term
type kind = O | Kfun of kind * kind

type nonterminal = (string * kind)

(* store the original name of each non-terminal and its kind *)
type var_names = string array array (* store the original name of each variable *)

(** The total number of formal parameters and nonterminal body *)
type rule = int * term

module SortedVars = SortedList.Make(struct
    type t = var_id
    let compare = Pervasives.compare
  end)

module SortedNTs = SortedList.Make(struct
    type t = nt_id
    let compare = Pervasives.compare
  end)

let arity_of_t (a : term) : int =
  match a with
  | A -> 1
  | B -> 2
  | E -> 0
  | _ -> failwith "Expected a terminal"

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


let rec arity2kind k =
  if k = 0 then O else Kfun(O, arity2kind(k - 1))
   
let rec size_of_term t =
  match t with
  | NT _ | A | B | E | Var _ -> 1
  | App (t1, t2) -> (size_of_term t1) + (size_of_term t2)

let rec size_of_rule r = 
  let _, t =  r in size_of_term t

class grammar nonterminals var_names rules = object(self)
  val nonterminals : nonterminal array = nonterminals
  val var_names : string array array = var_names
  val rules : rule array = rules

  method start_nt = 0
  method rule (nt : nt_id) : rule = rules.(nt)
  method replace_rule (nt : nt_id) (rule : rule) =
    rules.(nt) <- rule
  method nt_count : int = Array.length rules
  method arity_of_nt (nt : nt_id) : int = fst rules.(nt)
  method rules = rules

  method size = Array.fold_left (fun n -> fun r -> n + (size_of_rule r)) 0 rules

  method name_of_nt (nt : nt_id) : string = fst nonterminals.(nt)
  method name_of_var (x : var_id) : string =
    let nt, i = x in
    (* variable added by normalization *)
    if nt < 0 || nt >= Array.length var_names then
      "v" ^ (string_of_int i)
    else if i >= Array.length var_names.(nt) then
      "v" ^ (string_of_int i)
    else
      var_names.(nt).(i)

  method string_of_term (term : term) : string =
    match term with
    | NT f -> self#name_of_nt f
    | A -> "a"
    | B -> "b"
    | E -> "e"
    | Var x -> self#name_of_var x
    | App (t1, t2) -> "(" ^ (self#string_of_term t1) ^ " " ^ (self#string_of_term t2) ^ ")"

  method print_term (term : term) =
    print_string (self#string_of_term term)

  method print_gram =
    for i = 0 to self#nt_count - 1 do 
      let arity, body = rules.(i) in
      begin
        print_string ((self#name_of_nt i)^" ");
        for j = 0 to arity - 1 do
          print_string ((self#name_of_var (i, j))^" ")
        done;
        print_string "-> ";
        self#print_term body;
        print_string "\n"
      end
    done

  method report_grammar =
    self#print_gram;
    print_string ("\nThe number of rewrite rules: "^(string_of_int self#nt_count)^"\n"^
                  "The size of recursion scheme: "^(string_of_int self#size)^"\n")
end

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
      
let rec arity_of_kind = function
  | O -> 0
  | Kfun (k1, k2) -> 1 + arity_of_kind k2
