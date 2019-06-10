open GrammarCommon
open Utilities

type term = TE of terminal | NT of nt_id | Var of var_id | App of term * term

(* store the original name of each non-terminal and its sort *)
type var_names = string array array (* store the original name of each variable *)

(** The total number of formal parameters and nonterminal body *)
type rule = int * term

let rec subst_term s term =
  match term with
  | TE _ | NT _ -> term
  | Var x ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
  | App (t1, t2) -> App (subst_term s t1, subst_term s t2)

let rec subst_nt_in_term s term =
  match term with
  | TE _ | Var _ -> term
  | NT x ->
    begin
      try 
        List.assoc x s
      with Not_found -> term
    end
  | App (t1, t2) -> App (subst_nt_in_term s t1, subst_nt_in_term s t2)
   
let rec size_of_term t =
  match t with
  | TE _ | NT _ | Var _ -> 1
  | App (t1, t2) -> (size_of_term t1) + (size_of_term t2)

let rec size_of_rule r = size_of_term (snd r)

(** A raw grammar.
    nonterminals are nonterminal names. var_names are names of variables in nonterminals
    used for pretty printing. May be empty and will be replaced by generic v1, v2, etc. in
    that case. rules are bodies of nonterminals. *)
class grammar (nt_names : string array) (var_names : string array array)
    (rules : rule array) = object(self)
  val var_names : string array array = var_names

  (** Sorts of nonterminals. *)
  val sorts : sort array = Array.make (Array.length rules) SAtom

  method start_nt : nt_id = 0
  method rule (nt : nt_id) : rule = rules.(nt)
  method replace_rule (nt : nt_id) (rule : rule) : unit = rules.(nt) <- rule
  method nt_count : int = Array.length rules
  method arity_of_nt (nt : nt_id) : int = fst rules.(nt)
  method rules = rules

  method size = Array.fold_left (fun n r -> n + (size_of_rule r)) 0 rules

  (* --- sorts --- *)

  method update_sorts (new_sorts : sort array) : unit =
    for nt = 0 to Array.length rules - 1 do
      sorts.(nt) <- new_sorts.(nt)
    done

  method nt_sort (nt : nt_id) : sort =
    sorts.(nt)

  (* --- printing and name lookups --- *)
  
  method name_of_nt (nt : nt_id) : string = nt_names.(nt)

  method nt_with_name (nt_name : string) : nt_id =
    let res = ref (-1) in
    Array.iteri (fun nt name ->
        if nt_name = name then
          res := nt
      ) nt_names;
    if !res = (-1) then
      failwith ("Nonterminal with name " ^ nt_name ^ " not found")
    else
      !res
  
  method name_of_var (x : var_id) : string =
    let nt, i = x in
    (* variable added by normalization *)
    if nt < 0 || nt >= Array.length var_names || i >= Array.length var_names.(nt) then
      "nt" ^ string_of_int nt ^ "v" ^ string_of_int i
    else
      var_names.(nt).(i)

  method string_of_term (term : term) : string =
    match term with
    | TE a -> string_of_terminal a
    | NT f -> self#name_of_nt f
    | Var x -> self#name_of_var x
    | App (t1, t2) -> "(" ^ self#string_of_term t1 ^ " " ^ self#string_of_term t2 ^ ")"

  method to_string : string =
    String.concat "\n" @@ Array.to_list @@
    (rules |> Array.mapi (fun i (arity, body) ->
         self#name_of_nt i ^ " " ^
         String.concat "" (Utilities.range 0 arity |> List.map (fun j ->
             self#name_of_var (i, j) ^ " "
           )) ^
         "-> " ^
         self#string_of_term body
       )
    )

  method grammar_info : string =
    self#to_string ^
    "\n\nThe number of rewrite rules: " ^ string_of_int self#nt_count ^ "\n" ^
    "The size of recursion scheme: " ^ string_of_int self#size
end

(** change normal tree with app nodes to tree with (head, list-of-arg-terms) nodes *)
let rec decompose_term (t : term) : term * term list =
  match t with
  | TE _ | NT _ | Var _ -> (t, [])
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
  | TE _ | Var _ -> false
  | NT f -> nt = f
  | App (t1, t2) -> (occur_nt_in_term nt t1) ||(occur_nt_in_term nt t2)

let rec contains_vars_in_term (term : term) : bool =
  match term with
  | Var _ -> true
  | App (t1, t2) ->
    contains_vars_in_term t1 || contains_vars_in_term t2
  | _ -> false

let rec vars_in_term (term : term) : vars = 
  match term with
  | TE _ | NT _ -> SortedVars.empty
  | Var v -> SortedVars.singleton v
  | App (t1, t2) ->
    SortedVars.merge (vars_in_term t1) (vars_in_term t2) 

let rec vars_in_terms (terms : term list) : vars =
  match terms with
  | [] -> SortedVars.empty
  | t :: terms' ->
    SortedVars.merge (vars_in_term t) (vars_in_terms terms')

(** Returns ascending list of variables in term that are not in an argument of a nonterminal or
    a terminal and are applied to something. *)
let rec headvars_in_term (term : term) : vars =
  match term with
  | TE _ | NT _ -> SortedVars.empty
  | Var _ -> SortedVars.empty
  | App (Var x, t2) ->
    SortedVars.merge (SortedVars.singleton x) (headvars_in_term t2)
  | App (t1, t2) ->
    SortedVars.merge (headvars_in_term t1) (headvars_in_term t2)

(** List of nonterminals used in term. *)
let rec nt_in_term (term : term) : SortedNTs.t =
  match term with
  | TE _ | Var _ -> SortedNTs.empty
  | NT x -> SortedNTs.singleton x
  | App (t1, t2) ->
    SortedNTs.merge (nt_in_term t1)  (nt_in_term t2)
