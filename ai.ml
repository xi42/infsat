open Grammar;;
open Automaton;;
open Utilities;;

type states = int list
type termid = int
type head = Hnt of nameNT | Hvar of nameV | Ht of nameT
(*
type aterm = term  * (term list) list
*)
type aterm = head  * termid list
   (* aterm = (t, [[t11; ...; t1k];...;[tj1; ...;tjk]]) represents
       t t11 ... t1k  ... tj1 ... tjk, where
       t,tij are subterms of the lefthand side of a rule of the grammar 
       [ti1;...;tik] share the same environment
    *)
type node = aterm * states

(** After the nonterminals are numbered, this is a map from nonterminals' ids to their bodies in
    head form. Bodies in head form are tuples (h, [as1; as2; ..]), where asX are integers that
    are mapped to lists of terms in head form, i.e., as1 = [a11; a12; ...]. The original tuple
    then represents
    h a11 a12 ... a1n a21 a22 ... a2m ...
    Mappings from asX to lists are in tab_id_terms. *)
let normalized_body = ref [||]

let lookup_body f = (!normalized_body).(f)

(** Maps textual state name, e.g., q0, to an integer identifier. *)
let tab_state_id = Hashtbl.create 100

(** Reverse of tab_state_id. *)
let tab_id_state = Hashtbl.create 100

(** Increasing counter for fresh identifiers. *)
let state_idref = ref 0
let new_state_id() =
  let x = !state_idref in
   (state_idref := x+1; x)

let register_state q =
  try 
    let _ = Hashtbl.find tab_state_id q in ()
  with Not_found ->
   ( let x=new_state_id() in
      Hashtbl.add tab_state_id q x;
      Hashtbl.add tab_id_state x q)

let id2state id =
  try Hashtbl.find tab_id_state id 
  with Not_found -> assert false

let state2id q = 
  try
  Hashtbl.find tab_state_id q
  with Not_found -> 
  (  print_string ("state "^q^" has not been registered\n");
    assert false)

(* necessary tables:
- trtab:
   information about transitions of the form
    (q,a) -->  [|Q1,...,Qk|]
  this is extracted from transition rules of the automaton.
  If the automaton is deterministic,
  the table should keep the map
    (q,a) --> ({q1},...,{qk})
  for each transition rule delta(q,a)=q1...qk.
  If the automaton is alternating,
  the table should keep the map
    (q,a) --> (Q1,...,Qk)
  where Qi is the set of states q occurring in the form of (i,q)
  in delta(q,a)

- map from aterm to node

- binding information, which maps 
   each variable x to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
   each non-terminal to a binding list of the form (x1,...,xk)|-> {(t11,...,t1k),...,(tj1,...,tjk)}
   (the former can be obtained from the latter and the table below)
   Should the binding also contain information about which terms share the environment
   (so, [[~t11];...;[~tik]] instead of (t11,...,t1k))
   
- map from each subterm to the non-terminal of the rule containing the subterm?
- map from each variable to a pair consisting of non-terminal and index?
  (to make it easy to find binding)
*)

(** Represents the transition delta(q,a) = Q1 Q2 .. QN for each letter a with arity N.
    Specifically q is int, a is letter, QX is a list of ints, and
    trtab[(q,a)][X] = QX *)
let trtab : (int*nameT, int list array) Hashtbl.t = Hashtbl.create 1000

let mk_trtab m =
  register_state m.init;
  List.iter register_state m.st; (* translating states to integers *)
  let tr = m.delta in
  Hashtbl.clear trtab;
  List.iter (fun ((q,a),qs) ->
   let arity = List.length qs in
   let x = Array.make arity [] in
   let indices = fromto 0 arity in
     List.iter 
     (fun (i,q') -> x.(i) <- [state2id q']) 
     (List.combine indices qs);
     Hashtbl.add trtab (state2id q,a) x (* make trtab be mapping (state id, letter) -> [[arg1 state id], [arg2 state id], ...], just like in m.delta, but with integers for states *)
   ) tr

(** Given multiple arrays of equal length, it iterates over them merging all elements as sets and
    returning the result. All but last array on the list are modified and the first one will
    contain the result. *)
(* TODO this should probably return fresh arrays *)
let rec merge_statevecs qsvecs =
  match qsvecs with
    [] -> assert false
  | [qsvec] -> qsvec
  | qsvec1::qsvecs' ->
     let merged = Array.copy qsvec1 in
       List.iter (fun qsvec2 -> let _=merge_statevec merged qsvec2 in ()) qsvecs';
       merged    
and merge_statevec qsvec1 qsvec2 =
   let len = Array.length qsvec1 in
    for i=0 to len-1 do
      qsvec1.(i) <- Utilities.merge_and_unify compare (qsvec1.(i)) (qsvec2.(i))
    done; 
    qsvec1

let rec get_qs form arity =
  match form with
    AlternatingAutomaton.Bool _ -> Array.make arity []
  | AlternatingAutomaton.Var (i,q) ->
     let x = Array.make arity [] in
       (x.(i-1) <- [state2id q]; x) (* index is shifted *)
  | AlternatingAutomaton.Or(f1, f2) ->
     merge_statevec (get_qs f1 arity) (get_qs f2 arity)
  | AlternatingAutomaton.And(f1, f2) ->
    merge_statevec (get_qs f1 arity) (get_qs f2 arity)
      

let mk_trtab_for_ata m =
  register_state m.AlternatingAutomaton.init;
  List.iter register_state m.AlternatingAutomaton.st;
  Hashtbl.clear trtab;
  List.iter (fun ((q,a), form) ->
    let arity = List.assoc a m.AlternatingAutomaton.alpha in
    let qs' = get_qs form arity in
      Hashtbl.add trtab (state2id q,a) qs')
   m.AlternatingAutomaton.delta

(** Mapping from int ids to lists of terms. when tab_id_terms[i] = (aterms, terms, vars), then
    aterms is a list of terms [a1; a2; ..; aN], each in head form (h, [i1; i2; ..; iM]).
    h is a terminal, nonterminal, or a variable. iX points at tab_id_terms[iX]. This represents
    an applicative term
    h a11 a12 ... a1K a21 ... aM1 ... aMR
    terms are aterms in the original tree representation, and vars is a list of all free variables
    in terms. Variables are represented as integer tuples (X, Y) for Y-th argument (0-indexed)
    of X-th nonterminal (0-indexed).
    Note that two terms with variables that are used in two different nonterminal definitions will
    have different ids, because variables are tuples (nt_id, var_id) that are disjoint for
    different nonterminal bodies. *)
let tab_id_terms = ref [||]

(** termid_isarg[i] contains a boolean whether tab_id_terms[i] was ever used as an argument when
    expanding terms in expand, i.e., if it was a used argument to a nonterminal. *)
let termid_isarg = ref [||]


let lookup_id_terms id =
 (!tab_id_terms).(id)

(** Changes (H, [ID]) into (H, [arg 1, arg 2, ...]) and (H, [ID1, ID2, ...]) into (H, [arg 1-1, arg 1-2, ..., arg 2-1, arg 2-2, ...]), i.e., looks up one layer and combines applications *)
let decompose_aterm (aterm: aterm) =
  let (h, termids) = aterm in
  let aterms =
    match termids with
      [] -> []
    | [id] -> let (aterms,_,_)=lookup_id_terms id in aterms
    | _ -> 
      List.rev_append
      (List.fold_left
       (fun aterms id ->
          let (aterms',_,_)=lookup_id_terms id in
    	    List.rev_append aterms' aterms) [] termids) []
  in (h, aterms)

(** Find transition delta(q,a) = [q1, q2, ...] or create it to empty set of states for each arg
    if not found. This breaks trtab, and the only reason everything works is that it breaks
    disjoint parts of trtab growing them into the end result. *)
let expand_state q a = 
   try Hashtbl.find trtab (q,a)
   with Not_found -> Array.make (Grammar.arity_of_t a) []

(** For each state q in qs, try to see where delta(q,a) = (Q1, ...) goes. Then, combine these
    lists index-wise (Q1-1 + Q2-1 + ..., Q1-2 + Q2-2 + ..., ...) and return it. *)
let expand_states qs a =
  merge_statevecs (List.map (fun q -> expand_state q a) qs) 

(* return a binding of the form:
    [ [t11;...;t1m]; ... [tk1;...;tkm]]
   each block [t11;...;t1m] shares the same environment
*)
(* let mk_binding _ termss = termss *)

(** binding_array_nt[f] contains a list of bindings for nonterminal f (int), i.e., a list of
    tuples (ts, qs) such that ts are terms that f was applied to under states qs, where qs is a
    reference to a list of states (ints), and ts is a list of tuples (i, j, asW) such that
    nonterminal f was applied to arguments
    f a11 a12 .. a1X a21 .. a2Y .. aP1 .. aPZ
    where tab_id_terms[asW] translates to a list of terms aW1 .. aWR for some R, and term aW1 was
    i-th on the list of arguments and term aWR was j-th on the list of arguments applied to f.
    In short, this is used to tell what terms where which arguments of f under what states. *)
let binding_array_nt = ref [||]

(** binding_array_var[f][i] contains terms in head form (h, [ID..]) that were i-th argument
    (0-indexed) to nonterminal f (int). *)
let binding_array_var = ref [||]

(** array_headvars[f] is a list of head variables in nonterminal's definition, i.e., variables
    that are applied to something. *)
let array_headvars = ref [||]

(** array_st_of_nt[f] is a list of states under which f was applied if f's definition has no
    variables in head position and Flags.eager is true. *)
let array_st_of_nt = ref [||]

let print_states qs =
  List.iter (fun q -> print_string ((id2state q)^",")) qs

let print_binding_and_qs (binding,qsref) =
   List.iter (fun (i,j,id1) ->
       print_string ("("^(string_of_int i)^","^(string_of_int j)^","^(string_of_int id1)^"), "))
   binding; 
   print_string "::";
   print_states !qsref;
   print_string "\n"

let print_binding binding =
   List.iter (fun (i,j,id1) ->
       print_string ("("^(string_of_int i)^","^(string_of_int j)^","^(string_of_int id1)^"), "))
   binding; 
   print_string "\n"

let print_binding_array() =
  print_string "bindings (nt --> bindings list )\n";
  for f=0 to Array.length !binding_array_nt - 1 do
    print_string ((Grammar.name_of_nt f)^":\n");
    List.iter print_binding_and_qs (!binding_array_nt).(f)
  done

(** Increasing counter for fresh identifiers for aterms (all terms and subterms in head form). *)
let terms_idref = ref 0
let new_terms_id() =
  let x = !terms_idref in
    (terms_idref := x+1; x)

(** Reverse of fst tab_id_terms, i.e., tab_id_terms[tab_terms_id[aterms]] = (aterms, _, _). *)
let tab_terms_id = Hashtbl.create 100000

(*
let lookup_aterms aterms =
  try
    Hashtbl.find tab_terms_id aterms
  with Not_found ->
    let id = new_terms_id() in
     (Hashtbl.add tab_terms_id aterms id;  id)
*)
(* tables that associate a list of terms [t1;...;tk] with its identifier *)

let id2aterms id =
  let (aterms,_,_)=(!tab_id_terms).(id) in aterms
let id2terms id =
  let (_,terms,_)=(!tab_id_terms).(id) in terms
let id2vars id =
  let (_,_,vars)=(!tab_id_terms).(id) in vars


let print_tab_id_terms() =
  print_string "Id --> Terms\n";
  for id=0 to !terms_idref-1 do
   if (!termid_isarg).(id) then 
    let terms = id2terms id in
    if terms=[] then ()
    else
    (
     print_int id;
     print_string ":";
     List.iter (fun t -> print_term t; print_string ", ") terms;
     print_string "\n")
   else ()
  done
  
let arity_of_term id =
 let (aterms,_,_) = lookup_id_terms id in
   List.length aterms

let rec add_index rho i =
  match rho with
    [] -> []
  | termsid::rho' -> (* for each args_id *)
    let n = List.length (id2terms termsid) in (* check how many terms are under args_id *)
(*       if n<9 then *)
    let j = i+n in
    (i,j-1,termsid)::(add_index rho' j) (* each termsid is converted to (first_term_number, last_term_number, termsid), like (0, 3, ...);(4, 5, ...);(6, 11, ...), i.e., start and end positions on a concatenated list of all terms *)

(* identifier of [t1;...;tk] to a set of non-terminals
   whose variables may be bound to [t1;...;tk] *)
(** tab_termid_nt[as] contains tuples (f, ts, qs) of nonterminals f, head terms ts, and states qs
    that were applied to list of terms tab_id_terms[as] and either Flags.eager is false or
    f has a head variable in its definition. *)
let tab_termid_nt = ref [| |] (*Hashtbl.create 10000 *)

let register_dep_termid_nt id nt termss qs =
  (!tab_termid_nt).(id) <-
      let x = (!tab_termid_nt).(id) in
(*      if List.mem (nt,termss,qs) x then x
      else
*)      (nt,termss,qs)::x
(*       merge_and_unify compare [(nt,termss,qs)] (!tab_termid_nt).(id)
*)

let lookup_dep_termid_nt id =
  (!tab_termid_nt).(id) 

(** When there was an enqueued node f [id1, id2, ...] for some nonterminal f and args id id1, id2,
    ... and with states qs. ids are converted to a list of arguments through tab_id_terms.
    If we join all these lists, we get arg1, arg2, ..., where the position of each argument is
    position of argument in its idX plus length of arguments of previous lists that id(1..X-1)
    stand for.
    This function prepends to bindings a tuple (A, ref qs), where A is a list of (n, m, id), where
    id is the args_id from tab_id_terms, and n, n+1, ..., m are numbers that represent which
    arguments does that list stand for (e.g., arg3, arg4 in f arg1 arg2 arg3 arg4 arg5). *)
(* TODO f not needed *)
let insert_nt_binding f rho qs bindings = 
  let rho' = add_index rho 0 in
  (rho', ref qs)::bindings (* prepend to bindings add_index and states *)


(** tab_variableheadnode[f][i] is a list of processed nodes that have variable (f,i) as head,
    i.e., i-th variable in definition of nonterminal f. *)
let tab_variableheadnode = ref [||] (* Hashtbl.create 10000 *)

let register_VariableHeadNode v (noderef: node ref) =
  let (nt,i) = v in
  let a = (!tab_variableheadnode).(nt) in
    a.(i) <- noderef::a.(i)
(*
  try 
    let x = Hashtbl.find tab_variableheadnode v in
      x := noderef::!x
  with Not_found ->
    Hashtbl.add tab_variableheadnode v (ref [noderef]) 
*)

let lookup_VariableHeadNode (nt,i) =
   (!tab_variableheadnode).(nt).(i)
(*
  try
     !(Hashtbl.find tab_variableheadnode v)
  with Not_found -> []
*)

(** Prepends term to list terms if it is not already there. Returns tuple of resulting list and
    boolean whether it was prepended to list. *)
let insert_var_binding term terms =
  if List.mem term terms then (terms,false)
  else (term::terms,true)

(*  merge_and_unify compare [term] terms
*)

let print_aterm (term,termss) =
  print_term term;
  List.iter (fun terms -> 
    print_string "[";
    List.iter (fun t ->
       print_string "(";
       print_term t;
       print_string ") ") terms;
    print_string "]";
   ) termss
     

let print_states qs =
  List.iter (fun q -> print_string ((id2state q)^" ")) qs

let print_node (aterm,qs) =
  print_aterm aterm;
  print_string ":";
  print_states qs

(*
let nodequeue = ref ([], [])
let clear_nodequeue() = (nodequeue := ([], []))
let enqueue_node node =
(*   print_string "Enqueued:"; print_node node; print_string "\n";*)
   Utilities.enqueue node nodequeue

let dequeue_node () =
   Utilities.dequeue nodequeue

let enqueue_nodes nodes =
   List.iter enqueue_node nodes
*)

(** Queue of nodes to process as a list of (t, qs), where t is a term in head form (H, [ID..]), and
    qs is a list of states (ints). The queue eventually processes all (t, qs) combinations that are
    possible during reducing the starting symbol, and more (some unnecessary terms may be analyzed,
    such as in K t id, and some unnecessary states may be analyzed). *)
let nodequeue = ref []

let clear_nodequeue() = (nodequeue := [])
let enqueue_node node =
(*   print_string "Enqueued:"; print_node node; print_string "\n";*)
   nodequeue := node::!nodequeue

let dequeue_node () =
   match !nodequeue with
     [] -> None
   | x::q -> (nodequeue := q; Some(x))

let enqueue_nodes nodes =
  List.iter enqueue_node nodes

(* TODO *)
let expand_varheadnode term (node: node ref) =
  let (aterm,qs) = !node in
  let (h,termss) = (*decompose_aterm*) aterm in
    match h with
      Hvar(x) ->
        let (h',terms)=term in
	   enqueue_node ((h', terms@termss),qs) 
    | _ -> assert false

(** Iterates (expand_varheadnode term) over everything in tab_variableheadnode[nt_id][arg_id] *)
let expand_varheadnodes f i term =
  let nodes = lookup_VariableHeadNode (f,i) in (* tab_variableheadnode[nt_id][arg_id] = [...] *)
   List.iter (expand_varheadnode term) nodes

(** Called when term was i-th argument in a call f arg1 arg2 ...
    It makes sure that binding_array_var[f][i] contains terms (H, [ID..]) that were
    i-th argument to nonterminal f, and calls expand_varheadnodes f i term when it was the first
    time adding it to binding_array_var. *)
let register_binding_singlevar f i term =
  let tab = (!binding_array_var).(f) in (* binding_array_var[nt_id][arg_id] = [...] *)
  let (binds,changed) = insert_var_binding term tab.(i) in (* making sure term is in binding_array_var[nt_id][arg_id] *)
  if changed then (* if it was added just now *)
    (tab.(i) <- binds; (* persist the addition *)
       expand_varheadnodes f i term)
   else
      ()

let lookup_binding_var (f,i) = 
   (!binding_array_var).(f).(i)

(** converts rho to lists of args in form (H, [ID..]) as they would appear in
    f arg1 arg2 ...
    after all args_id lists of arguments were concatenated.
    Then it calls
    register_binding_singlevar f i arg_i
    for each arg_i = arg1, arg2, ..., i.e., that arg_i was i-th argument to which f was applied *)
let rec register_var_bindings f rho i =
  match rho with
    [] -> ()
  | termsid::rho' ->
    let aterms = id2aterms termsid in (* convert args_id back to a list of (H, [ID..]) *)
    let aterms' = indexlist aterms in (* numbering these terms *)
    List.iter (* for each term register_binding_singlevar f global-numbering-id aterm *)
      (fun (j,aterm)-> register_binding_singlevar f (i+j) aterm)
      aterms';
    register_var_bindings f rho' (i+List.length aterms) (* recursively *)

let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
    qref := merge_and_unify compare qs !qref

let register_binding f rho qs =
  (* termid_isarg[args_id] contains info if it was ever used as argument *)
  (* binding_array_nt[f] contains a list of
     ((number of first term in app, number of last term in app, args_id for first bundle of terms in app)::..., states under which visited) *)
  List.iter (fun id -> (!termid_isarg).(id) <- true) rho;
  (!binding_array_nt).(f) <- (insert_nt_binding f rho qs (!binding_array_nt).(f));
  register_var_bindings f rho 0
let lookup_bindings_for_nt f =
  (!binding_array_nt).(f)

let merge_states qs1 qs2 = merge_and_unify compare qs1 qs2
let diff_states qs1 qss2 = List.filter (fun q -> not(List.mem q qss2)) qs1

(* aterm -> ref (aterm, qs) *)

module HType = struct type t=aterm;; let equal i j = i=j;; let hash = Hashtbl.hash_param 100 100 end
module ATermHashtbl = Hashtbl.Make(HType)

(** nodetab[aterm] = (aterm, qs), where qs is a list of states under which term aterm (in head
    form) was processed. *)
let nodetab = ATermHashtbl.create 100000

let register_newnode (aterm, qs) = 
  if ATermHashtbl.mem nodetab aterm then assert false;
(*  print_string "Registered:"; print_node (aterm,qs); print_string "\n";*)
  let node = ref (aterm,qs) in
  ATermHashtbl.add nodetab aterm node; (* make term (H, [ID..]) point at list of states *)
    node

let lookup_nodetab aterm = 
  try
    Some(ATermHashtbl.find nodetab aterm)
  with Not_found -> None

(** Processing a termss under states qs, termss = term1, term2, ... in (H, [ID..]) format *)
let expand_terminal a termss qs =
  let print_trtab() : unit =
    (print_string "trtab[";
    print_string a;
    print_string "] on first arg:";
    (List.iter (fun s ->
        print_int s;
        print_string " -> ";
        (try let a = (Hashtbl.find trtab (s,a)) in (match Array.length a with
          | 0 -> print_string "."
          | _ -> List.iter (fun s2 -> print_int s2; print_string " ") a.(0))
        with Not_found -> print_string "-"); print_string ",") qs)); print_string "\n" in
  print_trtab();
  print_string "expand_terminal ";
    print_string a;
    print_string " under states ";
    List.iter (fun s -> print_int s; print_string " ") qs;
    print_string "\n";
  let aterms = termss in
   let qss = expand_states qs a in  
        (* qss = [Q1;...;Qk] where Qi is the set of the possible states for the i-th child *)
   let aterms' = Utilities.indexlist aterms in
   print_trtab();
   List.iter (fun (i,aterm) ->
       if qss.(i)=[] then () else print_string "enqueued args under"; Array.iter (fun a -> print_string "["; List.iter (fun s -> print_int s; print_string " ") a; print_string "] ") qss; print_string "\n"; enqueue_node (aterm, qss.(i))) aterms'
   (* for each i-th argument, if the set of states is not empty, enqueue these terms under
      possible states *)


let states_of_node node =
  let (_,qs) = !node in qs

let update_states_of_node node qs =
  let (aterm,_)= !node in node := (aterm,qs)

(** Returns size of term as number of non-application terms on left-hand size of application (not number of terminals/nonterminals) *)
let rec size_of_appterm t =
 match t with
   App(t1,t2) ->
     ( match t1 with
          App(_,_) -> size_of_appterm t1 + size_of_appterm t2
        | _ -> 1+size_of_appterm t2)
 | _ -> 0
 
let size_of_rules r =
  Array.fold_left (fun s (_,t) -> s+ size_of_appterm t) 0 r

let term2head h =
   match h with
    Var(x) -> Hvar(x)
  | NT(f) -> Hnt(f)
  | T(a) -> Ht(a)
  | _ -> assert false
  
let vars_in_aterm (h,ids) =
  let vs1 = match h with Hvar(x)->[x] | _ -> [] in
    List.fold_left
            (fun vs id ->
	      merge_and_unify compare vs
	         (id2vars id)) vs1 ids 

let vars_in_aterms aterms =
 List.fold_left
 (fun vars aterm ->
    merge_and_unify compare vars (vars_in_aterm aterm))
  [] aterms

let rec convert_term t =
  let (h,terms)=Grammar.decompose_term t in
  if terms=[] then (term2head h, []) (* term2head just replaces Xxx with Hxxx constructor with same arg, but only for var, nt, and t *)
   else
     let aterms = List.map convert_term terms in (* recursively in arg terms *)
     let vars = vars_in_aterms aterms in (* get ascending list of var ids *)
     let id =
       try
         Hashtbl.find tab_terms_id aterms (* find list of args in tab_terms_id to get its id *)
       with Not_found ->
         ( let id = new_terms_id() in (* or make a fresh id *)
           Hashtbl.add tab_terms_id aterms id; (* name these args with that id *)
           (!tab_id_terms).(id) <- (aterms,terms,vars); (* save in tab_id_terms what list of terms is under that id - converted arg terms, original arg terms, list of vars used inside *)
         id)
     in
     (term2head h, [id]) (* return just the head and id of list of args, note that this fun will only return [] or [id] in snd *)

let dummy_aterm = (Hnt(-1), [])

let init_tab_id_terms g =
 let size = size_of_rules g.r in
 tab_id_terms := Array.make size ([],[],[]); (* for each a-term, i.e., @ x t, where x is not an application *)
 termid_isarg := Array.make size false;
 normalized_body := Array.make (Array.length g.r) (-1,dummy_aterm); (* convert each rule to a normalized form and store in this global array along with its arity (this is ref) *)
  for f=0 to Array.length g.r - 1 do
    let (arity,body)=Grammar.lookup_rule f in
    let u = convert_term body in
    (!normalized_body).(f) <- (arity,u) (* normalized_body now contains (arity, (H, [ID])), where H is a var/nonterminal/terminal and ID points in tab_id_terms at list of terms normalized to (H, [ID]) or (H, []) if there are no args *)
  done     

let init_expansion q0 =
 ATermHashtbl.clear nodetab;
(* Hashtbl.clear tab_variableheadnode; *)
 clear_nodequeue ();
 let g = !(Grammar.gram) in
 let num_of_nts = Array.length g.nt in
 init_tab_id_terms g; (* converts shape of nodes to head+list-of-args and caches each list-of-args in tab_id_terms *)
 binding_array_nt := Array.make num_of_nts []; (* binding_array_nt[nt_id] = [] *)
 binding_array_var := Array.make num_of_nts [||]; (* binding_array_var[nt_id][arg_id] = [] *)
 for i=0 to num_of_nts-1 do
   (!binding_array_var).(i) <- Array.make (arity_of_nt i) []
 done;
  tab_variableheadnode := Array.make num_of_nts [||];
  for i=0 to num_of_nts-1 do
    (!tab_variableheadnode).(i) <- Array.make (arity_of_nt i) [] (* tab_variableheadnode[nt_id][arg_id] = [] *)
  done;
 enqueue_node ((Hnt(0), []), [q0]) (* enqueue first nonterminal with no args and first state *)

let childnodes (h,termss) = 
(* we need to compute child nodes explicitly, 
  since aterms in the queue have not been registered yet.
  To avoid duplicated work, we may wish to register nodes immediately *)
  match h with
     Hnt(f) ->
          let (_,body) = lookup_body f in [body]
   | Hvar(v) ->
         let terms = lookup_binding_var v in
           List.map (fun (h,terms) -> (h,terms@termss)) terms;
   | _ -> assert false

let process_node (aterm,qs) = 
     let (h, termss) = decompose_aterm aterm in
     match lookup_nodetab aterm with
       Some(node) -> (* aterm has been processed before *)
        begin
         let qs' = states_of_node node in
         let qs'' = diff_states qs qs' in
         if qs''=[] then (* states qs have been processed before *)
           ()
         else begin
           update_states_of_node node (merge_states qs' qs''); (* update states in nodetab *)
           match h with
             Ht(a) -> expand_terminal a termss qs''
            | Hnt(f) -> (* re-process children with new states *)
              let (_,rho) = aterm in
              add_binding_st f rho qs'';
              let aterms = childnodes aterm in
                List.iter
                 (fun aterm1 -> enqueue_node (aterm1,qs'')) aterms
            | Hvar _ -> (* re-process children with new states *)
              let aterms = childnodes aterm in
                List.iter
                 (fun aterm1 -> enqueue_node (aterm1,qs'')) aterms
          end
        end
    | None -> (* aterm has not been processed *)
      let node = register_newnode (aterm,qs) in (* nodetab[aterm] = (aterm, qs) *)
       match h with
         Ht(a) -> expand_terminal a termss qs
       | Hvar(x) ->
          let (_,termids)=aterm in
          let terms = lookup_binding_var x in
           (List.iter (fun (h,terms) -> enqueue_node ((h,terms@termids),qs)) terms;
            register_VariableHeadNode x node)
       | Hnt(f) -> 
         let (_,body) = lookup_body f in (* TODO arity not used *)
         let (_,rho) = aterm in
         (register_binding f rho qs;
          (* registering that this nonterminal f used args rho with
             states qs,
             save info that arg_ids were used as args in termid_isarg[arg_id],
             prepends to binding_array_nt[nonterminal] (rho', ref qs) *)
          enqueue_node (body, qs)) (* if node was f [ID..] = t under qs then enqueue f qs
                                      disregarding any arguments to f *)

(* let num = ref 0 *)

let rec expand() =
    match dequeue_node() with
    None -> (print_string ("size of ACG: "^(string_of_int (ATermHashtbl.length nodetab))^"\n")
           (*  print_string ("# of expansion: "^(string_of_int (!num))^"\n") *))     (* no more node to expand *)
  | Some(aterm,qs) ->
    (* num := !num+1;*) process_node(aterm,qs); expand() (* recursively process each ((head, [args id]); state) *)

(** tab_linearity[terminal][i] = true iff terminal has transitions to at most one state in i-th
    argument. Initialized in Saturate.mk_linearity_tab. *)
let tab_linearity: (string, bool array) Hashtbl.t = Hashtbl.create 100

(* identifier of [t1;...;tk] --> identifiers of [s1;...;sl] 
   that depend on the value of [t1;...;tk];
   in other words, if id is mapped to [id1;...;idk] and
   the type of id has been updated, the types of id1,...,idk should
   be recomputed 
let tab_penv_binding = Hashtbl.create 10000
*)
(** tab_penv_binding[as] contains a list of identifiers of lists of arguments (aterms) asX such
    that term tab_id_terms[asX] was applied with nonterminal containing tab_id_terms[as]
    substituting one of more variables present in snd tab_id_terms[as] (i.e., somewhere in the
    whole applicative term).
    In other words, these are the aterms that as is substituted into. *)
let tab_penv_binding = ref [| |]

(* identifier of [t1;...;tk] ---> a list of [(i,j,id1);...]
  [(i1,j1,id1);...;(ik,j1,idk)] being an element of the list
  means that the i_x-th to j_x-th free variables in [t1;...;tk]
  may be bound to the terms represented by id_x 
let tab_binding_env: (termid, (int*int*termid) list list) Hashtbl.t = Hashtbl.create 10000
*)

(** tab_binding_env[as] describes which aterms (sequences of terms) substitute which variables in
    term with id as.
    This as aterm was present in some nonterminal with variables numbered form 0 to K.
    Specifically, it is a list of list of tuples (i, j, vs, as'), where each list of tuples is
    one application, and in this application arguments i-j (sub-interval of 0-K) were substituted
    (specifically variables vs (list of ints from interval i-j)) with aterms with id as'.
    Intuitively, this means that as' was substituted for a variable inside as. *)
let tab_binding_env = ref [| |]

(** Appends aterm id2 to id1's list of tab_penv_binding. *)
let register_dep_penv_binding id1 id2 =
 let ids = (!tab_penv_binding).(id1) in
(*   if List.mem id2 ids then ()
   else
 *)
    (!tab_penv_binding).(id1) <-id2::ids
(*
  try
   let idsref = Hashtbl.find tab_penv_binding id1 in
    (idsref := merge_and_unify compare [id2] !idsref)
  with Not_found ->
    Hashtbl.add tab_penv_binding id1 (ref [id2])
*)
let lookup_dep_id id =
  (!tab_penv_binding).(id)
(*
  try
   let idsref = Hashtbl.find tab_penv_binding id in
     !idsref
  with Not_found -> []
*)
let register_dep_binding_env id bindings =
  (!tab_binding_env).(id) <- bindings (* only place with actual modification *)
(*
  Hashtbl.add tab_binding_env id bindings
*)

let print_mask mask =
 print_string "[";
 List.iter(fun i-> print_string((string_of_int i)^",")) mask;
 print_string "]"
 
let print_binding_with_mask binding =
   List.iter (fun (i,j,mask,id1) ->
       print_string ("("^(string_of_int i)^ "," ^(string_of_int j) ^ ",");
       print_mask mask;
       print_string(", "^(string_of_int id1)^"), "))
   binding; 
   print_string "\n"

let print_tab_binding_env() =
  print_string "dependency info. (id --> [(i,j,id1);...])\n";
  for id=0 to Array.length !tab_binding_env - 1 do
    if (!termid_isarg).(id) then
     (print_int id; print_string ":\n";
      List.iter print_binding_with_mask (!tab_binding_env).(id))
  done

(* TODO unused
let register_dep_env_binding env (id:termid) =
  List.iter (fun (_,_,_,id1)-> register_dep_penv_binding id1 id) env
*)

let lookup_dep_id_envs id =
  (!tab_binding_env).(id)
(*
  try
    Hashtbl.find tab_binding_env id
  with Not_found -> []
*)

(** Splits a list of vars to ones less or equal to j and larger than j. *)
let rec split_vars vars j =
  match vars with
     [] -> ([], [])
   | v::vars' ->
      if v>j then ([], vars)
      else
        let (vars1,vars2)=split_vars vars' j in
	   (v::vars1,vars2)

(** Given vars of a nonterminal f and bindings (i, j, asX) with arguments that were substituting
    some of these vars, it returns tuples (i, j, vs, asX) with vs being all vars between i and j,
    inclusive. *)
(* TODO why not do it in the first fun? *)
let rec mk_binding_with_mask vars binding: (int * int * int list * int) list =
  match binding with
    [] -> []
  | (i, j, id)::binding' ->
      let (vars1,vars2) = split_vars vars j in
        if vars1=[] then
	   mk_binding_with_mask vars2 binding'
        else
(*          let vars1c = List.filter (fun i->not(List.mem i vars1)) (fromto i (j+1)) in *)
          (i, j, vars1, id)::(mk_binding_with_mask vars2 binding')

(** Given a list of variables v1, v2, ... from a nonterminal f and bindings from application
    f as1 as2 ..., where asX translates to lists of terms through tab_id_terms, it returns all
    bindings (i, j, asY) such that i <= vK <= j for some K, i.e., that at least one of terms in
    tab_id_terms[asY] was substituted for some variable in nonterminal f. *)
let rec filter_binding vars binding =
  match binding with
    [] -> []
  | (i,j,id)::binding' ->
      match vars with
         [] -> []
       | v::vars' ->
           if v<i then filter_binding vars' binding
	   else if v<=j then
	      (i,j,id)::(filter_binding vars' binding')
	   else filter_binding vars binding'

(** Computes all aterms identifiers present in a list of binding tuples, without duplicates. *)
let ids_in_bindings bindings =
  let ids =
    List.fold_left (fun ids binding ->
       List.rev_append (List.map (fun (_,_,id)->id) binding) ids
    ) [] bindings
  in
    delete_duplication_unsorted ids

(** Called for each term with term_id equal to id, that has free variables var, such that this
    term was an argument to a nonterminal. *)
let mk_binding_depgraph_for_terms id vars =
  if vars = [] then
     register_dep_binding_env id [[]]
  else
    let f = fst(List.hd vars) in (* figure out in which nonterminal the term is defined using
                                    variable id *)
    let vars' = List.map snd vars in (* get indexes of variables in term f *)
   let bindings = (!binding_array_nt).(f) in
   let bindings' =
     delete_duplication_unsorted (* sorts and removes duplicates *)
      (List.rev_map (fun (binding,_)->filter_binding vars' binding) bindings)
(*
     List.fold_left
       (fun bindings1 (binding,_) ->
         let b = filter_binding vars' binding in
   	   if List.mem b bindings1 then bindings1
	   else b::bindings1)
       [] bindings
*)       
   in
   let bindings_with_mask =
      List.rev_map (mk_binding_with_mask vars') bindings' (* tuples (i, j, vs, as) where as was
                                                             substituted for variables vs from
                                                             vars' *)
   in
   let ids = ids_in_bindings bindings' in (* asX that are substituted into f's variables *)
(*   
   let bindings_with_mask =
    List.fold_left
      (fun bindmasks (binding,_) ->
        let b = mk_binding_with_mask vars' binding in
	if List.mem b bindmasks then bindmasks
	else b::bindmasks)
      [] bindings
   in
*)
     register_dep_binding_env id bindings_with_mask; (* register that term with given term id
                                                        had was present in some nonterminal and
                                                        given term sequences with id asX were
                                                        substituted for arguments i-j of this
                                                        nonterminal and specifically the list of
                                                        variables used was vsX *)
     List.iter (fun id1 -> register_dep_penv_binding id1 id) ids
     (* appending current aterm's id to tab_penv_binding[asX] if f was applied to asX making a
        substitution of some variable in aterm to asX *)
(*
     List.iter (fun env-> register_dep_env_binding env id)  bindings_with_mask
*)
let mk_binding_depgraph_for_termss f (termss,qsref) =
(*  List.iter mk_binding_depgraph_for_terms termss;*)
  let qs = !qsref in (* states under which f was applied *)
  List.iter (fun (_,_,id) -> register_dep_termid_nt id f termss qs) termss (* for each term to which f was applied *)

let mk_binding_depgraph_for_nt f termsss =
  (* when no vars are only in arguments of nonterminals and terminals *)
  if (!array_headvars).(f)=[] && !Flags.eager then
    List.iter (fun (_,qsref)-> (* states under which f was applied *)
         (!array_st_of_nt).(f) <-
	      merge_and_unify compare (!array_st_of_nt).(f) !qsref)
    termsss	      
    (* if no variable occurs in the head position,
       we do not use binding information to compute the type of f *)
  else
    List.iter (mk_binding_depgraph_for_termss f) termsss

(** array_dep_nt_termid[f] is a list of as ids such that tab_terms_id[as] expanded to applicative
    form (i.e., recursively) contains nonterminal f somewhere and this term was used as an
    argument to some nonterminal. *)
let array_dep_nt_termid = ref [| |]

(** array_dep_nt_nt[f] contains all nonterminals (int) that have f present in their body except
    for ones present in array_dep_nt_nt_lin[f]. *)
let array_dep_nt_nt = ref [| |]

(** If Flags.incremental is false then array_dep_nt_nt_lin[f] contains list of nonterminals g that
    have f present in their body exactly once at root or applied a number of times to a terminal,
    i.e., t1 .. (t2 .. (tN (f arg1 .. argK) ..) ..) .. for some terminals tX and terms argY. *)
let array_dep_nt_nt_lin = ref [| |]

let print_dep_nt_nt_lin() =
 for i=0 to Array.length (!array_dep_nt_nt_lin)-1 do
   let nts = (!array_dep_nt_nt_lin).(i) in
   if nts=[] then ()
   else
     (print_string ((name_of_nt i)^" linearly occurs in ");
      List.iter (fun j-> print_string ((name_of_nt j)^",")) nts;
      print_string "\n")
 done

let init_array_dep_nt_termid() =
  let n = Array.length (!binding_array_nt) in (* number of nonterminals *)
  array_dep_nt_termid := Array.make n [] (* a list for each nonterminal *)

let init_array_dep_nt_nt() =
  let n = Array.length (!binding_array_nt) in
     array_dep_nt_nt := Array.make n [];
     array_dep_nt_nt_lin := Array.make n []

(* nt occurs in the term id *)
let register_dep_nt_termid nt id =
  let ids = (!array_dep_nt_termid).(nt) in
  (* this function can never be called with the same (nt,id) pair *)
  let ids' = id::ids (*merge_and_unify compare [id] ids*) in
   (!array_dep_nt_termid).(nt) <- ids'

let register_dep_nt_nt nt1 nt2 =
  let nts = (!array_dep_nt_nt).(nt1) in
  let nts' = merge_and_unify compare [nt2] nts in
   (!array_dep_nt_nt).(nt1) <- nts'

let register_dep_nt_nt_lin nt1 nt2 =
  let nts = (!array_dep_nt_nt_lin).(nt1) in
  let nts' = merge_and_unify compare [nt2] nts in
   (!array_dep_nt_nt_lin).(nt1) <- nts'

      

let lookup_dep_nt_termid nt =
  (!array_dep_nt_termid).(nt)
let lookup_dep_nt_nt nt =
  (!array_dep_nt_nt).(nt)
let lookup_dep_nt_nt_lin nt =
  (!array_dep_nt_nt_lin).(nt)

(** List of all nonterminals in terms without duplicates. *)
let rec nt_in_terms terms =
  match terms with
   [] -> []
 | t::terms' -> merge_and_unify compare (Grammar.nt_in_term t) (nt_in_terms terms')

let merge_nts_lin (nts1,nts2) (nts3,nts4) =
 let (nts11,nts12) =
    List.partition (fun f->List.mem f nts3 || List.mem f nts4) nts1 in
 let (nts31,nts32) =
    List.partition (fun f->List.mem f nts1 || List.mem f nts2) nts3 in
   (merge_and_unify compare nts12 nts32,
    merge_and_unify compare nts11
      (merge_and_unify compare nts31 
      (merge_and_unify compare nts2 nts4)))

(** Takes all nonterminals L in position at either term = L1, L1 arg1 .. argK, or
    t1 (.. (tN (L1 ..) ..) .., where tX are terminals, where L additionally satisfy the condition
    that they appear exactly once in the term. It returns ([L1; ..], [N1; ..]), where NX are
    other nonterminals present in the term.
    Intuitively, it returns on the left all nonterminals that have have a sequence (possibly
    empty) of terminals applied to them and appear exactly once in the term, and the rest of
    nonterminals on the right. *)
let rec nt_in_term_with_linearity term =
   match term with
     Var(_) -> ([], [])
   | T(_) ->  ([], [])
   | NT(f) -> ([f], [])
   | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
       (match h with
          NT(f) -> let nts = nt_in_terms terms in
	           if List.mem f nts then ([],nts) (* if head nt used twice *)
                   else ([f],nts) (* if head nt used once *)
	| Var(_) -> ([], nt_in_terms terms)
	| T(a) ->
	    let linearity_info = Hashtbl.find tab_linearity a in (* mapping if i-th arg maps to
                                                                    at most one state *)
	      nt_in_terms_with_linearity terms linearity_info 0 ([],[])
	| _ -> assert false)
	
and nt_in_terms_with_linearity terms linearity_info i (nts1,nts2) =
  match terms with (* iteration over terms and linearity info simultaneously *)
   [] -> (nts1,nts2) 
 | t::terms' ->
     let (nts1',nts2') =
        if linearity_info.(i) then
          nt_in_term_with_linearity t (* recursively *)
	else ([], Grammar.nt_in_term t) (* all nt in term *)
     in
     let (nts1'',nts2'') = merge_nts_lin (nts1',nts2') (nts1,nts2) in
       nt_in_terms_with_linearity terms' linearity_info (i+1) (nts1'',nts2'')


let mk_binding_depgraph() =
  tab_termid_nt := Array.make !terms_idref []; (* array of lists for each head term (aterm) *)
  tab_binding_env := Array.make !terms_idref [];
  tab_penv_binding := Array.make !terms_idref [];
  let n = Array.length (!binding_array_nt) in (* number of nonterminals *)
  array_headvars := Array.make n []; (* array of lists for each nonterminal *)
  array_st_of_nt := Array.make n [];
  for f=0 to n-1 do
    (!array_headvars).(f) <- (let (_,t)=Grammar.lookup_rule f in (* applicative rule definition *)
                              headvars_in_term t);
      mk_binding_depgraph_for_nt f (!binding_array_nt).(f)
  done;
  (* make dependency nt --> id (which means "id depends on nt") *)
  check_point();
  init_array_dep_nt_termid();
  for id'=0 to !terms_idref - 1 do (* for each aterm *)
   let id = !terms_idref - 1 -id' in
   if (!termid_isarg).(id) then (* that had something applied to it *)
     let (_,terms,vars) = (!tab_id_terms).(id) in (* and is in applicative form list of terms,
                                                     and has variables vars *)
     let nts = nt_in_terms terms in (* list of used nonterminals *)
     List.iter (fun nt -> register_dep_nt_termid nt id) nts
   else ()
  done;
  for id=0 to !terms_idref - 1 do
   if (!termid_isarg).(id) then
     let (_,_,vars) = (!tab_id_terms).(id) in (* for each term with given id that was an argument
                                                 to a nonterminal and had free variables vars *)
     mk_binding_depgraph_for_terms id vars
   else ()
  done;
  check_point();
  (* make dependency nt1 --> nt2 (which means "nt2 depends on nt1") *)
  init_array_dep_nt_nt();
  let g = !(Grammar.gram) in
  let n = Array.length g.nt in
    for i=0 to n-1 do
      let (_,t) = Grammar.lookup_rule i in
      let (nts1,nts2) = nt_in_term_with_linearity t in
        List.iter (fun nt-> register_dep_nt_nt nt i) nts2;
        (if !Flags.incremental then
            List.iter (fun nt-> register_dep_nt_nt_lin nt i) nts1
         else 
            List.iter (fun nt-> register_dep_nt_nt nt i) nts1)
    done;
  if !Flags.debugging then
   (print_binding_array();
    print_tab_id_terms();
    print_tab_binding_env();
    print_dep_nt_nt_lin())
  else ()
