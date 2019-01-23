open Grammar
open Utilities

(** All sequences of terms converted into head form and having the same environment
    TODO describe what environment
    have a unique identifier assigned to them. *)
type aterms_id = int
(** Head of a term in head form. *)
type head = Hnt of nameNT | Hvar of nameV | Ht of nameT
(** Aterm is a term in head form. It consists of a head and identifiers of sequences of aterms
    that are its arguments. If aterm is (h, [a1;..;aK]) and aX represents a sequence of terms
    [tX1;..;tXl] for some l then the whole aterm represents an application
    h t11 .. t1A t21 .. t2B .. tK1 .. tKZ. *)
type aterm = head * aterms_id list
(** Node that is enqueued when performing 0CFA analysis. *)
type node = aterm
type binding = (int * int * aterms_id) list

(** After the nonterminals are numbered, this is a map from nonterminals' ids to their bodies in
    head form. Bodies in head form are tuples (h, [as1; as2; ..]), where asX are integers that
    are mapped to lists of terms in head form, i.e., as1 = [a11; a12; ...]. The original tuple
    then represents
    h a11 a12 ... a1n a21 a22 ... a2m ...
    Mappings from asX to lists are in tab_id_terms. *)
let normalized_body : aterm array ref = ref [||]

let lookup_body f = (!normalized_body).(f)

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
let tab_id_terms : (aterm list * Grammar.term list * nameV list) array ref = ref [||]

(** termid_isarg[i] contains a boolean whether tab_id_terms[i] was ever used as an argument when
    expanding terms in expand, i.e., if it was a used argument to a nonterminal. *)
let termid_isarg : bool array ref = ref [||]


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

(** binding_array_nt[f] contains a list of bindings for nonterminal f (int), i.e., a list of
    tuples (ts, qs) such that ts are terms that f was applied to under states qs, where qs is a
    reference to a list of states (ints), and ts is a list of tuples (i, j, asW) such that
    nonterminal f was applied to arguments
    f a11 a12 .. a1X a21 .. a2Y .. aP1 .. aPZ
    where tab_id_terms[asW] translates to a list of terms aW1 .. aWR for some R, and term aW1 was
    i-th on the list of arguments and term aWR was j-th on the list of arguments applied to f.
    In short, this is used to tell what terms where which arguments of f under what states. *)
let binding_array_nt : binding list array ref = ref [||]

(** binding_array_var[f][i] contains terms in head form (h, [ID..]) that were i-th argument
    (0-indexed) to nonterminal f (int). *)
let binding_array_var : aterm list array array ref = ref [||]


(** array_headvars[f] is a list of head variables in nonterminal's definition, i.e., variables
    that are applied to something. *)
let array_headvars : nameV list array ref = ref [||]

let print_binding binding =
   List.iter (fun (i,j,id1) ->
       print_string ("("^(string_of_int i)^","^(string_of_int j)^","^(string_of_int id1)^"), "))
   binding; 
   print_string "\n"

let print_binding_array() =
  print_string "bindings (nt --> bindings list )\n";
  for f=0 to Array.length !binding_array_nt - 1 do
    print_string ((Grammar.name_of_nt f)^":\n");
    List.iter print_binding (!binding_array_nt).(f)
  done

(** Increasing counter for fresh identifiers for aterms (all terms and subterms in head form). *)
let next_aterms_id = ref 0
let new_aterms_id() =
  let x = !next_aterms_id in
  begin
    next_aterms_id := x + 1;
    x
  end

let aterms_count() : int = !next_aterms_id

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

let id2aterms (id : aterms_id) : aterm list =
  let (aterms,_,_)=(!tab_id_terms).(id) in aterms
    
let id2terms (id : aterms_id) : Grammar.term list =
  let (_,terms,_)=(!tab_id_terms).(id) in terms
    
let id2vars (id : aterms_id) : nameV list  =
  let (_,_,vars)=(!tab_id_terms).(id) in vars


let print_tab_id_terms() =
  print_string "Id --> Terms\n";
  for id=0 to !next_aterms_id-1 do
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
let tab_termid_nt : (int * binding) list array ref = ref [| |]

(* TODO change int to nt_id *)
let register_dep_termid_nt (id : aterms_id) (nt : int) (termss : binding) =
  (!tab_termid_nt).(id) <-
      let x = (!tab_termid_nt).(id) in
(*      if List.mem (nt,termss,qs) x then x
      else
*)      (nt,termss)::x
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
let insert_nt_binding (args : int list) bindings = 
  let iargs = add_index args 0 in
  iargs::bindings


(** tab_variableheadnode[f][i] is a list of processed nodes that have variable (f,i) as head,
    i.e., i-th variable in definition of nonterminal f. *)
let tab_variableheadnode : node ref list array array ref = ref [||]

let register_VariableHeadNode v (noderef: node ref) =
  let (nt,i) = v in
  let a = (!tab_variableheadnode).(nt) in
    a.(i) <- noderef::a.(i)

let lookup_VariableHeadNode (nt,i) =
   (!tab_variableheadnode).(nt).(i)

(** Prepends term to list terms if it is not already there. Returns tuple of resulting list and
    boolean whether it was prepended to list. *)
let insert_var_binding (term : 'a) (terms : 'a list) : 'a list * bool =
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
     
let print_node aterm =
  print_aterm aterm

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
let nodequeue : node list ref = ref []

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

let expand_varheadnode term (node: node ref) =
  let aterm = !node in
  let (h,termss) = aterm in
    match h with
      Hvar(x) ->
        let (h',terms)=term in
	   enqueue_node (h', terms@termss)
    | _ -> assert false

(** Iterates (expand_varheadnode term) over everything in tab_variableheadnode[nt_id][arg_id] *)
let expand_varheadnodes f i term =
  let nodes = lookup_VariableHeadNode (f,i) in
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

(*
let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
    qref := merge_and_unify compare qs !qref
*)

(** Register information that there was a call f args, i.e., save this as a binding in
    binding_array_nt and register in termid_isarg that args were an argument to nonterminal f. *)
let register_binding (f : int) (args : int list) =
  (* binding_array_nt[f] contains a list of
     ((number of first term in app, number of last term in app, args_id for first bundle of terms in app)::..., states under which visited) *)
  List.iter (fun id -> (!termid_isarg).(id) <- true) args;
  (!binding_array_nt).(f) <- (insert_nt_binding args (!binding_array_nt).(f));
  register_var_bindings f args 0
let lookup_bindings_for_nt f =
  (!binding_array_nt).(f)

(*
let merge_states qs1 qs2 = merge_and_unify compare qs1 qs2
let diff_states qs1 qss2 = List.filter (fun q -> not(List.mem q qss2)) qs1
*)
    
(* aterm -> ref (aterm, qs) *)
module HType = struct type t=aterm;; let equal i j = i=j;; let hash = Hashtbl.hash_param 100 100 end
module ATermHashtbl = Hashtbl.Make(HType)

(** nodetab[aterm] = (aterm, qs), where qs is a list of states under which term aterm (in head
    form) was processed. *)
(* TODO change this to set *)
let nodetab = ATermHashtbl.create 100000

(** Registering in nodetab that a new aterm is being processed. *)
let register_newnode aterm = 
  if ATermHashtbl.mem nodetab aterm then assert false;
  let node = ref aterm in
  ATermHashtbl.add nodetab aterm node;
  node

let lookup_nodetab aterm = 
  try
    Some(ATermHashtbl.find nodetab aterm)
  with Not_found -> None

(** Enqueueing all argument aterms. The terminal does not matter. *)
let expand_terminal termss =
  List.iter (fun aterm -> enqueue_node aterm) termss

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
  | Var(x) -> Hvar(x)
  | NT(f) -> Hnt(f)
  | T(a) -> Ht(a)
  | _ -> assert false
  
let vars_in_aterm ((h, ids) : aterm) : nameV list =
  let vs1 =
    match h with
    | Hvar(x) -> [x]
    | _ -> []
  in
  List.fold_left (fun vs id -> merge_and_unify compare vs (id2vars id)) vs1 ids

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
         ( let id = new_aterms_id() in (* or make a fresh id *)
           Hashtbl.add tab_terms_id aterms id; (* name these args with that id *)
           (!tab_id_terms).(id) <- (aterms,terms,vars); (* save in tab_id_terms what list of terms is under that id - converted arg terms, original arg terms, list of vars used inside *)
         id)
     in
     (term2head h, [id]) (* return just the head and id of list of args, note that this fun will only return [] or [id] in snd *)

let dummy_aterm : aterm = (Hnt(-1), [])

let init_tab_id_terms g =
  let size = size_of_rules g.r in
  tab_id_terms := Array.make size ([],[],[]); (* for each a-term, i.e., @ x t, where x is not an application *)
  termid_isarg := Array.make size false;
  normalized_body := Array.make (Array.length g.r) dummy_aterm; (* convert each rule to a normalized form and store in this global array along with its arity (this is ref) *)
  for f=0 to Array.length g.r - 1 do
    let (arity,body)=Grammar.lookup_rule f in
    let u = convert_term body in
    (!normalized_body).(f) <- u (* normalized_body now contains (arity, (H, [ID])), where H is a var/nonterminal/terminal and ID points in tab_id_terms at list of terms normalized to (H, [ID]) or (H, []) if there are no args *)
  done     

let init_expansion() =
  ATermHashtbl.clear nodetab;
  clear_nodequeue();
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
  enqueue_node (Hnt(0), []) (* enqueue first nonterminal with no args and first state *)

let childnodes (h,termss) = 
(* we need to compute child nodes explicitly, 
  since aterms in the queue have not been registered yet.
  To avoid duplicated work, we may wish to register nodes immediately *)
  match h with
     Hnt(f) -> [lookup_body f]
   | Hvar(v) ->
         let terms = lookup_binding_var v in
           List.map (fun (h,terms) -> (h,terms@termss)) terms;
   | _ -> assert false

(** Processing aterms. *)
let process_node aterm = 
  match lookup_nodetab aterm with
  | Some(node) -> (* aterm has been processed before *)
    ()
  | None -> (* the aterm has not been processed yet *)
    (* decoding arguments as aterm ids into aterms *)
    let (h, termss) = decompose_aterm aterm in
    (* saving that the aterm is already processed *)
    let node = register_newnode aterm in
    (* expanding the calls to see what aterms go in what variables *)
    match h with
    | Ht(_) ->
      (* ignore the terminal and go deeper *)
      expand_terminal termss
    | Hvar(x) ->
      let (_, h_args) = aterm in
      (* check what aterms flow into x *)
      let x_aterms = lookup_binding_var x in
      (* substitute these aterms into x and enqueue resulting application *)
      List.iter (fun (h, x_args) -> enqueue_node (h, x_args@h_args)) x_aterms;
      register_VariableHeadNode x node
    | Hnt(f) ->
      (* get body aterm *)
      let (_, h_args) = aterm in
      begin
        (* Remember in binding_array_nt that there was an application f h_args. Also remember
           that h_args were being used as an argument to a nonterminal in termid_isarg. *)
        register_binding f h_args;
        (* enqueue the body aterm ignoring all arguments *)
        enqueue_node (lookup_body f)
      end

(* let num = ref 0 *)

let rec expand() =
    match dequeue_node() with
    None -> (print_string ("size of ACG: "^(string_of_int (ATermHashtbl.length nodetab))^"\n")
           (*  print_string ("# of expansion: "^(string_of_int (!num))^"\n") *))     (* no more node to expand *)
  | Some(aterm) ->
    (* num := !num+1;*) process_node aterm; expand() (* recursively process each ((head, [args id]); state) *)

(* identifier of [t1;...;tk] --> identifiers of [s1;...;sl] 
   that depend on the value of [t1;...;tk];
   in other words, if id is mapped to [id1;...;idk] and
   the type of id has been updated, the types of id1,...,idk should
   be recomputed
   let tab_penv_binding = Hashtbl.create 10000 TODO remove old ver *)

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

let lookup_dep_id id =
  (!tab_penv_binding).(id)

let register_dep_binding_env id bindings =
  (!tab_binding_env).(id) <- bindings (* only place with actual modification *)

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

let lookup_dep_id_envs id =
  (!tab_binding_env).(id)

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
let rec filter_binding (vars : int list) (binding : binding) : binding =
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
      (List.rev_map (fun binding ->filter_binding vars' binding) bindings)
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
let mk_binding_depgraph_for_termss (f : int) (termss : binding) =
  List.iter (fun (_,_,id) -> register_dep_termid_nt id f termss) termss (* for each term to which f was applied *)

let mk_binding_depgraph_for_nt (f : int) (termsss : binding list) =
  (* when no vars are only in arguments of nonterminals and terminals *)
  if (!array_headvars).(f)=[] && !Flags.eager then
    ()
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
  | Var(_) -> ([], [])
  | T(_) ->  ([], [])
  | NT(f) -> ([f], [])
  | App(_,_) ->
    let (h,terms) = Grammar.decompose_term term in
    match h with
    | NT(f) -> let nts = nt_in_terms terms in
      if List.mem f nts then ([],nts) (* if head nt used twice *)
      else ([f],nts) (* if head nt used once *)
    | Var(_) -> ([], nt_in_terms terms)
    | T(a) ->
      (* c has no children. a has a single child, so it is linear. b has two children, but only
         one at a time is used. Even if we do b (N ..) (N ..) that yield different types, only
         one N is used as long as there is no other N present. Therefore, b is also linear. *)
      nt_in_terms_with_linearity terms 0 ([],[])
    | _ -> assert false
    
and nt_in_terms_with_linearity terms i (nts1,nts2) =
  match terms with (* iteration over terms and linearity info simultaneously *)
   [] -> (nts1,nts2) 
 | t::terms' ->
     let (nts1',nts2') = nt_in_term_with_linearity t (* recursively *) in
     let (nts1'',nts2'') = merge_nts_lin (nts1',nts2') (nts1,nts2) in
       nt_in_terms_with_linearity terms' (i+1) (nts1'',nts2'')


let mk_binding_depgraph() =
  tab_termid_nt := Array.make !next_aterms_id []; (* array of lists for each head term (aterm) *)
  tab_binding_env := Array.make !next_aterms_id [];
  tab_penv_binding := Array.make !next_aterms_id [];
  let n = Array.length (!binding_array_nt) in (* number of nonterminals *)
  array_headvars := Array.make n []; (* array of lists for each nonterminal *)
  for f=0 to n-1 do
    (!array_headvars).(f) <- (let (_,t)=Grammar.lookup_rule f in (* applicative rule definition *)
                              headvars_in_term t);
      mk_binding_depgraph_for_nt f (!binding_array_nt).(f)
  done;
  (* make dependency nt --> id (which means "id depends on nt") *)
  check_point();
  init_array_dep_nt_termid();
  for id'=0 to !next_aterms_id - 1 do (* for each aterm *)
   let id = !next_aterms_id - 1 -id' in
   if (!termid_isarg).(id) then (* that had something applied to it *)
     let (_,terms,vars) = (!tab_id_terms).(id) in (* and is in applicative form list of terms,
                                                     and has variables vars *)
     let nts = nt_in_terms terms in (* list of used nonterminals *)
     List.iter (fun nt -> register_dep_nt_termid nt id) nts
   else ()
  done;
  for id=0 to !next_aterms_id - 1 do
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
